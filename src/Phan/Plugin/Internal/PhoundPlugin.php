<?php

declare(strict_types=1);

use ast\Node;
use Phan\AST\ContextNode;
use Phan\Language\Context;
use Phan\Language\Element\Clazz;
use Phan\PluginV3\PluginAwarePostAnalysisVisitor;
use Phan\CodeBase;
use Phan\Language\Element\ClassElement;
use Phan\Config;

/**
 * Populates a sqlite database with callsites of class elements, as well as class, trait, and interface
 * hierarchies. Class elements include methods, static methods, properties, static properties,
 * and constants. Class heirarchies include classes and their parent-child relationships, interfaces, and traits.
 * 
 * The database can be queried to find callsites of a given class element as well as class, trait,
 * and interface hierarchy. 
 *
 * Examples:
 *
 * 1) Search for callsites of the \Foo::bar method:
 *     select * from callsites where element = '\Foo::bar' and type = 'method' order by callsite
 *
 * 2) Search for callsites of the \Foo::bar method in a specific directory 'my_directory':
 *     select * from callsites where element = '\Foo::bar' and type = 'method' and callsite like 'my_directory%' order by callsite
 *
 * 3) Search for callsites of the \Foo::baz property:
 *     select * from callsites where element = '\Foo::baz' and type = 'prop' order by callsite
 *
 * 4) Search for callsites of the \Foo::BANG constant:
 *     select * from callsites where element = '\Foo::BANG' and type = 'const' order by callsite
 * 
 * 5) Search for all classes which extend from a base class:
 * 
 * 6) Find all concrete classes using a particular trait:
 * 
 * 7) Search for all classes which implement a given interface:
 * 
 * 8) Search for 
 * 
 */
final class PhoundVisitor extends PluginAwarePostAnalysisVisitor
{

    private const MAX_COLS = 3; // table with the most columns (callsites): element, type, callsite

    // Avoid `SQLite3::prepare(): Unable to prepare statement: 1, too many SQL variables`
    // See #9: https://www.sqlite.org/limits.html
    private const BULK_INSERT_SIZE = intval(999 / self::MAX_COLS);

    /** @var SQLite3 */
    private static $db;
    private static SQLite3Stmt $callsites_prepared_insert;
    private static SQLite3Stmt $classes_prepared_insert;
    private static SQLite3Stmt $interfaces_prepared_insert;
    private static SQLite3Stmt $traits_prepared_insert;
    private static SQLite3Stmt $interface_relationships_prepared_insert;
    private static SQLite3Stmt $interface_interfaces_prepared_insert;
    private static SQLite3Stmt $class_relationships_prepared_insert;

    /** @var list<array{string,string,string}> */
    private static $callsites = [];
    private static $classes = [];
    private static $interfaces = [];
    private static $traits = [];
    private static $trait_traits = [];
    private static $interface_relationships = [];
    private static $interface_interfaces = [];
    private static $class_relationships = [];
    private static $class_interfaces = [];
    private static $class_traits = [];

    private const TABLES = [
        'callsites' => [
            'columns' => [
                'element TEXT NOT NULL',
                'type TEXT NOT NULL',
                'callsite TEXT NOT NULL',
                'id INTEGER PRIMARY KEY',
            ]
        ],
        'classes' => [
            'columns' => [
                'name TEXT NOT NULL PRIMARY KEY',
                'filepath TEXT NOT NULL',
            ]
        ],
        'interfaces' => [
            'columns' => [
                'name TEXT NOT NULL PRIMARY KEY',
                'filepath TEXT NOT NULL',
            ]
        ],
        'traits' => [
            'columns' => [
                'name TEXT NOT NULL PRIMARY KEY',
                'filepath TEXT NOT NULL',
            ]
        ],
        'trait_traits' => [
            'columns' => [
                'trait TEXT',
                'uses_trait TEXT',
            ],
            'relationships' => [
                'FOREIGN KEY(trait) REFERENCES traits(name)',
                'FOREIGN KEY(uses_trait) REFERENCES traits(name)',
            ]
        ],
        'interface_relationships' => [
            'columns' => [
                'parent TEXT',
                'child TEXT',
            ],
            'relationships' => [
                'FOREIGN KEY(parent) REFERENCES interfaces(name)',
                'FOREIGN KEY(child) REFERENCES interfaces(name)',
            ]
        ],
        'interface_interfaces' => [
            'columns' => [
                'interface TEXT',
                'implements TEXT',
            ],
            'relationships' => [
                'FOREIGN KEY(interface) REFERENCES interfaces(name)',
                'FOREIGN KEY(implements) REFERENCES interfaces(name)',
            ]
        ],
        'class_relationships' => [
            'columns' => [
                'parent TEXT',
                'child TEXT',
            ],
            'relationships' => [
                'FOREIGN KEY(parent) REFERENCES classes(name)',
                'FOREIGN KEY(child) REFERENCES classes(name)',
            ]
        ],
        'class_interfaces' => [
            'columns' => [
                'class TEXT',
                'interface TEXT',
            ],
            'relationships' => [
                'FOREIGN KEY(class) REFERENCES classes(name)',
                'FOREIGN KEY(interface) REFERENCES interfaces(name)',
            ]
        ],
        'class_traits' => [
            'columns' => [
                'class TEXT',
                'trait TEXT',
            ],
            'relationships' => [
                'FOREIGN KEY(trait) REFERENCES classes(name)',
                'FOREIGN KEY(trait) REFERENCES traits(name)',
            ]
        ],
    ];

    /**
     * @param CodeBase $code_base
     * @param Context  $context
     * @throws Exception
     */
    public function __construct(CodeBase $code_base, Context $context) {
        parent::__construct($code_base, $context);

        if (self::$db) {
            return;
        }

        $db_path = (string) (Config::getValue('plugin_config')['phound_sqlite_path'] ?? '');
        if ($db_path === '') {
            throw new Exception("You must specify a `plugin_config.phound_sqlite_path` in your phan configuration.");
        }
        self::$db = new SQLite3($db_path);

        // cleanup in reverse for foreign key constraints
        foreach (array_reverse(self::TABLES) as $table => $table_meta) {
            if (!self::$db->exec("DROP TABLE IF EXISTS $table")) {
                throw new Exception();
            }
        }

        // build tables in natural order
        foreach (self::TABLES as $table => $table_meta) {
            $column_str = implode(', ', $table_meta['columns']);

            if (isset($table['relationships'])) {
                $column_str .= ', ' . implode(', ', $table_meta['relationships']);
            }

            if (!self::$db->exec("create table $table($column_str)")) {
                throw new Exception();
            }
        }

        if (!self::$db->exec('CREATE INDEX element_and_callsite ON callsites (element, callsite)')) {
            throw new Exception();
        }

        if (!self::$db->exec("PRAGMA synchronous = OFF")) {
            throw new Exception();
        }
        if (!self::$db->exec("PRAGMA journal_mode = OFF")) {
            throw new Exception();
        }
        if (!self::$db->exec("PRAGMA foreign_keys = ON")) {
            throw new Exception();
        }
        if (!self::$db->exec("PRAGMA page_size = 4096")) {
            throw new Exception();
        }

        self::$callsites_prepared_insert  = $this->createBulkInsertPreparedStatement(self::BULK_INSERT_SIZE);
        self::$classes_prepared_insert    = $this->createBaseNodeBulkInsertPreparedStatement("classes", self::BULK_INSERT_SIZE);
        self::$interfaces_prepared_insert = $this->createBaseNodeBulkInsertPreparedStatement("interfaces", self::BULK_INSERT_SIZE);
        self::$traits_prepared_insert     = $this->createBaseNodeBulkInsertPreparedStatement("traits", self::BULK_INSERT_SIZE);
        self::$interface_relationships_prepared_insert = $this->createRelationshipBulkInsertPreparedStatement("interface_relationships", self::BULK_INSERT_SIZE);
        self::$interface_interfaces_prepared_insert    = $this->createRelationshipBulkInsertPreparedStatement("interface_interfaces", self::BULK_INSERT_SIZE);
        self::$class_relationships_prepared_insert     = $this->createRelationshipBulkInsertPreparedStatement("class_relationships", self::BULK_INSERT_SIZE);
    }

    /**
     * @param  int    $bulk_insert_size
     * @throws Exception
     */
    private static function createBulkInsertPreparedStatement(int $bulk_insert_size): SQLite3Stmt {
        $bulk_insert_sql = "INSERT OR IGNORE INTO callsites ('element', 'type', 'callsite') VALUES ";
        $bulk_insert_sql .= str_repeat("(?, ?, ?), ", $bulk_insert_size);
        $bulk_insert_sql = rtrim($bulk_insert_sql, ', ');
        $stmt = self::$db->prepare($bulk_insert_sql);
        if ($stmt === false) {
            throw new Exception();
        }
        return $stmt;
    }

    /**
     * @param string    $table_name
     */
    private static function createBaseNodeBulkInsertPreparedStatement(
        string $table_name,
        int $bulk_insert_size
    ): SQLite3Stmt {
        $bulk_insert_sql = "INSERT INTO $table_name ( 'name', 'filepath') VALUES ";
        $bulk_insert_sql .= str_repeat("(?, ?), ", $bulk_insert_size);
        $bulk_insert_sql = rtrim($bulk_insert_sql, ', ');
        if (!$stmt = self::$db->prepare($bulk_insert_sql)) {
            throw new Exception();
        }
        return $stmt;
    }

    private static function createRelationshipBulkInsertPreparedStatement(
        string $table_name,
        int $bulk_insert_size
    ): SQLite3Stmt {
        $table_meta = self::TABLES[$table_name];
        $col_names = [];
        foreach ($table_meta['columns'] as $column) {
            $col_names[] = "'" . explode(' ', $column)[0] . "'";
        }
        $insert_columns = str_replace(' TEXT', '', implode(', ', $col_names));
        $bulk_insert_sql = "INSERT INTO $table_name ($insert_columns) VALUES ";
        $bulk_insert_sql .= str_repeat("(?, ?), ", $bulk_insert_size);
        $bulk_insert_sql = rtrim($bulk_insert_sql, ', ');
        if (!$stmt = self::$db->prepare($bulk_insert_sql)) {
            throw new Exception();
        }
        return $stmt;
    }

    /**
     * @throws Exception
     */
    public function visitNew(Node $node)
    {
        try {
            $elements = (new ContextNode(
                $this->code_base,
                $this->context,
                $node
            ))->getMethodList('__construct', false, false, true);
        } catch (Exception $_) {
            return;
        }
        $this->genericVisitClassElements($elements, 'method');
    }

    /**
     * @throws Exception
     */
    public function visitMethodCall(Node $node)
    {
        try {
            $elements = (new ContextNode(
                $this->code_base,
                $this->context,
                $node
            ))->getMethodList($node->children['method'], false, false); // @phan-suppress-current-line PhanPartialTypeMismatchArgument
        } catch (Exception $_) {
            return;
        }
        $this->genericVisitClassElements($elements, 'method');
    }


    /**
     * @param Node $node a node of type AST_NULLSAFE_METHOD_CALL
     * @override
     * @throws Exception
     */
    public function visitNullsafeMethodCall(Node $node): void
    {
        $this->visitMethodCall($node);
    }

    /**
     * @throws Exception
     */
    public function visitStaticCall(Node $node)
    {
        try {
            $elements = (new ContextNode(
                $this->code_base,
                $this->context,
                $node
            ))->getMethodList($node->children['method'], true, false); // @phan-suppress-current-line PhanPartialTypeMismatchArgument
        } catch (Exception $_) {
            return;
        }
        $this->genericVisitClassElements($elements, 'method');
    }

    /**
     * Visit a node with kind `\ast\AST_CLASS_CONST`
     * @throws Exception
     */
    public function visitClassConst(Node $node) {
        try {
            $elements = (new ContextNode(
                $this->code_base,
                $this->context,
                $node
            ))->getClassConstList();
        } catch (Exception $_) {
            return;
        }
        $this->genericVisitClassElements($elements, 'const');
    }

    /**
     * Visit a node with kind `\ast\AST_STATIC_PROP`
     * @throws Exception
     */
    public function visitStaticProp(Node $node) {
        try {
            $elements = (new ContextNode(
                $this->code_base,
                $this->context,
                $node
            ))->getPropertyList(true);
        } catch (Exception $_) {
            return;
        }
        $this->genericVisitClassElements($elements, 'prop');
    }

    /**
     * Visit a node with kind `\ast\AST_PROP`
     * @throws Exception
     */
    public function visitProp(Node $node) {
        try {
            $elements = (new ContextNode(
                $this->code_base,
                $this->context,
                $node
            ))->getPropertyList(false);
        } catch (Exception $_) {
            return;
        }
        $this->genericVisitClassElements($elements, 'prop');
    }

    /**
     * Visit a node with kind `\ast\AST_NULLSAFE_PROP`
     * @throws Exception
     */
    public function visitNullsafeProp(Node $node) {
        $this->visitProp($node);
    }

    /**
     * Helper function to add class elements to the DB
     * @param  list<ClassElement> $elements
     * @param  string       $type
     * @throws Exception
     */
    public function genericVisitClassElements(array $elements, string $type): void {
        foreach ($elements as $element) {
            $element_name = $element->getFQSEN()->__toString();
            $callsite = $this->context->__toString();
            self::$callsites[] = [$element_name, $type, $callsite];

            if (count(self::$callsites) >= self::BULK_INSERT_SIZE) {
                self::doBulkWrite(self::$callsites_prepared_insert);
            }
        }
    }

    /**
     * @param  SQLite3Stmt $stmt
     * @throws Exception
     */
    private static function doBulkWrite(SQLite3Stmt $stmt): void {
        sort(self::$callsites);
        $bind_index = 1;
        foreach (self::$callsites as $callsite) {
            $stmt->bindValue($bind_index, $callsite[0], SQLITE3_TEXT);
            $bind_index++;
            $stmt->bindValue($bind_index, $callsite[1], SQLITE3_TEXT);
            $bind_index++;
            $stmt->bindValue($bind_index, $callsite[2], SQLITE3_TEXT);
            $bind_index++;
        }
        self::execStatement($stmt);
        self::$callsites = [];
    }

    /**
     * Called when visiting classes, interfaces, and traits, including anonymous 
     * versions of the same. Phan generates FQSENs consistently for anonymous classes 
     * using file modification time, i.e. if a file contains anonymous_class_83cba571, 
     * it will always contain anonymous_class_83cba571 unless/until that file is modified.
     */
    public function visitClass(Node $node) {
        if (!$this->context->isInClassScope()) {
            return;
        }

        $clazz = $this->context->getClassInScope($this->code_base);
        $filepath = $this->context->getProjectRelativePath();

        if ($clazz->isClass()) {
            self::handleClass($clazz, $filepath);

        } else if ($clazz->isInterface()) {
            self::handleInterface($clazz, $filepath);

        } else if ($clazz->isTrait()) {
            self::handleTrait($clazz, $filepath);

        } else {
            throw new Exception("Unknown class type: $clazz");
        }
    }

    /** 
     * Processes a class to obtain its name, filepath, relationships, interfaces, and traits.
     */
    private static function handleClass(Clazz $clazz, string $filepath) {
        $name = $clazz->getFQSEN()->__toString();
        self::$classes[] = [$name, $filepath];

        if (count(self::$classes) >= self::BULK_INSERT_SIZE) {
            self::doHierarchyBulkWrite(self::$classes, self::$classes_prepared_insert);
            self::$classes = [];
        }

        if ($clazz->hasParentType()) {
            $parent_name = $clazz->getParentClassFQSEN();
            self::$class_relationships[] = [$parent_name, $name];
        }

        if (count(self::$class_relationships) >= self::BULK_INSERT_SIZE) {
            self::doHierarchyBulkWrite(self::$class_relationships, self::$class_relationships_prepared_insert);
            self::$class_relationships = [];
        }

        $impl_interfaces = $clazz->getInterfaceFQSENList();
        foreach ($impl_interfaces as $iface) {
            self::$class_interfaces[] = [$name, $iface];
        }

        if (count(self::$class_interfaces) >= self::BULK_INSERT_SIZE) {
            $stmt = self::createRelationshipBulkInsertPreparedStatement("class_interfaces", count(self::$class_interfaces));
            self::doHierarchyBulkWrite(self::$class_interfaces, $stmt);
            self::$class_interfaces = [];
        }

        $uses_traits = $clazz->getTraitFQSENList();
        foreach ($uses_traits as $trait) {
            self::$class_traits[] = [$name, $trait];
        }

        if (count(self::$class_traits) >= self::BULK_INSERT_SIZE) {
            $stmt = self::createRelationshipBulkInsertPreparedStatement("class_traits", count(self::$class_traits));
            self::doHierarchyBulkWrite(self::$class_traits, $stmt);
            self::$class_traits = [];
        }
    }

    /** 
     * Processes an interface to obtain its name, filepath, relationships, and implemented interfaces.
     */
    private static function handleInterface(Clazz $clazz, string $filepath) {
        $name = $clazz->getFQSEN()->__toString();
        self::$interfaces[] = [$name, $filepath];

        if (count(self::$interfaces) >= self::BULK_INSERT_SIZE) {
            self::doHierarchyBulkWrite(self::$interfaces, self::$interfaces_prepared_insert);
            self::$interfaces = [];
        }

        if ($clazz->hasParentType()) {
            $parent_name = $clazz->getParentClassFQSEN();
            self::$interface_relationships[] = [$parent_name, $name];
        }

        if (count(self::$interface_relationships) >= self::BULK_INSERT_SIZE) {
            self::doHierarchyBulkWrite(
                self::$interface_relationships,
                self::$interface_relationships_prepared_insert
            );
            self::$interface_relationships = [];
        }

        if (count($clazz->getInterfaceFQSENList()) > 0) {
            $impl_interfaces = $clazz->getInterfaceFQSENList();
            foreach ($impl_interfaces as $iface) {
                self::$interface_interfaces[] = [$name, $iface];
            }
        }
        
        if (count(self::$interface_interfaces) >= self::BULK_INSERT_SIZE) {
            self::doHierarchyBulkWrite(
                self::$interface_interfaces,
                self::$interface_interfaces_prepared_insert
            );
            self::$interface_interfaces = [];
        }
    }

    /** 
     * Processes a trait to obtain its name, filepath, and used traits.
     */
    private static function handleTrait(Clazz $clazz, string $filepath) {
        $name = $clazz->getFQSEN()->__toString();
        self::$traits[] = [$name, $filepath];

        if (count(self::$traits) >= self::BULK_INSERT_SIZE) {
            self::doHierarchyBulkWrite(self::$traits, self::$traits_prepared_insert);
            self::$traits = [];
        }

        $uses_traits = $clazz->getTraitFQSENList();
        foreach ($uses_traits as $trait) {
            self::$trait_traits[] = [$name, $trait];
        }

        if (count(self::$trait_traits) >= self::BULK_INSERT_SIZE) {
            $stmt = self::createRelationshipBulkInsertPreparedStatement("trait_traits", count(self::$trait_traits));
            self::doHierarchyBulkWrite(self::$trait_traits, $stmt);
            self::$trait_traits = [];
        }
    }

    /**
     * Bind any 2 values to a row for both tables and relationship tables, just because they have the same
     * # of columns. if base tables diverge in # of columns from relationship tables, this breaks.
     */
    private static function doHierarchyBulkWrite(array $nodes, SQLite3Stmt $stmt): void {
        $bind_index = 1;
        foreach ($nodes as $node) {
            $stmt->bindValue($bind_index, $node[0], SQLITE3_TEXT);
            $bind_index++;
            $stmt->bindValue($bind_index, $node[1], SQLITE3_TEXT);
            $bind_index++;
        }
        self::execStatement($stmt);
    }

    private static function execStatement(SQLite3Stmt $stmt) {
        if (!$stmt->execute()) {
            throw new Exception();
        }
        if (!$stmt->reset()) {
            throw new Exception();
        }
        if (!$stmt->clear()) {
            throw new Exception();
        }
    }

    /**
     * Finish pending bulk writes.
     * @throws Exception
     */
    public static function finalizeProcess(): void {
        if (count(self::$callsites) >= 0) {
            $stmt = self::createBulkInsertPreparedStatement(count(self::$callsites));
            self::doBulkWrite($stmt);
        }

        if (count(self::$classes) > 0) {
            $stmt = self::createBaseNodeBulkInsertPreparedStatement("classes", count(self::$classes));
            self::doHierarchyBulkWrite(self::$classes, $stmt);
        }
        if (count(self::$interfaces) > 0) {
            $stmt = self::createBaseNodeBulkInsertPreparedStatement("interfaces", count(self::$interfaces));
            self::doHierarchyBulkWrite(self::$interfaces, $stmt);
        }
        if (count(self::$traits) > 0) {
            $stmt = self::createBaseNodeBulkInsertPreparedStatement("traits", count(self::$traits));
            self::doHierarchyBulkWrite(self::$traits, $stmt);
        }
        if (count(self::$class_relationships) > 0) {
            $stmt = self::createRelationshipBulkInsertPreparedStatement("class_relationships", count(self::$class_relationships));
            self::doHierarchyBulkWrite(self::$class_relationships, $stmt);
        }
        if (count(self::$class_interfaces) > 0) {
            $stmt = self::createRelationshipBulkInsertPreparedStatement("class_interfaces", count(self::$class_interfaces));
            self::doHierarchyBulkWrite(self::$class_interfaces, $stmt);
        }
        if (count(self::$class_traits) > 0) {
            $stmt = self::createRelationshipBulkInsertPreparedStatement("class_traits", count(self::$class_traits));
            self::doHierarchyBulkWrite(self::$class_traits, $stmt);
        }
        if (count(self::$interface_relationships) > 0) {
            $stmt = self::createRelationshipBulkInsertPreparedStatement("interface_relationships", count(self::$interface_relationships));
            self::doHierarchyBulkWrite(self::$interface_relationships, $stmt);
        }
        if (count(self::$trait_traits) > 0) {
            $stmt = self::createRelationshipBulkInsertPreparedStatement("trait_traits", count(self::$trait_traits));
            self::doHierarchyBulkWrite(self::$trait_traits, $stmt);
        }
    }

}

use Phan\PluginV3;
use Phan\PluginV3\PostAnalyzeNodeCapability;
use Phan\PluginV3\FinalizeProcessCapability;
use Phan\PluginV3\AnalyzeFunctionCallCapability;
use Phan\AST\UnionTypeVisitor;
use Phan\Language\Element\FunctionInterface;

/**
 * Plugin to go with PhoundVisitor.
 */
final class PhoundPlugin extends PluginV3 implements PostAnalyzeNodeCapability, AnalyzeFunctionCallCapability, FinalizeProcessCapability
{

    /**
     * Returns the name of the visitor class to be instantiated and invoked to analyze a node in the analysis phase.
     * (To post-analyze a node)
     * (PostAnalyzeNodeCapability is run after PreAnalyzeNodeCapability and after analysis of child nodes)
     *
     * The class should be created by the plugin visitor, and must extend PluginAwarePostAnalysisVisitor.
     *
     * If state needs to be shared with a visitor and a plugin, a plugin author may use static variables of that plugin.
     *
     * @return string - The name of a class extending PluginAwarePostAnalysisVisitor
     */
    public static function getPostAnalyzeNodeVisitorClassName(): string
    {
        return PhoundVisitor::class;
    }

    /**
     * @param CodeBase $code_base @phan-unused-param
     * @return array<string,Closure(CodeBase,Context,FunctionInterface,list<mixed>,?Node)>
     * maps FQSEN of function or method to a closure used to analyze the function in question.
     * '\A::foo' or 'A::foo' as a key will override a method, and '\foo' or 'foo' as a key will override a function.
     * Closure Type: function(CodeBase $code_base, Context $context, Func|Method $function, array $args, ?Node $node) : void {...}
     *
     * If compatibility with older Phan versions is needed, make the param for $node optional.
     *
     * Note that $function->getMostRecentParentNodeListForCall() can be used to get the parent node list of the current call (will be the empty array if fetching it failed).
     */
    public function getAnalyzeFunctionCallClosures(CodeBase $code_base): array
    {
        // Unit tests invoke this repeatedly. Cache it.
        static $analyzers = null;
        if ($analyzers === null) {
            $analyzers = self::getAnalyzeFunctionCallClosuresStatic();
        }
        return $analyzers;
    }

    /**
     * Ensure that we track callsites in callables passed to call_user_func,
     * forward_static_call, call_user_func_array, forward_static_call_array,
     * Closure::fromCallable, etc.
     *
     * Much of the logic in here was cribbed from https://github.com/phan/phan/blob/0fd8121798fa1c77d7f7608cf36d71f0b8325880/src/Phan/Plugin/Internal/ClosureReturnTypeOverridePlugin.php#L199
     *
     * @return array<string,\Closure>
     */
    private static function getAnalyzeFunctionCallClosuresStatic(): array
    {
        /**
         * @param list<Node|int|string|float> $args
         * @throws Exception
         */
        $generic_callback = static function(
            CodeBase $code_base,
            Context $context,
            array $args
        ): void {
            $function_like_list = UnionTypeVisitor::functionLikeListFromNodeAndContext($code_base, $context, $args[0], true);
            if (\count($function_like_list) === 0) {
                return;
            }

            $elements = [];
            foreach ($function_like_list as $function) {
                if ($function instanceof ClassElement) {
                    $elements[] = $function;
                }
            }

            if ($elements) {
                $phound_visitor = new PhoundVisitor($code_base, $context);
                $phound_visitor->genericVisitClassElements($elements, 'method');
            }
        };

        /**
         * @param list<Node|int|string|float> $args
         * @throws Exception
         */
        $call_user_func_callback = static function (
            CodeBase $code_base,
            Context $context,
            FunctionInterface $unused_function,
            array $args,
            ?Node $_
        ) use ($generic_callback) : void {
            if (\count($args) < 1) {
                return;
            }
            $generic_callback($code_base, $context, $args);
        };

        /**
         * @param list<Node|int|string|float> $args
         * @throws Exception
         */
        $call_user_func_array_callback = static function (
            CodeBase $code_base,
            Context $context,
            FunctionInterface $unused_function,
            array $args,
            ?Node $_
        ) use ($generic_callback) : void {
            if (\count($args) < 2) {
                return;
            }
            $generic_callback($code_base, $context, $args);
        };

        /**
         * @param list<Node|int|string|float> $args
         * @throws Exception
         */
        $from_callable_callback = static function (
            CodeBase $code_base,
            Context $context,
            FunctionInterface $unused_function,
            array $args,
            ?Node $_
        ) use ($generic_callback) : void {
            if (\count($args) !== 1) {
                return;
            }

            $generic_callback($code_base, $context, $args);
        };

        return [
            'call_user_func'            => $call_user_func_callback,
            'forward_static_call'       => $call_user_func_callback,
            'call_user_func_array'      => $call_user_func_array_callback,
            'forward_static_call_array' => $call_user_func_array_callback,
            'Closure::fromCallable'     => $from_callable_callback,
        ];
    }

    /**
     * This is called after the other forms of analysis are finished running.
     * Useful if a PluginV3 needs to aggregate results of analysis.
     * This may be used to emit additional issues.
     *
     * This is run once per forked analysis process.
     * Some plugins using this, such as UnusedSuppressionPlugin,
     * will not work as expected with more than one process.
     * If possible, write plugins to emit issues immediately.
     * @unused-param $code_base
     * @throws Exception
     */
    public function finalizeProcess(CodeBase $code_base): void
    {
        PhoundVisitor::finalizeProcess();
    }

}

return new PhoundPlugin();
