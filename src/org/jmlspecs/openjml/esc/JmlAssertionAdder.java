/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;


import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlChoose;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlConstraintMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseCallable;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignalsOnly;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlModelProgramStatement;
import org.jmlspecs.openjml.JmlTree.JmlPrimitiveTypeTree;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSetComprehension;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementDecls;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementHavoc;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import org.jmlspecs.openjml.JmlTree.JmlStatementSpec;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefListExpression;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMonitorsFor;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;
import org.jmlspecs.openjml.Utils.JmlNotImplementedException;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCAssert;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCBreak;
import com.sun.tools.javac.tree.JCTree.JCCase;
import com.sun.tools.javac.tree.JCTree.JCCatch;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCContinue;
import com.sun.tools.javac.tree.JCTree.JCDoWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCEnhancedForLoop;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCForLoop;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCImport;
import com.sun.tools.javac.tree.JCTree.JCInstanceOf;
import com.sun.tools.javac.tree.JCTree.JCLabeledStatement;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewArray;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.tree.JCTree.JCReturn;
import com.sun.tools.javac.tree.JCTree.JCSkip;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCSwitch;
import com.sun.tools.javac.tree.JCTree.JCSynchronized;
import com.sun.tools.javac.tree.JCTree.JCThrow;
import com.sun.tools.javac.tree.JCTree.JCTry;
import com.sun.tools.javac.tree.JCTree.JCTypeApply;
import com.sun.tools.javac.tree.JCTree.JCTypeCast;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCWildcard;
import com.sun.tools.javac.tree.JCTree.LetExpr;
import com.sun.tools.javac.tree.JCTree.TypeBoundKind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

/** This class translates an attributed Java+JML AST, creating a new 
 * Java-compatible AST that includes assertions to check for all the various 
 * Java and JML conditions that need checking.
 * <P>
 * The resulting AST is an (almost) complete copy - it does not share any 
 * mutable structure with the original AST, so the original AST can be reused; 
 * it represents each identifier in a separate JCIdent, so that a succeeding 
 * Single-assignment operation can change identifier names in place.
 * <UL>
 * <LI>If the field 'fullTranslation' is true, then all AST nodes, even 
 * non-mutable nodes, such as JCLiteral, are duplicated. The copied AST may 
 * still share non-AST objects such as Name and Symbol objects, and references 
 * to MethodSpecs, TypeSpecs, and FieldSpecs.
 * <LI>If the field 'fullTranslation' is false, then, for efficiency, some node
 * classes, considered to be non-mutable, are still shared, such as JCLiteral, 
 * JCAnnotation, JCModifiers.
 * <P>
 * There are three modes of translation:
 * <UL>
 * <LI>pureCopy=true: This makes an (almost) pure copy of the AST, without 
 * converting or adding any nodes. Note that any translation mode may use 
 * pureCopy for a sub-tree. Also note that some nodes include references to 
 * other nodes in the tree (e.g., a class declaration includes a reference to 
 * its top-level compilation unit); these are appropriately translated. 
 * The 'almost' is because
 * (a) the result is still affected by the 'fullTranslation' option, and (b)
 * some nodes are expanded - type nodes are expanded to be fully-qualified types
 * and class field references will have 'this' or the fully-qualified typename
 * prepended.
 * 
 * <LI>esc=true,rac=false,pureCopy=false: This inserts all JML semantics as new 
 * Java constructs and JML assert and assume statements,
 * retaining the Java control flow statements. The result is a Java AST
 * with some JML features but is not executable.
 * 
 * <LI>rac=true,esc=false,pureCopy=false: This inserts all executable JML checks 
 * as calls to an assertionFailure method - which can dynamically choose to 
 * print out warning messages, throw exceptions, or execute a Java assert.
 * The translated AST is a transformation of the original program, but is
 * functionally equivalent to it, aside from the additional checks.
 * 
 * <LI>esc=true,rac=true,pureCopy=false: unsupported.
 * <LI>esc=false,rac=false,pureCopy=false: unsupported.
 * </UL>
 * <P>
 * With either rac or esc on, the translated AST uses only a subset of Java
 * functionality. All JML features are translated into assertions and Java statements.
 * <P>
 * Within both the rac and esc modes, subtrees may be translated with 
 * 'translatingJML' true - this should not be set by the caller, but is used to
 * translate Java constructs in JML expressions differently than Java constructs
 * in Java code.
// * <UL> -- FIXME - fix all of the following
// * <LI>Java expressions:
// * </UL>
// * <LI>binary operations - arithmetic, bit, logical all allowed in Java statements and JML assertions;
// * instanceof is allowed in Java, translated into a type relationship in JML
// * <LI>unary operations - minus and negation allowed; pre- and post-increment
// * and decrement converted to separate operations and assignment
// * <LI>assignment - retained 
// * <LI>assign-op - separated into operation and assignment
// * <LI>type cast - TBD
// * <LI>field selection - TBD
// * <LI>array index - retained, but uses JmlBBArrayAccess nodes instead of JCArrayAccess
// * <LI> 
// * <LI>object allocation - TBD
// * <LI>array allocation - TBD
// * <LI>anonymous class expression - TBD
// * <LI>...TBD
// * </UL>
// * <LI>Java statements:
// * <UL>
// * <LI>if, switch, try statements are retained
// * <LI>for, while, do, foreach statements are retained but may be transformed 
// * into other loop types to accommodate inserting loop specifications
// * <LI>variable declarations - TBD
// * <LI>local class declarations - TBD
// * <LI>method declarations, class declarations, import declarations - all retained
// * </UL>
// * <LI> JML expressions:
// * <UL>
// * <LI> binary logical operations - converted to Java equivalents
// * <LI> subtype operation - TBD
// * <LI> ... TBD
// * </UL>
// * <LI> JML statements and features:
// * <UL>
// * <LI> assert, assume statements - is esc mode, these are retained as JML statements
// * in rac mode, they are converted to RAC checks
// * <LI> method clauses: requires, ensures, signals - converted to assertions
// * </UL>
 * 
 *
 */

// DESIGN NOTE: This AST visitor operates in two modes - when translating Java
// and when translating JML. These are both implemented in the one tree visitor,
// controlled by the class field 'translatingJML'. I considered having two
// scanners, one for each mode. However, there was then a lot of code 
// duplication or similarity, with the similar code being separated into two
// classes. Also, calling the correct translation function proved to be more
// error prone than in the design with just one scanner class. For better or
// worse, the one-class design is what is implemented here.

// DESIGN NOTE: We can't simply extend a tree copier because (a) many nodes are
// transformed into nodes of a different class, and (b) many nodes produce
// multiple output nodes - e.g. statements are transformed into a series of
// statements.

public class JmlAssertionAdder extends JmlTreeScanner {

    // Parameters of this instance of JmlAssertionAdder 
    
    /** If true then every part of every AST is copied; if false then items
     * expected to be immutable such as JCLiteral, qualified ids (in import
     * statements, static type designators), JCAnnotation are not duplicated. 
     * Non-AST objects
     * such as Type, Token or JmlToken values are not duplicated in any case.
     */
    public boolean fullTranslation = true;
    
    // NOTE: We support !esc || !rac but not esc && rac.
    //@ invariant !esc || !rac;
    
    /** True if we are translating for static checks */
    public boolean esc ;
    
    /** True if we are translating for RAC */
    public boolean rac ;
    
    /** If true, we are making a pure copy */
    public boolean pureCopy;
    
    /** If true, then error messages in generated RAC code include source
     * code snippets with the customary textual ^ pointers to error locations.
     * This adds bulk to the RAC-ed program, though I've not measured whether
     * it is significant.
     */
    public boolean showRacSource;
    
    /** If true, then in the RAC translation, assume statements and assumptions
     * generated by ESC, are checked as if they were assert statements.
     */
    public boolean racCheckAssumeStatements;

    /** If true, then explicit checks are included even when the Java
     * language would catch the error itself (e.g., OpenJML will check for a
     * null reference in advance of a dereference and Java throwing a 
     * NullPointerException). This should always be true for esc, but only
     * true for rac if the appropriate option is set.
     */
    public boolean javaChecks;
    
    // Constant items set in the constructor
    
    /** The compilation context */
    final protected Context context;
    
    /** Cached value of the Log tool */
    final protected Log log;
    
    /** Cached value of the specs database */
    final protected JmlSpecs specs;
    
    /** Cached value of JmlTypes */
    final protected JmlTypes jmltypes;
    
    /** Cached value of the AST node factory */
    final protected JmlTree.Maker M;
    
    /** Cached value of the names table */
    final protected Names names;
    
    /** Cached value of the symbol table */
    final protected Symtab syms;
    
    /** Cached value of the Types tool */
    final protected Types types;
    
    /** Cached value of the Utils tool */
    final protected Utils utils;
    
    /** Cached value of the Nowarns object */
    final protected Nowarns nowarns;
    
    /** Cached value of the Attribute tool */
    final protected JmlAttr attr;
    
    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    final protected JmlTreeUtils treeutils;
    
    /** The tool to find class symbols */
    final protected ClassReader reader;
    
    /** The symbol for the runtime Utils class */
    final protected ClassSymbol utilsClass;

    /** The Name used for the result of a method */
    final protected Name resultName;
    
    /** The symbol for the variable that holds the result of a method */
    protected Symbol resultSym = null;
    
    /** The Name used for exceptions thrown in the body of a method */
    final protected Name exceptionName;
    
    /** The symbol for the variable that tracks exceptions in the body of a method */
    protected Symbol exceptionSym = null;
    
    /** The symbol for the variable that holds allocation ids to distinguish dynamically allocated objects */
    protected Symbol allocSym = null;
    
    /** The symbol for the variable that says whether an object is allocated */
    protected Symbol isAllocSym = null;
    
    /** A counter used to make distinct ids for newly allocated Objects */
    protected int allocCounter = 0;
    
    /** Exception Symbols used for various methods */
    protected Map<JCMethodDecl,Symbol> exceptionSymbols = new HashMap<JCMethodDecl,Symbol>();
    
    /** The Name used for catching exceptions thrown by called methods */
    final protected Name exceptionNameCall;
    
    /** The Name used for holding the location at which the final return or throw statement occurs */
    final protected Name terminationName;
    
    /** The symbol to go with terminationName. */
    protected Symbol terminationSym = null;

    /** Termination Symbols used for various methods */
    protected Map<JCMethodDecl,Symbol> terminationSymbols = new HashMap<JCMethodDecl,Symbol>();
    
    // Fields used and modified during translation
    // These should only be modified by visit methods
    
    /** The AST being processed when in a sub-tree of a method declaration */
    protected JmlMethodDecl methodDecl = null;
    
    /** The parent class of the method being converted, for use while the
     * declarations of the class are being walked, and while a method is
     * being translated stand-alone (without having been reached by walking
     * the tree from above).
     */
    protected JmlClassDecl classDecl = null;
    
    /** The Ident to use when translating this - starts as the this for the
     * receiver object, but can change as methods or constructors are called.
     */
    protected JCIdent currentThisId;
    
    /** The counter used to make uniquely named variables for preconditions,
     * unique within a method body. */
    int precount = 0;
    
    /** The counter used to make uniquely named variables for assertions,
     * unique within a method body. */
    protected int assertCount = 0;
    
    /** A counter that ensures unique variable names (within a method body). */
    protected int count = 0;
    
    /** A map from formal parameter to actual argument, used when translating
     * methods called within a method body; also used to map formals in inherited
     * method specs to actual arguments or to the formals in the base method.
     */
    protected Map<Symbol,JCExpression> paramActuals;
    
    /** A map from formals to a declaration of a variable that holds the formal's
     * value at method body entrance (for use by postconditions).
     */
    protected Map<Symbol,JCVariableDecl> preparams = new HashMap<Symbol,JCVariableDecl>();
    
    /** A map from specification case to a JCIdent that is a variable holding
     * the value of the precondition for that specification case.
     */
    protected Map<JmlSpecificationCase,JCIdent> preconditions = new HashMap<JmlSpecificationCase,JCIdent>();
    
    /** A map from old nodes to new ones, for use when there are node references
     * (rather than copies of trees) within an AST. In particular used to 
     * set the target fields for break and continue statements.
     */
    protected java.util.Map<JCTree,JCTree> treeMap = new HashMap<JCTree,JCTree>();
    
    /** A List used to accumulate translated definitions of a class, for cases
     * where new declarations are needed.
     */
    protected ListBuffer<JCTree> classDefs = null;
    
    /** A list to collect statements as they are being generated. */
    protected ListBuffer<JCStatement> currentStatements;

    /** A list aliased with the place to put computations of \pre expressions. */
    protected ListBuffer<JCStatement> oldStatements;

    /** The prelude statements of the current method */
    protected ListBuffer<JCStatement> initialStatements;
    
    /** A stack of 'currentStatements' . The current value of 'currentStatements'
     * is NOT on this stack. */
    protected LinkedList<ListBuffer<JCStatement>> statementStack = new LinkedList<ListBuffer<JCStatement>>();

    /** A stack of labeled statements that might be targets of continue statements */
    java.util.Stack<JCLabeledStatement> continueStack = new java.util.Stack<JCLabeledStatement>();

    /** Stack of the synthetic index (trip count) variables for loops enclosing
     * the code under current consideration.
     */
    protected java.util.List<JCVariableDecl> indexStack = new LinkedList<JCVariableDecl>();
    
    /** true when translating JML constructs, false when translating Java constructs.
     * This is set and manipulated by the visitor methods 
     */
    protected boolean translatingJML = false;
    
    /** Contains an expression that is used as a guard in determining whether expressions
     * are well-defined. For example, suppose we are translating the expression 
     * a != null && a[i] == 0. Then condition is 'true' when a!=null is translated.
     * But when a[i] is translated, 'condition' will be a != null. The well-definedness
     * check for a[i] will then be (a != null) ==> (a != null && i >= 0 && i < a.length).
     * So the full expression is well-defined only if that implication can be proved given 
     * other pre-conditions.
     */
    protected JCExpression condition;
    
    /** Set to true when we are translating a normal or exceptional postcondition. It is used
     * to be sure the correct scope is used when method parameters are used in the postcondition.
     * If a method parameter is used in a postcondition it is evaluated in the pre-state since
     * any changes to the parameter within the body of the method are discarded upon exit and
     * are invisible outside the method (i.e. in the postcondition).
     */
    protected boolean isPostcondition;
    
    /** Used to note the environment (i.e., \old label) under which we are currently
     * evaluating; null indicates the current state; an empty string indicates
     * the pre-state, otherwise it is the JCIdent of the label in the \old statement
     */
    @Nullable protected JCIdent oldenv;
    
    /** The \old label to use for the pre-state */
    final protected JCIdent preLabel;
    
    /** Used to hold the result of non-expression AST nodes */
    protected JCTree result;
    
    /** Used to hold the result of expression AST nodes, so equal to 'result'
     * when 'result' is a JCExpression. */
    protected JCExpression eresult;
    
    /** Assertions that can be changed to be feasibility checks */
    public Map<Symbol,java.util.List<JCTree.JCParens>> assumptionChecks = new HashMap<Symbol,java.util.List<JCTree.JCParens>>();
    public Map<Symbol,java.util.List<JmlTree.JmlStatementExpr>> assumptionCheckStats = new HashMap<Symbol,java.util.List<JmlTree.JmlStatementExpr>>();
    
    // FIXME - review which of these bimaps is actually needed
    
    /** A bi-map used to record the mapping between original and rewritten nodes, for reporting expression values */
    public BiMap<JCTree, JCTree> exprBiMap = new BiMap<JCTree, JCTree>();
    
    /** A bi-map used to record statement mappings for reporting counterexample paths */
    public BiMap<JCTree,JCTree> pathMap = new BiMap<JCTree,JCTree>();
    
    /** A bi-map used to record the mapping between original and rewritten method ASTs */
    public BiMap<JmlMethodDecl, JmlMethodDecl> methodBiMap = new BiMap<JmlMethodDecl, JmlMethodDecl>();

    /** A bi-map used to record the mapping between original and rewritten class ASTs */
    public BiMap<JmlClassDecl, JmlClassDecl> classBiMap = new BiMap<JmlClassDecl, JmlClassDecl>();

    /** A map from Class Symbols to an ident containing the this symbol for that class */
    public Map<Symbol,JCIdent> thisIds = new HashMap<Symbol,JCIdent>();
    
    public int assumeCheckCount = 0;
    
    public final static String assumeCheckVar = "__JML_AssumeCheck_";
    
    public VarSymbol assumeCheckSym;
    
    public Map<JmlMethodDecl,java.util.List<JmlStatementExpr>> assumeChecks = new HashMap<JmlMethodDecl,java.util.List<JmlStatementExpr>>();
    
    
    /** (Public API) Creates an object to do the rewriting and assertion insertion. This object
     * can be reused to translate different method bodies, so long as the arguments
     * to this constructor remain appropriate. May not have both esc and rac true;
     * if both are false, the mode is implicitly pureCopy.
     * @param context the compilation context to be used
     * @param esc true if the resulting AST is to be used for ESC, otherwise false
     * @param fac true if the resulting AST is to be used for RAC, otherwise false
     */
    public JmlAssertionAdder(Context context, boolean esc, boolean rac) {
        this.context = context;
        this.esc = esc;
        this.rac = rac;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.nowarns = Nowarns.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.jmltypes = JmlTypes.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.attr = JmlAttr.instance(context);
        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        this.exceptionNameCall = names.fromString(Strings.exceptionCallVarString);
        this.terminationName = names.fromString(Strings.terminationVarString);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
        this.utilsClass = reader.enterClass(names.fromString(Strings.runtimeUtilsFQName));
        this.preLabel = treeutils.makeIdent(Position.NOPOS,Strings.empty,syms.intType); // Type does not matter
        initialize();
    }
    
    /** (Public API) Reinitializes the object to start a new class or compilation unit or method */
    public void initialize() {
        this.showRacSource = !JmlOption.isOption(context,JmlOption.NO_RAC_SOURCE.optionName());
        this.racCheckAssumeStatements = !JmlOption.isOption(context,JmlOption.NO_RAC_CHECK_ASSUMPTIONS.optionName());
        this.javaChecks = esc || (rac && !JmlOption.isOption(context,JmlOption.NO_RAC_JAVA_CHECKS.optionName()));
        this.count = 0;
        this.assertCount = 0;
        this.precount = 0;
        this.preparams.clear();
        this.preconditions.clear();
        //this.labels.clear();
        this.pureCopy = !(esc||rac);
        this.treeMap.clear();
        this.oldenv = null;
        racMessages.clear();
        escMessages.clear();
        assumptionChecks.clear();
        assumptionCheckStats.clear();
    }
    
    public void initialize2(long flags) {
        {
            // We are in an initializer block
            // We need a method symbol to be the owner of declarations 
            // (otherwise they will have the class as owner and be thought to
            // be fields)


            MethodSymbol msym;
            if (methodDecl != null) {
                msym = methodDecl.sym;
            } else {
                msym = new MethodSymbol(
                        flags, 
                        classDecl.name, 
                        null, 
                        classDecl.sym);
                methodDecl = //M.MethodDef(msym, null,null);
                        new JmlMethodDecl(
                                M.Modifiers(flags, M.Annotations(List.<com.sun.tools.javac.code.Attribute.Compound>nil())),
                                classDecl.name,
                                null,
                                null,
                                null,
                                null,
                                null, //body,
                                null,
                                msym);
            }
            JCVariableDecl d = treeutils.makeVarDef(syms.exceptionType,exceptionName,msym,
                    treeutils.makeNullLiteral(methodDecl.pos));
            exceptionSym = d.sym;
            exceptionSymbols.put(methodDecl,exceptionSym);
            currentStatements.add(d);
        }

        {
            JCVariableDecl d = treeutils.makeVarDef(syms.intType,terminationName,methodDecl.sym,
                    treeutils.makeIntLiteral(methodDecl.pos,0));
            terminationSym = d.sym;
            terminationSymbols.put(methodDecl, terminationSym);
            currentStatements.add(d);
        }
        if (esc) {
            Name name = names.fromString(assumeCheckVar);
            JCVariableDecl d = treeutils.makeVarDef(syms.intType, name, methodDecl.sym, Position.NOPOS); // NOPOS so the name is not mangled
            assumeCheckSym = d.sym;
            d.sym.owner = null;
            currentStatements.add(d);
        }
        
        exprBiMap.put(treeutils.nullLit,treeutils.nullLit);

    }
    
    // FIXME - this comment needs review and correction
    /** Creates the overall framework for the block:
     * <PRE> 
         preconditions
         try {
            method body
         } finally {
            postconditions
         }
        </PRE>
     * <P>
     * The converted method body is a new block with the following characteristics:
     * <UL>
     * <LI>control flow statements are still present: if-then-else, switch, try-catch-finally blocks
     * <LI>expressions in Java code are decomposed into individual operations, with temporaries. This is so that
     * (a) it is easy to add any assertions prior to a specific operation
     * (b) it is straightforward to handle any operation with side-effects, even in the context of
     * short-circuit operations
     * <LI>assertions are added in for any checks that are desired (see the list below)
     * <LI>specification expressions are not decomposed into individual operations, since all the
     * sub-expressions are supposed to be pure; however, additional assertions are added before any
     * specification expression to check that the specification expression is well-defined - TODO
     * <LI>conditional and short-circuit expressions (in Java code) are converted into if-then-else statements;
     * again, this is to simplify handling of side-effects in sub-expressions - TODO for short-circuit
     * <LI>all identifiers are made unique by combining the name with location information; but no
     * conversions for single-assignment are performed - TODO
     * </UL>
     * <P>
     * These operations are converted: 
     * <UL>
     * <LI>JML equivalence to boolean =
     * <LI>JML inequivalence to boolean !=
     * <LI>JML reverse implies (p <== q) to (p || !q)
     * <LI>Java assignments with operations are decomposed into the operation and the assignment
     * </UL>
     * <LI>These operations are retained:
     * <UL>
     * <LI>assignment
     * <LI>integer and floating +, -, *, /, %
     * <LI>== and !=
     * <LI>comparison operations (integer and floating)
     * <LI>bit and or xor
     * 
     * </UL>
     * <LI>TODO: mod, integer division, shift operations, bit operations, JML implies, JML subtype,
     * instanceof, short-circuit boolean operations
     * <LI>TODO: handle method calls
     * <LI>TODO: handle method calls in specifications
     * <LI>TODO: new Object, new Array expressions
     * <LI>TODO: quantifier and set comprehension expressions
     * <LI>TODO: \fresh operation
     * <LI>TODO: \nonnullelements
     * </UL>
     * <P>
     * These assumptions and checks are added in:
     * <UL>
     * <LI>assume the method preconditions, including null method parameters
     * <LI>assume any class invariants, including null field declarations
     * <LI>assert the method postconditions
     * <LI>assume any explicit assumption
     * <LI>assert any explicit assertion
     * <LI>assert the method exceptional postconditions - TODO
     * <LI>check for null-dereference on each field access
     * <LI>check for null-dereference on each array access - TODO
     * <LI>check for index out of bounds on each array access - TODO
     * <LI>check for assignment of null to any non-null variable or field
     * <LI>check for out of range arithmetic operations - TODO
     * </UL>
     * 
     * @return JCBlock with all assumptions, assertions, added declarations
     */
    
    /** (Public API) Returns a new JCBlock representing the rewritten body of the given method declaration.
     */
    public JCBlock convertMethodBody(JmlMethodDecl pmethodDecl, JmlClassDecl pclassDecl) {
        initialize();
        return convertMethodBodyNoInit(pmethodDecl,pclassDecl);
    }

    /** Internal method to do the method body conversion */
    protected JCBlock convertMethodBodyNoInit(JmlMethodDecl pmethodDecl, JmlClassDecl pclassDecl) {
        int prevAssumeCheckCount = assumeCheckCount;
        JmlMethodDecl prev = this.methodDecl;
        JmlClassDecl prevClass = this.classDecl;
        JCIdent savedThisId = this.currentThisId;
        Symbol savedExceptionSym = this.exceptionSym;
        Symbol savedResultSym = this.resultSym;
        Symbol savedTerminationSym = this.terminationSym;
        ListBuffer<JCStatement> prevStats = initialStatements;
        ListBuffer<JCStatement> savedOldStatements = oldStatements;
        
        try {
            assumeCheckCount = 0;
            this.methodDecl = pmethodDecl;
            this.classDecl = pclassDecl != null ? pclassDecl : utils.getOwner(methodDecl) ;
            this.initialStatements = new ListBuffer<JCStatement>();
            ListBuffer<JCStatement> outerFinalizeStats = new ListBuffer<JCStatement>();
            boolean isConstructor = methodDecl.sym.isConstructor();
            oldStatements = initialStatements;
            currentStatements = initialStatements;
            
            if (!isConstructor && methodDecl.restype.type.tag != TypeTags.VOID) {
                // The compiler complains that the result variable might not be
                // initialized on every path, even in programs in which it appears
                // obvious that it is. So we initialize it here to a null-like value.
                JCVariableDecl d = treeutils.makeVarDef(methodDecl.restype.type,resultName,methodDecl.sym,
                        treeutils.makeZeroEquivalentLit(methodDecl.pos,methodDecl.restype.type));
                resultSym = d.sym;
                initialStatements.add(d);
            }
            initialize2(0L);
            if (allocSym == null) {
                allocSym = treeutils.makeVarSymbol(0, names.fromString(Strings.allocName), syms.intType, classDecl.pos);
                allocSym.owner = classDecl.sym;
                isAllocSym = treeutils.makeVarSymbol(0, names.fromString(Strings.isAllocName), syms.booleanType, classDecl.pos);;
                isAllocSym.owner = classDecl.sym;

                if (esc) {
                    // THIS is an id that is a proxy for the this object on which a method is called;
                    // we need to distinguish it from uses of 'this' in the text
                	// FIXME - should make this NonNull
                    VarSymbol THISSym = treeutils.makeVarSymbol(Flags.STATIC,names.fromString(Strings.thisName),classDecl.sym.type, Position.NOPOS);
                    THISSym.owner = classDecl.sym;
                    this.currentThisId = treeutils.makeIdent(classDecl.pos,THISSym);
                    this.thisIds.put(classDecl.sym, this.currentThisId);
                    exprBiMap.put(this.currentThisId, this.currentThisId);
                } else { // rac
                    // For RAC we use the actual 'this'   FIXME - not sure about this design - perhaps just need to be cautious about what is translated and what is not
                    this.currentThisId = treeutils.makeIdent(classDecl.pos, classDecl.thisSymbol);
                }
            }
            if (esc) {
                currentStatements = initialStatements;
                addAssume(classDecl.pos(),Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeEquality(classDecl.pos(),currentThisId,classDecl.type));
            }

            if (isConstructor && rac) {
                ListBuffer<JCStatement> newstats = new ListBuffer<JCStatement>();
                addPrePostConditions(initialStatements,outerFinalizeStats);
                // FIXME - need to fix RAC So it can check preconditions etc.
                newstats.addAll(methodDecl.body.stats);
                newstats.addAll(initialStatements);
                newstats.addAll(outerFinalizeStats);
                
                return M.at(methodDecl.body.pos()).Block(methodDecl.body.flags,newstats.toList());
                // FIXME - skip constructors until we have them working correctly
            }
            
            // The form of the translated method is this:
            //     assume invariants and preconditions, assigning precondition
            //         values to designated identifiers  [initialStatements]
            //     try {
            //         translation of all the method body statements [currentStatements, after the pushBlock]
            //     } finally {
            //         assert all the postconditions, suitably guarded by the 
            //         values of the preconditions in each specification case
            //         (which is why they have to be declared before the try
            //         statement) [outerFinalizeStatements]
            //     }
            // Values of the result, any exception active, and the termination
            // position (location of last return or throw statement) are tracked

            // We create this first, so that it is the first one in the list.
            // We'll add the block into the right spot later.
            // Other checks will be created during addPrePostConditions
            pushBlock();
            addAssumeCheck(methodDecl,currentStatements,"end of preconditions"); // FIXME - use a smaller highlight range than the whole method - perhaps the specs?
            JCStatement preconditionAssumeCheck = popBlock(0,methodDecl.pos());

            pushBlock();
            
            initialStatements.add( comment(methodDecl.pos(),"Check Preconditions"));
            outerFinalizeStats.add( comment(methodDecl.pos(),"Check Postconditions"));
            addPrePostConditions(initialStatements, outerFinalizeStats);

            addStat(initialStatements,preconditionAssumeCheck);
            
            addStat( comment(methodDecl.pos(),"Method Body"));
            if (methodDecl.body != null) scan(methodDecl.body.stats);
            JCBlock newMainBody = popBlock(0,methodDecl.body == null ? methodDecl.pos(): methodDecl.body.pos());
            
            
            // The outerTryStatement just has a finally clause in which the
            // postconditions and exceptional postconditions are checked.
            if (JmlOption.value(context,JmlOption.FEASIBILITY).equals("all") ||
            		JmlOption.value(context,JmlOption.FEASIBILITY).equals("exit")) {
            	addAssumeCheck(methodDecl,outerFinalizeStats,"at program exit");
            }
            JCTry outerTryStatement = M.at(methodDecl.pos()).Try(
                            newMainBody,
                            List.<JCCatch>nil(),
                            M.Block(0, outerFinalizeStats.toList()));
            
            initialStatements.add(outerTryStatement);
            return M.at(methodDecl.pos()).Block(0,initialStatements.toList());
        } catch (JmlNotImplementedException e) {
            throw e;
        } catch (RuntimeException e) {
            String message = e.getMessage();
            if (message == null) message = "Internal exception: " + e.getClass();
            StringWriter sw = new StringWriter();
            e.printStackTrace(new PrintWriter(sw));
            message = message + JmlTree.eol + sw.toString();
            Log.instance(context).error("jml.internal.notsobad",message);
            return null;
        } finally {
            this.assumeCheckCount = prevAssumeCheckCount;
            this.methodDecl = prev;
            this.classDecl = prevClass;
            this.initialStatements = prevStats;
            this.currentThisId = savedThisId;
            this.resultSym = savedResultSym;
            this.exceptionSym = savedExceptionSym;
            this.terminationSym = savedTerminationSym;
            this.oldStatements = savedOldStatements;
            this.currentStatements = null;
        }
    }
    
    
    // Generic node translation methods. Most of these may add statements to 
    // 'currentStatements'.
    
    // DESIGN NOTE: These routines expect all visit nodes to return a value in
    // 'result' and (for JCExpression derivatives) in 'eresult'. However, in
    // all modes except pureCopy, there may be side-effects of other statements
    // or declarations being produced; in addition, the class of the returned 
    // node may be different than that of the argument, because of the 
    // rac or esc translation.
    
    /** (Public API) Converts a non-expression AST, returning the converted tree;
     * this may be called externally on ClassDecl and CompilationUnit
     * trees, but should not be called outside of JmlAssertionAdder
     * on trees lower in the AST. In purecopy mode, T can be any JCTree derived
     * type;  but otherwise, it may only be either JCTree or JCExpression
     * (possibly JCStatement) */
    @SuppressWarnings("unchecked")
    public @Nullable <T extends JCTree> T convert(@Nullable T tree) {
        if (tree == null) { result = null; return null; }
        scan(tree);

        if (result == null) exprBiMap.putf(tree,null);
        else exprBiMap.put(tree, result);

        return (T)result;
    }
    
    /** Returns a translation of a list of tree, possibly pushing additional
     * statements onto 'currentStatements'; the same restrictions on T apply
     * as above.
     */
    protected @Nullable <T extends JCTree> List<T> convert(@Nullable List<T> trees) {
        if (trees==null) return null;
        ListBuffer<T> newlist = new ListBuffer<T>();
        for (T t: trees) {
            newlist.add(convert(t));
        }
        return newlist.toList();
    }
    
    /** Returns a translation of a list of tree, possibly pushing additional
     * statements onto 'currentStatements'; the same restrictions on T apply
     * as above.
     */
    protected @Nullable <T extends JCTree> java.util.List<T> convert(@Nullable java.util.List<T> trees) {
        if (trees==null) return null;
        java.util.List<T> newlist = new LinkedList<T>();
        for (T t: trees) {
            newlist.add(convert(t));
        }
        return newlist;
    }
    
    /** Returns a translation of an expression, possibly pushing additional
     * statements onto 'currentStatements'
     */
    protected @Nullable JCExpression convertExpr(@Nullable JCExpression tree) {
        eresult = null; // Just so it is initialized in case assignment is forgotten
        if (tree != null) {
            super.scan(tree);
            if (rac && eresult != null && eresult.type != null && jmltypes.isJmlType(eresult.type)) eresult.type = jmltypes.repSym((JmlType)eresult.type).type;
            exprBiMap.put(tree,eresult);
        }
        return eresult;
    }
    
    /** Returns a translation of a list of expression, possibly pushing additional
     * statements onto 'currentStatements'
     */
    protected @Nullable List<JCExpression> convertExprList(@Nullable List<? extends JCExpression> trees) {
        if (trees==null) return null;
        ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
        for (JCExpression t: trees) {
            scan(t);
            newlist.add(eresult);
            exprBiMap.put(t,eresult);
        }
        return newlist.toList();
    }
    
    /** Does a pure copy of the tree; once convertCopy is called on a node, child
     * calls to convertExpr or convert will also be in pureCopy mode. */
    protected @Nullable <T extends JCTree> T convertCopy(@Nullable T tree) {
        boolean savedCopy = pureCopy;
        try {
            pureCopy = true;
            return convert(tree);
        } finally {
            pureCopy = savedCopy;
        }
    }

    /** Does a pure copy of the list of trees */
    protected  <T extends JCTree> List<T> convertCopy(List<T> trees) {
        boolean savedCopy = pureCopy;
        try {
            pureCopy = true;
            ListBuffer<T> newlist = new ListBuffer<T>();
            for (T t: trees) {
                newlist.add(convertCopy(t));
            }
            return newlist.toList();
        } finally {
            pureCopy = savedCopy;
        }
    }

    /** Does a pure copy of the list of trees */
    protected  <T extends JCTree> java.util.List<T> convertCopy(java.util.List<T> trees) {
        boolean savedCopy = pureCopy;
        try {
            pureCopy = true;
            java.util.List<T> newlist = new java.util.LinkedList<T>();
            for (T t: trees) {
                newlist.add(convertCopy(t));
            }
            return newlist;
        } finally {
            pureCopy = savedCopy;
        }
    }

    /** Translates an AST as JML - that is, assuming that the AST is pure;
     * this call is used to switch to the translatingJML mode, setting the
     * condition and isPostcondition to the given values,
     * restoring isPostcondition and translatingJML upon return.
     */
    protected @Nullable JCExpression convertJML(@Nullable JCExpression that, JCExpression condition, boolean isPostcondition) {
        if (that == null) return null;
        boolean savedp = this.isPostcondition;
        boolean savedt = this.translatingJML;
        try {
            this.isPostcondition = isPostcondition;
            this.condition = condition;
            this.translatingJML = true;
            return convertExpr(that);
        } finally {
            this.isPostcondition = savedp;
            this.translatingJML = savedt;
        }
    }

    /** Begins JML scanning for a non-postcondition */
    protected @Nullable JCExpression convertJML(@Nullable JCExpression that) {
        return convertJML(that, treeutils.trueLit, false);
    }

    
    /** Applies convertJML to a list of expressions, returning the new list. */
    protected @Nullable List<JCExpression> convertJML(@Nullable List<JCExpression> trees) {
        if (trees==null) return null;
        else {
            ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
            for (JCExpression tree: trees) {
                convertJML(tree, treeutils.trueLit, false);
                newlist.add(eresult);
            }
            return newlist.toList();
        }
    }
    

    /** Translates a block, but without adding the block to the statement list;
     * any side-effect statements are placed within the new block. */
    protected @Nullable JCBlock convertBlock(@Nullable JCBlock block) {
        if (block == null) return null;
        pushBlock();
        scan(block.stats);
        return popBlock(block.flags,block.pos());
    }

    /** Translates a list of statements, returning a block containing the translations */
    protected JCBlock convertIntoBlock(DiagnosticPosition pos, List<JCStatement> stats) {
        pushBlock();
        scan(stats);
        return popBlock(0,pos);
    }

    /** Translates one statement, returning a block containing the translation
     * (including any statements it spawns); if the statement is a block, then
     * the block's statements are translated, so there is not an excess nested
     * block. */
    protected JCBlock convertIntoBlock(DiagnosticPosition pos, JCStatement stat) {
        pushBlock();
        if (stat instanceof JCBlock) scan(((JCBlock)stat).stats); else scan(stat);
        return popBlock(0,pos);
    }

    /** Start collecting statements for a new block; push currentStatements 
     * onto a stack for later use */
    protected void pushBlock() {
        statementStack.add(0,currentStatements);
        currentStatements = new ListBuffer<JCStatement>();
    }
    
    /** Wrap the active currentStatements as a block (which is returned) and 
     * then resume collecting statements with currentStatements value on the 
     * top of the stack (which is also removed from the stack) 
     */
    protected JCBlock popBlock(long flags, DiagnosticPosition pos) {
        JCBlock b = M.at(pos).Block(flags, currentStatements.toList());
        currentStatements = statementStack.removeFirst();
        return b;
    }
    
    /** Add a statement at the end of the active currentStatements sequence,
     * returning the argument */ 
    protected <T extends JCStatement> T addStat(T stat) {
        if (currentStatements != null) currentStatements.add(stat);
        else if (classDefs != null) classDefs.add(stat); 
        else log.error(stat.pos,  "jml.internal", "No place to add a statement");
        return stat;
    }
    
    /** Add a statement at the end of the given buffer of statements,
     * returning the statement added */ 
    protected <T extends JCStatement> T addStat(ListBuffer<JCStatement> stats, T stat) {
        stats.add(stat);
        return stat;
    }
    
    /** This generates a JmlExpressionStatement comment statement with the given string as
     * text; the statement is not added to any statement list.
     */
    protected JmlStatementExpr comment(DiagnosticPosition pos, String s) {
        return M.at(pos).JmlExpressionStatement(JmlToken.COMMENT,null,M.at(pos).Literal(s));
    }
    
    /** This generates a comment statement whose content is the
     * given JCTree, pretty-printed; the statement is not added to any statement list
     */
    protected JmlStatementExpr comment(JCTree t) {
        String s = JmlPretty.write(t,false);
        int k = s.indexOf(JmlTree.eol); // No multi-line comments
        if (k == -1) k = s.length();
        final int maxlength = 80;
        if (k > maxlength) { s = s.substring(0,k) + " ..."; }
        return comment(t.pos(),s);
    }
    
    /** Issue an internal error message and throw an exception. */
    protected void error(DiagnosticPosition pos, String msg) {
        log.error(pos, "esc.internal.error", msg);
        throw new JmlInternalError(msg);
    }
    
    // FIXME - this is a hack - fix and document
    // These are used so that we don't send repeated notImplemented messages
    static Set<String> racMessages = new HashSet<String>();
    static Set<String> escMessages = new HashSet<String>();
    
    /** Issues a diagnostic message (note) containing the message in the given
     * exception.
     */
    protected void notImplemented(String location, JmlNotImplementedException source) {
        String message = location + source.getMessage();
        String key = source.pos.getPreferredPosition() + message;
        if (rac ? !racMessages.add(key) : !escMessages.add(key)) return;
        log.note(source.pos, 
                rac ? "rac.not.implemented" : "esc.not.implemented", 
                message);
    }
    
    /** Issues a diagnostic message (note) containing the given message.
     */
    protected void notImplemented(DiagnosticPosition pos, String message) {
        String key = pos.getPreferredPosition() + message;
        if (rac ? !racMessages.add(key) : !escMessages.add(key)) return;
        log.note(pos, 
                rac ? "rac.not.implemented" : "esc.not.implemented", 
                        message);
    }
    
    
    /** Adds an assertion with the given label and (already translated) expression
     * to 'currentStatements'. 'codepos' is the position within the code where
     * the assertion is triggered; log.currentSource() is used as the sourcefile
     * in which 'codepos' lies. 'associatedSource' and 'associatedPos' are the
     * location of the specification clause from which this assertion derives,
     * if any.
     * The args are arguments for the resource key giving the error message
     * corresponding to the given Label.
     * Returns null if no assertion was added
     */

    protected @Nullable JCStatement addAssert(
            DiagnosticPosition codepos, // FIXME _ document whether nullable and behavior
            Label label, 
            JCExpression translatedExpr, 
            @Nullable DiagnosticPosition associatedPos, 
            @Nullable JavaFileObject associatedSource, 
            @Nullable JCExpression info, 
            Object ... args) {
        
        boolean isTrue = treeutils.isTrueLit(translatedExpr); 
        boolean isFalse = treeutils.isFalseLit(translatedExpr);
        if (isTrue) return null; // Literally true - don't even add the statement
        if (nowarns.suppress(log.currentSource(), codepos == null ? Position.NOPOS : codepos.getPreferredPosition(), label.toString())) return null;
        String assertID = Strings.assertPrefix + (++assertCount);
        Name assertname = names.fromString(assertID);
        JavaFileObject dsource = log.currentSourceFile();
        JCVariableDecl assertDecl = treeutils.makeVarDef(syms.booleanType,assertname,methodDecl == null? classDecl.sym : methodDecl.sym,translatedExpr);
        currentStatements.add(assertDecl);
        if (esc) {
            JmlStatementExpr st = treeutils.makeAssert(codepos,label,treeutils.makeIdent(translatedExpr.pos,assertDecl.sym));
            st.source = dsource;
            st.associatedPos = associatedPos == null ? Position.NOPOS : associatedPos.getPreferredPosition();
            st.associatedSource = associatedSource;
            st.optionalExpression = info;
            st.id = assertID;
            treeutils.copyEndPosition(st.expression, translatedExpr);
            treeutils.copyEndPosition(st, translatedExpr); // Note that the position of the expression may be that of the associatedPos, not of the original assert, if there even is one
            currentStatements.add(st);
            return st;
        } 
        if (rac) {
            JCDiagnostic diag = JCDiagnostic.Factory.instance(context).warning(log.currentSource(), codepos, "rac." + label, args);
            String msg = (showRacSource? diag.toString() : diag.noSource()).replace("warning: ", "");
            if (associatedPos != null) {
                diag = JCDiagnostic.Factory.instance(context).warning(
                        new DiagnosticSource(associatedSource != null ? associatedSource : log.currentSourceFile(),null), 
                		associatedPos, 
                		Utils.testingMode || !showRacSource ? "jml.associated.decl" : "jml.associated.decl.cf",
                		        utils.locationString(codepos.getPreferredPosition()));
                String msg2 = (showRacSource? diag.toString() : diag.noSource()).replace("warning: ", "");
                msg = msg + JmlTree.eol + msg2;
            }
            if (JmlOption.isOption(context, JmlOption.RAC_COMPILE_TO_JAVA_ASSERT)) {
                JCStatement st = M.at(codepos).Assert(translatedExpr, treeutils.makeStringLiteral(translatedExpr.pos,msg));
                currentStatements.add(st);
                return st;
            } else {
                if (info == null) {
                    info = treeutils.makeStringLiteral(translatedExpr.pos,msg);
                }
                JCStatement st = assertFailure(info,codepos,label);
                if (!isFalse) st = M.at(codepos).If(
                        treeutils.makeNot(codepos == null ? Position.NOPOS : codepos.getPreferredPosition(), treeutils.makeIdent(translatedExpr.pos,assertDecl.sym)), 
                        st, null);
                currentStatements.add(st);
                return st;
            }
        }
        return null;
    }

    /** Adds an assertion with the given label and (already translated) expression
     * to 'currentStatements'. 'codepos' is the position within the code where
     * the assertion is triggered; log.currentSource() is used as the sourcefile
     * in which 'codepos' lies. There is no associated position or extra information.
     * The args are arguments for the resource key giving the error message
     * corresponding to the given Label.
     */
    protected JCStatement addAssert(
            DiagnosticPosition codepos, 
            Label label, 
            JCExpression expr, 
            Object ... args) {
        return addAssert(codepos,label,expr,null,null,null,args);
    }
    
    /** Creates a statement at which we can check feasibility */
    protected void addAssumeCheck(JCTree item, ListBuffer<JCStatement> list, String description) {
        if (!esc) return;
        // We create feasibility check points by adding assertions of the 
        // form assumeCheckVar != n, for different values of n > 0.
        // Then for normal checking of the method, we assert assumeCheckVar == 0
        // so all the introduced asserts are trivially true.
        // But plater we can pop the assumeCheckVar == 0 and add 
        // assumeCHeckVar == k, to check feasibility at point k.
        
        ++assumeCheckCount;
        java.util.List<JmlStatementExpr> descs = assumeChecks.get(methodDecl);
        if (descs == null) assumeChecks.put(methodDecl, descs = new LinkedList<JmlStatementExpr>());
        JCIdent id = treeutils.makeIdent(item.pos, assumeCheckSym);
        JCExpression bin = treeutils.makeBinary(item.pos,JCTree.NE,treeutils.intneqSymbol,id,treeutils.makeIntLiteral(item.pos,assumeCheckCount));
        ListBuffer<JCStatement> prev = currentStatements;
        currentStatements = list;
        JmlStatementExpr a = (JmlStatementExpr)addAssert(item.pos(), Label.ASSUME_CHECK, bin);
        a.description = description;
        descs.add(a);
        currentStatements = prev;
    }
    
    /** Adds an assertion with the given label and (already translated) expression
     * to 'currentStatements'. 'codepos' is the position within the code where
     * the assertion is triggered; log.currentSource() is used as the sourcefile
     * in which 'codepos' lies. The last two arguments give the file and position
     * within the file of the associated specification that is potentially violated.
     * The args are arguments for the resource key giving the error message
     * corresponding to the given Label.
     */
    protected JCStatement addAssert(
            DiagnosticPosition codepos, 
            Label label, 
            JCExpression expr, 
            DiagnosticPosition associatedPos, 
            JavaFileObject associatedSource, 
            Object ... args) {
        return addAssert(codepos,label,expr,associatedPos,associatedSource,null,args);
    }
    
    /** Creates a call of org.jmlspecs.utils.Utils.assertionFailure(s), where
     * s is a literal containing the value of the argument, for RAC translations
     * @param sp the string to make into the literal argument of the call
     * @param pos the character position of the created AST
     * @return an assert statement indication an assertion failure
     */
    protected JCStatement assertFailure(JCExpression sp, DiagnosticPosition pos, Label label) {
        JCFieldAccess m = findUtilsMethod(pos,org.jmlspecs.utils.Utils.ASSERTION_FAILURE);
        JCExpression c = M.at(pos).Apply(null,m,List.<JCExpression>of(sp,treeutils.makeStringLiteral(0,label.info()))).setType(syms.voidType);
        return M.at(pos).Exec(c);
    }

    
    /** Creates an assumption that two expressions are equal, adding the assumption to 'currentStatements'. */
    protected JmlStatementExpr addAssumeEqual(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression lhs, 
            JCExpression rhs) {
        return addAssume(pos,label,treeutils.makeBinary(pos.getPreferredPosition(),JCTree.EQ,lhs,rhs),null,null,null);
    }
    
    /** Creates an assumption, adding it to 'currentStatements' */
    protected JmlStatementExpr addAssume(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression ex) {
        return addAssume(pos,label,ex,null,null,null);
    }
    
    /** Creates an assumption with an associated declaration (perhaps in a different file), 
     * adding it to 'currentStatements' (does nothing if esc and rac are false)*/
    protected JmlStatementExpr addAssume(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression ex, 
            @Nullable DiagnosticPosition associatedPos, 
            @Nullable JavaFileObject associatedSource) {
        return addAssume(pos,label,ex,associatedPos,associatedSource,null);
    }
    
    /** Creates an assumption with an associated declaration (perhaps in a 
     * different file), adding it to 'currentStatements' */
    protected JmlStatementExpr addAssume(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression translatedExpr, 
            @Nullable DiagnosticPosition associatedPosition, 
            @Nullable JavaFileObject associatedSource, 
            @Nullable JCExpression info) {
        JmlStatementExpr st = null;
        if (esc) {
            st = treeutils.makeAssume(pos,label,translatedExpr);
            st.source = log.currentSourceFile();
            st.associatedPos = associatedPosition == null ? Position.NOPOS : associatedPosition.getPreferredPosition();
            st.associatedSource = associatedSource;
            st.optionalExpression = info;
            st.id = Strings.assumePrefix + (++assertCount);
            if (currentStatements != null) currentStatements.add(st);
            else classDefs.add(st);

        }
        if (rac && racCheckAssumeStatements) {
            addAssert(pos,label,translatedExpr,associatedPosition,associatedSource,info);
        }
        return st;
    }

    /** Creates an AST for calling a method with the given name from the
     * org.jmlspecs.utils.Utils class (that is available at runtime)
     * @param methodName the name of the method 
     * @return the corresponding AST
     */
    protected JCFieldAccess findUtilsMethod(DiagnosticPosition pos, String methodName) {
        JCIdent utilsClassIdent = M.Ident(utilsClass);
        Name n = names.fromString(methodName);
        Scope.Entry e = utilsClass.members().lookup(n);
        Symbol ms = e.sym;
        if (e.sym == null) {
            error(pos,"Method is not found in the runtime library: " + methodName);
            return null; // does not return
        } else {
            JCFieldAccess m = M.at(pos).Select(utilsClassIdent,n);
            m.sym = ms;
            m.type = m.sym.type;
            return m;
        }
    }
    
    /** Creates an expression AST for a call of the given static method (from
     * org.jmlspecs.utils.Utils).
     * @param methodName the name of the method to call
     * @param translatedArgs the ASTs which are the (already translated) arguments
     * @return the resulting AST
     */
    protected JCExpression methodCallUtilsExpression(DiagnosticPosition pos, String methodName, JCExpression ... translatedArgs) {
        JCFieldAccess m = findUtilsMethod(pos,methodName);
        List<JCExpression> args = new ListBuffer<JCExpression>().appendArray(translatedArgs).toList();
        JCMethodInvocation c = M.at(pos).Apply(null,m,args);
        if (m.type instanceof Type.MethodType){ 
            c.setType(((Type.MethodType)m.type).restype);
        } else if (m.type instanceof Type.ForAll) {
            Type.ForAll tfa = (Type.ForAll)m.type;
            c.setType(((Type.MethodType)tfa.qtype).restype);
        } else {
            error(pos,"Unknown method type in methodCallUtilsExpression: " + methodName + " " + m.type.getClass());
        }
        return c;
    }

    /** Creates a statement AST for a call of the given method (from
     * org.jmlspecs.utils.Utils).
     * @param methodName the name of the method to call
     * @param translatedArgs the ASTs which are the (already translated) arguments
     * @return the resulting AST
     */
    protected JCStatement methodCallUtilsStatement(DiagnosticPosition pos, String methodName, JCExpression ... translatedArg) {
        JCExpression c = methodCallUtilsExpression(pos, methodName, translatedArg);
        return M.at(pos).Exec(c);
    }

    
    /** Creates a declaration for a unique temporary name with the given type and position,
     * with no initialization, adds it to currentStatements and returns an Ident
     * for the new symbol. */
    protected JCIdent newTemp(DiagnosticPosition pos, Type t) {
        Name n = M.Name(Strings.tmpVarString + (++count));
        JCVariableDecl d = treeutils.makeVarDef(t, n, esc ? null : methodDecl.sym , esc ? Position.NOPOS : pos.getPreferredPosition()); // FIXME - see note below
        // We mark all temporaries as final, as an indication that they will
        // be used only once.  // FIXME - do this or not? can we avoid the esc? check above?
//        d.mods.flags |= Flags.FINAL;
//        d.sym.flags_field |= Flags.FINAL;
        currentStatements.add(d);
        JCIdent id = M.at(pos).Ident(d.sym);
        return id;
    }
    
    /** Creates a declaration for a unique temporary initialized to the given expression. */
    protected JCIdent newTemp(JCExpression expr) {
        return newTemp(Strings.tmpVarString + (++count),expr);
    }
    
    protected JCIdent newTemp(String name, /*@ non_null */JCExpression expr) {
        return newTemp(expr.pos, name, expr);
    }

    
    /** Creates a declaration for the given name initialized to the given expression. */
    protected JCIdent newTemp(int pos, String name, /*@ non_null */JCExpression expr) {
        Name n = M.Name(name);
        // By having the owner be null, the BasicBlocker2 does not append any unique-ifying suffix - FIXME - does this affect RAC?
        JCVariableDecl d = treeutils.makeVarDef(
                expr.type.tag == TypeTags.BOT ? syms.objectType : expr.type, 
                n, 
                esc ? null : methodDecl != null ? methodDecl.sym : classDecl.sym, 
                expr); 
        d.pos = pos;
        d.sym.pos = Position.NOPOS; // We set the position to NOPOS so that the temporary name is not further encoded
        // We mark all temporaries as final, as an indication that they will
        // be used only once.
//        d.mods.flags |= Flags.FINAL;
//        d.sym.flags_field |= Flags.FINAL;
        currentStatements.add(d);
        JCIdent id = treeutils.makeIdent(expr.getStartPosition(),d.sym);
        treeutils.copyEndPosition(d,expr);
        treeutils.copyEndPosition(id,expr);
        return id;
    }

    /** Creates a declaration for a new name and type initialized to a zero-equivalent literal. */
    protected JCIdent newTempNull(DiagnosticPosition pos, Type type) {
        Name n = M.Name(Strings.tmpVarString + (++count));
        // By having the owner be null, the BasicBlocker2 does not append any unique-ifying suffix - FIXME - does this affect RAC?
        JCVariableDecl d = treeutils.makeVarDef(
                type, 
                n, 
                esc ? null : methodDecl != null ? methodDecl.sym : classDecl.sym, // FIXME - actually sholdn't stuff at the class level be put in an initializer block?
                treeutils.makeZeroEquivalentLit(pos.getPreferredPosition(),type)); 
        d.sym.pos = Position.NOPOS;
        // We mark all temporaries as final, as an indication that they will
        // be used only one.
//        d.mods.flags |= Flags.FINAL;
//        d.sym.flags_field |= Flags.FINAL;
        currentStatements.add(d);
        JCIdent id = treeutils.makeIdent(pos.getPreferredPosition(),d.sym);
        return id;
    }


    /** Returns true if the given symbol has a Helper annotation */
    public boolean isHelper(Symbol symbol) {
        return symbol.attribute(attr.tokenToAnnotationSymbol.get(JmlToken.HELPER))!=null;

    }
    
    /** Returns true if the given symbol has a Model annotation */
    public boolean isModel(Symbol symbol) {
        return symbol.attribute(attr.tokenToAnnotationSymbol.get(JmlToken.MODEL))!=null;
    }
    

    /** Creates a try statement that wraps the given block and catches any
     * RuntimeException; the catch block prints the given message; esc just
     * returns the given block
     */
    public JCStatement wrapRuntimeException(DiagnosticPosition pos, JCBlock block, String message, @Nullable JCBlock catchStats) {
        if (!rac) return block;
        int p = pos.getPreferredPosition();
        Name n = names.fromString(Strings.runtimeException); // FIXME - this does not need to be repeated every time
        JCVariableDecl vd = treeutils.makeVarDef(syms.runtimeExceptionType, n, methodDecl.sym, p);
        JCIdent ex = treeutils.makeIdent(p,vd.sym);
        JCExpression str = treeutils.makeStringLiteral(p,message);
        JCStatement st = methodCallUtilsStatement(pos,org.jmlspecs.utils.Utils.REPORT_EXCEPTION,str,ex);
        JCBlock bl = M.at(pos).Block(0, 
                st != null ? ( catchStats != null ? List.<JCStatement>of(st,catchStats) : List.<JCStatement>of(st))
                           : ( catchStats != null ? List.<JCStatement>of(catchStats) : List.<JCStatement>nil()));
        JCCatch catcher = M.at(pos).Catch(vd,bl);
        return M.at(pos).Try(block,List.<JCCatch>of(catcher),null);
    }

    /** Creates a try statement that wraps the given block and catches the
     * given exception; the declaration is the declaration of the variable to
     * use in the catch block; the catch block prints the given message and
     * executes the given stats.
     */
    public JCStatement wrapException(DiagnosticPosition pos, JCBlock block, JCVariableDecl exceptionDecl, @Nullable JCBlock catchStats) {
        JCBlock bl = catchStats != null ? catchStats :  M.at(pos).Block(0, List.<JCStatement>nil());
        JCCatch catcher = M.at(pos).Catch(exceptionDecl,bl);
        return M.at(pos).Try(block,List.<JCCatch>of(catcher),null);
    }

    /** Computes and adds checks for all the pre and postcondition clauses. */
    // FIXME - review this
    protected void addPrePostConditions( 
            ListBuffer<JCStatement> initialStats, 
            ListBuffer<JCStatement> finalizeStats
            ) {
        
        JCMethodDecl methodDecl = this.methodDecl;
        boolean methodIsStatic = methodDecl.sym.isStatic();
        boolean isConstructor = methodDecl.sym.isConstructor();
        ListBuffer<JCStatement> savedCurrentStatements = currentStatements;
        currentStatements = initialStats;

        // Add a precondition that the parameter != null on each formal parameter, if needed
        // Not adding these because the nonnull conditions are part of the deNestedSpecs.
        // However it would be nice to use these and leave them out of the  combinedPrecondition
        // because we get more accurate error messages.
        // Added  back - appears to be needed for ESC - FIXME - review all this
        if (esc) {
            for (JCVariableDecl d: methodDecl.params) {
                if (specs.isNonNull(d.sym, (Symbol.ClassSymbol)d.sym.owner.owner)) {
                    addAssume(d.pos(),Label.NULL_CHECK,treeutils.makeNeqObject(d.pos,treeutils.makeIdent(d.pos, d.sym),  treeutils.makeNullLiteral(d.pos)));
                }
                
                if (!d.sym.type.isPrimitive()) {
                    JCExpression e1 = treeutils.makeEqObject(d.pos,treeutils.makeIdent(d.pos, d.sym), treeutils.makeNullLiteral(d.pos));
                    JCExpression e2 = treeutils.makeSelect(d.pos, treeutils.makeIdent(d.pos, d.sym), isAllocSym);
                    addAssume(d.pos(),Label.IMPLICIT_ASSUME,treeutils.makeOr(d.pos, e1, e2));
                }
            }
            
            int pos = methodDecl.pos;
            JCVariableDecl qd = treeutils.makeVarDef(syms.objectType, names.fromString("obj"), methodDecl.sym, methodDecl.pos);
            JCFieldAccess fa = treeutils.makeSelect(pos, treeutils.makeIdent(methodDecl.pos, qd.sym), allocSym);
            JCBinary comp = treeutils.makeBinary(pos,JCTree.LE,treeutils.intleSymbol,fa,treeutils.makeIntLiteral(pos, 0));
            JCExpression e = M.at(pos).JmlQuantifiedExpr(JmlToken.FORALL, List.<JCVariableDecl>of(qd), null, comp);
            //addAssume(methodDecl.pos(),Label.IMPLICIT_ASSUME,e);
            
            fa = treeutils.makeSelect(pos, treeutils.makeIdent(methodDecl.pos, currentThisId.sym), isAllocSym);
            addAssume(methodDecl.pos(),Label.IMPLICIT_ASSUME,fa);

            fa = treeutils.makeSelect(pos, treeutils.makeIdent(methodDecl.pos, currentThisId.sym), allocSym);
            comp = treeutils.makeBinary(pos,JCTree.EQ,treeutils.inteqSymbol,fa,treeutils.makeIntLiteral(pos, 0));
            addAssume(methodDecl.pos(),Label.IMPLICIT_ASSUME,comp);

        }
        
        /* Declare new variables, initialized to the values of the formal 
         * parameters, so that they can be referred to in postconditions. 
         */
        for (JCVariableDecl d: methodDecl.params) {
            JCVariableDecl dd = treeutils.makeVarDef(d.type,M.Name(Strings.formalPrefix+d.name.toString()),  
                    d.sym.owner, M.Ident(d.sym));
            dd.pos = dd.sym.pos = d.sym.pos;
            preparams.put(d.sym,dd);
            if (esc) dd.sym.owner = null; // FIXME - is this used anymore?
            addStat(dd);
        }
        
        paramActuals = new HashMap<Symbol,JCExpression>();
        ListBuffer<JCStatement> preStats = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> ensuresStats = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> exsuresStats = new ListBuffer<JCStatement>();
        
        // Construct a condition, to be used later, that the method has not thrown an exception
        DiagnosticPosition methodPos = methodDecl.pos();
        JCExpression noException = treeutils.makeEqObject(methodPos.getPreferredPosition(),
                treeutils.makeIdent(methodPos.getPreferredPosition(), exceptionSym), treeutils.nullLit);
        
        // the following list of parents includes self
        java.util.List<ClassSymbol> parents = utils.parents((ClassSymbol)methodDecl.sym.owner);
        
        // Iterate through parent classes and interfaces, assuming relevant axioms and invariants
        // These are checked prior to calling the callee
        currentStatements = preStats;
        for (ClassSymbol csym: parents) {
            JmlSpecs.TypeSpecs tspecs = specs.get(csym);

            for (JmlTypeClause clause : tspecs.clauses) {
                JmlTypeClauseExpr t;

                try {
                    switch (clause.token) {
                        case INVARIANT:
                            if (!methodIsStatic || utils.hasAny(clause.modifiers,Flags.STATIC)) {
                                if (!isHelper(methodDecl.sym) && (methodIsStatic || !isConstructor) &&
                                        utils.jmlvisible(classDecl.sym, csym, clause.modifiers.flags, methodDecl.mods.flags) // FIXME - test visibility
                                        ) {
                                    t = (JmlTypeClauseExpr)clause;
                                    addTraceableComment(t.expression,clause.toString());
                                    addAssume(methodDecl.pos(),Label.INVARIANT_ENTRANCE,
                                            convertJML(t.expression),
                                            clause.pos(),clause.source);
                                }
                            }
                            break;
                        case AXIOM:
                            if (rac) {
                                notImplemented(clause.pos(), "axiom clause");
                            } else if (esc) {
                                t = (JmlTypeClauseExpr)clause;
                                addAssume(methodDecl.pos(),Label.AXIOM,
                                        convertJML(t.expression),
                                        clause.pos(),clause.source);
                            }
                            break;
                        default:
                            // Skip

                    }
                } catch (JmlNotImplementedException e) {
                    notImplemented(clause.token.internedName() + " clause containing ", e);
                }
            }
        }
        
        // Accumulate the invariants to be checked after the callee returns
        // FIXME - iterate over parent classes and interfaces in reverse order!!
        currentStatements = ensuresStats;
        for (ClassSymbol csym: parents) {
            JmlSpecs.TypeSpecs tspecs = specs.get(csym);
            for (JmlTypeClause clause : tspecs.clauses) {
                if (!utils.jmlvisible(classDecl.sym, csym, clause.modifiers.flags, methodDecl.mods.flags)) continue;
                JmlTypeClauseExpr t;
                try {
                    switch (clause.token) {

                        case INVARIANT:
                            if (!methodIsStatic || utils.hasAny(clause.modifiers,Flags.STATIC)) {
                                if (!isHelper(methodDecl.sym)) {
                                    pushBlock();
                                    t = (JmlTypeClauseExpr)clause;
                                    addTraceableComment(t.expression,clause.toString());
                                    addAssert(methodDecl.pos(),Label.INVARIANT_EXIT,
                                            convertJML(t.expression),
                                            clause.pos(),clause.source);
                                    addStat( popBlock(0,clause.pos()));
                                }
                            }
                            break;
                        case CONSTRAINT:
                            // FIXME - need to check the list of method signatures
                            if ((!isConstructor && (!methodIsStatic || utils.hasAny(clause.modifiers,Flags.STATIC))) ||
                                    (isConstructor && utils.hasAny(clause.modifiers,Flags.STATIC))) {
                                pushBlock();
                                JmlTypeClauseConstraint tt = (JmlTypeClauseConstraint)clause;
                                addTraceableComment(tt.expression,clause.toString());
                                addAssert(methodDecl.pos(),Label.CONSTRAINT,
                                        convertJML(tt.expression),
                                        clause.pos(),
                                        clause.source);
                                addStat( popBlock(0,clause.pos()));
                            }
                            break;
                        case INITIALLY:
                            if (isConstructor && !isHelper(methodDecl.sym)) {
                                pushBlock();
                                t = (JmlTypeClauseExpr)clause;
                                addTraceableComment(t.expression,clause.toString());
                                addAssert(methodDecl.pos(),Label.INITIALLY,
                                        convertJML(t.expression),
                                        clause.pos(),clause.source);
                                addStat( popBlock(0,clause.pos()));
                            }
                            break;
                        default:
                            // Skip

                    }
                } catch (JmlNotImplementedException e) {
                    notImplemented(clause.token.internedName() + " clause containing ",e);
                    continue;
                }

            }
        }

        JCExpression combinedPrecondition = null;
        
        // Iterate over all methods that methodDecl overrides, collecting specs
        boolean sawSomeSpecs = false;
        for (MethodSymbol msym: utils.parents(methodDecl.sym)) {
            if (msym.params == null) continue; // FIXME - we should do something better? or does this mean binary with no specs?
            JmlMethodSpecs denestedSpecs = JmlSpecs.instance(context).getDenestedSpecs(msym);

            // Set up the map from parameter symbol of the overridden method to 
            // corresponding parameter of the target method.
            // We need this even if names have not changed, because the parameters 
            // will have been attributed with different symbols.
            Iterator<VarSymbol> iter = msym.params.iterator();
            for (JCVariableDecl dp: methodDecl.params) {
                paramActuals.put(iter.next(),treeutils.makeIdent(dp.pos, dp.sym));
            }


            for (JmlSpecificationCase scase : denestedSpecs.cases) {
                sawSomeSpecs = true;
                if (!utils.jmlvisible(classDecl.sym, msym.owner, scase.modifiers.flags, methodDecl.mods.flags)) continue;
                JCIdent preident = null;
                JCExpression preexpr = null;
                currentStatements = preStats;
                for (JmlMethodClause clause : scase.clauses) {
                    switch (clause.token) {
                        case OLD:
                            for (JCVariableDecl decl : ((JmlMethodClauseDecl)clause).decls) {
                                JCVariableDecl newdecl = treeutils.makeVarDef(decl.type, decl.name, decl.sym.owner, convertExpr(decl.init));
                                newdecl.pos = decl.pos;
                                addStat(decl);
                                JCIdent id = treeutils.makeIdent(clause.pos, newdecl.sym);
                                exprBiMap.put(id, convertExpr(id));
                                addTraceableComment(decl,clause.toString());
                            }
                            break;
                        case REQUIRES:
                            JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                            if (preexpr == null) preexpr = ex;
                            else preexpr = treeutils.makeAnd(preexpr.pos, preexpr, ex);
                            addTraceableComment(ex,clause.toString());
                            break;
                        default:
                    }
                }
                if (preexpr == null) {
                    preexpr = treeutils.trueLit;
                } else {
                    try {
                        preexpr = convertJML(preexpr);
                    } catch (JmlNotImplementedException e) {
                        notImplemented("requires clause containing ",e);
                        continue;
                    }
                }
                precount++;
                Name prename = names.fromString(Strings.prePrefix + precount);
                JCVariableDecl dx = treeutils.makeVarDef(syms.booleanType, prename, methodDecl.sym, treeutils.falseLit);
                dx.pos = scase.pos;
                preident = treeutils.makeIdent(scase.pos, dx.sym);
                addStat(initialStats,dx);
                addStat(currentStatements, treeutils.makeAssignStat(scase.pos, preident, preexpr));
                preconditions.put(scase, preident);
                if (combinedPrecondition == null || preexpr == treeutils.trueLit) {
                    combinedPrecondition = preident;
                } else {
                    combinedPrecondition = treeutils.makeOr(combinedPrecondition.pos, combinedPrecondition, preident);
                }

                boolean sawSignalsOnly = false;

                for (JmlMethodClause clause : scase.clauses) {
                    try {
                        switch (clause.token) {
                            // FIXME - would be nice if RAC postconditions could refer to the last return that was executed
                            case ENSURES:
                            {
                                currentStatements = ensuresStats;
                                pushBlock();
                                JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                                addTraceableComment(ex,clause.toString());
                                ex = convertJML(ex,preident,true);
                                ex = treeutils.makeImplies(clause.pos, preident, ex);
                                // FIXME - if the clause is synthetic, the source file may be null, and for signals clause
                                addAssert(methodDecl.pos(),Label.POSTCONDITION,ex,clause.pos(),clause.sourcefile);
                                addStat(popBlock(0,clause.pos()));
                                break;
                            }

                            case SIGNALS: // FIXME - need to check exception type of the exception
                            {
                                currentStatements = exsuresStats;
                                pushBlock();
                                JCVariableDecl vd = ((JmlMethodClauseSignals)clause).vardef;
                                JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionSym);
                                if (vd != null) {
                                    JCTypeCast tc = M.at(clause.pos()).TypeCast(vd.type, exceptionId);
                                    vd.init = esc ? exceptionId : tc;
                                    addStat(vd);
                                }
                                {
                                    JCIdent nid = convertCopy(exceptionId);
                                    exprBiMap.put(nid, exceptionId);
                                    addTraceableComment(clause,nid,"Terminated with exception");
                                }
                                //JCVariableDecl evar = treeutils.makeVarDef(vd.type, vd.name, decl.sym, tc); // FIXME - needs a unique name
                                //addStat(evar);
                                JCExpression ex = ((JmlMethodClauseSignals)clause).expression;
                                addTraceableComment(ex,clause.toString());
                                ex = convertJML(ex,preident,true);
                                ex = treeutils.makeImplies(clause.pos, preident, ex);
                                addAssert(methodDecl.pos(),Label.SIGNALS,ex,clause.pos(),clause.sourcefile);
                                addStat(popBlock(0,clause.pos()));
                                break;
                            }

                            case SIGNALS_ONLY:
                            {
                                sawSignalsOnly = true;
                                if (!esc) { // FIXME _ fix this when esc handles types
                                    currentStatements = exsuresStats;
                                    pushBlock();
                                    JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionSym);
                                    JCExpression condd = treeutils.falseLit;
                                    for (JCExpression t: ((JmlMethodClauseSignalsOnly)clause).list) {
                                        JCExpression tc = M.at(t.pos()).TypeTest(exceptionId, t).setType(syms.booleanType);
                                        condd = treeutils.makeOr(clause.pos, condd, tc);
                                    }
                                    //JCExpression name = methodCallUtilsExpression(clause.pos(),"typeName",exceptionId);
                                    condd = treeutils.makeImplies(clause.pos, preident, condd);
                                    addAssert(methodDecl.pos(),Label.SIGNALS_ONLY,condd,clause.pos(),clause.sourcefile);
                                    addStat(popBlock(0,methodDecl.pos()));
                                }
                                break;
                            }

                            case DIVERGES:
                            {
                                // FIXME _ implement
                                currentStatements = ensuresStats;
                                pushBlock();
                                JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                                addTraceableComment(ex,clause.toString());
                                ex = convertJML(ex,preident,true);
                                ex = treeutils.makeImplies(clause.pos, preident, ex);
                                //addAssert(methodDecl.pos(),Label.SIGNALS,ex,currentStatements,clause.pos(),clause.sourcefile);
                                popBlock(0,clause.pos());
                                notImplemented(clause.pos(),clause.token.internedName() + " clause");
                                break;
                            }

                            case DURATION:
                            case WORKING_SPACE:
                            {
                                // FIXME - implement
                                currentStatements = ensuresStats;
                                pushBlock();
                                JCExpression ex = ((JmlMethodClauseConditional)clause).expression;
                                ex = convertJML(ex,preident,true);
                                ex = treeutils.makeImplies(clause.pos, preident, ex);
                                //addAssert(methodDecl.pos(),Label.SIGNALS,ex,currentStatements,clause.pos(),clause.sourcefile);
                                popBlock(0,clause.pos());
                                notImplemented(clause.pos(),clause.token.internedName() + " clause");
                                break;
                            }


                            // FIXME - more clauses to implement?

                            case REQUIRES:
                                break;
                            default:
                        }
                    } catch (JmlNotImplementedException e) {
                        notImplemented(clause.token.internedName() + " clause containing ",e);
                        continue;
                    }
                    
                }
                if (!sawSignalsOnly && rac) {
                    sawSomeSpecs = true;
                    currentStatements = exsuresStats;
                    pushBlock();
                    JCIdent exceptionId = treeutils.makeIdent(scase.pos,exceptionSym);
                    JCExpression condd = treeutils.falseLit;
                    DiagnosticPosition pos = null;
                    for (JCExpression ex: methodDecl.thrown) {
                        if (pos == null) pos = ex.pos();
                        JCExpression tc = M.at(ex.pos()).TypeTest(exceptionId, ex).setType(syms.booleanType);
                        condd = treeutils.makeOr(ex.pos, condd, tc);
                    }
                    addAssert(esc ? null :methodDecl.pos(),Label.SIGNALS_ONLY,condd,pos == null ? methodDecl.pos() : pos, log.currentSourceFile());
                    addStat(popBlock(0,methodDecl.pos()));
                }
            }
            if (!sawSomeSpecs && rac) {
                currentStatements = exsuresStats;
                pushBlock();
                JCIdent exceptionId = treeutils.makeIdent(methodDecl.pos,exceptionSym);
                JCExpression condd = treeutils.falseLit;
                DiagnosticPosition pos = null;
                for (JCExpression ex: methodDecl.thrown) {
                    if (pos == null) pos = ex.pos();
                    JCExpression tc = M.at(ex.pos()).TypeTest(exceptionId, ex).setType(syms.booleanType);
                    condd = treeutils.makeOr(ex.pos, condd, tc);
                }
                addAssert(esc ? null :methodDecl.pos(),Label.SIGNALS_ONLY,condd,pos == null ? methodDecl.pos() : pos, log.currentSourceFile());
                addStat(popBlock(0,methodDecl.pos()));
            }

        }


        methodPos = methodDecl.pos();

        // If combinedPrecondition is null then there were no specs, so the implicit precondition is true and does not
        // need to be checked
        if (combinedPrecondition != null) {
            currentStatements = preStats;
            // FIXME - associated location? where?
            addAssume(combinedPrecondition.pos(),Label.PRECONDITION,combinedPrecondition);
        }
        
        currentStatements = savedCurrentStatements;
        if (rac) {
            Name n;
            JCVariableDecl vd;
            JCIdent ex;
            
            if (!isConstructor) {
                n = names.fromString("preEx");
                vd = treeutils.makeVarDef(syms.runtimeExceptionType, n, methodDecl.sym, methodDecl.pos);
                ex = treeutils.makeIdent(methodDecl.pos,vd.sym);
                JCExpression str = treeutils.makeStringLiteral(methodDecl.pos,"Runtime exception while evaluating preconditions - preconditions are undefined in JML");
                JCStatement st = methodCallUtilsStatement(methodDecl.pos(),"reportException",str,ex);
                JCBlock bl = M.at(methodDecl.pos).Block(0, List.<JCStatement>of(st));
                JCCatch catcher = M.at(methodDecl.pos).Catch(vd,bl);
                bl = M.at(methodDecl.pos).Block(0, preStats.toList());
                st = M.at(methodDecl.pos).Try(bl,List.<JCCatch>of(catcher),null);
                preStats = new ListBuffer<JCStatement>();
                preStats.add(st);
            }
            
            {
                n = names.fromString("postEx");
                vd = treeutils.makeVarDef(syms.runtimeExceptionType, n, methodDecl.sym, methodDecl.pos);
                ex = treeutils.makeIdent(methodDecl.pos,vd.sym);
                JCExpression str = treeutils.makeStringLiteral(methodDecl.pos,"Runtime exception while evaluating postconditions - postconditions are undefined in JML");
                JCStatement st = methodCallUtilsStatement(methodDecl.pos(),"reportException",str,ex);
                JCBlock bl = M.at(methodDecl.pos).Block(0, List.<JCStatement>of(st));
                JCCatch catcher = M.at(methodDecl.pos).Catch(vd,bl);
                bl = M.at(methodDecl.pos).Block(0, ensuresStats.toList());
                ensuresStats = new ListBuffer<JCStatement>();
                if (!bl.stats.isEmpty()) {
                    st = M.at(methodDecl.pos).Try(bl,List.<JCCatch>of(catcher),null);
                    ensuresStats.add(st);
                }
            }
            
            if (!isConstructor) {
                
                n = names.fromString("sigEx");
                vd = treeutils.makeVarDef(syms.runtimeExceptionType, n, methodDecl.sym, methodDecl.pos);
                ex = treeutils.makeIdent(methodDecl.pos,vd.sym);
                JCExpression str = treeutils.makeStringLiteral(methodDecl.pos,"Runtime exception while evaluating exceptional postconditions - signals clauses are undefined in JML");
                JCStatement st = methodCallUtilsStatement(methodDecl.pos(),"reportException",str,ex);
                JCBlock bl = M.at(methodDecl.pos).Block(0, List.<JCStatement>of(st));
                JCCatch catcher = M.at(methodDecl.pos).Catch(vd,bl);
                bl = M.at(methodDecl.pos).Block(0, exsuresStats.toList());
                exsuresStats = new ListBuffer<JCStatement>();
                if (!bl.stats.isEmpty()) {
                    st = M.at(methodDecl.pos).Try(bl,List.<JCCatch>of(catcher),null);
                    exsuresStats.add(st);
                }
            
            }
            
        }
        initialStats.appendList(preStats);
        if (ensuresStats.isEmpty() && exsuresStats.isEmpty()) {
            // skip
        } else {
            JCStatement ifstat = M.at(methodPos).If(noException,M.Block(0, ensuresStats.toList()),M.Block(0,exsuresStats.toList()));
            finalizeStats.add(ifstat);
        }
        paramActuals = null;

    }
    

    // VISITOR METHODS
    
    // OK
    @Override
    public void visitTopLevel(JCCompilationUnit that) {
        // OpenJML should never call this, because JCCompilationUnit nodes should be
        // replaced by JmlCompilationUnit nodes. We implement this just in case, but
        // always produce a JmlCompilationUnit node
        if (pureCopy) {
          JmlCompilationUnit n = M.at(that.pos()).TopLevel(that.packageAnnotations,that.pid,convert(that.defs));
          n.docComments = that.docComments; // TODO: This needs to be remapped
          n.endPositions = that.endPositions; // TODO: This needs to be remapped
          n.flags = that.flags;
          //n.mode = that.mode;
          n.lineMap = that.lineMap;
          n.namedImportScope = that.namedImportScope;
          n.packge = that.packge;
          n.setType(that.type);
          n.sourcefile = that.sourcefile;
          n.starImportScope = that.starImportScope;
          //n.specsCompilationUnit = that.specsCompilationUnit;
          //n.specsTopLevelModelTypes = that.specsTopLevelModelTypes;
          result = n;

        }
        if (translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitTopLevel while translating JML: " + that.getClass());
            return;
        }
        error(that.pos(),"Unexpected call of JmlAssertionAdder.visitTopLevel: " + that.getClass());
    }

    // OK
    @Override
    public void visitImport(JCImport that) {
        // OpenJML should never call this, because JCImport nodes should be
        // replaced by JmlImport nodes. We implement this just in case, but
        // always produce a JmlImport node
        
        JCTree qualid = that.qualid;
        if (fullTranslation) qualid = convert(qualid);
        result = M.at(that.pos()).Import(qualid, that.staticImport);
    }

    // OK
    @Override
    public void visitClassDef(JCClassDecl that) {
        // OpenJML should never call this, because JCClassDecl nodes should be
        // replaced by JmlClassDecl nodes. We implement this just in case, but
        // always produce a JmlClassDecl node.

        if (pureCopy) {
            JmlClassDecl d = M.at(that.pos()).ClassDef(
                    convert(that.mods),
                    that.name,
                    convert(that.typarams),
                    convert(that.extending),
                    convert(that.implementing),
                    convert(that.defs));
            d.setType(that.type);
            d.docComment = null;
            d.env = null;
            d.specsDecls = null;
            d.superSymbol = null;
            d.sym = that.sym;
            d.thisSymbol = null;
            d.toplevel = null;
            d.typeSpecs = null;
            d.typeSpecsCombined = null;
            result = d;
            classBiMap.put((JmlClassDecl)that,d);
            return;
        }
        if (translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitClassDef while translating JML: " + that.getClass());
            return;
        }
        error(that.pos(), "Unexpectedly calling JmlAssertionAdder.visitClassDef: " + that.getClass());
    }

    // OK
    @Override
    public void visitMethodDef(JCMethodDecl that) {
        // In OpenJML, we expect to always have JmlMethodDecl nodes, and so 
        // never to call this visit class
        // However, just in case a user creates one, we translate it
        if (pureCopy) {
            JmlMethodDecl m = M.at(that.pos()).MethodDef(
                    convert(that.mods),
                    that.name,
                    convert(that.restype),
                    convert(that.typarams),
                    convert(that.params),
                    convert(that.thrown),
                    convert(that.body),
                    convert(that.defaultValue));
            m.setType(that.type);
            m.sym = that.sym;
            m.cases = null;
            m._this = null;
            m.docComment = null;
            m.methodSpecsCombined = null;
            m.owner = null;
            m.sourcefile = null;
            m.specsDecl = null;
            result = m;
            methodBiMap.put((JmlMethodDecl)that,m);
            return;
        }
        if (translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitMethodDef while translating JML: " + that.getClass());
            return;
        }
        error(that.pos(),"Unexpected visit call in JmlAssertionAdder.visitMethodDef: " + that.getClass());
    }

    // OK
    @Override
    public void visitVarDef(JCVariableDecl that) {
        if (pureCopy) {
            JmlVariableDecl v = M.at(that.pos()).VarDef(
                    convert(that.mods),
                    that.name,
                    convert(that.vartype),
                    convert(that.init));
            v.setType(that.type);
            v.sym = that.sym;
            v.docComment = null;
            v.fieldSpecs = null;
            v.fieldSpecsCombined = null;
            v.sourcefile = null;
            v.specsDecl = null;
            result = v;
            return;
        }
        if (translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitVarDef while translating JML: " + that.getClass());
            return;
        }
        error(that.pos(),"Unexpected visit call in JmlAssertionAdder.visitVarDef: " + that.getClass());
    }

    //OK
    @Override
    public void visitSkip(JCSkip that) {
        if (!pureCopy) addTraceableComment(that);
        result = addStat(M.at(that.pos()).Skip());
        // Caution - JML statements are subclasses of JCSkip
    }

    //OK
    @Override
    public void visitBlock(JCBlock that) {
        JmlMethodDecl prev = this.methodDecl;
        if (currentStatements == null) {
            // We are in an initializer block
            // We need a method symbol to be the owner of declarations 
            // (otherwise they will have the class as owner and be thought to
            // be fields)
            MethodSymbol msym = new MethodSymbol(
                    that.flags, 
                    classDecl.name, 
                    null, 
                    classDecl.sym);
            methodDecl = //M.MethodDef(msym, null,null);
                    new JmlMethodDecl(
                            M.Modifiers(that.flags, M.Annotations(List.<com.sun.tools.javac.code.Attribute.Compound>nil())),
                            classDecl.name,
                            null,
                            null,
                            null,
                            null,
                            null, //body,
                            null,
                            msym);

        }
        JCBlock bl;
        try {
            pushBlock();
            if (exceptionSym == null) {
                initialize2(that.flags & Flags.STATIC);
            }
            scan(that.stats);
            bl = popBlock(that.flags,that.pos());
            if (currentStatements != null) {
                addStat(bl);
            } else {
                classDefs.add(bl);
            }
        } finally {
            methodDecl = prev;
        }
        result = bl;
    }

    // OK - should call visitJmlDoWhileLoop instead
    @Override
    public void visitDoLoop(JCDoWhileLoop that) {
        error(that.pos(),"Unexpected visit call in JmlAssertionAdder.visitDoLoop: " + that.getClass());
    }

    // OK - should call visitJmlWhileLoop instead
    @Override
    public void visitWhileLoop(JCWhileLoop that) {
        error(that.pos(),"Unexpected visit call in JmlAssertionAdder.visitWhileLoop: " + that.getClass());
    }

    // OK - should call visitJmlForLoop instead
    @Override
    public void visitForLoop(JCForLoop that) {
        error(that.pos(),"Unexpected visit call in JmlAssertionAdder.visitForLoop: " + that.getClass());
    }

    // OK - should call visitJmlEnhancedForLoop instead
    @Override
    public void visitForeachLoop(JCEnhancedForLoop that) {
        error(that.pos(),"Unexpected visit call in JmlAssertionAdder.visitForeachLoop: " + that.getClass());
    }
    
    Map<Name,ListBuffer<JCStatement>> labelActiveOldLists = new HashMap<Name,ListBuffer<JCStatement>>();
    Map<Name,ListBuffer<JCStatement>> labelOldLists = new HashMap<Name,ListBuffer<JCStatement>>();

    //OK
    @Override
    public void visitLabelled(JCLabeledStatement that) {
        if (!pureCopy) addStat(comment(that.pos(),"label:: " + that.label + ": ..."));
        // Note that the labeled statement will turn into a block
        // FIXME - the block may have introduced declarations that are then used after the block? also may not work correctcly for labelled loops
        JCLabeledStatement stat = M.at(that.pos()).Labelled(that.label, null);
        treeMap.put(that, stat);
        labelActiveOldLists.put(that.label, currentStatements);
        JCBlock block;
        try {
            block = convertIntoBlock(that.pos(),that.body);
            stat.body = block;
            result = addStat(stat);
        } finally {
            labelActiveOldLists.remove(that.label);
            labelOldLists.put(that.label,  currentStatements);
            treeMap.remove(that);
        }
    }

    //OK
    @Override
    public void visitSwitch(JCSwitch that) {
        if (!pureCopy) {
            addStat(traceableComment(that,that,"switch " + that.getExpression() + " ...","Selection"));
        }
        try {
            JCExpression selector = convertExpr(that.selector);
            if (!pureCopy) {
                if (javaChecks && !selector.type.isPrimitive()) {
                    JCExpression e = treeutils.makeNeqObject(that.pos, selector, treeutils.nullLit);
                    addAssert(that.selector.pos(), Label.POSSIBLY_NULL_VALUE, e);
                }
                if (that.selector.type.equals(syms.stringType)) {
                    // skip
                } else if ((that.selector.type.tsym.flags_field & Flags.ENUM) != 0) {
                    // skip
                } else {
                    selector = addImplicitConversion(that.pos(),syms.intType,selector);
                }
            }
            JCSwitch sw = M.at(that.pos()).Switch(selector, null);
            // record the translation from old to new AST before translating the body
            treeMap.put(that,sw);
            ListBuffer<JCCase> cases = new ListBuffer<JCCase>();
            for (JCCase c: that.cases) {
                JCExpression pat = convertExpr(c.pat);
                JCBlock b = convertIntoBlock(c.pos(),c.stats);
                b.stats = b.stats.prepend(traceableComment(c,c,(c.pat == null ? "default:" : "case " + c.pat + ":"),null));
                JCCase cc = M.at(c.pos).Case(pat,b.stats);
                cases.add(cc);
            }
            sw.cases = cases.toList();
            result = addStat(sw.setType(that.type));
        } finally {
            treeMap.remove(that);
        }
    }

    //OK
    @Override
    public void visitCase(JCCase that) {
        // JCCase is handled directly in visitSwitch
        error(that.pos(),"JmlAssertionAdder.visitCase should not be called");
    }
    
    // OK except concurrency checks
    @Override
    public void visitSynchronized(JCSynchronized that) {
        if (!pureCopy) {
            addTraceableComment(that,"synchronized " + that.getExpression() + " ...");
        }
        JCExpression lock = convertExpr(that.lock);
        if (that.lock instanceof JCParens && ((JCParens)that.lock).expr instanceof JCIdent && ((JCIdent)((JCParens)that.lock).expr).name.toString().equals("this")) {
            // Don't need to check that 'this' is not null, though this is a complicated and error-prone check
        } else if (javaChecks) {
            JCExpression e = treeutils.makeNeqObject(that.lock.pos, lock, treeutils.nullLit);
            addAssert(that.lock.pos(), Label.POSSIBLY_NULL_VALUE, e);
        }
        JCBlock block = convertBlock(that.body);
        result = addStat(M.at(that.pos()).Synchronized(lock, block).setType(that.type));
        // FIXME - need to add concurrency checks
    }

    // OK
    // FIXME - review and cleanup for both esc and rac
    @Override
    public void visitTry(JCTry that) {
        if (!pureCopy) addStat(comment(that.pos(),"try ...")); // Don't need to trace the try keyword
        JCBlock body = convertBlock(that.body);

        List<JCCatch> catchers = null;
        if (that.catchers != null) {
            ListBuffer<JCCatch> ncatchers = new ListBuffer<JCCatch>();
            for (JCCatch catcher: that.catchers) {
                JCBlock block = convertBlock(catcher.getBlock());
                //block.stats = block.stats.prepend(traceableComment(catcher.getParameter(),catcher.getParameter(),"catch (" + catcher.param +") ..."));
                block.stats = block.stats.prepend(comment(catcher.getParameter(),"catch (" + catcher.param +") ..."));
                
                // EXCEPTION = NULL
                int sp = catcher.getParameter().getStartPosition();
                JCIdent exId = treeutils.makeIdent(sp, exceptionSym);
                treeutils.copyEndPosition(exId, catcher.getParameter());
                JCStatement st = treeutils.makeAssignStat(sp, exId, treeutils.nullLit);
                block.stats = block.stats.prepend(st);
                
                JCIdent nid = treeutils.makeIdent(sp, catcher.getParameter().sym);
                treeutils.copyEndPosition(nid, catcher.getParameter());
                exprBiMap.put(nid,convertCopy(nid));
//                block.stats = block.stats.prepend(traceableComment(catcher.getParameter(),nid,"Exception caught"));
// FIXME - the nid is not being evaluated for the trace

                // TERMINATION = 0
                JCIdent termid = treeutils.makeIdent(catcher.pos,terminationSym);
                block.stats = block.stats.prepend(treeutils.makeAssignStat(catcher.pos, termid, treeutils.zero));

                JCVariableDecl odecl = catcher.getParameter();  
                JmlVariableDecl decl = M.at(odecl.pos()).VarDef(odecl.sym,  null); // Catcher declarations have no initializer
                JCCatch ncatcher = M.at(catcher.pos()).Catch(decl,block);
                ncatcher.setType(catcher.type);
                ncatchers.add(ncatcher);
            }
            catchers = ncatchers.toList();
        }
        JCBlock finalizer = convertBlock(that.finalizer);
        List<JCTree> newResources = convertCopy(that.resources);
        // FIXME - no checks implemented on the resources
        JCTry st =  M.at(that.pos()).Try(newResources, body, catchers, finalizer);
        st.setType(that.type);
        result = addStat(st);
        return;

//        ListBuffer<JCStatement> finalizerstats = new ListBuffer<JCStatement>();
//
//        if (that.catchers != null && !that.catchers.isEmpty()) {
// 
//            JCIdent id = M.at(that.pos()).Ident(exceptionSym);
//            JCExpression ret = treeutils.makeEqObject(that.pos, id, treeutils.nullLit);
//            M.at(that.pos());
//            JCIf ifstat = M.If(ret, M.Block(0, List.<JCStatement>nil()), null);
//            finalizerstats.add(ifstat);
//
//            for (JCCatch catcher: that.catchers) {
//                ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
//
//                // [type of catch clause] [catch clause id ] = EXCEPTION
//                id = M.at(that.pos()).Ident(exceptionSym);  // FIXME - should this have a type cast?
//                JCVariableDecl vd = treeutils.makeVarDef(catcher.param.type, catcher.param.name, catcher.param.sym.owner, id);
//                stats.add(vd);
//
//                // EXCEPTION = null
//                id = treeutils.makeIdent(that.pos,exceptionSym);
//                stats.add(treeutils.makeAssignStat(that.pos, id, treeutils.nullLit));
//
//                // TERMINATION = 0
//                id = treeutils.makeIdent(that.pos,terminationSym);
//                stats.add(treeutils.makeAssignStat(that.pos,id, treeutils.zero));
//
//                // FIXME - need to put in the instanceof operation
//
//                // add statements from the catch block
//                JCBlock catchblock = convertBlock(catcher.body);
//                stats.addAll(catchblock.stats);
//
//                M.at(catcher.pos());
//                JCIf ifstatc = M.If(treeutils.trueLit, M.Block(catcher.body.flags, stats.toList()), null);
//                ifstat.elsepart = ifstatc;
//                ifstat = ifstatc;
//            }
//        }
//
//        if (that.finalizer != null) {
//            JCBlock finalizer = convertBlock(that.finalizer);
//            finalizerstats.add(finalizer);
//        }
//
//        // if (TERMINATION > 0) return ...
//        JCIdent id = treeutils.makeIdent(that.pos, terminationSym);
//        JCBinary cond = treeutils.makeBinary(that.pos,JCTree.GT, id, treeutils.zero );
//        JCIf ifstat = M.If(cond,  M.Return(resultSym == null ? null : M.Ident(resultSym)), null);
//        finalizerstats.add(ifstat);
//
//        // if (TERMINATION < 0) throw ...
//        id = treeutils.makeIdent(that.pos, terminationSym);
//        cond = treeutils.makeBinary(that.pos,JCTree.LT, id, treeutils.zero );
//        ifstat = M.If(cond,  M.Throw(M.Ident(exceptionSym)), null);
//        finalizerstats.add(ifstat);
//        
//        
//        JCStatement stat = M.at(that.pos()).Try(body, List.<JCCatch>nil(), M.Block(0, finalizerstats.toList()));
//        addStat(stat);
//        result = stat;
    }

    // OK
    @Override
    public void visitCatch(JCCatch that) {
        // Catch statements are handled along with Try
        error(that.pos(),"JmlAssertionAdder.visitCatch should not be called");
    }

    // OK
    @Override
    public void visitConditional(JCConditional that) {
        if (!pureCopy) addStat(comment(that.pos()," ... conditional ..."));

        JCExpression cond = convertExpr(that.cond);
        if (translatingJML || pureCopy ) {
            JCExpression prev = condition;
            try {
                // Note if pureCopy is true we are doing a strict copy.
                // Although we compute 'condition' here, it should not be used
                // anywhere.
                condition = treeutils.makeAnd(that.pos, prev, cond);
                JCExpression truepart = convertExpr(that.truepart);
                condition = treeutils.makeAnd(that.pos, prev, treeutils.makeNot(that.falsepart.pos, cond)); // FIXME - should we copy cond before reusing?
                JCExpression falsepart = convertExpr(that.falsepart);
                result = eresult = M.at(that.pos()).Conditional(cond,truepart,falsepart).setType(that.type);
            } finally {
                condition = prev;
            }
            return;
        }
        if (!cond.type.isPrimitive()) cond = addImplicitConversion(cond.pos(),syms.booleanType,cond);
        
        Name resultname = names.fromString(Strings.conditionalResult + (++count));
        JCVariableDecl vdecl = treeutils.makeVarDef(that.type, resultname, esc? null : methodDecl.sym, that.pos);
        addStat(vdecl);
        
        pushBlock();

        JCExpression tres = convertExpr(that.truepart);
        tres = addImplicitConversion(that.truepart.pos(),that.type,tres);
        JCIdent id = treeutils.makeIdent(that.truepart.pos, vdecl.sym);
        if (esc) {
            addAssumeEqual(that.truepart.pos(), Label.ASSIGNMENT, 
                    id, tres);
        } else { // rac
            addStat( treeutils.makeAssignStat(that.truepart.pos, id, tres));
        }
        JCBlock trueblock = popBlock(0,that.truepart.pos());
        
        pushBlock();

        JCExpression fres = convertExpr(that.falsepart);
        fres = addImplicitConversion(that.falsepart.pos(),that.type,fres);
        id = treeutils.makeIdent(that.falsepart.pos, vdecl.sym);
        if (esc) {
            addAssumeEqual(that.falsepart.pos(), Label.ASSIGNMENT, 
                    id, fres);
        } else { // rac
            addStat( treeutils.makeAssignStat(that.falsepart.pos, id, fres));
        }
        
        JCStatement stat = M.If(cond, trueblock, popBlock(0,that.falsepart.pos()));
        
        addStat(stat);
        result = eresult = treeutils.makeIdent(that.pos, vdecl.sym);
    }

    // OK
    @Override
    public void visitIf(JCIf that) {
        if (!pureCopy) {
            addStat(traceableComment(that,that,"if " + that.getCondition() + " ...", "Condition"));
        }
        JCExpression cond = convertExpr(that.cond);
        cond = addImplicitConversion(that.cond.pos(),syms.booleanType,cond);

        // The scanned result of the then and else parts must always be a block
        // because multiple statements might be produced, even from a single
        // statement in the branch.
        
        JCBlock thenpart = convertIntoBlock(that.thenpart.pos(),that.thenpart);
        
        JCBlock elsepart = that.elsepart == null ? null :
            convertIntoBlock(that.elsepart.pos(), that.elsepart);

        JCStatement st = M.at(that.pos()).If(cond,thenpart,elsepart).setType(that.type);
        result = addStat( st );
    }
    
    protected void addTraceableComment(JCTree t) {
        JCStatement c = comment(t);
        pathMap.put(t, c);
        addStat(c);
    }
    
    protected void addTraceableComment(JCTree t, String description) {
        addStat(traceableComment(t,t,description,null));
    }

    protected void addTraceableComment(JCTree t, JCExpression expr, String description) {
        addStat(traceableComment(t,expr,description,null));
    }

    protected void addTraceableComment(JCTree t, JCTree expr, String description, String info) {
        addStat(traceableComment(t,expr,description,info));
    }

    protected JCStatement traceableComment(JCTree t, JCTree expr, String description, String info) {
        JmlStatementExpr c = comment(t.pos(),description);
        c.id = info;
        pathMap.put(expr, c);
        return c;
    }

    @Override
    public void visitExec(JCExpressionStatement that) {
        if (!pureCopy) {
            addTraceableComment(that);
        }
        JCExpression arg = convertExpr(that.getExpression());
        
        // For rac and esc, assignments become a new variable,
        // so no exec statement is needed, and arg is then an ident.
        
        // Similarly, method invocations that return a value become a 
        // temporary id, and no additional Exec statement is needed
        
        // Otherwise we create an Exec statement
        
        if (arg instanceof JCMethodInvocation || arg instanceof JCAssign || arg instanceof JCAssignOp || arg instanceof JCUnary) {
            result = addStat( M.at(that.pos()).Exec(arg).setType(that.type) );
            //pathMap.put(that, result);
//        } else if (arg instanceof JCIdent) {
//            // result and eresult are unchanged from the call to convertExpr
//        } else if (arg != null) {
//            log.warning(that.pos,"jml.internal.notsobad", "Unexpected kind of AST in visitExec: " + arg.getClass());
        } else {
            //pathMap.put(that,lastStat);
        }
    }

    // OK
    @Override
    public void visitBreak(JCBreak that) {
        if (!pureCopy) {
            addTraceableComment(that);
        }
        JCBreak st = M.at(that.pos()).Break(that.label);
        st.target = treeMap.get(that.target);
        if (st.target == null) {
        	error(that.pos(),"Unknown break target");
        }
        st.setType(that.type);
        result = addStat(st);
    }

    // OK
    @Override
    public void visitContinue(JCContinue that) {
        if (!pureCopy) {
            addTraceableComment(that);
        }
        if (that.label == null && !pureCopy) {
            // The translation of loops puts the body of a loop in its own
            // block so that continue statements can break out of it and go
            // to do the 'step' part of the loop. The continue should be
            // exiting the innermost loop, but a break may have a more inner
            // block - so we always put a label and set the target.
            JCBreak st = M.at(that.pos()).Break(null);
            st.setType(that.type);
            st.label = continueStack.peek().getLabel();
            st.target = continueStack.peek();
            result = addStat(st);
        } else {
            JCContinue st = M.at(that.pos()).Continue(that.label);
            st.setType(that.type);
            st.target = treeMap.get(that.target);
            if (st.target == null) {
                error(that.pos(),"Unknown continue target");
            }
            result = addStat(st);
        }
    }
    

    // OK
    @Override
    public void visitReturn(JCReturn that) {
        if (!pureCopy) addTraceableComment(that);

        JCExpression retValue = convertExpr(that.getExpression());
        if (!pureCopy) {
            if (retValue != null) {
                retValue = addImplicitConversion(that.pos(),methodDecl.restype.type,retValue);
                JCIdent resultid = treeutils.makeIdent(that.pos,resultSym);
                JCStatement stat = treeutils.makeAssignStat(that.pos,resultid,retValue);
                addStat(stat);
                retValue = treeutils.makeIdent(that.pos,resultSym);
            }
            
            // Record the value of the termination location
            JCIdent id = treeutils.makeIdent(that.pos,terminationSym);
            JCLiteral intlit = treeutils.makeIntLiteral(that.pos,that.pos);
            JCStatement stat = treeutils.makeAssignStat(that.pos,id,intlit);
            addStat(stat);
            
            // If the return statement is in a finally block, there may have been an exception
            // in the process of being thrown - so we set EXCEPTION to null.
            id = treeutils.makeIdent(that.pos,exceptionSym);
            stat = treeutils.makeAssignStat(that.pos,id,treeutils.nullLit);
            addStat(stat);
        }
        
        result = addStat( M.at(that.pos()).Return(retValue).setType(that.type) );
    }

    // OK
    // FIXME - review for esc
    @Override
    public void visitThrow(JCThrow that) {
        if (!pureCopy) addTraceableComment(that);

        if (!esc) {
            JCExpression expr = convertExpr(that.getExpression());
            if (rac) {
                JCIdent id = treeutils.makeIdent(that.pos,exceptionSym);
                addStat( treeutils.makeAssignStat(that.pos,id,expr) );
            }
            result = addStat(M.at(that.pos()).Throw(expr).setType(that.type));
            return;
        }
        
        // assert expr != null;
        pushBlock();
        JCExpression exceptionExpr = convertExpr(that.expr);
        JCExpression e = treeutils.makeNeqObject(that.expr.pos, exceptionExpr, treeutils.makeNullLiteral(that.expr.getEndPosition(log.currentSource().getEndPosTable())));
        if (javaChecks) addAssert(e.pos(), Label.POSSIBLY_NULL_VALUE, e);
        
        if (that.expr.type.tag != TypeTags.BOT) {
            // Declare a local variable of the type of the exception expression, initialilzed to the expression
            Name local = names.fromString(Strings.exceptionVarString + "_L_" + that.pos);
            JCVariableDecl decl = treeutils.makeVarDef(that.expr.type,local,exceptionSym.owner,exceptionExpr); 
            addStat(decl);
            
            // Set the value of the global EXCEPTION variable to the expression
            JCIdent id = treeutils.makeIdent(that.pos,exceptionSym);
            JCIdent localid = treeutils.makeIdent(exceptionExpr.pos,decl.sym);
            JCExpressionStatement assign = treeutils.makeAssignStat(that.pos,id,localid);
            exprBiMap.put(that, assign);
            exprBiMap.put(that, assign.expr);
            addStat(assign);
            
            // Assign the termination value
            JCIdent tid = treeutils.makeIdent(that.pos,terminationSym);
            JCStatement term = M.Exec(M.Assign(tid,treeutils.makeIntLiteral(that.pos,-that.pos)));
            addStat(term);
            
            // throw the local expression value
            localid = treeutils.makeIdent(that.pos,decl.sym);
            JCThrow thrw = M.at(that.pos()).Throw(localid);
            addStat(thrw);
            
        }
        JCBlock block = popBlock(0,that.pos());
        result = addStat(block);
    }

    // OK - this is a Java assert statement
    @Override
    public void visitAssert(JCAssert that) {
        // FIXME - in esc we may want to treat this as an exception throwing Java statement
        
        // ESC will eventually convert this to a Jml assertion, but RAC wants
        // it left as a Java assertion statement
        if (!pureCopy) addTraceableComment(that);
        
        JCExpression cond = convertExpr(that.getCondition());
        JCExpression info = convertExpr(that.getDetail());
        
        if (pureCopy || rac) {
            result = addStat( M.at(that.pos()).Assert(cond, info).setType(that.type) );
        } else { // esc
            result = addAssert(that.pos(),Label.EXPLICIT_ASSERT,cond,null,null,info);
            if (info != null) newTemp(info); // The deetail expression is evaluated but not used anywhere
        }
    }
    
    // FIXME - review all the assignable checks for appropriate use of translations and this
    
    protected
    boolean isContainedIn(VarSymbol x, VarSymbol y) {
        if (x == y) return true;
        if (x == classDecl.thisSymbol && y == currentThisId.sym) return true;
        FieldSpecs fs = specs.getSpecs(x);
        for (JmlTypeClause tc: fs.list) {
            if (tc.token == JmlToken.IN) {
                JmlTypeClauseIn inclause = (JmlTypeClauseIn)tc;
                for (JmlGroupName gn: inclause.list) {
                    if (isContainedIn(gn.sym,y)) return true;
                }
            }
        }
        return false;
    }
    
    /** Check that the given storeref is a subset of the given 
     * pstoreref, returning the condition under which the storeref
     * is allowed.
     */
    protected
    JCExpression assignmentAllowed(JmlStoreRefKeyword storeref, JCExpression pstoreref) {
        DiagnosticPosition pos = storeref.pos();
        if (pstoreref instanceof JmlStoreRefKeyword && ((JmlStoreRefKeyword)pstoreref).token == JmlToken.BSEVERYTHING) return treeutils.trueLit;
        JmlToken token = storeref.token;
        if (token == JmlToken.BSNOTHING) return treeutils.trueLit; 
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (token == JmlToken.BSEVERYTHING && ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (token == JmlToken.BSEVERYTHING && ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            if (token == JmlToken.BSEVERYTHING) return treeutils.falseLit; 

        } else if (pstoreref instanceof JCFieldAccess) {
            if (token == JmlToken.BSEVERYTHING) return treeutils.falseLit; 

        } else if (pstoreref instanceof JCArrayAccess) {
            if (token == JmlToken.BSEVERYTHING) return treeutils.falseLit; 

        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            if (token == JmlToken.BSEVERYTHING) return treeutils.falseLit; 

        }
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + storeref + " vs. " + pstoreref);
        return treeutils.falseLit;
    }
    
    /** Check that the given id is a subset of the given 
     * pstoreref, returning the condition under which the id
     * is allowed.
     */
    protected
    JCExpression assignmentAllowed(JCIdent id, JCExpression pstoreref, VarSymbol baseThisSym, VarSymbol targetThisSym) {
        DiagnosticPosition pos = id.pos();
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            JCIdent pid = (JCIdent)pstoreref;
            if (id.sym == pid.sym) {
                if (baseThisSym == targetThisSym) return treeutils.trueLit;
                JCExpression id1 = treeutils.makeIdent(id.pos, targetThisSym);
                JCExpression id2 = treeutils.makeIdent(pstoreref.pos, baseThisSym);
                return treeutils.makeEqObject(id.pos, id1, id2);
            }
            else return treeutils.falseLit;

        } else if (pstoreref instanceof JCFieldAccess) {
            // TODO: Check that this.* includes static fields of a class
            JCFieldAccess pfa = (JCFieldAccess)pstoreref;
            JCExpression sel = pfa.selected;
            Symbol s0 = sel instanceof JCIdent ? ((JCIdent)sel).sym : 
                sel instanceof JCFieldAccess ? ((JCFieldAccess)sel).sym :
                    null;
                while (true) {
                    if (sel instanceof JCArrayAccess) { sel = ((JCArrayAccess)sel).indexed; continue; }
                    if (sel instanceof JmlStoreRefArrayRange) { sel = ((JmlStoreRefArrayRange)sel).expression; continue; }
                    break;
                }
                Symbol s = sel instanceof JCIdent ? ((JCIdent)sel).sym : 
                    sel instanceof JCFieldAccess ? ((JCFieldAccess)sel).sym :
                        null;
                    if (id.sym != pfa.sym && pfa.sym != null) return treeutils.falseLit;
                    if (id.sym.isStatic()  && pfa.sym != null) return treeutils.trueLit;
                    if (id.sym.isStatic()  && pfa.sym == null && s0 == classDecl.sym) return treeutils.trueLit;
                    if (id.sym.isStatic()  && pfa.sym == null && s0 != classDecl.sym) return treeutils.falseLit;
                    if (!id.sym.isStatic() && pfa.sym == null) {
                        if (s instanceof Symbol.ClassSymbol) return treeutils.falseLit;
                    }
                    JCIdent idthis = treeutils.makeIdent(pos.getPreferredPosition(), targetThisSym);
                    JCExpression result = treeutils.makeEqObject(pos.getPreferredPosition(), idthis, 
                            convertJML(pfa.selected)); // FIXME - needs check for not implemented
                    return result; 

        } else if (pstoreref instanceof JCArrayAccess) {
            return treeutils.falseLit; 

        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            return treeutils.falseLit; 
        }
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + id + " vs. " + pstoreref);
        return treeutils.falseLit;
    }
    
    /** Check that the given storeref is a subset of the given 
     * pstoreref, returning the condition under which the storeref
     * is allowed.
     */
    protected
    JCExpression assignmentAllowed(JCFieldAccess fa, JCExpression pstoreref, VarSymbol baseThisSym, VarSymbol targetThisSym) {
        DiagnosticPosition pos = fa.pos();
        int posp = pos.getPreferredPosition();
        JCExpression pfac = pstoreref instanceof JCFieldAccess && ((JCFieldAccess)pstoreref).sym == null ? 
                pstoreref
                : convertJML(pstoreref);
        if (pfac instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pfac).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pfac instanceof JCIdent) {
            JCIdent pid = (JCIdent)pfac;
            if (!isContainedIn((VarSymbol)fa.sym,(VarSymbol)pid.sym)) return treeutils.falseLit;
            if (pid.sym.isStatic()) return treeutils.trueLit;
            JCIdent idthis = treeutils.makeIdent(posp, baseThisSym);
            JCExpression result = treeutils.makeEqObject(posp, idthis, 
                     convertJML(fa.selected));

            return result; 

        } else if (pfac instanceof JCFieldAccess) {
            JCFieldAccess pfa = (JCFieldAccess)pfac;
            if (pfa.sym != null) {
                boolean contained = isContainedIn((VarSymbol)fa.sym,(VarSymbol)pfa.sym);
                if (!contained) {
                    // a.x vs b.y with x != y, so automatically false
                    return treeutils.falseLit;
                }
                if (contained && !pfa.sym.isStatic()) {
                    // a.x vs. b.x  with x not static, so result is (a == b)
                    JCExpression result = treeutils.makeEqObject(posp, convertJML(fa.selected), convertJML(pfa.selected));
                    return result;
                }
                if (contained && pfa.sym.isStatic()) {
                    // a.x vs. b.x  with x static, so result is true - a and b have to be the same type
                    return treeutils.trueLit;
                }
            }
            if (pfa.sym == null) {  // FIXME - review this
                // a.x vs b.* (x may be *, a,b may be expressions or types)
                // FIXME - it matters here whether this.* includes static fields
                JCExpression e = fa.selected;
                Symbol fs = e instanceof JCIdent ? ((JCIdent)e).sym :
                    e instanceof JCFieldAccess ? ((JCFieldAccess)e).sym :
                        null;
                e = convertJML(pfa.selected);
                Symbol pfs = e instanceof JCIdent ? ((JCIdent)e).sym :
                        e instanceof JCFieldAccess ? ((JCFieldAccess)e).sym :
                            null;
                if (pfs instanceof Symbol.ClassSymbol) {
                    // ?.x vs
                    boolean same = fs == pfs;
                    JCExpression result = same ? treeutils.trueLit : treeutils.falseLit;
                    return result;
                } else if (fs instanceof Symbol.ClassSymbol) {
                    boolean same = fs == pfs;
                    JCExpression result = same ? treeutils.trueLit : treeutils.falseLit;
                    return result;
                } else {
                    JCExpression result = treeutils.makeEqObject(posp, convertJML(fa.selected), e);
                    return result;
                }
            }
            
        } else if (pfac instanceof JCArrayAccess) {
            return treeutils.falseLit; 
            
        } else if (pfac instanceof JmlStoreRefArrayRange) {
            return treeutils.falseLit; 
            
        }
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + fa + " vs. " + pfac);
        return treeutils.falseLit;
    }

    /** Check that the given storeref is a subset of the given 
     * pstoreref, returning the condition under which the storeref
     * is allowed.
     */
    protected
    JCExpression assignmentAllowed(JCArrayAccess aa, JCExpression pstoreref) {
        DiagnosticPosition pos = aa.pos();
        int posp = pos.getPreferredPosition();
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            return treeutils.falseLit; 

        } else if (pstoreref instanceof JCFieldAccess) {
            return treeutils.falseLit; 
            
        } else if (pstoreref instanceof JCArrayAccess) {
            JCArrayAccess paa = (JCArrayAccess)pstoreref;
            JCExpression a1 = convertJML(aa.indexed);
            JCExpression result = treeutils.makeEqObject(posp, a1, convertJML(paa.indexed));
            if (paa.index == null ) return result;
            if (aa.index == null) return treeutils.falseLit;
            a1 = convertJML(aa.index);
            result = treeutils.makeAnd(posp,result,
                    treeutils.makeBinary(posp,JCTree.EQ,treeutils.inteqSymbol,a1,convertJML(paa.index)));
            return result;
            
        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange paa = (JmlStoreRefArrayRange)pstoreref;
            JCExpression a1 = convertJML(aa.indexed);
            JCExpression arrayConverted = convertJML(paa.expression);
            JCExpression result = treeutils.makeEqObject(posp, a1, arrayConverted);
            if (aa.index == null) {
                if (paa.lo == null && paa.hi == null) return result;
                if (paa.hi == null) return treeutils.makeAnd(posp, result, treeutils.makeBinary(pos.getPreferredPosition(), JCTree.EQ, treeutils.inteqSymbol, convertJML(paa.lo),treeutils.zero));
                
                // FIXME - compare paa.hi to array.length, paa.lo to zero if not null
                return treeutils.falseLit;
            } else {
                JCExpression aat = aa.index;
                result = treeutils.makeAnd(posp,result,
                        treeutils.makeAnd(posp,
                                treeutils.makeBinary(posp,JCTree.LE,treeutils.intleSymbol,
                                        paa.lo == null ? treeutils.zero : convertJML(paa.lo),convert(aat)),
                                        paa.hi == null ? treeutils.makeBinary(posp, JCTree.LT,treeutils.intltSymbol,
                                                aat, treeutils.makeLength(paa.pos(),arrayConverted) )
                                                : treeutils.makeBinary(posp, JCTree.LE,treeutils.intleSymbol,
                                                        aat, convertJML(paa.hi))
                                                ));
                return result;
            }
        }
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + aa + " vs. " + pstoreref);
        return treeutils.falseLit;
    }

    /** Check that the given storeref is a subset of the given 
     * pstoreref, returning the condition under which the storeref
     * is allowed.
     */
    protected
    JCExpression assignmentAllowed(JmlStoreRefArrayRange aa, JCExpression pstoreref) {
        DiagnosticPosition pos = aa.pos();
        int posp = pos.getPreferredPosition();
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            return treeutils.falseLit; 

        } else if (pstoreref instanceof JCFieldAccess) {
            return treeutils.falseLit; 
            
        } else if (pstoreref instanceof JCArrayAccess) {
            JCArrayAccess paa = (JCArrayAccess)pstoreref;
            JCExpression result = treeutils.makeEqObject(posp, convertJML(aa.expression), convertJML(paa.indexed));
            if (paa.index == null) return result;
            JCExpression paat = convertJML(paa.index);
            result = treeutils.makeAnd(posp, result, treeutils.makeBinary(posp,JCTree.EQ,treeutils.inteqSymbol, 
                    aa.lo == null ? treeutils.zero : convertJML(aa.lo), paat));
//            result = treeutils.makeAnd(pos, result, treeutils.makeBinary(pos,JCTree.EQ,treeutils.inteqSymbol, 
//                    aa.hi == null ? /* FIXME - array length -1 */ : jmlrewriter.translate(aa.hi), paat));
            return result;
        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange paa = (JmlStoreRefArrayRange)pstoreref;
            JCExpression result = treeutils.makeEqObject(posp, convertJML(aa.expression), convertJML(paa.expression));
            JCExpression a1 = aa.lo == null ? treeutils.zero : convertJML(aa.lo);
            JCExpression a2 = paa.lo == null ? treeutils.zero : convertJML(paa.lo);
            result = treeutils.makeAnd(posp, result, treeutils.makeBinary(posp,JCTree.LE,treeutils.intleSymbol, 
                    a2, a1));

            // FIXME - in the null case we want array length - 1
            a1 = aa.hi == null ? treeutils.zero : convertJML(aa.hi);
            a2 = paa.hi == null ? treeutils.zero : convertJML(paa.hi);
            result = treeutils.makeAnd(posp, result, treeutils.makeBinary(pos.getPreferredPosition(),JCTree.LE,treeutils.intleSymbol, 
                    a1, a2));

            return result;
        }
        
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + aa + " vs. " + pstoreref);
        return treeutils.falseLit;
    }

    /** Check that the given storeref is a subset of the given 
     * pstoreref, returning the condition under which the storeref
     * is allowed.
     */
    protected 
    JCExpression assignmentAllowed(JCExpression storeref, JCExpression pstoreref,
            VarSymbol baseThisSym, VarSymbol targetThisSym) {
        if (storeref instanceof JmlStoreRefKeyword) {
            return assignmentAllowed((JmlStoreRefKeyword)storeref,pstoreref);

        } else if (storeref instanceof JCIdent) {
            return assignmentAllowed((JCIdent)storeref,pstoreref,baseThisSym,targetThisSym);
            
        } else if (storeref instanceof JCFieldAccess) {
            return assignmentAllowed((JCFieldAccess)storeref,pstoreref,baseThisSym,targetThisSym);
            
        } else if (storeref instanceof JCArrayAccess) {
            return assignmentAllowed((JCArrayAccess)storeref,pstoreref);
            
        } else if (storeref instanceof JmlStoreRefArrayRange) {
            return assignmentAllowed((JmlStoreRefArrayRange)storeref,pstoreref);
            
        }
        
        log.error(storeref.pos,"esc.not.implemented", "Assignability comparison: " + storeref + " vs. " + pstoreref);
        return treeutils.falseLit;
    }
    
    /** Add assertions that the lhs is allowed to 
     * be assigned to within the given method; pos is the position of any
     * generated assertion.
     */
    protected void checkAssignable(JCMethodDecl mdecl, JCExpression lhs, DiagnosticPosition pos,
            VarSymbol baseThisSym, VarSymbol targetThisSym) {
        for (JmlSpecificationCase c: specs.getDenestedSpecs(methodDecl.sym).cases) {
            JCExpression check = checkAssignable(lhs,c,baseThisSym,targetThisSym);
            if (check != treeutils.trueLit) {
                DiagnosticPosition cpos = c.pos();
                for (JmlMethodClause m : c.clauses) {
                    if (m.token == JmlToken.ASSIGNABLE) { cpos = m.pos(); break; }
                }
                addAssert(pos,Label.ASSIGNABLE,check,cpos,c.sourcefile);
            }
        }

    }

    /** Check that the given storeref is allowed by the given 
     * specification case, returning the condition under which the storeref
     * is allowed.
     */
    protected @Nullable
    JCExpression checkAssignable(JCExpression storeref, JmlSpecificationCase c, Symbol baseThisSym, Symbol targetThisSym) {
        // If the storeref is a local identifier, then assignment is allowed
        if ((storeref instanceof JCIdent) && ((JCIdent)storeref).sym.owner instanceof Symbol.MethodSymbol) return treeutils.trueLit; 

        JCIdent pre = preconditions.get(c);
        pre = treeutils.makeIdent(pre.pos, pre.sym); // a new id for the same symbol
        boolean anyAssignableClauses = false;
        JCExpression asg = treeutils.falseLit;
        for (JmlMethodClause mclause : c.clauses) {
            try {
                switch (mclause.token) {
                    case ASSIGNABLE:
                        // Is storeref allowed by some item in the parent method's list?
                        List<JCExpression> pstorerefs = ((JmlMethodClauseStoreRef)mclause).list;
                        for (JCExpression pstoreref: pstorerefs) {
                            JCExpression nasg = assignmentAllowed(storeref,pstoreref,(VarSymbol)baseThisSym,(VarSymbol)targetThisSym);
                            // optimizing asg = asg || nasg
                            asg = nasg == treeutils.trueLit ? nasg :
                                asg == treeutils.falseLit ? nasg :
                                    nasg == treeutils.falseLit ? asg :
                                        asg == treeutils.trueLit ? asg :
                                            treeutils.makeOr(storeref.pos,asg,nasg);
                        }
                        anyAssignableClauses = true;
                        break;
                    default:
                        break;
                }
            } catch (JmlNotImplementedException e) {
                notImplemented("assignable clause containing ",e);
            }
        }
        // If there are no assignable clauses at all, the default is
        // \everything - so the result of the check is then true.
        if (!anyAssignableClauses) asg = treeutils.trueLit;
        if (asg != treeutils.trueLit) {
            return treeutils.makeImplies(storeref.pos, pre, asg);
        } else {
            return asg;
        }
    }
    
    // FIXME - document and review
    protected void checkAgainstCallerSpecs(JCExpression scannedItem, JCExpression precondition,
            JCIdent baseThisId, /*@nullable*/ JCIdent targetThisId) {
        JmlMethodSpecs mspecs = specs.getDenestedSpecs(methodDecl.sym);
        if (mspecs == null) return; // FIXME - why would this happen?
        List<JmlSpecificationCase> cases = mspecs.cases;
        for (JmlSpecificationCase c : cases) {
            JCExpression condition = checkAssignable(scannedItem,c, baseThisId.sym,targetThisId == null ? null : targetThisId.sym);
            if (condition != treeutils.trueLit) {
                condition = treeutils.makeImplies(scannedItem.pos, precondition, condition);
                addAssert(scannedItem.pos(),Label.ASSIGNABLE,condition,c.pos(),c.sourcefile);
            }
        }
    }

    // FIXME - needs work
    @Override
    public void visitApply(JCMethodInvocation that) {
        //System.out.println("APPLY ENTER " + statementStack.size());
        // FIXME - needs result set - needs proper handling of pure methods etc.
        if ((translatingJML && rac) || pureCopy) {
            // FIXME - need to check definedness by testing preconditions
            List<JCExpression> typeargs = convertExprList(that.typeargs);
            JCExpression meth = convertExpr(that.meth);
            List<JCExpression> args = convertExprList(that.args);
            JCMethodInvocation app = M.at(that.pos()).Apply(typeargs, meth, args).setType(that.type);
            app.varargsElement = that.varargsElement; // a Type
            result = eresult = app;
            return;
        }
        applyHelper(that);
    }
    
    protected List<JCExpression> convertArgs(List<JCExpression> args, List<Type> argtypes) {
        ListBuffer<JCExpression> out = new ListBuffer<JCExpression>();
        Iterator<Type> iter = argtypes.iterator();
        for (JCExpression a: args) {
            a = convertExpr(a);
            a = addImplicitConversion(a.pos(),iter.next(),a);
            if ((a instanceof JCIdent) && ((JCIdent)a).name.toString().startsWith(Strings.tmpVarString)) {
            } else {
                // This check is a hack and a bit expensive. It makes sure that
                // every argument is represented by a tetmporary variable. 
                // Without this an argument that is just an Ident or a Literal
                // and is not used ends up without its value captured for
                // tracing
                a = newTemp(a);
            }
            out.add(a);
        }
        return out.toList();
    }
    
    protected void applyHelper(JCExpression that) {

        Symbol savedSym = resultSym;
        Symbol savedExceptionSym = exceptionSym; // FIXME - doesnot get changed so why save it?
        JCIdent savedThisId = currentThisId;
        Map<Symbol,JCExpression> savedParamActuals = paramActuals; // restore in a finall block FIXME
        Map<Symbol,JCVariableDecl> savedpreparams = preparams;
        ListBuffer<JCStatement> savedOldStatements = oldStatements;
        
        JCVariableDecl exceptionDeclCall = 
                translatingJML && esc? null : treeutils.makeVarDef(syms.exceptionType, exceptionNameCall, methodDecl.sym, that.pos);
        
        
        try {
            boolean methodIsStatic = methodDecl.sym.isStatic();
            boolean isConstructor = methodDecl.sym.isConstructor();

            // Translate the method name, and determine the thisid for the
            // method call
            
            JCIdent newThisId;
            List<JCExpression> trArgs;
            List<JCExpression> typeargs;
            Type varargsElement;
            JCExpression meth = null;
            JCMethodInvocation apply = null;
            JCNewClass newclass = null;
            
            JCExpression convertedCaller = null;
            MethodSymbol calleeMethodSym = null;

            if (that instanceof JCMethodInvocation) {
                apply = (JCMethodInvocation)that;
                meth = apply.meth;
                trArgs = apply.args;
                typeargs = apply.typeargs;
                varargsElement = apply.varargsElement;
            } else if (that instanceof JCNewClass) {
                newclass = (JCNewClass) that;
                trArgs = newclass.args;
                typeargs = newclass.typeargs;
                varargsElement = newclass.varargsElement;
            } else {
                error(that.pos(),"Invalid argument type for JmlAssertionAdder.applyHelper");
                return;
            }

            // FIXME - do we need to convert the varargsElement or its associated expressions
            // Convert all the expressions
            // There is duplicate code because we have to be sure to evaluate everything in order
            JCExpression trExpr = null;
            if (meth instanceof JCIdent) {
                JCIdent id = (JCIdent)meth; // There is no conversion for method names - FIXME - but do we need to get the correct 'this'?
                
                typeargs = convert(typeargs);
                trArgs = convertArgs(trArgs,meth.type.asMethodType().argtypes);

                calleeMethodSym = (MethodSymbol)id.sym;

                JCMethodInvocation mExpr = M.at(that.pos()).Apply(typeargs,meth,trArgs);
                mExpr.setType(that.type);
                mExpr.varargsElement = varargsElement;
                trExpr = mExpr;
                newThisId = id.sym.isStatic() ? null : currentThisId;
                
            } else if (meth instanceof JCFieldAccess) {
                JCFieldAccess fa = (JCFieldAccess)meth;
                JCExpression convertedReceiver = null;
                newThisId = null;
                if (!treeutils.isATypeTree(fa.selected)) {
                    convertedReceiver = convertExpr(fa.selected); // This checks for null, I would think, if necessary FIXME - verify this.
                    if (!fa.sym.isStatic()) {
                        convertedReceiver = newTemp(convertedReceiver);
                        newThisId = (JCIdent)convertedReceiver;
                        if (javaChecks) {
                            // Check that receiver is not null
                            JCExpression e = treeutils.makeNeqObject(fa.selected.pos,convertedReceiver,treeutils.nullLit);
                            addAssert(fa.selected.pos(),Label.POSSIBLY_NULL_DEREFERENCE,e); // FIXME - if this is called within JML, then UNDEFINED_NULL?
                        }
                    }
                } else {
                    convertedReceiver = fa.selected;
                    // FIXME - expand type ?
                }

                typeargs = convert(typeargs);
                trArgs = convertArgs(trArgs,meth.type.asMethodType().argtypes);

                JCFieldAccess fameth = M.at(meth.pos).Select(convertedReceiver, fa.name);
                fameth.sym = fa.sym;
                fameth.type = fa.type;
                calleeMethodSym = (MethodSymbol)fa.sym;
                
                JCMethodInvocation mExpr = M.at(that.pos()).Apply(typeargs,fameth,trArgs);
                mExpr.setType(that.type);
                mExpr.varargsElement = varargsElement; // a Type
                trExpr = mExpr;
                
            } else if (newclass != null) {
                
                calleeMethodSym = (MethodSymbol)newclass.constructor;
                
                JCExpression convertedReceiver = convertExpr(newclass.encl);
                if (javaChecks && convertedReceiver != null && !treeutils.isATypeTree(convertedReceiver)) {
                    // Check that receiver is not null
                    JCExpression e = treeutils.makeNeqObject(newclass.encl.pos,convertedReceiver,treeutils.nullLit);
                    addAssert(newclass.encl.pos(),Label.POSSIBLY_NULL_DEREFERENCE,e); // FIXME - if this is called within JML, then UNDEFINED_NULL?
                }

                typeargs = convert(typeargs);
                trArgs = convertArgs(trArgs,calleeMethodSym.type.asMethodType().argtypes);

                JCNewClass expr = M.at(that.pos()).NewClass(
                        convertedReceiver,
                        typeargs, 
                        convert(newclass.clazz), 
                        trArgs, 
                        convert(newclass.def));
                expr.constructor = newclass.constructor;
                expr.constructorType = newclass.constructorType;
                expr.varargsElement = varargsElement;
                expr.setType(that.type);
                trExpr = expr;
                
                newThisId = null; // FIXME result of new call - can only be used in post-conditions
                
            } else {
                error(that.pos(),"Unknown alternative in interpreting method call");
                return;
            }
            
            
            // This holds declarations of ids that hold values of call parameters
            // in the pre-state of the callee, for use in pre and postconditions
            preparams = new HashMap<Symbol,JCVariableDecl>();  // FIXME - is this used? where it is it initialized?
            
            
            // Set up the result variable - for RAC we have to do this
            // outside the block that starts a few lines down, because the
            // result is a temporary ident that is used in subsequent 
            // expressions - at least if the method returns a value and the
            // method call is a subexpression of a larger expression
            
            Type resultType = calleeMethodSym.type.getReturnType();
            if (newclass != null) resultType = newclass.clazz.type;
            
            boolean isVoid = resultType.tag == TypeTags.VOID;
            
            // A variable for the method call result is declared, and then 
            // everything else is within a block.
            JCIdent resultId = null;
            if (!isVoid) {
                if (rac) resultId = newTempNull(that.pos(),resultType); // initialized to null
                else if (newclass == null) {
                    resultId = newTemp(that.pos(),resultType);
                } else {
                    JCVariableDecl decl = treeutils.makeVarDef(that.type,names.fromString(Strings.newObjectVarString + that.pos), null, that.pos);
                    addStat(decl);
                    resultId = treeutils.makeIdent(that.pos, decl.sym);
                }
            }
            
            resultSym = resultId == null ? null : resultId.sym;
            if (newclass != null) {
                newThisId = resultId;
                // FIXME - what about newclass.encl
            }
            
            if (esc && newclass != null) {
                addAssume(that.pos(),Label.IMPLICIT_ASSUME,treeutils.makeNeqObject(that.pos, convertCopy(resultId), treeutils.nullLit));
//                JCExpression tt = null;
//                for (ClassSymbol sym : utils.parents((ClassSymbol)newclass.type.tsym)) {
//                    JCExpression ttt = M.at(that.pos()).TypeTest(convertCopy(resultId), treeutils.makeType(newclass.pos, sym.type));
//                    tt = tt == null ? ttt : treeutils.makeAnd(newclass.pos, tt, ttt);
//                }
//                addAssume(that.pos(),Label.IMPLICIT_ASSUME,tt);
                
                JmlMethodInvocation typeof = M.at(that.pos()).JmlMethodInvocation(JmlToken.BSTYPEOF, convertCopy(resultId));
                //typeof.type = 
                JmlMethodInvocation stype = M.at(that.pos()).JmlMethodInvocation(JmlToken.BSTYPELC, convert(newclass.clazz));
                //stype.type = 
                addAssume(that.pos(),Label.IMPLICIT_ASSUME,treeutils.makeEqObject(that.pos, typeof, stype));
                typeof = M.at(that.pos()).JmlMethodInvocation(JmlToken.BSTYPEOF, convertCopy(resultId));
                typeof.javaType = true;
                //typeof.type = 
                stype = M.at(that.pos()).JmlMethodInvocation(JmlToken.BSTYPELC, convert(newclass.clazz));
                stype.javaType = true;
                //stype.type = 
                addAssume(that.pos(),Label.IMPLICIT_ASSUME,treeutils.makeEqObject(that.pos, typeof, stype));

                JCFieldAccess fa = treeutils.makeSelect(that.pos, convertCopy(resultId), isAllocSym);
                addAssume(that.pos(),Label.IMPLICIT_ASSUME,treeutils.makeNot(that.pos, fa));
                fa = treeutils.makeSelect(that.pos, convertCopy(resultId), allocSym);
                JCExpressionStatement st = treeutils.makeAssignStat(that.pos, fa, treeutils.makeIntLiteral(that.pos, ++allocCounter));
                addStat( st );
                fa = treeutils.makeSelect(that.pos, convertCopy(resultId), isAllocSym);
                st = treeutils.makeAssignStat(that.pos, fa, treeutils.makeBooleanLiteral(that.pos,true));
                addStat( st );
            }

            
            pushBlock();
            ListBuffer<JCStatement> saved = currentStatements;
            oldStatements = currentStatements;
            
            // Get all the parent classes and interfaces, including self (last)
            java.util.List<ClassSymbol> callerParents = utils.parents((ClassSymbol)methodDecl.sym.owner);

            
            if (true) {
                addStat(comment(that.pos(), "Checking caller invariants before calling method " + utils.qualifiedMethodSig(calleeMethodSym)));
                // Iterate through parent classes and interfaces, adding relevant invariants
                for (ClassSymbol csym: callerParents) {
                    JmlSpecs.TypeSpecs tspecs = specs.get(csym);
                    for (JmlTypeClause clause : tspecs.clauses) {
                        try {
                            if (clause.token == JmlToken.INVARIANT) {
                                if (isConstructor && !methodIsStatic) continue;
                                if (methodIsStatic && !utils.hasAny(clause.modifiers,Flags.STATIC)) continue;
                                if (!utils.jmlvisible(classDecl.sym, csym, clause.modifiers.flags, methodDecl.mods.flags)) continue;
                                if (isHelper(calleeMethodSym)) continue;
                                JmlTypeClauseExpr t = (JmlTypeClauseExpr)clause;
                                // FIXME - what if undefined?
                                addAssert(that.pos(),Label.INVARIANT_EXIT_CALLER,
                                        convertJML(t.expression),
                                        clause.pos(),clause.source);
                            }
                        } catch (JmlNotImplementedException e) {
                            notImplemented(clause.token.internedName() + " clause containing ", e);
                        }
                    }
                }
            }

            ClassSymbol calleeClass = (ClassSymbol)calleeMethodSym.owner;
            java.util.List<ClassSymbol> calleeParents = utils.parents(calleeClass);
            currentThisId = newThisId;
            JCExpression collectedInvariants = treeutils.trueLit;
            
            if (!translatingJML) {
            addStat(comment(that.pos(), "Checking callee invariants by the caller"));
            // Iterate through parent classes and interfaces, adding relevant invariants
            for (ClassSymbol csym: calleeParents) {
                JmlSpecs.TypeSpecs tspecs = specs.get(csym);

                for (JmlTypeClause clause : tspecs.clauses) {
                    try {
                        if (clause.token == JmlToken.INVARIANT) {
                            if (calleeMethodSym.isConstructor() && !calleeMethodSym.isStatic()) continue;
                            if (calleeMethodSym.isStatic() && !utils.hasAny(clause.modifiers,Flags.STATIC)) continue;
                            if (isHelper(calleeMethodSym)) continue;
                            // This checks whether the invariant of the callee's parent class
                            // is visible within the caller - which is all we can hope for.
                            if (!utils.jmlvisible(classDecl.sym, csym, clause.modifiers.flags, methodDecl.mods.flags)) continue;
                            // FIXME - what if undefined? also fix model methods
                            try {
                                JmlTypeClauseExpr t = (JmlTypeClauseExpr)clause;
                                JCExpression convexpr = convertJML(t.expression);
                                if (!translatingJML) {
                                    addAssert(that.pos(),Label.INVARIANT_ENTRANCE,
                                            convexpr,
                                            clause.pos(),clause.source);
                                } else {
                                    collectedInvariants = treeutils.makeAnd(clause.pos, collectedInvariants, convexpr);
                                }
                            } catch (NoModelMethod e) {
                                // continue
                            }
                        }
                    } catch (JmlNotImplementedException e) {
                        notImplemented(clause.token.internedName() + " clause containing ", e);
                    }
                }
            }
            }

            // A list to hold the preconditions, in order by specification case
            java.util.List<JCExpression> preExpressions = new LinkedList<JCExpression>();
            
            // Collects the complete precondition over all specification cases
            JCExpression combinedPrecondition = treeutils.falseLit;
            
            // Identify the clause to point to as the associated declaration if the precondition fails.
            // The combinedPrecondition may be an OR of many specification cases,
            // each of which may be an AND of clauses - so if the precondition is
            // falses, every sepcification case is false.
            JmlMethodClauseExpr clauseToReference = null;
            
            // Iterate over all specs to find preconditions, with the callee
            // method itself last
            addStat(comment(that.pos(), "Checking callee preconditions by the caller"));
            for (MethodSymbol mpsym: utils.parents(calleeMethodSym)) {
                // This initial logic must match that below for postconditions

                JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
                if (calleeSpecs == null && mpsym == calleeMethodSym ) {
                    // This happens for a binary class with no specs for the given method.
                    //log.noticeWriter.println("NO SPECS FOR METHOD CALL(A) " + sym.owner + "." + sym);
                    calleeSpecs = JmlSpecs.defaultSpecs(that.pos).cases; // FIXME - should we insert a default if a parent has specs?
                } 
                if (calleeSpecs == null) continue; // parent method has no specs

                if (calleeSpecs.decl == null) continue ; // FIXME - when does this happen?
                
                paramActuals = new HashMap<Symbol,JCExpression>();
                Iterator<JCVariableDecl> iter = calleeSpecs.decl.params.iterator();
                for (JCExpression arg: trArgs) {
                    paramActuals.put(iter.next().sym, arg);
                }
                if (esc) {
                    if (newclass != null && newclass.clazz instanceof JCTypeApply) {
                        Iterator<Symbol.TypeSymbol> tpiter = calleeClass.getTypeParameters().iterator(); // calleeSpecs.decl.typarams.iterator();
                        for (JCExpression tp: ((JCTypeApply)newclass.clazz).arguments ) {
                            paramActuals.put(tpiter.next(), tp);
                        }
                    }
                    if (newclass == null && ( typeargs == null || typeargs.isEmpty())) {
                        List<Type> list = ((Type.MethodType)calleeMethodSym.type).argtypes;
                        Iterator<Type> tpiter = list.iterator();
                        for (Type tp: ((Type.MethodType)meth.type).argtypes ) {
                            paramActuals.put(tpiter.next().tsym, treeutils.makeType(that.pos, tp));
                        }
                    }
                    if (newclass == null && typeargs != null && !typeargs.isEmpty()) {
                        Iterator<Symbol.TypeSymbol> tpiter = calleeMethodSym.getTypeParameters().iterator();
                        for (JCExpression tp: typeargs ) {
                            paramActuals.put(tpiter.next(), tp);
                        }
                    }
                }

                // For each specification case, we accumulate the precondition
                // and we create a block that checks the assignable statements
                for (JmlSpecificationCase cs : calleeSpecs.cases) {
                    if (!utils.jmlvisible(classDecl.sym, mpsym.owner, cs.modifiers.flags, methodDecl.mods.flags)) continue;
                    JCExpression pre = translatingJML ? condition : treeutils.trueLit;
                    try {
                        JmlMethodClauseExpr mcc = null; // Remember the first clause in the specification case
                        for (JmlMethodClause clause : cs.clauses) {
                            switch (clause.token) {
                                case REQUIRES:
                                    JmlMethodClauseExpr mce = (JmlMethodClauseExpr)clause;
                                    JCExpression e = convertJML(mce.expression,pre,false); // Might throw an exception
                                    pre = pre == treeutils.trueLit ? e : treeutils.makeAnd(pre.pos, pre, e);
                                    if (mcc == null) mcc = mce;
                                    break;
                                default:
                            }
                        }
                        if (mcc != null) clauseToReference = mcc;
                    } catch (NoModelMethod e) {
                        pre = treeutils.falseLit;
                    } catch (JmlNotImplementedException e) {
                        notImplemented("requires clause containing ",e);
                        pre = treeutils.falseLit;
                    }
                    preExpressions.add(pre); // Add to the list of spec cases, in order of declaration
                    combinedPrecondition = combinedPrecondition == treeutils.falseLit ? pre : treeutils.makeOr(pre.pos, combinedPrecondition, pre);
                    if ((!translatingJML || rac) && methodDecl != null && methodDecl.sym != null) {  // FIXME - not quite sure of this guard // FIXME - what should we check for field initializers
                        // Handle assignable clauses
                        pushBlock(); // A block for assignable tests
                        boolean anyAssignableClauses = false;
                        for (JmlMethodClause clause : cs.clauses) {
                            // We iterate over each storeref item in each assignable clause
                            // of each specification case of the callee - for each item we check
                            // that assigning to it (under the appropriate preconditions)
                            // is allowed by each of the specification cases of the caller specs.
                            try {
                                if (clause.token == JmlToken.ASSIGNABLE) {
                                    List<JCExpression> storerefs = ((JmlMethodClauseStoreRef)clause).list;
                                    for (JCExpression item: storerefs) {
                                        checkAgainstCallerSpecs(convertJML(item),pre, savedThisId, newThisId);
                                    }
                                    anyAssignableClauses = true;
                                }
                            } catch (NoModelMethod e) {
                                // continue // FIXME - warn?
                            } catch (JmlNotImplementedException e) {
                                notImplemented("assignable clause containing ",e);
                            }
                        }
                        if (!anyAssignableClauses) {
                            // If there are no assignable clauses in the spec case,
                            // the default is \\everything
                            checkAgainstCallerSpecs(M.at(cs.pos()).JmlStoreRefKeyword(JmlToken.BSEVERYTHING),pre, savedThisId, newThisId);
                        }
                        JCBlock bl = popBlock(0,cs.pos()); // Ending the assignable tests block
                        if (!bl.stats.isEmpty()) addStat( M.at(cs.pos()).If(pre, bl, null) );
                    }
                }
                paramActuals.clear();
            }
            if (clauseToReference != null) {
                pushBlock();
                if (translatingJML) {
                    JCExpression conj = treeutils.makeAnd(methodDecl.pos, collectedInvariants, combinedPrecondition);
                    addAssert(that.pos(),Label.UNDEFINED_PRECONDITION,
                            treeutils.makeImplies(methodDecl.pos, condition, conj),
                            clauseToReference.pos(),clauseToReference.source());
                    
                } else {
                    addAssert(that.pos(),Label.PRECONDITION,
                            combinedPrecondition,
                            clauseToReference.pos(),clauseToReference.source());
                }
                JCBlock bl = popBlock(0,that.pos());
                addStat( wrapRuntimeException(that.pos(), bl, 
                        "JML undefined precondition - exception thrown",
                        null));
            }

            ListBuffer<JCStatement> ensuresStatsOuter = new ListBuffer<JCStatement>();
            ListBuffer<JCStatement> exsuresStatsOuter = new ListBuffer<JCStatement>();

            // Now put in the actual method call
            // For esc, the resultSym is used in the postconditions; there is 
            // no actual call of the method. Similarly for new object expressions.
            
            // FIXME - do need to state something about the allocation of the result of the new object expression
            
            if (rac) {
                ListBuffer<JCStatement> s = currentStatements;
                currentStatements = ensuresStatsOuter;
                if (apply != null) addStat(comment(apply.pos(),"converted method call"));
                if (newclass != null) addStat(comment(newclass.pos(),"converted new-object call"));

                JCStatement call;
                if (newclass != null) {
                    addStat(treeutils.makeAssignStat(that.pos, resultId, trExpr));
                    trExpr = resultId;
                    currentThisId = newThisId = resultId;
                } else if (isVoid) {
                    call = M.at(that.pos()).Exec(trExpr);
                    addStat(call);
                } else {
                    call = treeutils.makeAssignStat(that.pos, resultId, trExpr);
                    addStat(call);
                }
                currentStatements = s;
            }

            ensuresStatsOuter.add(comment(that.pos(),"Assuming callee normal postconditions"));
            exsuresStatsOuter.add(comment(that.pos(),"Assuming callee exceptional postconditions"));

            // Now we iterate over all specification cases in all parent
            // methods again, this time putting in the post-condition checks
            
            for (MethodSymbol mpsym: utils.parents(calleeMethodSym)) {
                // This initial logic must match that above for preconditions
                JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
                if (calleeSpecs == null && mpsym == calleeMethodSym ) {
                    // This happens for a binary class with no specs for the given method.
                    //log.noticeWriter.println("NO SPECS FOR METHOD CALL(A) " + sym.owner + "." + sym);
                    calleeSpecs = JmlSpecs.defaultSpecs(that.pos).cases;
                } 
                if (calleeSpecs == null) continue;
                if (calleeSpecs.decl == null) continue; // FIXME - should not happen - model methods?

                if (calleeSpecs.cases.isEmpty()) continue;
                
                paramActuals = new HashMap<Symbol,JCExpression>();
                Iterator<JCVariableDecl> iter = calleeSpecs.decl.params.iterator();
                for (JCExpression arg: trArgs) {
                    paramActuals.put(iter.next().sym, arg);
                }
                // FIXME - we should set condition
                for (JmlSpecificationCase cs : calleeSpecs.cases) {
                    if (!utils.jmlvisible(classDecl.sym, mpsym.owner, cs.modifiers.flags, methodDecl.mods.flags)) continue;
                    ListBuffer<JCStatement> ensuresStats = new ListBuffer<JCStatement>();
                    ListBuffer<JCStatement> exsuresStats = new ListBuffer<JCStatement>();
                    JCExpression pre = preExpressions.remove(0);
                    if (pre == treeutils.falseLit) continue; // Don't bother with postconditions if corresponding precondition is explicitly false 
                    condition = pre; // FIXME - is this right? what about the havoc statement?
                    for (JmlMethodClause clause : cs.clauses) {
                        try {
                            switch (clause.token) {
                                case REQUIRES: 
                                    break;
                                case ENSURES:
                                    currentStatements = ensuresStats;
                                    addStat(comment(clause));
                                    pushBlock();
                                    try {
                                        JCExpression e = convertJML(((JmlMethodClauseExpr)clause).expression, condition, true);
                                        addAssume(that.pos(),Label.POSTCONDITION,e,clause.pos(),clause.sourcefile);
                                    } catch (NoModelMethod e) { // FIXME - need this elsewhere as well, e.g., signals
                                        // continue
                                    }
                                    JCBlock bl = popBlock(0,that.pos());
                                    addStat( wrapRuntimeException(clause.pos(), bl, // wrapRuntimeException is a no-op except for rac
                                            "JML undefined postcondition - exception thrown",
                                            null));
                                    break;
                                case ASSIGNABLE:
                                    currentStatements = ensuresStats;
                                    if (esc) {
                                        addStat(comment(clause));
                                        List<JCExpression> havocs = convertJML(((JmlMethodClauseStoreRef)clause).list);
                                        JCStatement havoc = M.at(clause.pos).JmlHavocStatement(havocs);
                                        addStat(havoc);
                                    }
                                    break;
                                case SIGNALS:
                                    // FIXME - review this
                                    currentStatements = exsuresStats;
                                    addStat(comment(clause));
                                    
                                    JCVariableDecl vdo = ((JmlMethodClauseSignals)clause).vardef;
                                    pushBlock();
                                    Type vdtype = syms.exceptionType;
                                    if (vdo != null) {
                                        JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionDeclCall.sym);
                                        JCExpression tc = M.at(vdo.pos()).TypeCast(vdo.type, exceptionId);
                                        JCVariableDecl vd = treeutils.makeVarDef(vdo.type,vdo.name,vdo.sym.owner, esc ? exceptionId : tc);
                                        vdtype = vd.type;
                                        addStat(vd);
                                        paramActuals.put(vdo.sym, treeutils.makeIdent(vd.pos,vd.sym));
                                    }
                                    // Should the condition be augmented with exception not null and of the right type?
                                    JCExpression e = convertJML(((JmlMethodClauseSignals)clause).expression, condition, true);
                                    JCExpression ex = treeutils.trueLit;
                                    if (vdo != null) {
                                        ex = M.at(clause.pos()).TypeTest(treeutils.makeIdent(clause.pos, exceptionDeclCall.sym),
                                                treeutils.makeType(clause.pos, vdtype)).setType(syms.booleanType);
                                        paramActuals.remove(vdo.sym);
                                    }
                                    addAssume(esc ? null :that.pos(),Label.SIGNALS,e,clause.pos(),clause.sourcefile == null ? log.currentSourceFile() : clause.sourcefile); // FIXME - clause.sourcefile can be null if it is a constructted default clause - is this the right way to handle it?
                                    JCStatement st = M.at(clause.pos()).If(ex,popBlock(0,that.pos()),null);

                                    addStat( wrapRuntimeException(clause.pos(), M.at(clause.pos()).Block(0,List.<JCStatement>of(st)), 
                                                "JML undefined exceptional postcondition - exception thrown",
                                                null));
                                    break;
                                default:
                                    // FIXME - implement others
                                    break;
                            }
                        } catch (JmlNotImplementedException e) {
                            notImplemented(clause.token.internedName() + " clause containing ",e);
                        }

                    }
                    if (!ensuresStats.isEmpty()) {
                        JCBlock ensuresBlock = M.at(cs.pos+1).Block(0, ensuresStats.toList());
                        // The +1 is so that the position of this if statement
                        // and hence the names of the BRANCHT and BRANCHE variables
                        // is different from the if prior to the apply // FIXME - review if this is still needed
                        JCStatement st = M.at(cs.pos+1).If(pre,ensuresBlock,null);
                        JCBlock bl = M.at(cs.pos+1).Block(0,List.<JCStatement>of(st));
                        ensuresStatsOuter.add( wrapRuntimeException(cs.pos(), bl, "JML undefined precondition while checking postconditions - exception thrown", null));
                    }
                    if (!exsuresStats.isEmpty()) {
                        JCBlock exsuresBlock = M.at(cs.pos+1).Block(0, exsuresStats.toList());
                        // The +1 is so that the position of this if statement
                        // and hence the names of the BRANCHT and BRANCHE variables
                        // is different from the if prior to the apply // FIXME - review if this is still needed
                        JCStatement st = M.at(cs.pos+1).If(pre,exsuresBlock,null);
                        JCBlock bl = M.at(cs.pos+1).Block(0,List.<JCStatement>of(st));
                        exsuresStatsOuter.add( wrapRuntimeException(cs.pos(), bl, "JML undefined precondition while checking exceptional postconditions - exception thrown", null));
                    }
                }
                paramActuals.clear();
            }                
            // FIXME - need constraints

            if (!translatingJML) {

                ListBuffer<JCStatement> ensuresStats = new ListBuffer<JCStatement>();
                ListBuffer<JCStatement> exsuresStats = new ListBuffer<JCStatement>();
                currentStatements = ensuresStats;
                addStat(comment(that.pos(), "Assuming callee invariants by the caller after exiting the callee"));
                currentStatements = exsuresStats;
                addStat(comment(that.pos(), "Assuming callee invariants by the caller after exiting the callee"));

                // Iterate through parent classes and interfaces, adding relevant invariants
                for (ClassSymbol csym: calleeParents) {
                    JmlSpecs.TypeSpecs tspecs = specs.get(csym);

                    for (JmlTypeClause clause : tspecs.clauses) {
                        try {
                            if (clause.token == JmlToken.INVARIANT) {
                                if (calleeMethodSym.isConstructor() && !calleeMethodSym.isStatic()) continue;
                                if (calleeMethodSym.isStatic() && !utils.hasAny(clause.modifiers,Flags.STATIC)) continue;
                                if (isHelper(calleeMethodSym)) continue;
                                // This checks whether the invariant of the callee's parent class
                                // is visible within the caller - which is all we can hope for.
                                if (!utils.jmlvisible(classDecl.sym, csym, clause.modifiers.flags, methodDecl.mods.flags)) continue;
                                // FIXME - what if undefined? also fix model methods
                                try {
                                    JmlTypeClauseExpr t = (JmlTypeClauseExpr)clause;
                                    currentStatements = ensuresStats;
                                    addAssume(that.pos(),Label.INVARIANT_EXIT,
                                            convertJML(t.expression),
                                            clause.pos(),clause.source);
                                    currentStatements = exsuresStats;
                                    addAssume(that.pos(),Label.INVARIANT_EXIT,
                                            convertJML(t.expression),
                                            clause.pos(),clause.source);
                                } catch (NoModelMethod e) {
                                    // continue
                                }
                            }
                        } catch (NoModelMethod e) {
                            // continue // FIXME - warn?
                        } catch (JmlNotImplementedException e) {
                            notImplemented(clause.token.internedName() + " clause containing ", e);
                        }
                    }
                }

                currentThisId = savedThisId;
                // Iterate through parent classes and interfaces, adding relevant invariants
                currentStatements = ensuresStats;
                addStat(comment(that.pos(), "Assuming caller invariants upon reentering the caller"));
                currentStatements = exsuresStats;
                addStat(comment(that.pos(), "Assuming caller invariants upon reentering the caller"));
                for (ClassSymbol csym: callerParents) {
                    JmlSpecs.TypeSpecs tspecs = specs.get(csym);

                    for (JmlTypeClause clause : tspecs.clauses) {
                        try {
                            if (clause.token == JmlToken.INVARIANT) {
                                if (isConstructor && !methodIsStatic) continue;
                                if (methodIsStatic && !utils.hasAny(clause.modifiers,Flags.STATIC)) continue;
                                if (!utils.jmlvisible(classDecl.sym, csym, clause.modifiers.flags, methodDecl.mods.flags)) continue;
                                if (isHelper(calleeMethodSym)) continue;
                                JmlTypeClauseExpr t = (JmlTypeClauseExpr)clause;
                                // FIXME - what if undefined?
                                currentStatements = ensuresStats;
                                addAssume(that.pos(),Label.INVARIANT_REENTER_CALLER,
                                        convertJML(t.expression),
                                        clause.pos(),clause.source);
                                currentStatements = exsuresStats;
                                addAssume(that.pos(),Label.INVARIANT_REENTER_CALLER,
                                        convertJML(t.expression),
                                        clause.pos(),clause.source);
                            }
                        } catch (JmlNotImplementedException e) {
                            notImplemented(clause.token.internedName() + " clause containing ", e);
                        }
                    }
                }

                if (!rac || !onlyComments(ensuresStats)) {
                    JCBlock ensuresBlock = M.at(that.pos).Block(0, ensuresStats.toList());
                    ensuresStatsOuter.add( wrapRuntimeException(that.pos(), ensuresBlock, "JML undefined invariant while checking postconditions - exception thrown", null));
                }
                if (!rac || !onlyComments(exsuresStats)) {
                    JCBlock exsuresBlock = M.at(that.pos).Block(0, exsuresStats.toList());
                    exsuresStatsOuter.add( wrapRuntimeException(that.pos(), exsuresBlock, "JML undefined invariant while checking exceptional postconditions - exception thrown", null));
                }

            }

            // FIXME - the source must be handled properly

            // FIXME - review what follows

            currentStatements = saved;
            
            // Make try block
            if (exceptionSym != null && exceptionDeclCall != null) exsuresStatsOuter.add(treeutils.makeAssignStat(that.pos,treeutils.makeIdent(that.pos, exceptionSym),treeutils.makeIdent(that.pos, exceptionDeclCall.sym)));
            
            // TERMINATION
            // The termination symbol will be null if a method call is present in class-level declaration
            // FIXME - not sure what precisely should be done - should we declare a termination symbol in this case? RAC probably needs it.
            if (terminationSym != null) {
                JCIdent tid = treeutils.makeIdent(that.pos,terminationSym);
                JCStatement term = treeutils.makeAssignStat(that.pos,tid,treeutils.makeIntLiteral(that.pos,-that.pos));
                exsuresStatsOuter.add(term);
            }
            
            if (exceptionDeclCall != null) {
                exsuresStatsOuter.add(M.at(that.pos()).Throw(treeutils.makeIdent(that.pos, exceptionDeclCall.sym)));
            } else if (rac) {
                System.out.println("DID NOT EXPECT THIS"); // FIXME
            }
            
            JCBlock ensuresBlock = M.at(that.pos()).Block(0, ensuresStatsOuter.toList());
            if (rac) {
                JCBlock exsuresBlock = M.at(that.pos()).Block(0, exsuresStatsOuter.toList());
                addStat( wrapException(that.pos(), ensuresBlock, exceptionDeclCall, exsuresBlock ));
                addStat( popBlock(0,methodDecl.pos()) ); // Final outer block
            } else if (esc) {
                if (exceptionDeclCall != null) { // FIXME - what is happening if exceptionDeclCall is null - is the method pure?
                    // declare the exception variable
                    addStat(exceptionDeclCall);
                    JCIdent nexceptionId = treeutils.makeIdent(that.getStartPosition(),exceptionDeclCall.sym);
                    treeutils.copyEndPosition(nexceptionId, that);
                    {
                        JCStatement c = comment(that,"Exception thrown by " + 
                                    (apply == null ? newclass.constructor : meth instanceof JCIdent ? ((JCIdent)meth).sym : ((JCFieldAccess)meth).sym));
                        exsuresStatsOuter = exsuresStatsOuter.prepend(c);
                        JCExpression nex = convertCopy(nexceptionId);
                        pathMap.put(nex,c);
                        exprBiMap.put(nex,nexceptionId);
//                        log.noticeWriter.println("POSs " + nexceptionId.getStartPosition()
//                                   + " " + nexceptionId.getEndPosition(log.currentSource().getEndPosTable())
//                                   + " " + nex.getStartPosition()
//                                   + " " + nex.getEndPosition(log.currentSource().getEndPosTable()));
                    }
                    JCBinary ch = treeutils.makeEqObject(that.pos, nexceptionId, treeutils.nullLit);
                    JCBlock exsuresBlock = M.at(that.pos()).Block(0, exsuresStatsOuter.toList());
                    JCStatement st = M.at(that.pos).If(ch, ensuresBlock, exsuresBlock);
                    addStat(st);
                } else {
                    addStat(ensuresBlock);
                }
                addStat( popBlock(0,methodDecl.pos()) ); // Final outer block
            }

            if (resultId != null) result = eresult = treeutils.makeIdent(resultId.pos, resultId.sym);
            else result = eresult = null;
            
        } finally {
            paramActuals = savedParamActuals;
            resultSym = savedSym;
            exceptionSym = savedExceptionSym;
            preparams = savedpreparams;
            currentThisId = savedThisId;
            oldStatements = savedOldStatements;
        }
    }

        // FIXME - what about type arguments
//        pushTypeArgs();
//        if (tfa != null) {
//            // tfa is the declaration of a parameterized method
//            // that is the actual call, which may not have explicit parameters
//            Iterator<Type> tv = tfa.tvars.iterator();
//            Iterator<JCExpression> e = that.typeargs.iterator();
//            if (e.hasNext()) {
//                while (tv.hasNext()) {
//                    typeargs.put(tv.next().tsym,e.next().type);
//                }
//            } else {
//                log.noticeWriter.println("NOT IMPLEMENTED - parameterized method call with implicit type parameters");
//            }
//        }

//        // FIXME - concerned that the position here is not after the
//        // positions of all of the arguments
//        if (false) {
//            eresult = insertSpecMethodCall(that.pos,msym,obj,that.typeargs,newargs.toList());
//        } else {
//            eresult = insertMethodCall(that,msym,obj,that.getTypeArguments(),newargs.toList()); // typeargs ? FIXME
//        }
//
////        popTypeArgs();
//        
//        
//
//        MethodSymbol msym = null;
////        if (that.meth instanceof JCIdent) msym = (MethodSymbol)((JCIdent)that.meth).sym;
////        else if (that.meth instanceof JCFieldAccess) msym = (MethodSymbol)((JCFieldAccess)that.meth).msym;
////        else {
////            //FIXME ERROR
////        }
////        JmlMethodSpecs calleeSpecs = JmlSpecs.instance(context).getDenestedSpecs(msym).deSugared;
////        calleeSpecs.
//        JCExpression e = M.Apply(that.typeargs,method,newargs.toList());
//        e.pos = that.pos;
//        e.setType(that.type);
//        if (that.type.tag != TypeTags.VOID) eresult = newTemp(e);
//        else eresult = e;
//        // TODO Auto-generated method stub
//        //throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//    }
    
    /** Returns true iff the only statements on the list are comment statements */
    protected boolean onlyComments(ListBuffer<JCStatement> list) {
        if (list.isEmpty()) return true;
        for (JCStatement s: list) {
            if (!(s instanceof JmlStatementExpr && ((JmlStatementExpr)s).token == JmlToken.COMMENT)) return false;
        }
        return true;
    }

    // FIXME - review newClass

    @Override
    public void visitNewClass(JCNewClass that) {

        // FIXME - need to check definedness by testing preconditions when translatingJML

        ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
        for (JCExpression arg: that.args) {
            args.add(convertExpr(arg));
        }
        // FIXME - need to call the constructor; need an assertion about the type of the result; about allocation time

        if (pureCopy) {
            JCNewClass expr = M.at(that.pos()).NewClass(
                    that.encl, 
                    convert(that.typeargs), 
                    convert(that.clazz), 
                    args.toList(), 
                    convert(that.def));
            expr.constructor = that.constructor;
            expr.constructorType = that.constructorType;
            expr.varargsElement = that.varargsElement;
            expr.setType(that.type);
            result = eresult = expr;
            return;
        }
        applyHelper(that);

    }

    // FIXME - review newArray
    // OK
    @Override
    public void visitNewArray(JCNewArray that) {
        // Note that a JCNewArray can be the full new array expression: new Type[]{...}
        // But in a multi-dimensional initializer, each nested {...} is itself
        // a JCNewArray, though now with a null elemtype. 

        ListBuffer<JCExpression> dims = new ListBuffer<JCExpression>();
        for (JCExpression dim: that.dims) {
            JCExpression ex = convertExpr(dim);
            dims.add(ex);
            if (!pureCopy && ex != null) {
                JCBinary comp = treeutils.makeBinary(that.pos, JCTree.LE, treeutils.intleSymbol, treeutils.zero, ex);
                addAssert(that.pos(),
                        translatingJML ? Label.UNDEFINED_NEGATIVESIZE : Label.POSSIBLY_NEGATIVESIZE, 
                        comp);
            }
        }
        
        ListBuffer<JCExpression> elems = new ListBuffer<JCExpression>();
        if (that.elems != null) {
            for (JCExpression elem: that.elems) {
                elems.add(convertExpr(elem));
            }
        } else {
            elems = null;
        }

        if (pureCopy) {
            JCExpression elemtype = convert(that.elemtype);
            result = eresult = M.at(that.pos()).NewArray(elemtype, dims.toList(), elems == null ? null: elems.toList()).setType(that.type);
        } else if (rac || translatingJML) {
            // This will create a fully-qualified version of the type name
            JCExpression elemtype = that.elemtype == null ? null : treeutils.makeType(that.elemtype.pos, that.elemtype.type);
            result = eresult = M.at(that.pos()).NewArray(elemtype, dims.toList(), elems == null ? null: elems.toList()).setType(that.type);
            if (!translatingJML) result = eresult = newTemp(eresult);
        } else { // esc
            JCVariableDecl id = treeutils.makeVarDef(that.type,names.fromString(Strings.newArrayVarString + that.pos), null, that.pos);
            addStat(id);
            result = eresult = treeutils.makeIdent(that.pos, id.sym);
            addAssume(that.pos(),Label.NULL_CHECK,treeutils.makeNeqObject(that.pos, eresult, treeutils.nullLit));
            // FIXME - need assertions about size of array and about any known array elements; about allocation time
            // also about type of the array
        }
    }

    // OK
    @Override
    public void visitParens(JCParens that) {
        JCExpression arg = convertExpr(that.getExpression());
        result = eresult = M.at(that.pos()).Parens(arg).setType(that.type);
        treeutils.copyEndPosition(eresult,that);
    }
    
    // FIXME - check endpos everywhere
    
    // FIXME - check this; document this
    protected JCExpression addImplicitConversion(DiagnosticPosition pos, Type lhstype, JCExpression rhs) {
        if (lhstype.isPrimitive() && !rhs.type.isPrimitive() && (!rac || !jmltypes.isJmlType(lhstype))) {
            // UnBoxing - check for null rhs
            // But we don't unbox for rac for JML types because those are represented as a non-primitive anyway
            if (javaChecks) {
                JCExpression e = treeutils.makeNeqObject(pos.getPreferredPosition(), rhs, treeutils.nullLit);
                addAssert(pos, Label.POSSIBLY_NULL_UNBOX, e);
            }
        }
        if (rac) {
            if ((lhstype == jmltypes.BIGINT || lhstype == jmltypes.repSym(jmltypes.BIGINT).type) && 
                    rhs.type.isPrimitive() && !jmltypes.isJmlType(rhs.type)) {
                return treeutils.makeUtilsMethodCall(rhs.pos,"bigint_valueOf",List.<JCExpression>of(rhs));
            } else {
                return rhs; // RAC handles implicit conversions implicitly
            }
        }
        
        if (types.isSameType(lhstype,rhs.type)) return rhs;
        
        Type unboxed = unbox(rhs.type);
        int tag = unboxed.tag;
        String methodName =
                tag == TypeTags.INT ? "intValue" :
                tag == TypeTags.SHORT ? "shortValue" :
                tag == TypeTags.LONG ? "longValue" :
                tag == TypeTags.BOOLEAN ? "booleanValue" :
                tag == TypeTags.DOUBLE ? "doubleValue" :
                tag == TypeTags.FLOAT ? "floatValue" :
                tag == TypeTags.BYTE ? "byteValue" :
                tag == TypeTags.CHAR ? "charValue" : null;
                ;
        if (lhstype.isPrimitive() && !rhs.type.isPrimitive()) {
            // int = Integer and the like
            JCIdent id = M.Ident(names.fromString(methodName));
            JCExpression mth = M.at(rhs.pos()).JmlMethodInvocation(id, List.<JCExpression>of(rhs));
            mth.type = lhstype;
            if (translatingJML) {
                eresult = mth;
            } else {
                eresult = newTemp(mth);
            }
        } else if (!lhstype.isPrimitive() && rhs.type.isPrimitive()) {
            // Integer = int and the like
            eresult = newTemp(rhs.pos(), lhstype);
            // assert TValue(eresult) == rhs
            JCIdent id = M.Ident(names.fromString(methodName));
            JmlMethodInvocation call = M.JmlMethodInvocation(id, List.<JCExpression>of(eresult));
            call.setType(unboxed); // Note: no symbol set, since this is JML
            JCExpression e = treeutils.makeEquality(rhs.pos,call,rhs);
            addAssume(rhs.pos(),Label.EXPLICIT_ASSUME,e);
            e = treeutils.makeNeqObject(pos.getPreferredPosition(), eresult, treeutils.nullLit);
            addAssume(pos,Label.EXPLICIT_ASSUME,e);

        } else {
            
        }
        return eresult;
    }
    
    protected Type unbox(Type t) {
        Type tt = types.unboxedType(t);
        if (tt == Type.noType) tt = t;
        return tt;
    }
    
    JCTree lastStat;

    // FIXME - review
    @Override
    public void visitAssign(JCAssign that) {
        if (pureCopy) {
            JCExpression lhs = convertExpr(that.lhs);
            JCExpression rhs = convertExpr(that.rhs);
            result = eresult = treeutils.makeAssign(that.pos,  lhs, rhs);
            return;
        }
        if (that.lhs instanceof JCIdent) {
            JCIdent id = (JCIdent)that.lhs;
            JCExpression lhs = convertExpr(that.lhs);
            JCExpression rhs = convertExpr(that.rhs);
            rhs = addImplicitConversion(that.pos(),lhs.type, rhs);

            if (specs.isNonNull(id.sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(that.pos, rhs, treeutils.nullLit);
                // FIXME - location of nnonnull declaration?
                addAssert(that.pos(), Label.POSSIBLY_NULL_ASSIGNMENT, e);
            }
            for (JmlSpecificationCase c: specs.getDenestedSpecs(methodDecl.sym).cases) {
                JCExpression check = checkAssignable(lhs,c,currentThisId.sym,currentThisId.sym);
                if (!treeutils.isTrueLit(check)) {
                    DiagnosticPosition pos = c.pos();
                    // The assignment is not allowed if it is nowhere in the
                    // assignable clauses; we point to the first one. If there are
                    // none the default is \everywhere, which is always allowed.
                    for (JmlMethodClause m : c.clauses) {
                        if (m.token == JmlToken.ASSIGNABLE) { pos = m.pos(); break; }
                    }
                    addAssert(that.pos(),Label.ASSIGNABLE,check,pos,c.sourcefile);
                }
            }
            
            JCExpressionStatement st = treeutils.makeAssignStat(that.pos,  lhs, rhs);
            addStat( st );
            lastStat = st.expr;
            exprBiMap.put(that,st.expr);
            result = eresult = lhs;
            exprBiMap.put(that.lhs, eresult);

            if (!(lhs instanceof JCIdent)) {
                result = eresult = newTemp(lhs);
                exprBiMap.put(that.lhs, eresult);
            }

        } else if (that.lhs instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)(that.lhs);
            JCFieldAccess newfa;
            if (!fa.sym.isStatic()) {
                JCExpression obj = convertExpr(fa.selected);
                JCExpression e = treeutils.makeNeqObject(obj.pos, obj, treeutils.nullLit);
                if (javaChecks) addAssert(that.lhs.pos(), Label.POSSIBLY_NULL_DEREFERENCE, e);
                newfa = treeutils.makeSelect(that.pos, obj, fa.sym);
                //Map<JCTree,Integer> table = log.currentSource().getEndPosTable();
                //log.noticeWriter.println("FA " + fa.getStartPosition() + " " + fa.getEndPosition(table) + " " + newfa.getStartPosition() + " " + newfa.getEndPosition(table));
            } else {
                // We must evaluate the fa.lhs if it is an expression and not a type,
                // even though the value is not used (and might even be null)
                if (!treeutils.isATypeTree(fa.selected)) {
                    scan(fa.selected);
                }
                // If the field is static, substitute the type tree
                
                JCExpression obj = treeutils.makeType(fa.getStartPosition(), fa.sym.owner.type);
                newfa = treeutils.makeSelect(that.pos, obj, fa.sym);
                
            }
            JCExpression rhs = convertExpr(that.rhs);
            if (specs.isNonNull(fa.sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nullLit);
                // FIXME - location of nnonnull declaration?
                addAssert(that.pos(), Label.POSSIBLY_NULL_ASSIGNMENT, e);
            }

            for (JmlSpecificationCase c: specs.getDenestedSpecs(methodDecl.sym).cases) {
                JCExpression check = checkAssignable(fa,c,currentThisId.sym,currentThisId.sym);
                if (!treeutils.isTrueLit(check)) {
                    DiagnosticPosition pos = c.pos();
                    for (JmlMethodClause m : c.clauses) {
                        if (m.token == JmlToken.ASSIGNABLE) { pos = m.pos(); break; }
                    }
                    addAssert(that.pos(),Label.ASSIGNABLE,check,pos,c.sourcefile);
                }
            }

            JCExpressionStatement st = treeutils.makeAssignStat(that.pos, newfa, rhs);
            addStat( st );
            lastStat = st.expr;
            exprBiMap.put(that, st.expr);
            result = eresult = newTemp(newfa);
            exprBiMap.put(that.lhs, eresult);
               
        } else if (that.lhs instanceof JCArrayAccess) {
            // that.lhs.getPreferredPosition() is the position of the [ in 
            // the array access expression
            JCArrayAccess aa = (JCArrayAccess)(that.lhs);
            JCExpression array = convertExpr(aa.indexed);
            JCExpression e = treeutils.makeNeqObject(array.pos, array, treeutils.nullLit);
            if (javaChecks) addAssert(array.pos(), Label.POSSIBLY_NULL_DEREFERENCE, e);

            JCExpression index = convertExpr(aa.index);
            index = addImplicitConversion(index.pos(),syms.intType,index);
            e = treeutils.makeBinary(index.pos, JCTree.GE, index, treeutils.zero);
            if (javaChecks) addAssert(aa.index.pos(), Label.POSSIBLY_NEGATIVEINDEX, e);
            
            JCFieldAccess newfa = treeutils.makeLength(array.pos(),array);
            e = treeutils.makeBinary(index.pos, JCTree.GT, newfa, index);
            if (javaChecks) addAssert(that.lhs.pos(), Label.POSSIBLY_TOOLARGEINDEX, e);
            
            // FIXME - test this
            for (JmlSpecificationCase c: specs.getDenestedSpecs(methodDecl.sym).cases) {
                JCExpression check = checkAssignable(aa,c,currentThisId.sym,currentThisId.sym);
                if (!treeutils.isTrueLit(check)) {
                    DiagnosticPosition pos = c.pos();
                    for (JmlMethodClause m : c.clauses) {
                        if (m.token == JmlToken.ASSIGNABLE) { pos = m.pos(); break; }
                    }
                    addAssert(that.pos(),Label.ASSIGNABLE,check,pos,c.sourcefile);
                }
            }

            JCExpression rhs = convertExpr(that.rhs);
            JCArrayAccess lhs = new JmlBBArrayAccess(null,array,index);
            lhs.pos = aa.pos;
            lhs.type = aa.type;
            JCExpressionStatement st = treeutils.makeAssignStat(that.pos,lhs,rhs);
            addStat( st );
            lastStat = st.expr;
            exprBiMap.put(that, st.expr);
            result = eresult = newTemp(lhs);
            exprBiMap.put(that.lhs, eresult);
            
        } else {
            error(that.pos(),"An unknown kind of assignment seen in JmlAssertionAdder: " + that.lhs.getClass());
        }
    }
    
    // OK
    @Override
    public void visitAssignop(JCAssignOp that) {
        if (pureCopy) {
            JCExpression lhs = convertExpr(that.lhs);
            JCExpression rhs = convertExpr(that.rhs);
            JCAssignOp a = M.at(that.pos()).Assignop(that.getTag(), lhs, rhs);
            a.operator = that.operator;
            a.setType(that.type);
            result = eresult = a;
            return;
        }
        visitAssignopHelper(that,false);
    }

    // OK
    protected void visitAssignopHelper(JCAssignOp that, boolean post) {
        JCExpression lhs = that.lhs;
        JCExpression rhs = that.rhs;
        int op = that.getTag() - JCTree.ASGOffset;
        boolean lhsscanned = false;
        if (lhs instanceof JCIdent) {
            lhs = convertExpr(lhs); // This may no longer be a JCIdent (e.g. f may become this.f or T.f) 
            lhsscanned = true;
        }
        if (lhs instanceof JCIdent) {
            // We start with: id = expr
            // We generate
            //    ... statements for the subexpressions of lhs (if any)
            //    ... statements for the subexpressions of expr
            //    temp = lhs' op rhs'
            //    lhs' = temp
            
            Type t = unbox(that.type);
            
            JCExpression lhsc = addImplicitConversion(lhs.pos(),t,lhs);

            rhs = convertExpr(rhs);
            rhs = addImplicitConversion(rhs.pos(),t,rhs);
            
            addBinaryChecks(that, op, lhsc, rhs);

            rhs = treeutils.makeBinary(that.pos,op,that.operator,lhsc,rhs);
            treeutils.copyEndPosition(rhs, that);

            checkAssignable(methodDecl, lhs, that.pos(), (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);

            // Note that we need to introduce the temporary since the rhs contains
            // identifiers that may be captured by the lhs. - TODO - need an example?
            JCIdent id = newTemp(rhs);
            JCExpression newlhs = treeutils.makeIdent(lhs.pos,((JCIdent)lhs).sym);
            JCExpressionStatement st = addStat(treeutils.makeAssignStat(that.getStartPosition(), newlhs, id));
            result = eresult = post ? id : newlhs;
            exprBiMap.put(that.lhs,eresult);
            lastStat = st.expr;
            
        } else if (lhs instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)lhs;
            JCFieldAccess newfa;
            if (fa.sym.isStatic()) {
                if (!lhsscanned && !treeutils.isATypeTree(fa.selected))  convertExpr(fa.selected);
                JCExpression typetree = treeutils.makeType(fa.selected.pos, fa.sym.owner.type);
                newfa = treeutils.makeSelect(fa.selected.pos, typetree, fa.sym);
                newfa.name = fa.name;
                rhs = convertExpr(rhs);
                
            } else {
                JCExpression sel = lhsscanned ? fa.selected : convertExpr(fa.selected);

                newfa = M.at(lhs.pos()).Select(sel, fa.name);
                newfa.sym = fa.sym;
                newfa.type = fa.type;

                if (javaChecks) {
                    JCExpression e = treeutils.makeNeqObject(lhs.pos, sel, treeutils.nullLit);
                    addAssert(that.pos(), Label.POSSIBLY_NULL_DEREFERENCE, e);
                }

                rhs = convertExpr(rhs);
                rhs = addImplicitConversion(rhs.pos(),that.type,rhs);
                if (specs.isNonNull(fa.sym,methodDecl.sym.enclClass())) {
                    JCExpression e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nullLit);
                    // FIXME - location of nnonnull declaration?
                    addAssert(that.pos(), Label.POSSIBLY_NULL_ASSIGNMENT, e);
                }

            }
            addBinaryChecks(that,op,newfa,rhs);
            checkAssignable(methodDecl, lhs, that, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);

            // We have to make a copy because otherwise the old and new JCFieldAccess share
            // a name field, when in fact they must be different
            JCFieldAccess newlhs = treeutils.makeSelect(newfa.pos,newfa.selected,newfa.sym);

            // Note that we need to introduce the temporary since the rhs may contain
            // identifiers that will be captured by the lhs. (TODO - example?)
            rhs = treeutils.makeBinary(that.pos,op ,newfa,rhs);
            JCIdent id = newTemp(rhs);
            JCExpressionStatement st = addStat(treeutils.makeAssignStat(that.getStartPosition(), newlhs, id));
            treeutils.copyEndPosition(st, that);
            result = eresult = post ? id : newTemp(newlhs);
            exprBiMap.put(that.lhs, eresult);
            lastStat = st.expr;
            
        } else if (lhs instanceof JCArrayAccess) {
            JCArrayAccess aa = (JCArrayAccess)lhs;
            JCExpression array = convertExpr(aa.indexed);
            if (javaChecks) {
                JCExpression e = treeutils.makeNeqObject(array.pos, array, treeutils.nullLit);
            // FIXME - location of nnonnull declaration?
                addAssert(that.pos(), Label.POSSIBLY_NULL_DEREFERENCE, e);
            }

            JCExpression index = convertExpr(aa.index);
            index = addImplicitConversion(index.pos(),syms.intType,index);
            if (javaChecks) {
                JCExpression e = treeutils.makeBinary(index.pos, JCTree.GE, index, treeutils.zero);
                addAssert(that.pos(), Label.POSSIBLY_NEGATIVEINDEX, e);
            }
            
            JCFieldAccess newfa = treeutils.makeLength(array.pos(), array);
            if (javaChecks) {
                JCExpression e = treeutils.makeBinary(index.pos, JCTree.LT, index, newfa);
                addAssert(that.pos(), Label.POSSIBLY_TOOLARGEINDEX, e);
            }

            checkAssignable(methodDecl, lhs, that, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);

            rhs = convertExpr(rhs);
            rhs = addImplicitConversion(rhs.pos(),that.type,rhs);

            lhs = new JmlBBArrayAccess(null,array,index); // FIXME - use factory
            lhs.pos = aa.pos;
            lhs.type = aa.type;
            lhs = newTemp(lhs);

            addBinaryChecks(that,op,lhs,rhs);
            
            // Note that we need to introduce the temporary since the rhs contains
            // identifiers that will be captured by the lhs. (TODO _ example?)
            rhs = treeutils.makeBinary(that.pos,op,lhs,rhs);
            JCIdent id = newTemp(rhs);
            
            lhs = new JmlBBArrayAccess(null,array,index); // FIXME - use factory
            lhs.pos = aa.pos;
            lhs.type = aa.type;
            
            JCExpressionStatement st = addStat(treeutils.makeAssignStat(that.getStartPosition(), lhs, id));
            treeutils.copyEndPosition(st, that);
            result = eresult = post ? id : newTemp(lhs);
            exprBiMap.put(that.lhs, eresult);
            lastStat = st.expr;
            
        } else {
            error(that.pos(),"Unexpected kind of AST in JmlAssertionAdder.visitAssignOp: " + that.getClass());
        }
    }

    /** This translates Java unary operations: ++ -- ! ~ - + */
    // FIXME - these need to be re-looked at
    @Override
    public void visitUnary(JCUnary that) {
        int tag = that.getTag();
        if (pureCopy) {
            // FIXME - need implicit conversions & boxing here as well
            JCExpression arg = convertExpr(that.getExpression());
            result = eresult = treeutils.makeUnary(that.pos,tag,that.getOperator(),arg);
            if (rac && jmltypes.isJmlType(that.type)) {
                if (that.type == jmltypes.BIGINT) {
                    treeutils.makeUtilsMethodCall(that.pos,"bigint_neg",convertExpr(that.getExpression()));
                }
            }
        } else if (translatingJML) {
            // FIXME - need implicit conversions & boxing here as well
            JCExpression arg = convertExpr(that.getExpression());
            if (rac && jmltypes.isJmlType(that.type)) {
                if (that.type == jmltypes.BIGINT) {
                    result = eresult = treeutils.makeUtilsMethodCall(that.pos,"bigint_neg",convertExpr(that.getExpression()));
                }
                if (that.type == jmltypes.REAL) {
                    result = eresult = treeutils.makeUtilsMethodCall(that.pos,"real_neg",convertExpr(that.getExpression()));
                }
            } else {
                result = eresult = treeutils.makeUnary(that.pos,tag,that.getOperator(),arg);
            }
        } else if (tag == JCTree.PREDEC || tag == JCTree.PREINC) {
            JCAssignOp b = M.at(that.getStartPosition()).Assignop(tag == JCTree.PREDEC ? JCTree.MINUS_ASG : JCTree.PLUS_ASG ,that.getExpression(),treeutils.one);
            treeutils.copyEndPosition(b, that);
            b.setType(that.type);
            b.operator = treeutils.findOpSymbol(tag == JCTree.PREDEC ? JCTree.MINUS : JCTree.PLUS ,that.type);
            visitAssignopHelper(b,false);
        } else if (tag == JCTree.POSTDEC || tag == JCTree.POSTINC){
            JCExpression arg = convertExpr(that.getExpression());
            JCIdent id = newTemp(arg);
            JCAssignOp b = M.at(that.pos()).Assignop(tag == JCTree.POSTDEC ? JCTree.MINUS_ASG : JCTree.PLUS_ASG, that.getExpression() ,treeutils.one);
            treeutils.copyEndPosition(b, that);
            b.setType(that.type);
            b.operator = treeutils.findOpSymbol(tag == JCTree.POSTDEC ? JCTree.MINUS : JCTree.PLUS,that.type);
            visitAssignopHelper(b,true);
            exprBiMap.put(that.getExpression(),eresult);
            result = eresult = id;
        } else {
            JCExpression arg = convertExpr(that.getExpression());
            addUnaryChecks(that,tag,arg);
            arg = addImplicitConversion(that.pos(),that.type,arg);
            JCExpression expr = treeutils.makeUnary(that.pos,tag,that.getOperator(),arg);
            result = eresult = newTemp(expr);
        }
    }
    
    // FIXME - boxing conversions for ++ --?
    
    /** Add any assertions to check for problems with binary operations. */
    protected void addBinaryChecks(JCExpression that, int op, JCExpression lhs, JCExpression rhs) {

        
        if (op == JCTree.DIV || op == JCTree.MOD) {
            JCExpression nonzero = treeutils.makeBinary(that.pos, JCTree.NE, rhs, treeutils.makeIntLiteral(that.pos, 0));
            if (javaChecks) addAssert(that.pos(),Label.POSSIBLY_DIV0,nonzero);
        }
        // NOTE: In Java, a shift by 0 is a no-op (aside from type promotion of the lhs);
        // a shift by a positive or negative amount s is actually a shift by 
        // the amount (s & 31) for int lhs or (s & 63) for long lhs.
        // So any rhs value is legal, but may be unexpected.
        
        if (op == JCTree.SL || op == JCTree.SR || op == JCTree.USR) {
            int mask =  (lhs.type.tag == TypeTags.LONG) ? 63 : 31;
            JCExpression expr = treeutils.makeBinary(that.pos,  JCTree.BITAND, 
                    mask == 31 ? treeutils.intbitandSymbol : treeutils.longbitandSymbol,
                    rhs, treeutils.makeIntLiteral(that.pos,  mask));
            expr = treeutils.makeBinary(that.pos, JCTree.EQ, rhs, expr);
            addAssert(that.pos(),Label.POSSIBLY_LARGESHIFT,expr);
        }
        // FIXME - add a command-line switch to enable the above?
        // FIXME - add checks for numeric overflow
        
    }

    /** Add any assertions to check for problems with unary operations. */
    protected void addUnaryChecks(JCExpression that, int op, JCExpression expr) {

        // FIXME - add checks for numeric overflow
        
    }
    
    // FIXME - check that condition is never used when pureCopy == true

    // OK
    @Override
    public void visitBinary(JCBinary that) {
        // FIXME - check on numeric promotion, particularly shift operators
        int tag = that.getTag();
        if (pureCopy) {
            JCExpression lhs = convertExpr(that.getLeftOperand());
            JCExpression rhs = convertExpr(that.getRightOperand());
            result = eresult = treeutils.makeBinary(that.pos,tag,that.getOperator(),lhs,rhs);
        } else if (translatingJML) {
            JCExpression prev = condition;
            try {
                Type maxJmlType = that.getLeftOperand().type;
                if (jmltypes.isJmlType(that.getRightOperand().type)) maxJmlType = that.getRightOperand().type;
                
                JCExpression lhs = convertExpr(that.getLeftOperand());
                JCExpression rhs = that.getRightOperand();
                // FIXME - check that all the checks in makeBinaryCHecks are here - or somehow reuse that method here
                // same for unary checks
                if (tag == JCTree.AND) {
                    if (!lhs.type.isPrimitive()) lhs = addImplicitConversion(lhs.pos(),syms.booleanType,lhs);
                    condition = treeutils.makeAnd(that.lhs.pos, condition, lhs);
                    rhs = convertExpr(rhs); // condition is used within scanExpr so this statement must follow the previous one
                    if (!rhs.type.isPrimitive()) rhs = addImplicitConversion(rhs.pos(),syms.booleanType,rhs);
                } else if (tag == JCTree.OR) { 
                    if (!lhs.type.isPrimitive()) lhs = addImplicitConversion(lhs.pos(),syms.booleanType,lhs);
                    condition = treeutils.makeAnd(that.lhs.pos, condition, treeutils.makeNot(that.lhs.pos,lhs));
                    rhs = convertExpr(rhs); // condition is used within scanExpr so this statement must follow the previous one
                    if (!rhs.type.isPrimitive()) rhs = addImplicitConversion(rhs.pos(),syms.booleanType,rhs);
                } else if (tag == JCTree.DIV || tag == JCTree.MOD) {
                    lhs = addImplicitConversion(lhs.pos(),that.type,lhs);
                    rhs = convertExpr(rhs);
                    rhs = addImplicitConversion(rhs.pos(),that.type,rhs);
                    JCExpression nonzero = treeutils.makeBinary(that.pos, JCTree.NE, rhs, treeutils.makeIntLiteral(that.rhs.pos, 0));
                    if (javaChecks) addAssert(that.pos(),Label.UNDEFINED_DIV0,treeutils.makeImplies(that.pos, condition, nonzero));
                } else if ((tag == JCTree.EQ || tag == JCTree.NE) && maxJmlType == jmltypes.TYPE) {
                    rhs = convertExpr(rhs);
                    if (rac) lhs = treeutils.makeUtilsMethodCall(that.pos,"isEqualTo",lhs,rhs);
                    else lhs = treeutils.makeBinary(that.pos, JCTree.EQ, lhs, rhs);
                    if (tag == JCTree.NE) lhs = treeutils.makeNot(that.pos, lhs);
                    result = eresult = lhs;
                    // Exit because we are replacing the == operator with a 
                    // function call
                    eresult.pos = that.getStartPosition();
                    treeutils.copyEndPosition(eresult, that);
                    return;
                } else if ((tag == JCTree.EQ || tag == JCTree.NE) && maxJmlType == jmltypes.BIGINT) {
                    lhs = addImplicitConversion(lhs.pos(),maxJmlType,lhs);
                    rhs = convertExpr(rhs);
                    rhs = addImplicitConversion(rhs.pos(),maxJmlType,rhs);
                    if (rac) {
                        lhs = treeutils.makeUtilsMethodCall(that.pos,"bigint_eq",lhs,rhs);
                    } else {
                        lhs = treeutils.makeBinary(that.pos, JCTree.EQ, lhs, rhs);
                    }
                    if (tag == JCTree.NE) lhs = treeutils.makeNot(that.pos, lhs);
                    result = eresult = lhs;
                    eresult.pos = that.getStartPosition();
                    treeutils.copyEndPosition(eresult, that);
                    return;
                } else if ((tag == JCTree.EQ || tag == JCTree.NE) && maxJmlType == jmltypes.REAL) {
                    rhs = convertExpr(rhs);
                    if (rac) lhs = treeutils.makeUtilsMethodCall(that.pos,"real_eq",lhs,rhs);
                    else lhs = treeutils.makeBinary(that.pos, JCTree.EQ, lhs, rhs);
                    if (tag == JCTree.NE) lhs = treeutils.makeNot(that.pos, lhs);
                    result = eresult = lhs;
                    eresult.pos = that.getStartPosition();
                    treeutils.copyEndPosition(eresult, that);
                    return;
                } else {
                        Type t = that.type;
                        if (t == syms.booleanType) {
                            // Compute a max type - FIXME - need to do this for all types
                            t = maxJmlType;
                        }
                        // FIXME - this is incorrect, but handles Jml primitive types at least
                        if (jmltypes.isJmlType(t)){ 
                            lhs = addImplicitConversion(lhs.pos(),t,lhs);
                            rhs = convertExpr(rhs);
                            rhs = addImplicitConversion(rhs.pos(),t,rhs);
                        } else {
                            rhs = convertExpr(rhs);
                        }
                }
                // FIXME - add checks for numeric overflow - PLUS MINUS MUL
                if (rac && jmltypes.isJmlType(maxJmlType)) {
                    if (maxJmlType == jmltypes.BIGINT || maxJmlType == jmltypes.REAL) {
                        String fcn;
                        switch (tag) {
                            case JCTree.PLUS: fcn = "add"; break;
                            case JCTree.MINUS: fcn = "sub"; break;
                            case JCTree.MUL: fcn = "mul"; break;
                            case JCTree.DIV: fcn = "div"; break;
                            case JCTree.MOD: fcn = "mod"; break;
                            case JCTree.LT: fcn = "lt"; break;
                            case JCTree.LE: fcn = "le"; break;
                            case JCTree.GT: fcn = "gt"; break;
                            case JCTree.GE: fcn = "ge"; break;
                            default: fcn = "";// error
                        }
                        String pre = maxJmlType == jmltypes.BIGINT ? "bigint_" : "real_";
                        result = eresult = treeutils.makeUtilsMethodCall(that.pos,pre+fcn,lhs,rhs);
                    }
                } else {
                    result = eresult = treeutils.makeBinary(that.pos,tag,that.getOperator(),lhs,rhs);
                }
            } finally {
                // Really only need the try-finally for AND and OR, but 
                // putting the whole if into the try sinmplifies the code
                condition = prev;
            }
        } else {
            if (tag == JCTree.OR) {
                JCConditional cond = M.at(that.pos()).Conditional(that.lhs,treeutils.trueLit,that.rhs);
                cond.setType(that.type);
                visitConditional(cond);
                // FIXME _ positions?
                return;
            }
            if (tag == JCTree.AND) {
                JCConditional cond = M.at(that.pos()).Conditional(that.lhs,that.rhs,treeutils.falseLit);
                cond.setType(that.type);
                visitConditional(cond);
                // FIXME - positions?
                return;
            }
            boolean comp = tag == JCTree.EQ || tag == JCTree.NE || tag == JCTree.GE || tag == JCTree.LE || tag == JCTree.LT || tag == JCTree.GT;
            boolean shift = tag == JCTree.SL || tag == JCTree.SR || tag == JCTree.USR;
            boolean arith = tag == JCTree.PLUS || tag == JCTree.MINUS || tag == JCTree.MUL || tag == JCTree.DIV || tag == JCTree.MOD;
            boolean bit = tag == JCTree.BITAND || tag == JCTree.BITOR || tag == JCTree.BITXOR;
            
            Symbol s = that.getOperator();
                    
            JCExpression lhs = convertExpr(that.getLeftOperand());
            if (comp) lhs = addImplicitConversion(lhs.pos(),unbox(that.lhs.type),lhs); // FIXME - what final type
            else if (shift) lhs = addImplicitConversion(lhs.pos(),unbox(that.type),lhs); // FIXME - what final type
            else lhs = addImplicitConversion(lhs.pos(),that.type,lhs);
            
            JCExpression rhs = convertExpr(that.getRightOperand());
            if (comp) rhs = addImplicitConversion(rhs.pos(),unbox(that.rhs.type),rhs); // FIXME - what final type
            else if (shift) {
                Type t = unbox(that.rhs.type);
                if (!t.equals(syms.longType)) t = syms.intType; 
                rhs = addImplicitConversion(rhs.pos(),syms.intType,rhs);
            }
            else rhs = addImplicitConversion(rhs.pos(),that.type,rhs);
            
            addBinaryChecks(that,tag,lhs,rhs);
            JCBinary bin = treeutils.makeBinary(that.pos,tag,that.getOperator(),lhs,rhs);
            result = eresult = newTemp(bin);
        }
        eresult.pos = that.getStartPosition(); // Need to make the start of the temporary Ident the same as the start of the expression it represents
        treeutils.copyEndPosition(eresult, that);
    }

    @Override
    public void visitTypeCast(JCTypeCast that) {
        // Note - casting a null produces a null value
        Type origType = that.getExpression().type;
        JCExpression lhs = convertExpr(that.getExpression());
        JCTree type = that.getType();
        JCTree clazz = treeutils.makeType(that.pos, type.type);
        
        if (rac && that.type.isPrimitive() && jmltypes.isJmlType(origType)) {
            if (that.type == origType) {
                result = eresult = lhs; // Noop
                // FIXME - will need a cast from real to bigint
            } else {
                String s = "bigint_to" + type.toString();
                JCExpression e = treeutils.makeUtilsMethodCall(that.pos,s,List.<JCExpression>of(lhs));
                result = eresult = e;
            }
            return;
        }
        JCExpression newexpr = M.at(that.pos()).TypeCast(clazz,lhs);
        newexpr.setType(that.type);
        treeutils.copyEndPosition(newexpr,that);
        
        if (pureCopy) {
            result = eresult = newexpr;
            return;
        }
        
        // Check that expression is either null or the correct type
        JCExpression eqnull = treeutils.makeEqObject(that.pos,lhs,treeutils.makeNullLiteral(that.pos));

        // FIXME - here and elsewhere, for rac, do we check for conditions that Java will check for itself?
        
        if (types.isSameType(clazz.type,lhs.type)) {
            // redundant
        } else if (clazz.type.isPrimitive()) {
            if (lhs.type.isPrimitive()) {
                // Must be numeric to numeric - do numeric range checks
                // FIXME - implement

            } else {
                // must be unboxing (object to primitive)
                // FIXME - implement

            }
        } else {
            if (lhs.type.isPrimitive()) {
                // Must be primitive to object (boxing) 
                // FIXME - implement
            } else {
                // object to object
                // For RAC, we check that the expression will not throw an exception
                // and then we calculate it
                // For ESC, we do the same check, but we don't do the case
                JCTree erasure = clazz;
                if (clazz instanceof JCTypeApply) erasure = ((JCTypeApply)clazz).clazz;
                JCExpression typeok = M.at(that.pos()).TypeTest(lhs, erasure);
                typeok.setType(syms.booleanType);
                // FIXME - end position?
                JCExpression cond = treeutils.makeOr(that.pos, eqnull, typeok);
                if (javaChecks) {
                    if (translatingJML) {
                        cond = treeutils.makeImplies(that.pos,condition,cond);
                        addAssert(that.pos(),Label.UNDEFINED_BADCAST,cond, lhs.type, clazz.type);
                    } else {
                        addAssert(that.pos(),Label.POSSIBLY_BADCAST,cond, lhs.type, clazz.type);
                    } 
                }
                if (esc) {
                    newexpr = lhs;
                }
            }
        }
        result = eresult = translatingJML ? newexpr : newTemp(newexpr);
    }

    // OK
    /** This translates the instanceof operation */
    @Override
    public void visitTypeTest(JCInstanceOf that) {
        JCExpression lhs = convertExpr(that.getExpression());
        JCTree type = that.getType();
        JCTree clazz = treeutils.makeType(type.pos, type.type);

        // No checks needed - Java allows (null instanceof type)
        // The value is always false
        JCInstanceOf e = M.at(that.pos()).TypeTest(lhs,clazz);
        e.setType(that.type);
        treeutils.copyEndPosition(e,that);
        result = eresult = (translatingJML || pureCopy) ? e : newTemp(e);

    }

    // OK
    @Override
    public void visitIndexed(JCArrayAccess that) {

        JCExpression indexed = convertExpr(that.indexed);

        // FIXME - for now we don't check undefinedness inside quantified expressions
        if (javaChecks && !pureCopy && localVariables.isEmpty()) {
            JCExpression nonnull = treeutils.makeNeqObject(that.indexed.pos, indexed, 
                    treeutils.makeNullLiteral(that.indexed.getEndPosition(log.currentSource().getEndPosTable())));
            if (translatingJML) {
                nonnull = treeutils.makeImplies(that.pos, condition, nonnull);
                addAssert(that.pos(),Label.UNDEFINED_NULL_DEREFERENCE,nonnull);
            } else {
                addAssert(that.pos(),Label.POSSIBLY_NULL_DEREFERENCE,nonnull);
            }
        }

        JCExpression index = convertExpr(that.index);
        index = addImplicitConversion(index.pos(),syms.intType,index);
        if (javaChecks && !pureCopy && localVariables.isEmpty()) {
            JCExpression compare = treeutils.makeBinary(that.index.pos, JCTree.LE, 
                    treeutils.makeIntLiteral(that.index.pos, 0), 
                    index);
            if (translatingJML) {
                compare = treeutils.makeImplies(that.pos, condition, compare);
                addAssert(compare.pos(),Label.UNDEFINED_NEGATIVEINDEX,compare);
            } else {
                addAssert(compare.pos(),Label.POSSIBLY_NEGATIVEINDEX,compare);
            }
        }
        
        JCExpression length = treeutils.makeLength(that.indexed.pos(),indexed);
        if (javaChecks && !pureCopy && localVariables.isEmpty()) {
            JCExpression compare = treeutils.makeBinary(that.pos, JCTree.GT, length, 
                    index); // We use GT to preserve the textual order of the subexpressions
            if (translatingJML) {
                compare = treeutils.makeImplies(that.pos, condition, compare); // FIXME condition is going to goof up the position information
                addAssert(compare.pos(),Label.UNDEFINED_TOOLARGEINDEX,compare);
            } else {
                addAssert(compare.pos(),Label.POSSIBLY_TOOLARGEINDEX,compare);
            }
        }

        if (pureCopy && !(that instanceof JmlBBArrayAccess)) {
            JCArrayAccess aa = M.at(that.pos()).Indexed(indexed,index);
            aa.setType(that.type);
            result = eresult = aa;
        } else {
            JmlBBArrayAccess aa = new JmlBBArrayAccess(null,indexed,index); // FIXME - switch to factory
            aa.pos = that.pos;
            aa.setType(that.type);
            aa.arraysId = that instanceof JmlBBArrayAccess ? ((JmlBBArrayAccess)that).arraysId : null;
            result = eresult = (translatingJML) ? aa : newTemp(aa);
        }
        treeutils.copyEndPosition(result, that);
    }

    // OK
    @Override
    public void visitSelect(JCFieldAccess that) {
        JCExpression selected;
        if (pureCopy || localVariables.contains(that.sym)) {
            result = eresult = treeutils.makeSelect(that.pos, convertExpr(that.getExpression()), that.sym);
        } else if (translatingJML && that.sym == null) {
            // This can happen while scanning a store-ref x.* 
            JCExpression sel = convertJML(that.selected); // FIXME - what if static; what if not a variable
            JCFieldAccess fa = M.Select(sel, (Name)null);
            fa.pos = that.pos;
            fa.sym = null;
            result = eresult = fa;
        } else if (translatingJML && attr.isModel(that.sym)) {
            JCExpression sel = convertJML(that.selected); // FIXME - what if static; what if not a variable
            Name mmName = names.fromString(Strings.modelFieldMethodPrefix + that.name.toString());
            JmlSpecs.TypeSpecs tyspecs = specs.getSpecs((ClassSymbol)that.sym.owner);
            for (JmlTypeClauseDecl x: tyspecs.modelFieldMethods) {
                if (x.decl instanceof JmlMethodDecl && ((JmlMethodDecl)x.decl).name.equals(mmName)) {
                    JmlMethodDecl md = (JmlMethodDecl)x.decl;
                    JCMethodInvocation app = treeutils.makeMethodInvocation(that.pos(),sel,md.sym);
                    result = eresult = app;
                    treeutils.copyEndPosition(result, that);
                    return;
                }
            }
            // This is an internal error - the wrapper for the model field method
            // should have been created during the MemberEnter phase.
            if (rac) throw new NoModelMethod();
            error(that.pos(), "No corresponding model method for model field " + that.sym);
            return;
        } else if (that.sym instanceof Symbol.TypeSymbol) {
            // This is a type name, so the tree should be copied, but without inserting temporary assignments
            // makeType creates a fully-qualified name
            result = eresult = treeutils.makeType(that.pos,that.type);
        } else {
            selected = convertExpr(that.selected);
            boolean var = false;
            if (!that.sym.isStatic() && that.selected instanceof JCIdent && !localVariables.contains(((JCIdent)that.selected).sym)) {
                JCExpression nonnull = treeutils.makeNeqObject(that.pos, selected, 
                        treeutils.nullLit);
                if (translatingJML) nonnull = treeutils.makeImplies(that.pos, condition, nonnull);
                if (javaChecks && localVariables.isEmpty()) {
                    addAssert(nonnull.pos(),
                        translatingJML? Label.UNDEFINED_NULL_DEREFERENCE : Label.POSSIBLY_NULL_DEREFERENCE,
                                nonnull);
                }
                var = true;
            }
            if (that.sym.owner instanceof ClassSymbol) {
                if (specs.isNonNull(that.sym,classDecl.sym) && that.sym instanceof VarSymbol && !localVariables.contains(that.sym)) {
                    JCFieldAccess e = M.at(that.pos()).Select(selected,that.name);
                    e.sym = that.sym;
                    e.type = that.type;
                    JCExpression nl = treeutils.makeNullLiteral(that.pos);
                    treeutils.copyEndPosition(nl,e);
                    JCExpression nonnull = treeutils.makeNeqObject(that.pos, e, nl);
                    addAssume(nonnull.pos(),Label.NULL_FIELD,nonnull);
                }
            }
            JCFieldAccess fa = treeutils.makeSelect(that.pos,selected,that.sym);
            result = eresult = (translatingJML || !var) ? fa : newTemp(fa);
            if (oldenv != null) {
                result = eresult = treeutils.makeOld(that.pos,eresult,oldenv);
            }
        }
        treeutils.copyEndPosition(result, that);
    }
    
    public static class NoModelMethod extends RuntimeException {
    }
    
    // FIXME - check use of condition everywhere 
    
    java.util.List<Symbol> reps = new LinkedList<Symbol>();
    
    // OK
    @Override
    public void visitIdent(JCIdent that) {
        if (pureCopy) {
            result = eresult = treeutils.makeIdent(that.pos, that.sym);
            treeutils.copyEndPosition(eresult, that);
            return;
        }
        // If we are translating the postcondition then parameters
        // must be mapped to the values at the beginning of the method, 
        // not the current values
        if (translatingJML) {
            JCVariableDecl decl;
            if (isPostcondition && preparams != null && (decl=preparams.get(that.sym)) != null) {
                result = eresult = treeutils.makeIdent(that.pos,decl.sym);
                treeutils.copyEndPosition(eresult, that);
                return;
            }
        }
        // Check if the id is a model field, and if so:
        // if rac, then map it to a call of
        // the corrresponding model method. We have to use model methods 
        // instead of just inlining the represents clause expression because
        // the model field/method may be overridden in derived classes.
        if (attr.isModel(that.sym) && that.sym instanceof VarSymbol) {
            if (!reps.contains(that.sym)) {
                reps.add(0,that.sym);
                try {
                    if (rac) {
                        Name mmName = names.fromString(Strings.modelFieldMethodPrefix + that.name.toString());
                        JmlSpecs.TypeSpecs tyspecs = specs.getSpecs(classDecl.sym);
                        for (JmlTypeClauseDecl x: tyspecs.modelFieldMethods) {
                            if (x.decl instanceof JmlMethodDecl && ((JmlMethodDecl)x.decl).name.equals(mmName)) {
                                JmlMethodDecl md = (JmlMethodDecl)x.decl;
                                JCMethodInvocation app = treeutils.makeMethodInvocation(that.pos(),null,md.sym);
                                result = eresult = app;
                                treeutils.copyEndPosition(eresult, that);
                                return;
                            }
                        }
                        if (rac) throw new NoModelMethod();
                        error(that.pos(), "No corresponding model method for " + that.sym);
                        return;
                    }
                    if (esc) {
                        TypeSpecs tspecs = specs.getSpecs((ClassSymbol)that.sym.owner);
                        for (JmlTypeClause tc : tspecs.clauses) {
                            if (tc.token == JmlToken.REPRESENTS) {
                                JmlTypeClauseRepresents rep = (JmlTypeClauseRepresents)tc;

                                if (((JCIdent)rep.ident).sym.equals(that.sym)) {
                                    if (oldenv == null) {
                                        JmlStatementHavoc st = M.at(that.pos).JmlHavocStatement(List.<JCExpression>of(rep.ident));
                                        addStat(st);
                                    }
                                    if (rep.suchThat){
                                        addAssume(that.pos(),Label.IMPLICIT_ASSUME,
                                                convertExpr(rep.expression));

                                    } else {
                                        addAssumeEqual(that.pos(),Label.IMPLICIT_ASSUME,
                                                convertExpr(rep.ident),
                                                convertExpr(rep.expression));
                                    }
                                }
                            }
                        }
                    }
                } finally {
                    reps.remove(that.sym);
                }
            }
        }
        // Lookup if there is some other translation of the id. For example, 
        // this could be a translation of the formal from the specification 
        // in a parent class mapped to the formal in the target class. It
        // can also be the mapping from a formal to actual argument.
        JCExpression actual = paramActuals == null ? null : paramActuals.get(that.sym);
        if (actual != null) {
            // Replicate the AST so we are not sharing ASTs across multiple
            // instances of the original ID.
            result = eresult = convertCopy(actual);
            eresult.pos = that.pos; // FIXME - this might be better if the actual were converted to a temporary Ident
            treeutils.copyEndPosition(eresult, that);
            
        } else if (localVariables.contains(that.sym)) {
            // just copy
            result = eresult = treeutils.makeIdent(that.pos,that.sym);
            
        } else if (that.sym instanceof Symbol.TypeSymbol) {
            // The input id is a type, so we expand it to a FQ name
            // If the input id is a type variable (that.type instanceof Type.TypeVar)
            // then makeType creates a new JCIdent, as is appropriate.
            result = eresult = treeutils.makeType(that.pos, that.type);
            
        } else if (!(that.sym.owner instanceof Symbol.TypeSymbol)) {
            // local variable  - just leave it as 
            // an ident (the owner is null or the method)
            JCIdent id = treeutils.makeIdent(that.pos, that.sym);
            result = eresult = id;

        } else if (currentThisId != null && that.sym == currentThisId.sym) {
            // 'this' - leave it as it is
            JCIdent id = treeutils.makeIdent(that.pos, currentThisId.sym);
            result = eresult = id;
            
        } else if (that.name.toString().equals("this")) {
            // 'this' - leave it as it is
            JCIdent id = treeutils.makeIdent(that.pos, currentThisId.sym);
            result = eresult = id;
            
        } else if (that.name.toString().equals("super")) {
            // 'super' - leave it as it is
            JCIdent id = treeutils.makeIdent(that.pos, currentThisId.sym);
            result = eresult = id;

        } else if (!that.sym.isStatic()) {
            // It is a non-static class field, so we prepend 'this'
            // FIXME - do we need to use the current this?
            JCIdent id  = treeutils.makeIdent(that.pos,currentThisId.sym);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,id,that.sym);
            if (that.sym instanceof VarSymbol && that.sym.owner instanceof ClassSymbol && specs.isNonNull(that.sym, classDecl.sym)) {
                JCExpression e = treeutils.makeNeqObject(that.pos, fa, treeutils.nullLit);
                addAssume(that.pos(),Label.NULL_FIELD,e);
            }
            result = eresult = fa;
            
        } else {
            // static class field - add the qualified name
            JCExpression typetree = treeutils.makeType(that.pos,that.sym.owner.type);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,typetree,that.sym);
            if (that.sym instanceof VarSymbol && that.sym.owner instanceof ClassSymbol && specs.isNonNull(that.sym, classDecl.sym)) {
                JCExpression e = treeutils.makeNeqObject(that.pos, fa, treeutils.nullLit);
                addAssume(that.pos(),Label.NULL_FIELD,e);
            }
            result = eresult = fa;
        }
        treeutils.copyEndPosition(eresult, that);
        if (oldenv != null) {
            result = eresult = treeutils.makeOld(that.pos, eresult, oldenv);
            treeutils.copyEndPosition(eresult, that);
        }
    }

    // OK
    @Override
    public void visitLiteral(JCLiteral that) {
        result = eresult = that;
        if (fullTranslation) {
            result = eresult = treeutils.makeDuplicateLiteral(that.pos, that);
            treeutils.copyEndPosition(eresult, that);
        }
        
    }

    // OK
    @Override
    public void visitTypeIdent(JCPrimitiveTypeTree that) {
        // This is a simple primitive type
        eresult = that;
        if (fullTranslation) {
            eresult = M.at(that.pos()).TypeIdent(that.typetag).setType(that.type);
        }
        result = eresult;
    }

    @Override
    public void visitTypeArray(JCArrayTypeTree that) {
        // This is a type literal that is an array - we just copy it
        if (fullTranslation) {
            result = eresult = M.at(that.pos()).TypeArray(convertExpr(that.elemtype)).setType(that.type);
        } else {
            result = eresult = that;
        }
    }

    // OK
    @Override
    public void visitTypeApply(JCTypeApply that) {
        result = eresult = !fullTranslation ? that :
            M.at(that.pos()).TypeApply(convertExpr(that.clazz),convertExprList(that.arguments)).setType(that.type);
    }

    // OK
    @Override
    public void visitTypeParameter(JCTypeParameter that) {
        result = !fullTranslation ? that :
            M.at(that.pos()).TypeParameter(that.name, convertExprList(that.bounds)).setType(that.type);
    }

    // OK
    @Override
    public void visitWildcard(JCWildcard that) {
        result = eresult = !fullTranslation ? that :
            M.at(that.pos()).Wildcard(convert(that.kind),convert(that.inner)).setType(that.type);
    }

    // OK
    @Override
    public void visitTypeBoundKind(TypeBoundKind that) {
        result = !fullTranslation ? that :
            M.at(that.pos()).TypeBoundKind(that.kind).setType(that.type);
    }

    // OK
    @Override
    public void visitAnnotation(JCAnnotation that) {
        // Only needed for a full tree copy
        // A JCAnnotation is a kind of JCExpression
        if (fullTranslation) {
            JCTree aType = treeutils.makeType(that.annotationType.pos, that.annotationType.type);
            // FIXME - where would any generated checks be put?
            List<JCExpression> args = convertCopy(that.args);
            JCAnnotation a = M.at(that.pos()).Annotation(aType,args);
            a.setType(a.annotationType.type);
            treeutils.copyEndPosition(a,that);
            result = eresult = a;
        } else {
            result = eresult = that;
        }
    }

    // OK
    @Override
    public void visitModifiers(JCModifiers that) {
        if (fullTranslation) {
            ListBuffer<JCAnnotation> annotations = new ListBuffer<JCAnnotation>();
            // FIXME - not doing any checking on the annotations - where would the checks go?
            for (JCAnnotation a: that.annotations) {
                annotations.add(convertCopy(a));
            }
            JCModifiers mods = M.at(that.pos()).Modifiers(that.flags, annotations.toList());
            result = mods;
        } else {
            result = that;
        }
    }

    // OK
    @Override
    public void visitErroneous(JCErroneous that) {
        List<? extends JCTree> errs = fullTranslation ? convertCopy(that.errs) : that.errs;
        result = eresult = M.at(that.pos()).Erroneous(errs).setType(that.type);
    }

    // FIXME - when is this actually used? or if?
    // OK
    @Override
    public void visitLetExpr(LetExpr that) {
        result = eresult = M.at(that.pos()).LetExpr(convert(that.defs), convert(that.expr)).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlBinary(JmlBinary that) {
        JCExpression saved = condition;
        try {
            JCExpression lhs = convertExpr(that.lhs);
            if (that.op != JmlToken.SUBTYPE_OF) lhs = addImplicitConversion(that.lhs.pos(),that.type,lhs);
            JCExpression rhs,t;
            switch (that.op) {
                case IMPLIES:
                    condition = treeutils.makeAnd(that.pos, condition, lhs);
                    rhs = convertExpr(that.rhs);
                    rhs = addImplicitConversion(that.rhs.pos(),that.type,rhs);
                    t = treeutils.makeNot(lhs.pos, lhs);
                    t = treeutils.makeOr(that.pos, t, rhs);
                    eresult = t;
                    break;

                case EQUIVALENCE:
                    rhs = convertExpr(that.rhs);
                    rhs = addImplicitConversion(that.rhs.pos(),that.type,rhs);
                    t = treeutils.makeBinary(that.pos, JCTree.EQ, treeutils.booleqSymbol, lhs, rhs);
                    eresult = t;
                    break;

                case INEQUIVALENCE:
                    rhs = convertExpr(that.rhs);
                    rhs = addImplicitConversion(that.rhs.pos(),that.type,rhs);
                    t = treeutils.makeBinary(that.pos, JCTree.NE, treeutils.boolneSymbol, lhs, rhs);
                    eresult = t;
                    break;

                case REVERSE_IMPLIES:
                    t = treeutils.makeNot(lhs.pos, lhs);
                    condition = treeutils.makeAnd(that.pos, condition, t);
                    rhs = convertExpr(that.rhs);
                    rhs = addImplicitConversion(that.rhs.pos(),that.type,rhs);
                    rhs = treeutils.makeNot(that.rhs.pos, rhs);
                    t = treeutils.makeOr(that.pos, lhs, rhs);
                    eresult = t;
                    break;

                case SUBTYPE_OF: // JML subtype
                    lhs = convertExpr(that.lhs);
                    rhs = convertExpr(that.rhs);
                    // \TYPE <: \TYPE
                    if (rac) {
                        JCExpression c = methodCallUtilsExpression(that.pos(),"isSubTypeOf",lhs,rhs);
                        eresult = c;
                    } else {
                        JmlMethodInvocation c = treeutils.makeJmlMethodInvocation(that.pos(),JmlToken.SUBTYPE_OF,that.type,lhs,rhs);
                        eresult = c;
                    }
                    break;
                        
                case JSUBTYPE_OF: // Java subtype
                    lhs = convertExpr(that.lhs);
                    rhs = convertExpr(that.rhs);
                    // Class <: Class - in case type checking allows it

                    // TODO - move to a utility method
                    // FIXME - do we intend that <: is always false among pairs of primitive types (even the same)
                    if (rac) {
                        Name n = names.fromString("isAssignableFrom");
                        Scope.Entry e = rhs.type.tsym.members().lookup(n);
                        Symbol ms = e.sym;
                        JCFieldAccess m = M.at(that.pos()).Select(rhs,n);
                        m.sym = ms;
                        m.type = m.sym.type;

                        JCExpression c = M.at(that.pos()).Apply(null,m,List.<JCExpression>of(lhs));
                        c.setType(syms.booleanType);
                        eresult = c;
                    } else {
                        eresult = treeutils.trueLit; // FIXME
                    }
                    break;

                    // FIXME - need <# <#= operators
                default:
                    error(that.pos(),"Unexpected token in JmlAssertionAdder.visitJmlBinary: " + that.op);

            }
        } finally {
            condition = saved;
        }
        result = eresult;
        eresult.pos = that.getStartPosition();
        treeutils.copyEndPosition(eresult, that);
    }

    // OK
    @Override
    public void visitJmlChoose(JmlChoose that) {
        result = M.at(that.pos()).JmlChoose(that.token,convert(that.orBlocks),convert(that.elseBlock)).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        JmlMethodDecl savedMethodDecl = this.methodDecl;
        JmlClassDecl savedClassDecl = this.classDecl;
        ListBuffer<JCTree> savedClassDefs = this.classDefs;
        ListBuffer<JCStatement> savedCurrentStatements = this.currentStatements;
        Symbol savedAllocSym = this.allocSym;
        Symbol savedIsAllocSym = this.isAllocSym;
        JCIdent savedThisId = this.currentThisId;

        
        if (that.sym.isInterface()) {
            // FIXME - should actually do a pure copy.?
            result = that;
            classBiMap.put(that,that);
            return;
        }
        try {
            this.classDecl = that;
            this.methodDecl = null;
            if (esc) {
                JCVariableDecl dd = treeutils.makeVarDef(classDecl.sym.type,names.fromString("THIS"),classDecl.sym,
                    Position.NOPOS); // FIXME - does this need initialization for RAC?
                dd.sym.flags_field |= Flags.STATIC;
                dd.mods.flags |= Flags.STATIC;
                this.currentThisId = treeutils.makeIdent(classDecl.pos,dd.sym);
                this.thisIds.put(classDecl.sym, this.currentThisId);
            } else { // rac
                this.currentThisId = treeutils.makeIdent(classDecl.pos,that.thisSymbol);
            }
            this.classDefs = new ListBuffer<JCTree>();
            this.currentStatements = null;

            {
                JCVariableDecl d = treeutils.makeVarDef(syms.intType,names.fromString(Strings.allocName),classDecl.sym,
                        treeutils.makeNullLiteral(classDecl.pos));
                allocSym = d.sym;
                d = treeutils.makeVarDef(syms.booleanType,names.fromString(Strings.isAllocName),classDecl.sym,
                        treeutils.makeNullLiteral(classDecl.pos));
                isAllocSym = d.sym;
            }

            for (JCTree t: that.defs) {
                scan(t);
            }
            
            JmlSpecs.TypeSpecs tyspecs = that.typeSpecsCombined;
            if (tyspecs != null) {
                for (JmlTypeClause t: tyspecs.clauses) {
                    switch (t.token){
                        case JMLDECL:
                        case REPRESENTS:
                            scan(t);
                            break;
                        case INVARIANT:
                        case CONSTRAINT:
                        case INITIALLY:
                        case AXIOM:
                        case IN:
                        case MAPS:
                            // skip
                            break;
                        default:
                            log.error(t.pos,"jml.internal","Clause type not handled in visitJmlClassDecl: " + t.token.internedName());
                    }
                }
                if (rac) for (JmlClassDecl t: tyspecs.modelTypes) {
                    scan(t);
                }
            }

            List<JCTree> defs = this.classDefs.toList();
            // FIXME - replicate all the other AST nodes
            List<JCTypeParameter> typarams = that.typarams;
            if (fullTranslation) typarams = convert(typarams);
            JmlClassDecl n = M.at(that.pos()).ClassDef(convert(that.mods),that.name,typarams,convertExpr(that.extending),convertExprList(that.implementing),defs);
            n.sym = that.sym;
            n.setType(that.type);
            n.superSymbol = that.superSymbol;
            n.thisSymbol = that.thisSymbol;
            n.toplevel = that.toplevel;  // FIXME - translate to new top level
            n.docComment = that.docComment;
            n.env = that.env; // FIXME - translate?
            n.specsDecls = that.specsDecls; // FIXME - these may be self-references - and I think there are now only one
            n.typeSpecs = null; //that.typeSpecs; // not copied - FIXME? here and elsewhere
            n.typeSpecsCombined = null; //that.typeSpecsCombined; // not copied
            if (savedClassDefs != null && n.sym.owner instanceof ClassSymbol) {
                savedClassDefs.add(n);
            } else if (currentStatements != null) {
                addStat(n);
            }
            result = n;
            classBiMap.put(that,n);
        } finally {
            this.classDecl = savedClassDecl;
            this.methodDecl = savedMethodDecl;
            this.classDefs = savedClassDefs;
            this.currentThisId = savedThisId;
            this.currentStatements = savedCurrentStatements;
            this.allocSym = savedAllocSym;
            this.isAllocSym = savedIsAllocSym;
        }
    }

    // OK
    @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        if (translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitJmlCompilationUnit while translating JML: " + that.getClass());
            return;
        }

        List<JCTree> defs = convert(that.defs);
        JmlCompilationUnit n = M.at(that.pos()).TopLevel(that.packageAnnotations,that.pid,defs);
        n.docComments = that.docComments; // FIXME: need to translate map
        n.endPositions = that.endPositions;
        n.flags = that.flags;
        n.mode = that.mode;
        n.lineMap = that.lineMap;
        n.namedImportScope = that.namedImportScope;
        n.packge = that.packge;
        n.setType(that.type);
        n.parsedTopLevelModelTypes = that.parsedTopLevelModelTypes; // FIXME: need to convert
        n.sourcefile = that.sourcefile;
        n.starImportScope = that.starImportScope;
        n.specsCompilationUnit = that.specsCompilationUnit; // FIXME: need to convert
        n.specsTopLevelModelTypes = convert(that.specsTopLevelModelTypes);
        result = n;
    }
    //OK
    @Override
    public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) {
        result = M.at(that.pos()).JmlConstraintMethodSig(convertExpr(that.expression),convertExprList(that.argtypes));
        result.setType(that.type);
    }

    // OK
    @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        if (pureCopy) {
            JCExpression e = convertExpr(that.cond);
            JmlDoWhileLoop loop = M.at(that.pos()).DoLoop(null,e);
            try {
                treeMap.put(that, loop);
                JCStatement bl = convert(that.body);
                loop.body = bl;
                loop.setType(that.type);
                loop.loopSpecs = convertCopy(that.loopSpecs); 
                result = loop;
            } finally {
                treeMap.remove(that);
            }
            return;
        }
        
        /*
         *   loop_invariant INV
         *   loop_variant  VAR
         *   label: do { BODY } while (COND);
         * becomes
         *   {
         *      ... declare index
         *      assert INV
         *      label: do {
         *         havoc
         *         assume INV
         *         TEMP = VAR
         *         assert 0 <= TEMP
         *         loop_bodyN: {
         *            ... statements from BODY
         *            ... continue --> break loop_bodyN;
         *            ... break --> break;
         *         }
         *         ... statements from COND // put before INV for side-effects
         *         assert INV
         *         TEMP2 = VAR
         *         assert TEMP2 < TEMP
         *         if (!COND') {
         *             assert INV;
         *             break;
         *         }
         *      } while (true);
         *   }
         *         
         */

        // FIXME - need label for loop if any and the target mapping
        
        // Outer block to restrict scopes of temporaries
        pushBlock();

        JCVariableDecl indexDecl = loopHelperDeclareIndex(that.pos());

        java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

        // Create this early so it is available as a target
        JmlWhileLoop loop = M.at(that.pos()).WhileLoop(treeutils.trueLit,null);
        treeMap.put(that, loop);

        // Test that invariants hold before entering loop
        loopHelperInitialInvariant(that.loopSpecs);

        // New loop body
        pushBlock();
        
        // Havoc all items that might be changed in the loop
        if (esc) {
            loopHelperHavoc(that.body.pos(),that.body,that.cond);
        }
        
        loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that);
        
        // Now in the loop, so check that the variants are non-negative
        loopHelperCheckNegative(decreasesIDs, that.pos());
        
        // Then translate the original loop body
        // Have to do some footwork to get the Block object before constructing its contents
        
        loopHelperMakeBody(that.body);
        
        // Now compute any side-effects of the loop condition
        addTraceableComment(that.cond,that.cond,"Loop test");
        JCExpression cond = convertExpr(that.cond);
        
        // increment the index
        loopHelperIncrementIndex(indexDecl);
        
        // After the loop, check the invariants and check that the variants have decreased
        loopHelperAssertInvariants(that.loopSpecs,decreasesIDs);
        
        // Construct the loop test and the exit block. The loop invariant is
        // tested again, though it is the same test as immediately above.
        loopHelperMakeBreak(that.loopSpecs,cond,loop,that.pos());

        // Finish up the new loop body
        // Finish up the output block
        loopHelperFinish(loop,that);
    }

    // OK
    @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        if (pureCopy) {
            JCExpression expr = convertExpr(that.expr);
            JCVariableDecl var = convert(that.var);
            // FIXME - should not do this two-level design
            JCEnhancedForLoop jloop = M.at(that.pos()).ForeachLoop(var,expr,null);
            List<JmlStatementLoop> loopSpecs = that.loopSpecs == null ? null : convertCopy(that.loopSpecs);
            JmlEnhancedForLoop loop = M.at(that.pos()).JmlEnhancedForLoop(jloop, loopSpecs);
            jloop.type = loop.type = that.type;
            try {
                treeMap.put(that, jloop);
                JCStatement bl = convert(that.body);
                loop.body = bl;
                loop.loopSpecs = that.loopSpecs == null ? null : convertCopy(that.loopSpecs); 
                result = loop;
            } finally {
                treeMap.remove(that);
            }
            return;
        }
        
        /*   loop_invariant INV
         *   loop_variant  VAR
         *   label: for (T v: ARRAY) BODY
         * becomes
         *   {
         *      ... statements from ARRAY
         *      ... declare INDEX = 0
         *      ... compute LENGTH
         *      assert INV
         *      label: while (true) {
         *         havoc
         *         assume INV
         *         TEMP = VAR
         *         if (INDEX >= LENGTH) {
         *             assert INV;
         *             break;
         *         }
         *         assert 0 <= TEMP
         *         declare v = ARRAY[INDEX]
         *         loop_bodyN: {
         *            ... statements from BODY
         *            ... continue --> break loop_bodyN;
         *            ... break --> break;
         *         }
         *         INDEX = INDEX + 1
         *         assert INV
         *         TEMP2 = VAR
         *         assert TEMP2 < TEMP
         *      }
         *      // FIXME - if break exits still have to satisfy invariant, put the check here
         *   }
         *         
         */
        /*   loop_invariant INV
         *   loop_variant  VAR
         *   label: for (T v: ITERABLE) BODY
         * becomes
         *   {
         *      ... statements from ITERABLE
         *      ... declare INDEX = 0
         *      ... declare ITERATOR = ITERABLE.iterator()
         *      assert INV
         *      label: while (true) {
         *         havoc
         *         assume INV
         *         TEMP = VAR
         *         if (ITERATOR.hasNext()) {
         *             assert INV;
         *             break;
         *         }
         *         declare v = ITERATOR.next()
         *         assert 0 <= TEMP
         *         loop_bodyN: {
         *            ... statements from BODY
         *            ... continue --> break loop_bodyN;
         *            ... break --> break;
         *         }
         *         INDEX = INDEX + 1
         *         assert INV
         *         TEMP2 = VAR
         *         assert TEMP2 < TEMP
         *      }
         *      // FIXME - if break exits still have to satisfy invariant, put the check here
         *   }
         *         
         */
        
        // FIXME - need label for loop if any and the target mapping
        
        // Outer block to restrict scopes of temporaries
        pushBlock();

        JCExpression array = convertExpr(that.expr);

        JCVariableDecl indexDecl = loopHelperDeclareIndex(that.pos());;

        java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

        // Create this early so it is available as a target
        JmlWhileLoop loop = M.at(that.pos()).WhileLoop(treeutils.trueLit,null);
        treeMap.put(that, loop);

        if (that.expr.type.tag == TypeTags.ARRAY) {
        
            JCExpression lengthExpr = treeutils.makeLength(array.pos(), array);
            lengthExpr = newTemp(lengthExpr); // FIXME - could give it a recognizable name

            // Test that invariants hold before entering loop
            loopHelperInitialInvariant(that.loopSpecs);

            // New loop body
            pushBlock();

            // Havoc all items that might be changed in the loop
            if (esc) {
                loopHelperHavoc(that.body.pos(),that.body,that.expr);
            }

            // Assume the invariants
            // Compute and remember the variants
            loopHelperAssumeInvariants(that.loopSpecs,decreasesIDs,that);

            // Compute the condition, recording any side-effects
            {

                JmlSingleton index = M.at(that.pos).JmlSingleton(JmlToken.BSINDEX);
                index.type = syms.intType;
                JCExpression ocond = treeutils.makeBinary(that.pos, JCTree.LT, 
                        index,
                        lengthExpr);
                JCExpression cond = convertJML(ocond);
                addTraceableComment(ocond,ocond,"Loop test");

                // The exit block tests the condition; if exiting, it tests the
                // invariant and breaks.
                loopHelperMakeBreak(that.loopSpecs,cond,loop,that.pos());
            }

            // Now in the loop, so check that the variants are non-negative
            loopHelperCheckNegative(decreasesIDs, that.pos());

            JCArrayAccess aa = new JmlBBArrayAccess(null,array,treeutils.makeIdent(that.pos, indexDecl.sym));
            aa.setType(that.var.type);
            JCVariableDecl loopVarDecl = treeutils.makeVarDef(that.var.type, 
                    that.var.name, methodDecl.sym, aa);
            addStat(loopVarDecl);


        } else {
            // Have an iterable instead of an array
            
            Name iteratorName = names.fromString("_JML_iterator_" + (++count));
            JCExpression iter = methodCallUtilsExpression(array.pos(),"iterator",array);
            Type restype;
            restype = new Type.ClassType.ClassType(Type.noType,List.<Type>of(array.type.getTypeArguments().head),iter.type.tsym);
            JCVariableDecl decl = treeutils.makeVarDef(
                    restype,
                    iteratorName,
                    methodDecl.sym,
                    iter);
            addStat(decl);
            
            // Test that invariants hold before entering loop
            loopHelperInitialInvariant(that.loopSpecs);

            // New loop body
            pushBlock();

            // Havoc all items that might be changed in the loop
            if (esc) {
                loopHelperHavoc(that.body.pos(),that.expr,that.body);
            }

            // Assume the invariants
            // Compute and remember the variants
            loopHelperAssumeInvariants(that.loopSpecs,decreasesIDs,that);

            // Compute the condition, recording any side-effects
            {

                // iterator.hasNext()
                JCExpression ocond = methodCallUtilsExpression(array.pos(),"hasNext",
                        treeutils.makeIdent(array.pos, decl.sym));
                JCExpression cond = convertCopy(ocond);
                addTraceableComment(ocond,ocond,"Loop test");

                // The exit block tests the condition; if exiting, it tests the
                // invariant and breaks.
                loopHelperMakeBreak(that.loopSpecs,cond,loop,that.pos());
            }
            
            // Now in the loop, so check that the variants are non-negative
            loopHelperCheckNegative(decreasesIDs, that.pos());

            // T v = ITERATOR.next()
            JCExpression value = methodCallUtilsExpression(array.pos(),"next",
                    treeutils.makeIdent(array.pos, decl.sym));
            addStat( treeutils.makeVarDef(
                    that.var.type,
                    that.var.name,
                    methodDecl.sym,
                    value) );

        }
        
        // Then translate the original loop body
        // Have to do some footwork to get the Block object before constructing its contents
        loopHelperMakeBody(that.body);
    
        // increment the index
        loopHelperIncrementIndex(indexDecl);
        
        // After the loop, check the invariants and check that the variants have decreased
        loopHelperAssertInvariants(that.loopSpecs,decreasesIDs);
        
        // Finish up the new loop body
        // Finish up the output block
        loopHelperFinish(loop,that);

        // FIXME Need to add specifications; also index and values variables
//        JCVariableDecl v = M.at(that.var.pos).VarDef(that.var.sym,null);
//        v.setType(that.var.type);
//        JCExpression e = scanExpr(that.expr);
//        pushBlock();
//        // Now havoc any variables changed in the loop
//        {
//            ListBuffer<JCExpression> targets = TargetFinder.findVars(that.getStatement(),null);
//            TargetFinder.findVars(that.getExpression(),targets);
//            // synthesize a modifies list
//            JmlStatementHavoc st = M.at(that.body.pos).JmlHavocStatement(targets.toList());
//            addStat(st);
//        }
//        scan(that.body);
//        JCBlock b = popBlock(0,that.body.pos);
//        addStat(M.at(that.pos()).ForeachLoop(v, e, b));
        // result?
    }
    
    /** Declares the synthetic index variable for the loop, adding the declaration
     * to the current statement list.
     */
    // OK
    protected JCVariableDecl loopHelperDeclareIndex(DiagnosticPosition pos) {
        Name indexName = names.fromString("index_" + pos.getPreferredPosition() + "_" + (++count));
        JCVariableDecl indexDecl = treeutils.makeVarDef(syms.intType, indexName, methodDecl.sym, treeutils.zero);
        indexDecl.sym.pos = pos.getPreferredPosition();
        indexDecl.pos = pos.getPreferredPosition();
        addStat(indexDecl);
        indexStack.add(0,indexDecl);
        return indexDecl;
    }
    
    /** Finds variables assigned in the loop body and adds a havoc statement */
    // OK
    // FIXME - needs checking that we are getting all of needed variables
    protected void loopHelperHavoc(DiagnosticPosition pos, List<? extends JCTree> list, JCTree... trees) {
        ListBuffer<JCExpression> targets = new ListBuffer<JCExpression>();
        if (list != null) for (JCTree t: list) {
            TargetFinder.findVars(t,targets);
        }
        for (JCTree t: trees) {
            TargetFinder.findVars(t,targets);
        }
        targets.add(treeutils.makeIdent(pos.getPreferredPosition(),indexStack.get(0).sym));
        // synthesize a modifies list
        JmlStatementHavoc st = M.at(pos.getPreferredPosition()).JmlHavocStatement(targets.toList());
        addStat(st);
    }
    
    // FIXME: implement loop_modifies?
    
    /** Finds variables assigned in the loop body and adds a havoc statement */
    // OK
    // FIXME - needs checking that we are getting all of needed variables
    protected void loopHelperHavoc(DiagnosticPosition pos, JCTree... trees) {
        loopHelperHavoc(pos, null, trees);
    }
    
    /** Adds a statement to increment the index variable */
    protected void loopHelperIncrementIndex(JCVariableDecl var) {
        JCIdent oldid = treeutils.makeIdent(var.pos, var.sym);
        JCIdent newid = treeutils.makeIdent(var.pos, var.sym);
        addStat( treeutils.makeAssignStat(var.pos, newid,
                treeutils.makeBinary(var.pos, JCTree.PLUS, treeutils.intplusSymbol, oldid, treeutils.one)));
    }
    
    /** Creates initial assert statements for any loop invariants */
    protected void loopHelperInitialInvariant(List<JmlStatementLoop> loopSpecs) {
        if (loopSpecs != null) {
            for (JmlStatementLoop inv: loopSpecs) {
                if (inv.token == JmlToken.LOOP_INVARIANT) {
                    JCExpression copy = convertCopy(inv.expression);
                    addTraceableComment(inv,copy,inv.toString());
                    JCExpression e = convertJML(copy);
                    addAssert(inv.pos(),Label.LOOP_INVARIANT_PRELOOP, e);
                }
            }
        }
    }
    
    /** Create the if statement that is the loop exit */
    protected void loopHelperMakeBreak(List<JmlStatementLoop> loopSpecs, JCExpression cond, JCTree loop, DiagnosticPosition pos) {
        pushBlock();
        JCBreak br = M.at(pos).Break(null);
        br.target = loop;
        addStat(br);
        JCBlock bl = popBlock(0,pos);
        JCExpression ncond = treeutils.makeNot(pos.getPreferredPosition(),cond);
        addStat(M.at(pos).If(ncond,bl,null));
    }
    
    /** Convert the loop body */
    protected void loopHelperMakeBody(JCStatement body) {
        addTraceableComment(body,null,"Begin loop body");
        JCBlock bodyBlock = M.at(body.pos()).Block(0, null);
        Name label = names.fromString("loopBody_" + body.pos + "_" + (++count));
        JCLabeledStatement lab = M.at(body.pos()).Labelled(label,bodyBlock);
        continueStack.push(lab);
        addStat(lab);

        try {
            JCBlock bl = convertIntoBlock(body.pos(),body);
            bodyBlock.stats = bl.stats;
        } finally {
            continueStack.pop();
        }
    }
    
    /** Inserts the invariants as assumptions; also computes initial values of
     * the variants. (at the beginning of a loop body) */
    protected void loopHelperAssumeInvariants(List<JmlStatementLoop> loopSpecs, java.util.List<JCIdent> decreasesIDs, JCTree that) {
        addTraceableComment(that, null, "Begin loop check");
        DiagnosticPosition pos = that.pos();
        
        // Assume the invariants
        if (loopSpecs != null) {
            for (JmlStatementLoop inv: loopSpecs) {
                if (inv.token == JmlToken.LOOP_INVARIANT) {
                    JCExpression copy = convertCopy(inv.expression);
                    addTraceableComment(inv,copy,inv.toString());
                    JCExpression e = convertJML(copy);
                    addAssume(inv.pos(),Label.LOOP_INVARIANT_ASSUMPTION, e);
                }
            }
        }
        {
            JCVariableDecl indexDecl = indexStack.get(0);
            JCIdent id = treeutils.makeIdent(pos.getPreferredPosition(),indexDecl.sym);
            JCBinary bin = treeutils.makeBinary(pos.getPreferredPosition(),JCTree.LE,treeutils.intleSymbol,treeutils.zero,id);
            addAssume(pos,Label.IMPLICIT_ASSUME, bin);
        }

        // Compute and remember the variants
        if (loopSpecs != null) {
            for (JmlStatementLoop inv: loopSpecs) {
                if (inv.token == JmlToken.DECREASES) {
                    JCExpression copy = convertCopy(inv.expression);
                    addTraceableComment(inv,copy,inv.toString(),"Initial Value of Loop Decreases Expression");
                    JCExpression e = convertJML(copy);
                    JCIdent id = newTemp(e);
                    decreasesIDs.add(id);
                }
            }
        }
    }
    
    /** Check that the variants are non-negative */
    protected void loopHelperCheckNegative(java.util.List<JCIdent> decreasesIDs, DiagnosticPosition pos) {
        for (JCIdent id: decreasesIDs) {
            JCBinary compare = treeutils.makeBinary(pos.getPreferredPosition(), JCTree.LE, treeutils.intleSymbol, treeutils.zero, id);
            addAssert(id.pos(),Label.LOOP_DECREASES_NEGATIVE,compare);
        }
    }

    /** Asserts the invariants and that the variants are decreasing */
    protected void loopHelperAssertInvariants(List<JmlStatementLoop> loopSpecs, java.util.List<JCIdent> decreasesIDs) {
        if (loopSpecs != null) {
            for (JmlStatementLoop inv: loopSpecs) {
                if (inv.token == JmlToken.LOOP_INVARIANT) {
                    JCExpression copy = convertCopy(inv.expression);
                    addTraceableComment(inv,copy,inv.toString());
                    JCExpression e = convertJML(copy);
                    addAssert(inv.pos(),Label.LOOP_INVARIANT, e);
                }
            }

            Iterator<JCIdent> iter = decreasesIDs.iterator();
            for (JmlStatementLoop inv: loopSpecs) {
                if (inv.token == JmlToken.DECREASES) {
                    JCExpression copy = convertCopy(inv.expression);
                    addTraceableComment(inv,copy,inv.toString());
                    JCExpression e = convertJML(copy);
                    JCIdent id = newTemp(e);
                    JCBinary bin = treeutils.makeBinary(inv.pos, JCTree.LT,  treeutils.intltSymbol, id, iter.next());
                    addAssert(inv.pos(),Label.LOOP_DECREASES, bin);
                }
            }
        }
        
    }
    
    /** Completes the loop */
    protected void loopHelperFinish(JmlWhileLoop loop, JCTree that) {
        JCBlock bl = popBlock(0,that.pos());
        loop.body = bl;
        loop.setType(that.type);
        addStat(loop);
        treeMap.remove(that);
        indexStack.remove(0);

        
        addStat(popBlock(0,that.pos()));
    }
    
    // OK
    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        if (pureCopy) {
            List<JCStatement> init = convert(that.init);
            JCExpression cond = convertExpr(that.cond);
            List<JCExpressionStatement> step = convert(that.step);
            JmlForLoop loop = M.at(that.pos()).ForLoop(init,cond,step,null);
            try {
                treeMap.put(that, loop);
                JCStatement bl = convert(that.body);
                loop.body = bl;
                loop.setType(that.type);
                loop.loopSpecs = convertCopy(that.loopSpecs); 
                result = loop;
            } finally {
                treeMap.remove(that);
            }
            return;
        }
        
        addTraceableComment(that,"for ...");
        
        /*   loop_invariant INV
         *   loop_variant  VAR
         *   label: for (INIT; COND; STEP) BODY
         * becomes
         *   {
         *      ... statements from INIT
         *      assert INV
         *      label: while (true) {
         *         havoc
         *         assume INV
         *         TEMP = VAR
         *         ... statements from COND
         *         if (!COND') {
         *             assert INV;
         *             break;
         *         }
         *         assert 0 <= TEMP
         *         loop_bodyN: {
         *            ... statements from BODY
         *            ... continue --> break loop_bodyN;
         *            ... break --> break;
         *         }
         *         ... statements from STEP
         *         assert INV
         *         TEMP2 = VAR
         *         assert TEMP2 < TEMP
         *      }
         *      // FIXME - if break exits still have to satisfy invariant, put the check here
         *   }
         *         
         */
        
        // FIXME - need label for loop if any and the target mapping
        
        // Outer block to restrict scopes of temporaries
        pushBlock();

        if (that.init != null) scan(that.init);
        
        JCVariableDecl indexDecl = loopHelperDeclareIndex(that.pos());;

        java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

        // Create this early so it is available as a target
        JmlWhileLoop loop = M.at(that.pos()).WhileLoop(treeutils.trueLit,null);
        treeMap.put(that, loop);

        // Test that invariants hold before entering loop
        loopHelperInitialInvariant(that.loopSpecs);

        // New loop body
        pushBlock();
        
        // Havoc all items that might be changed in the loop
        if (esc) {
            loopHelperHavoc(that.body.pos(),that.step,that.body,that.cond);
        }
        
        loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that);
        
        // Compute the condition, recording any side-effects
        if (that.cond != null) {
            
            addTraceableComment(that.cond,that.cond,"Loop test");
            JCExpression cond = convertExpr(that.cond);

            // The exit block tests the condition; if exiting, it breaks out of the loop
            loopHelperMakeBreak(that.loopSpecs, cond, loop, that.pos());
        }
        
        // Now in the loop, so check that the variants are non-negative
        loopHelperCheckNegative(decreasesIDs, that.pos());
        
        // Then translate the original loop body
        // Have to do some footwork to get the Block object before constructing its contents
        
        loopHelperMakeBody(that.body);
        
        if (that.step != null) scan(that.step);
        
        // increment the index
        loopHelperIncrementIndex(indexDecl);
        
        // After the loop, check the invariants and check that the variants have decreased
        loopHelperAssertInvariants(that.loopSpecs,decreasesIDs);
        
        // Finish up the new loop body
        // Finish up the output block
        loopHelperFinish(loop,that);
    }

    @Override
    public void visitJmlGroupName(JmlGroupName that) {
        JmlGroupName g = M.at(that.pos()).JmlGroupName(convertCopy(that.selection));
        g.setType(that.type);
        g.sym = that.sym;
        result = g;
    }

    // OK
    @Override
    public void visitJmlImport(JmlImport that) {
        // FIXME - need to rewrite qualid - might have a *; might have a method name
        result = M.at(that.pos()).Import(that.qualid, that.staticImport).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        JCExpression expr = convertExpr(that.expression);

        if (pureCopy) {
            result = eresult = M.at(that.pos()).JmlLblExpression(that.labelPosition, that.token, that.label, expr).setType(that.type);
            return;
        }
        // The format of this string is important in interpreting it in JmlEsc
        String nm = Strings.labelVarString + that.token.internedName().substring(1) + "_" + that.label;
        JCIdent id = newTemp(that.getLabelPosition(),nm,expr);
        id.pos = that.pos;
        //labels.push(nm);
        result = eresult = id;
        if (esc) ((VarSymbol)id.sym).pos = Position.NOPOS;
        if (rac) {
            JCExpression lit = treeutils.makeLit(that.getPreferredPosition(),syms.stringType,that.label.toString());
            String name = null;
            Type t = eresult.type;
            if (!t.isPrimitive()) {
                name = "reportObject";
            } else if (t.tag == TypeTags.INT) {
                name = "reportInt";
            } else if (t.tag == TypeTags.BOOLEAN) {
                name = "reportBoolean";
            } else if (t.tag == TypeTags.LONG) {
                name = "reportLong";
            } else if (t.tag == TypeTags.CHAR) {
                name = "reportChar";
            } else if (t.tag == TypeTags.SHORT) {
                name = "reportShort";
            } else if (t.tag == TypeTags.FLOAT) {
                name = "reportFloat";
            } else if (t.tag == TypeTags.DOUBLE) {
                name = "reportDouble";
            } else if (t.tag == TypeTags.BYTE) {
                name = "reportByte";
            } else if (t.tag == TypeTags.BOT) {
                name = "reportObject";
            } else if (t instanceof JmlType) {
                name = "reportObject";
            } else  {
                // this is a type error - should never get here
                error(that.pos(),"Unknown type in a \\lbl expression: " + t);
            }
            if (name != null) {
                JCFieldAccess m = findUtilsMethod(that.pos(),name);
                JCMethodInvocation c = M.at(that.pos()).Apply(null,m,List.<JCExpression>of(lit,treeutils.makeIdent(id.pos,id.sym))); 
                c.type = id.type;
                JCStatement st = M.at(that.pos()).Exec(c);
                if (that.token == JmlToken.BSLBLPOS) {
                    // Only report if the expression is true
                    // It is a type error if it is not boolean
                    st = M.at(that.pos()).If(treeutils.makeIdent(id.pos,id.sym), st, null);
                } else if (that.token == JmlToken.BSLBLNEG) {
                    // Only report if the expression is false
                    // It is a type error if it is not boolean
                    st = M.at(that.pos()).If(treeutils.makeNot(that.pos, treeutils.makeIdent(id.pos,id.sym)), st, null);
                }
                addStat(st);
            }
        }
    }

    // OK
    /** Assigns 'result' a new copy of the AST node */
    @Override
    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) {
        JmlMethodClauseCallable mc = M.at(that.pos()).JmlMethodClauseCallable(that.keyword);
        mc.setType(that.type);
        mc.methodSignatures = convertCopy(that.methodSignatures);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    /** Assigns 'result' a new copy of the AST node */
    @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        JmlMethodClauseConditional mc = M.at(that.pos()).JmlMethodClauseConditional(
                that.token,
                convertExpr(that.expression),
                convertExpr(that.predicate));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    /** Assigns 'result' a new copy of the AST node */
    @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        JmlMethodClauseDecl mc = M.at(that.pos()).JmlMethodClauseDecl(
                that.token,
                convert(that.decls));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    /** Assigns 'result' a new copy of the AST node */
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        JmlMethodClauseExpr mc = M.at(that.pos()).JmlMethodClauseExpr(
                that.token,
                convertExpr(that.expression));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    /** Assigns 'result' a new copy of the AST node */
    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        JmlMethodClauseGroup mc = M.at(that.pos()).JmlMethodClauseGroup(
                convert(that.cases));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    /** Assigns 'result' a new copy of the AST node */
    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        JmlMethodClauseSignals mc = M.at(that.pos()).JmlMethodClauseSignals(
                that.token,
                convert(that.vardef),
                convertExpr(that.expression));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    /** Assigns 'result' a new copy of the AST node */
    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        JmlMethodClauseSignalsOnly mc = M.at(that.pos()).JmlMethodClauseSignalsOnly(
                that.token,
                convertExprList(that.list));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        JmlMethodClauseStoreRef mc = M.at(that.pos()).JmlMethodClauseStoreRef(
                that.token,
                convertExprList(that.list));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
    	log.useSource(that.source());
        boolean saved = translatingJML;
        String nm = that.name.toString();
        if (attr.isModel(that.sym) && nm.startsWith(Strings.modelFieldMethodPrefix)) {
            if (that.body.stats.isEmpty()) {
                // We are presuming that all represents clauses are processed
                // (as part of scanning the specs defs in visitJmlClassDecl)
                // before we handle all the model field methods.
                log.warning(that.pos,"jml.no.model.method.implementation",nm.substring(Strings.modelFieldMethodPrefix.length())); // FIXME - extract name of model field
                JCReturn st = M.Return(treeutils.makeZeroEquivalentLit(that.pos,that.sym.type.getReturnType()));
                st.pos = that.pos;
                that.body.stats = List.<JCStatement>of(st);
                classDefs.add(that);
                return;
            }
        }
        try {
            // FIXME - implemente constructors - need super calls.
            //        if (that.restype == null) { classDefs.add(that); return; } // FIXME - implement constructors
            JCBlock body = convertMethodBodyNoInit(that,classDecl);

            List<JCTypeParameter> typarams = that.typarams;
            if (fullTranslation) typarams = convertCopy(typarams); // FIXME - is there anything to be translated
            List<JCVariableDecl> params = that.params;
            if (fullTranslation) params = convertCopy(params); // Just a copy - the parameters are just modifiers, types, and names
            JCExpression restype = that.restype;
            if (fullTranslation) restype = convertExpr(restype);
            JmlMethodDecl m = M.at(that.pos()).MethodDef(convert(that.mods), that.name, restype, typarams, params, convertExprList(that.thrown), body, convertExpr(that.defaultValue));
            m.sym = that.sym;
            m.setType(that.type);
            m._this = that._this;
            m.sourcefile = that.sourcefile;
            m.owner = that.owner; // FIXME - new class decl?
            m.docComment = that.docComment;
            m.cases = convertCopy(that.cases);
            m.methodSpecsCombined = that.methodSpecsCombined; // FIXME - copy?
            m.specsDecl = that.specsDecl; // FIXME - needs new reference
            if (classDefs != null) classDefs.add(m); // classDefs can be null if  JmlEsc.check is called directly on a JCMethodDecl
            result = m;
            methodBiMap.put(that,m);
        } catch (JmlNotImplementedException e) {
            notImplemented("method (or represents clause) containing ",e);
            log.error(e.pos,"jml.unrecoverable", "Unimplemented construct in a method or model method or represents clause");
        } finally {
            translatingJML = saved;
        }
    }

    /** Helper function to translate a \type expression for RAC */
    protected void translateTypelc(JCMethodInvocation tree) {
        // Argument is a type, not an expression, so we
        // replace it with a type literal
        JCExpression arg = tree.args.get(0);
        result = eresult = translateTypeArg(arg);
    }
    
    //  // FIXME - check this is the old method - why slightly different
    //  public void translateTypelc(JmlMethodInvocation that) {
    //      // Presumes this is indeed a \type invocation and
    //      // that the one argument is a Type
    //      JCTree type = that.args.get(0);
    //      result = eresult = treeutils.trType(that.pos, type);
    //  }



    //// FIXME - Docuiment - should this be used where generic typeargs exist?
    protected JCExpression translateTypeArg(JCExpression targ) {
        // Argument is a type, not an expression, so we
        // replace it with a type literal
        if (targ instanceof JCTree.JCTypeApply) {
            JCTree.JCTypeApply ta = (JCTree.JCTypeApply)targ;
            JCTree.JCFieldAccess f = M.Select(ta.clazz,names._class);
            f.type = syms.classType;
            f.sym = f.type.tsym;
            int size = ta.arguments.size();
            ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
            for (JCExpression ttarg : ta.arguments) {
                args.add(translateTypeArg(ttarg));
            }
            Type elemtype = args.elems.head.type;
            JCNewArray argsarray = M.NewArray(M.Type(elemtype), List.<JCExpression>of(treeutils.makeIntLiteral(Position.NOPOS, size)), args.toList());
            argsarray.type = new Type.ArrayType(elemtype,syms.arrayClass);
            return methodCallUtilsExpression(targ.pos(),"makeTYPE",f,argsarray);
        } else if (targ instanceof JCTree.JCWildcard) {
            return methodCallUtilsExpression(targ.pos(),"makeTYPEQ");
            // FIXME - need to handle more subtypes differently, I'm sure
        } else { // JCPrimitiveTypeTree, JCFieldAccess, JCIdent, JCArrayTypeTree
            JCTree.JCFieldAccess f = M.Select(targ,names._class);
            f.type = syms.classType;
            f.sym = f.type.tsym;
            return methodCallUtilsExpression(targ.pos(),"makeTYPE0",f);
        }
    }

    // OK
    /** Creates a type-checked expression for (expr).getClass() - for RAC */
    protected JCExpression methodCallgetClass(JCExpression expr) {
        Name n = names.fromString("getClass");
        Scope.Entry e = syms.objectType.tsym.members().lookup(n);
        Symbol ms = e.sym;
        JCFieldAccess m = M.Select(expr,n);
        m.sym = ms;
        m.type = m.sym.type;

        JCExpression c = M.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.classType);
        return c;
    }

    // FIXME - what about generic types
    // FIXME - what about arrays of arrays
    protected void translateTypeOf(JCMethodInvocation tree) {
        JCExpression arg = tree.args.get(0);
        int tag = arg.type.tag;
        switch (tag) {
            case TypeTags.ARRAY:
            case TypeTags.CLASS:
                eresult = methodCallgetClass(convertExpr(arg));
                break;
            case TypeTags.BOOLEAN:
                eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Boolean");
                break;
            case TypeTags.INT:
                eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Integer");
                break;
            case TypeTags.LONG:
                eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Long");
                break;
            case TypeTags.SHORT:
                eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Short");
                break;
            case TypeTags.BYTE:
                eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Byte");
                break;
            case TypeTags.FLOAT:
                eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Float");
                break;
            case TypeTags.DOUBLE:
                eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Double");
                break;
            case TypeTags.CHAR:
                eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Character");
                break;
            default:
                log.error(arg.pos,"jml.unknown.construct","typeof for " + arg.type,"JmlRac.translateTypeOf");
                // We give it an arbitrary value // FIXME - or do we call it undefined
                eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Boolean");
                break;
        }
        // Make a \TYPE from a Java class literal
        result = eresult = methodCallUtilsExpression(tree.pos(),"makeTYPE0",eresult);
    }
    
    protected JCExpression translateType(JCExpression type) {
        if (type.type instanceof Type.TypeVar) {
            JCExpression t = paramActuals.get(((Type.TypeVar)type.type).tsym);
            if (t != null) type = t;
        } 
        return convertExpr(type);
    }

    /** Helper method to translate \elemtype expressions for RAC */
    protected void translateElemtype(JCMethodInvocation tree) {
        // OK for Java types, but not complete for JML types - FIXME
        JCExpression arg = tree.args.head;
        arg = convertExpr(arg);
        if (tree.type == JmlTypes.instance(context).TYPE) {
            arg = methodCallUtilsExpression(tree.pos(),"erasure",arg);
        }
        Name n = names.fromString("getComponentType");
        Scope.Entry e = syms.classType.tsym.members().lookup(n);
        Symbol ms = e.sym;
        JCFieldAccess m = M.Select(arg,n);
        m.sym = ms;
        m.type = m.sym.type;

        JCExpression c = M.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.classType);
        result = eresult = c;
        if (tree.type == JmlTypes.instance(context).TYPE) {
            result = eresult = methodCallUtilsExpression(tree.pos(),"makeTYPE0",c);
        }
    }


    // OK
    // These are special JML fcn-like calls (e.g. \old, \nonnullelements, ...)
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        if (pureCopy) {
            JmlMethodInvocation m = M.at(that.pos()).JmlMethodInvocation(that.token, convertExprList(that.args));
            m.setType(that.type);
            m.label = that.label;
            m.startpos = that.startpos;
            m.varargsElement = that.varargsElement;
            // typeargs and meth are always null for a 
            result = eresult = m;
            return;
        }
        switch (that.token) {
            case BSPAST:
            case BSOLD:
            case BSPRE:
            {
                JCIdent savedEnv = oldenv;
                // FIXME _ this implementation is not adequate for checking postconditions with \old from callers
                // FIXME - also it does not work for rac at labelled locations
                try {
                    if (rac) {
                        ListBuffer<JCStatement> saved = currentStatements;
                        try {
                            if (that.args.size() == 2) {
                                currentStatements = new ListBuffer<JCStatement>();
                            } else {
                                currentStatements = oldStatements;
                            }
                            JCExpression arg = convertExpr(that.args.get(0));
                            String s = "_JML___old_" + (++count); // FIXME - Put string in Strings
                            Name nm = names.fromString(s);
                            JCVariableDecl v = treeutils.makeVarDef(arg.type,nm,methodDecl.sym,arg);
                            v.mods.flags |= Flags.FINAL;
                            addStat(v);
                            if (that.args.size() == 2) {
                                JCExpression e = that.args.get(1);
                                Name label = ((JCIdent)e).name;
                                ListBuffer<JCStatement> list = labelActiveOldLists.get(label);
                                if (list != null) {
                                    list.add(v);
                                } else {
                                    ListBuffer<JCStatement> stlist = labelOldLists.get(label);
                                    ListBuffer<JCStatement> newlist = new ListBuffer<JCStatement>();
                                    for (JCStatement st: stlist) {
                                        if (st instanceof JCLabeledStatement && ((JCLabeledStatement)st).label.equals(label)) {
                                            newlist.addAll(currentStatements);
                                        }
                                        newlist.add(st);
                                    }
                                    stlist.clear();
                                    stlist.addAll(newlist);
                                }
                            }
                            JCIdent id = treeutils.makeIdent(arg.pos,v.sym);
                            eresult = id;
                        } finally {
                            currentStatements = saved;
                        }
                    } else { // esc
                        if (that.args.size() == 1) {
                            oldenv = preLabel; // FIXME - could have a constant name for this
                        } else {
                            // The second argument is a label, held as a JCIdent
                            oldenv = (JCIdent)that.args.get(1);
                        }
                        JCExpression m = convertExpr(that.meth);
                        JCExpression arg = convertExpr(that.args.get(0)); // convert is affected by oldenv
                        JmlMethodInvocation meth;
                        if (that.args.size() == 1) {
                            meth = M.at(that.pos()).JmlMethodInvocation(that.token,arg);
                        } else {
                            // The second argument is a label, held as a JCIdent
                            meth = M.JmlMethodInvocation(that.token,arg,that.args.get(1));
                        }
                        meth.setType(that.type);
                        meth.pos = that.pos;
                        meth.startpos = that.startpos;
                        meth.varargsElement = that.varargsElement;
                        meth.meth = m;
                        meth.label = that.label;
                        meth.typeargs = that.typeargs; // FIXME - do these need translating?
                        eresult = meth;
                    }
                } finally {
                    oldenv = savedEnv;
                }
            }
            break;
            
            case BSNONNULLELEMENTS :
            if (rac) {
                int n = that.args.size();
                if (n == 0) {
                    result = eresult = treeutils.trueLit;
                } else {
                    JCExpression conj = null;
                    for (JCExpression arg : that.args) {
                        JCExpression e = methodCallUtilsExpression(arg.pos(),"nonnullElementCheck",arg);
                        conj = conj == null? e :
                            treeutils.makeAnd(arg.pos, conj, e);
                    }
                    result = eresult = convertExpr(conj);
                }
            } else { // esc
                JCExpression arg = convertExpr(that.args.get(0));
                JCBinary bin = treeutils.makeNeqObject(that.pos, arg, treeutils.nullLit);
                addAssert(that.pos(),Label.POSSIBLY_NULL_VALUE,
                        treeutils.makeImplies(that.pos, condition, bin));
                
                Name index = names.fromString("ind");
                JCVariableDecl d = treeutils.makeVarDef(syms.intType, index, null, that.pos);
                JCIdent id = treeutils.makeIdent(that.pos, d.sym);
                JCArrayAccess aa = M.at(that.pos).Indexed(arg, id);
                aa.type = syms.objectType;
                // FIXME - set correct component type
                JCBinary b1 = treeutils.makeBinary(that.pos,JCTree.LE,treeutils.zero,id);
                JCExpression len = treeutils.makeLength(that.pos(),arg);
                JCBinary b2 = treeutils.makeBinary(that.pos, JCTree.LT, id, len);
                bin = treeutils.makeNeqObject(that.pos, aa, treeutils.nullLit);
                JmlQuantifiedExpr q = M.at(that.pos).JmlQuantifiedExpr(JmlToken.BSFORALL,
                        List.<JCVariableDecl>of(d),
                        treeutils.makeBinary(that.pos, JCTree.AND, treeutils.andSymbol, b1, b2),
                        bin);
                q.type = syms.booleanType;
                result = eresult = convertExpr(q);
            }
            break;
            
            case BSTYPEOF:
                {
                    if (rac) {
                        translateTypeOf(that);
                    }
                    if (esc) {
                        JCExpression arg = convertExpr(that.args.get(0));
                        JmlMethodInvocation meth = M.at(that.pos()).JmlMethodInvocation(that.token,arg);
                        meth.startpos = that.startpos;
                        meth.varargsElement = that.varargsElement;
                        meth.meth = that.meth;
                        meth.type = that.type;
                        meth.label = that.label;
                        meth.typeargs = that.typeargs; // FIXME - do these need translating?
                        result = eresult = meth;
                    }
                }
                break;
    
            case BSTYPELC:
                if (rac) {
                    translateTypelc(that);
                }
                if (esc) {
                    JCExpression t = translateType(that.args.get(0));
                    result = eresult = treeutils.makeJmlMethodInvocation(that.pos(), JmlToken.BSTYPELC, that.type, t);
                }
                break;
            
            case BSELEMTYPE:
                if (rac) translateElemtype(that);
                if (esc) throw new JmlNotImplementedException(that.pos(),that.token.internedName());
                // FIXME - need esc
                break;

            case BSMAX :
            case BSFRESH :
            case BSREACH :
            case BSSPACE :
            case BSWORKINGSPACE :
            case BSDURATION :
            case BSISINITIALIZED :
            case BSINVARIANTFOR :
            case BSNOWARN:
            case BSNOWARNOP:
            case BSWARN:
            case BSWARNOP:
            case BSBIGINT_MATH:
            case BSSAFEMATH:
            case BSJAVAMATH:
                // FIXME - not implemented
                throw new JmlNotImplementedException(that.pos(),that.token.internedName());

            default:
                Log.instance(context).error("esc.internal.error","Unknown token in JmlAssertionAdder: " + that.token.internedName());
                throw new JmlNotImplementedException(that.pos(),that.token.internedName());
        }
        result = eresult;
    }

    @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        if (!pureCopy) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitJmlMethodSpecs: " + that.getClass());
            return;
        }
        
        List<JmlSpecificationCase> cases = convertCopy(that.cases);
        JmlMethodSpecs ms = M.at(that.pos()).JmlMethodSpecs(cases);
        ms.setType(that.type);
        ms.decl = that.decl; // FIXME - copy - needs remapping
        ms.deSugared = that.deSugared; // FIXME - copy
        ms.forExampleCases = that.forExampleCases; // FIXME - copy
        ms.impliesThatCases = that.impliesThatCases; // FIXME - copy
        result = ms;
    }

    // OK
    @Override
    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        result = M.at(that.pos()).JmlModelProgramStatement(convert(that.item)).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        JCExpression tree;
        if (rac && that.type instanceof JmlType) {
            tree =  M.at(that.pos()).JmlPrimitiveTypeTree(that.token).setType(that.type);
            //tree = ((JmlType)that.type).repType;
        } else {
            tree =  M.at(that.pos()).JmlPrimitiveTypeTree(that.token).setType(that.type);
        }
        result = eresult = tree;
    }

    java.util.List<Symbol> localVariables = new LinkedList<Symbol>();
    // OK
    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        if (pureCopy || esc) {
            for (JCVariableDecl d: that.decls) {
                localVariables.add(0,d.sym);
            }
            try {
                result = eresult = M.at(that.pos()).
                    JmlQuantifiedExpr(that.op,convertCopy(that.decls),convertExpr(that.range),convertExpr(that.value)).setType(that.type);
            } finally {
                for (JCVariableDecl d: that.decls) {
                    localVariables.remove(d.sym);
                }
            }
            return;
        }
        if (!translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitJmlQuantifiedExpr: " + that.getClass());
            return;
        }
        // FIXME - review the kinds of quantified expressions that are not translated
        if (that.racexpr != null) {
            result = eresult = that.racexpr; // FIXME: using convertCopy(that.racexpr); fails
        } else {
            log.note(that.pos(),"rac.not.implemented.quantified");
            result = eresult = treeutils.makeZeroEquivalentLit(that.pos,that.type);
        }
    }

    // OK
    @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        if (pureCopy || esc) {
            result = eresult = M.at(that.pos()).
                    JmlSetComprehension(convert(that.newtype),convert(that.variable),convertExpr(that.predicate)).setType(that.type);
            return;
        }
        // FIXME - implement
        throw new JmlNotImplementedException(that.pos(),"set comprehension expression");
        //return;
    }

    // OK
    @Override
    public void visitJmlSingleton(JmlSingleton that) {
        if (pureCopy) {
            JmlSingleton e = M.at(that.pos()).JmlSingleton(that.token);
            e.type = that.type;
            e.symbol = that.symbol;
            e.info = that.info;
            treeutils.copyEndPosition(e,that);
            result = eresult = e;
            return;
        }
        if (!translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitJmlSingleton: " + that.getClass());
            return;
        }
        switch (that.token) {
            case BSRESULT:
                if (resultSym == null) {
                    error(that.pos(), "It appears that \\result is used where no return value is defined"); // FIXME - not an internal error
                } else {
                    eresult = treeutils.makeIdent(that.pos, resultSym);
                }
                break;

            case INFORMAL_COMMENT: // FIXME - new informal comment syntax?
                eresult = treeutils.makeBooleanLiteral(that.pos,true);
                break;
                
            case BSEXCEPTION:
                if (exceptionSym == null) {
                    error(that.pos(),"It appears that \\exception is used where no exception value is defined" ); // FIXME - not an internal error
                } else {
                    eresult = treeutils.makeIdent(that.pos,exceptionSym);
                }
                break;

            case BSINDEX:
                if (indexStack.isEmpty()) {
                    error(that.pos(),"\\index expression used outside a loop");
                } else {
                    JCVariableDecl vd = indexStack.get(0);
                    JCIdent id = treeutils.makeIdent(that.pos,vd.sym);
                    eresult = id;
                }
                break;

                // FIXME - implement these
//            case BSVALUES:
//                if (that.info == null) {
//                    log.error(that.pos,"esc.internal.error","No loop index found for this use of " + that.token.internedName());
//                    result = null;
//                } else {
//                    result = newIdentUse((VarSymbol)that.info,that.pos);
//                }
//                break;
//            
//            case BSLOCKSET:
//            case BSSAME:
               

            case BSNOTSPECIFIED:
            case BSNOTHING:
            case BSEVERYTHING:
                eresult = that;
                if (fullTranslation) {
                    JmlSingleton e = M.at(that.pos()).JmlSingleton(that.token);
                    e.info = that.info;
                    e.symbol = that.symbol;
                    e.setType(that.type);
                    eresult = e;
                }
                break;

            default:
                Log.instance(context).error(that.pos, "jml.unknown.construct",that.token.internedName(),"JmlAssertionAdder.visitJmlSingleton");
                eresult = treeutils.nullLit; // Not sure continuation will be successful in any way
                break;
        }
        result = eresult;
    }
    

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        if (translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitJmlSpecificationCase while translating JML: " + that.getClass());
            return;
        }
        if (!pureCopy) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitJmlSpecificationCase: " + that.getClass());
            return;
        }
        
        JmlSpecificationCase sc = M.at(that.pos()).JmlSpecificationCase(
                convert(that.modifiers),
                that.code,
                that.token,
                that.also,
                that.clauses);
        sc.sourcefile = that.sourcefile;
        sc.block = that.block == null ? null : convertBlock(that.block); // model program
        sc.setType(that.type);
        result = sc;
    }

    @Override
    public void visitJmlStatement(JmlStatement that) {
        result = null;
        switch (that.token) {
            case DEBUG:
                // FIXME - resolve what sort of constructs are actually allowed in a debug and set statement
                Set<String> keys = utils.commentKeys;
                if (!keys.contains("DEBUG")) return;
                //$FALL-THROUGH$
            case SET:
                try {
                    if (!pureCopy) addTraceableComment(that); // after the check on the key
                    JCExpressionStatement st = that.statement;
                    // (almost) Duplicated from visitExec
                    JCExpression arg = convertJML(st.getExpression());
                    if (arg instanceof JCMethodInvocation || arg instanceof JCAssign || arg instanceof JCAssignOp || arg instanceof JCUnary) {
                        result = addStat( M.at(that.pos()).Exec(arg).setType(that.type) );
                    }
                } catch (JmlNotImplementedException e) {
                    notImplemented(that.token.internedName() + " statement containing ",e);
                    result = null;
                }
                break;

            default:
                String msg = "Unknown token in JmlAssertionAdder.visitJmlStatement: " + that.token.internedName();
                error(that.pos(), msg);
        }
    }

    // jmlrewriter? FIXME; also explain what this is
    @Override
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        if (translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitJmlStatementDecls while translating JML: " + that.getClass());
            return;
        }
        for (JCStatement stat: that.list) {
            stat.accept(this);
        }
        // FIXME - result = ?
    }

    // OK
    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        try {
          switch (that.token) {
            case ASSERT:
                addTraceableComment(that);
                JCExpression e = convertJML(that.expression);
                addAssumeCheck(that,currentStatements,"before explicit assert statement");
                result = addAssert(that.pos(),Label.EXPLICIT_ASSERT,e,null,null,that.optionalExpression); // FIXME - convert optionalExpression
                break;
            case ASSUME:
                addTraceableComment(that);
                JCExpression ee = convertJML(that.expression);
                result = addAssume(that.pos(),Label.EXPLICIT_ASSUME,ee,null,null,that.optionalExpression);
                addAssumeCheck(that,currentStatements,"after explicit assume statement");
                break;
            case COMMENT:
                JCExpression expr = fullTranslation ? convertJML(that.expression) : that.expression;
                {
                    JmlStatementExpr st = M.at(that.pos()).JmlExpressionStatement(that.token,that.label,expr);
                    st.setType(that.type);
                    st.associatedSource = that.associatedSource;
                    st.associatedPos = that.associatedPos;
                    st.optionalExpression = convertExpr(that.optionalExpression);
                    st.source = that.source;
                    result = addStat(st);
                }
                break;
            case UNREACHABLE:
                if (pureCopy) {
                    JmlStatementExpr st = M.at(that.pos()).JmlExpressionStatement(that.token,that.label,null);
                    st.setType(that.type);
                    st.associatedSource = that.associatedSource;
                    st.associatedPos = that.associatedPos;
                    st.optionalExpression = convertExpr(that.optionalExpression);
                    st.source = that.source;
                    result = addStat(st);
                } else {
                    addTraceableComment(that);
                    result = addAssert(that.pos(),Label.UNREACHABLE,treeutils.falseLit);
                }
                break;
            case HENCE_BY:
                // FIXME - implement HENCE_BY
                notImplemented(that.pos(),"hence_by statement");
                result = null;
                break;
            default:
                error(that.pos(),"Unknown token type in JmlAssertionAdder.visitJmlStatementExpr: " + that.token.internedName());
                break;
          }
        } catch (JmlNotImplementedException e) {
            notImplemented(that.token.internedName() + " statement containing ",e);
        }
    }

    // OK
    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) {
        if (translatingJML) {
            error(that.pos(),"Unexpected call of JmlAssertionAdder.visitJmlStatementHavoc while translating JML: " + that.getClass());
            return;
        }
        try {
            result = addStat( M.at(that.pos()).JmlHavocStatement(convertJML(that.storerefs)).setType(that.type));
        } catch (JmlNotImplementedException e) {
            notImplemented("havoc statement containing ",e);
        }
    }

    // OK
    @Override
    public void visitJmlStatementLoop(JmlStatementLoop that) {
        JmlStatementLoop st = M.at(that.pos()).JmlStatementLoop(that.token, convertExpr(that.expression));
        st.setType(that.type);
        st.sym = that.sym;
        result = st;
    }

    // OK
    @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        result = M.at(that.pos()).JmlStatementSpec(convert(that.statementSpecs)).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        result = eresult = M.at(that.pos()).JmlStoreRefArrayRange(
                convertExpr(that.expression),
                convertExpr(that.lo),
                convertExpr(that.hi)).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        eresult = that;
        if (fullTranslation) eresult = M.at(that.pos()).JmlStoreRefKeyword(that.token);
        result = eresult;
    }

    // OK
    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        if (pureCopy) {
            result = eresult = M.at(that.pos()).JmlStoreRefListExpression(that.token,convert(that.list)).setType(that.type);
            return;
        }
        switch (that.token){
            case BSNOTMODIFIED:
            {
                JCExpression and = null;
                for (JCExpression arg: that.list) {
                    // FIXME - use past instead of old?
                    // FIXME - what prestate should we refer to - e.g. refining statements and loops will have a different one
                    JCIdent earlierState = preLabel;
                    JCBinary bin;
                    if (arg instanceof JCIdent) {
                        JCExpression copy = convertCopy(arg);
                        JCExpression old = treeutils.makeOld(arg.pos, copy, earlierState);
                        bin = treeutils.makeEquality(arg.pos, arg, old);
                    } else if (arg instanceof JCFieldAccess && ((JCFieldAccess)arg).name != null) {
                        JCExpression copy = convertCopy(arg);
                        JCExpression old = treeutils.makeOld(arg.pos, copy, earlierState);
                        bin = treeutils.makeEquality(arg.pos, arg, old);
                    } else if (arg instanceof JmlStoreRefArrayRange) { // Apparently even single indexes are parsed into ranges
                        JmlStoreRefArrayRange ar = (JmlStoreRefArrayRange)arg;
                        if (ar.lo == ar.hi) {
                            JCExpression expr = M.at(arg.pos).Indexed(ar.expression,ar.lo);
                            expr.type = arg.type;
                            JCExpression copy = convertCopy(expr);
                            JCExpression old = treeutils.makeOld(arg.pos, copy, earlierState);
                            bin = treeutils.makeEquality(arg.pos, expr, old);
                        } else {
                            throw new JmlNotImplementedException(that.pos(),that.token.internedName());
                        }
                    } else {
                        // could be a.*, a[*], a[i..j]
                        throw new JmlNotImplementedException(that.pos(),that.token.internedName());
                    }
                    and = and == null ? bin : treeutils.makeAnd(that.pos, and, bin);
                }
                result = eresult = convertExpr(and);
                break;
            }

            default:
                result = eresult = M.at(that.pos()).JmlStoreRefListExpression(that.token,convert(that.list)).setType(that.type);
                
        }
    }

    // OK
    @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCIdent id = treeutils.makeIdent(that.identifier.pos,that.identifier.sym);
        JCExpression expr = convertExpr(that.expression);
        JmlTypeClauseConditional cl = M.at(that.pos()).JmlTypeClauseConditional(mods, that.token, id, expr);
        cl.setType(that.type);
        cl.source = that.source;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCExpression expr = convertExpr(that.expression);
        JmlTypeClauseConstraint cl = M.at(that.pos()).JmlTypeClauseConstraint(mods, expr, convert(that.sigs));
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        if (pureCopy) {
            JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
            JmlTypeClauseDecl cl = M.at(that.pos()).JmlTypeClauseDecl(convert(that.decl));
            cl.setType(that.type);
            cl.source = that.source;
            cl.modifiers = mods;
            cl.token = that.token;
            classDefs.add(cl);
            result = cl;
            return;
        }
        boolean saved = translatingJML;
        //translatingJML = true;
        try {
            scan(that.decl);
        } finally {
            translatingJML = saved;
        }
    }

    // OK
    @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCExpression expr = convertExpr(that.expression);
        JmlTypeClauseExpr cl = M.at(that.pos()).JmlTypeClauseExpr(mods, that.token, expr);
        cl.setType(that.type);
        cl.source = that.source;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JmlTypeClauseIn cl = M.at(that.pos()).JmlTypeClauseIn(convert(that.list));
        cl.modifiers = mods;
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        cl.parentVar = that.parentVar; // FIXME - need to convert declaration
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JmlTypeClauseInitializer cl = M.at(that.pos()).JmlTypeClauseInitializer(that.token);
        cl.modifiers = mods;
        cl.specs = that.specs; // FIXME - copy or remap reference
        cl.setType(that.type);
        cl.source = that.source;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCExpression expr = convertExpr(that.expression);
        JmlTypeClauseMaps cl = M.at(that.pos()).JmlTypeClauseMaps(expr,convert(that.list));
        cl.modifiers = mods;
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCIdent id = treeutils.makeIdent(that.identifier.pos,that.identifier.sym);
        JmlTypeClauseMonitorsFor cl = M.at(that.pos()).JmlTypeClauseMonitorsFor(mods, id, convert(that.list));
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        // FIXME - implement for esc
        if (pureCopy) {
            JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
            JCExpression id = convert(that.ident);
            JCExpression expr = convertExpr(that.expression);
            JmlTypeClauseRepresents cl = M.at(that.pos()).JmlTypeClauseRepresents(mods, id, that.suchThat, expr);
            cl.setType(that.type);
            cl.source = that.source;
            cl.token = that.token;
            classDefs.add(cl);
            result = cl;
            return;
        }
        
        if (rac && that.suchThat) {
            notImplemented(that.pos(),"relational represents clauses (\\such_that)");
            return;
        }
        
        JCExpression e = that.ident;
        Symbol sym = null;
        if (e instanceof JCIdent) sym = ((JCIdent)e).sym;
        else if (e instanceof JCFieldAccess) sym = ((JCFieldAccess)e).sym;
        else {
            log.warning(that.pos(),"jml.internal.notsobad",
                    "The lhs of a represents clause is expected to be an identifier or field access (found "+e.getClass()+")");
        }
        JmlSpecs.TypeSpecs typeSpecs = specs.getSpecs(classDecl.sym);
        if (sym != null) {
            // Construct a method that implements the represents clause
            Name name = names.fromString(Strings.modelFieldMethodPrefix + sym.name);
            JmlMethodDecl mdecl = null;
            // Check if we already have a method for this model field. Note
            // that the method itself might not have been processed yet, so it
            // will not necessarily by in the new list (classdefs). Also it 
            // might not yet be filled in by processing a represents clause.
            // Or it might never be filled in if it only has a representation
            // in a derived class.
            for (JmlTypeClauseDecl m: typeSpecs.modelFieldMethods) {
                JmlMethodDecl md = (JmlMethodDecl)m.decl;
                if (! md.name.equals(name)) continue; 
                try {
                    JCReturn st = M.at(that.pos()).Return(that.expression);
                    // We have a match
                    if (md.body.stats.isEmpty()) {
                        // But no body yet
                        md.body.stats = List.<JCStatement>of(st);
                    } else {
                        log.warning(that.pos,"jml.duplicate.represents");
                    }
                } catch (JmlNotImplementedException ee) {
                    // Can't implement this represents clause because
                    // of some non-translatable expression within it
                    notImplemented(that.pos(),"represents clause containing " + ee.toString() + " expression");
                }
                mdecl = md;
                break;
            }
            if (mdecl == null) {
                // We can get here if there is no model field at all, but then
                // there would have been an error on resolving the target of
                // the represents clause.  The usual route to this code is
                // when a subclass has a represents clause for a super class's
                // model field.

                long flags = Flags.PUBLIC | Flags.SYNTHETIC;
                flags |= (that.modifiers.flags & Flags.STATIC);
                JCModifiers mods = M.Modifiers(flags);
                JCMethodDecl msdecl = treeutils.makeMethodDefNoArg(mods,name,that.ident.type,classDecl.sym);
                try {
                    JCReturn st = M.Return(convertJML(that.expression));
                    msdecl.body.stats = List.<JCStatement>of(st);
                } catch (JmlNotImplementedException ee) {
                    // Can't implement this represents clause because
                    // of some non-translatable expression within it
                    notImplemented(that.pos(),"represents clause containing " + ee.getMessage() + " expression");
                }
                classDefs.add(msdecl);
                JmlTypeClauseDecl tcd = M.JmlTypeClauseDecl(msdecl);
                tcd.modifiers = msdecl.mods;
                typeSpecs.modelFieldMethods.append(tcd);
            }
        }
        result = null;
    }


    // FIXME - needs review
    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        
        if (pureCopy) { 
            result = M.at(that.pos()).VarDef(that.sym,convertExpr(that.init));
            return;
        }
        
        JCIdent newident = null;
        if (esc) {
            that.ident = treeutils.makeIdent(that.pos,that.sym);
            // We don't use convertExpr, because that might chang the JCIdent to a JCFieldAccess
            newident = treeutils.makeIdent(that.pos, that.sym);
            exprBiMap.put(that.ident,newident);
        } else if (rac) {
            if (that.type instanceof JmlType) {
                that.vartype = ((JmlPrimitiveTypeTree)that.vartype).repType;
                that.type = jmltypes.repSym((JmlType)that.type).type;
                that.sym.type = that.type;
            }
        }
        
        
        if (!inClassDecl()) {
            addTraceableComment(that,that,that.toString(),null);
        }
       
        if (( that.type.tsym.flags_field & Flags.ENUM)!= 0) { // FIXME - should check the initializer expressions of enums
            JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,that.init);
            stat.ident = newident;

            if (inClassDecl()) classDefs.add(stat);
            else addStat(stat);

            result = stat;
            return;
        }
        
        boolean inClassDecl = inClassDecl(); 
        if (localVariables.contains(that.sym)) {
            JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,null);
            stat.ident = newident;
            if (inClassDecl) classDefs.add(stat);
            else addStat(stat);
            result = stat;
            return;
        }
        // Called during translation of model methods
        if (JmlAttr.instance(context).isGhost(that.mods)) {
            try {
                JCExpression init = null;
                
                // If we are in a method, there is nowhere to push statements
                // so we make a block and later turn it into an initializer block
                if (inClassDecl) { pushBlock();  }
                
                init = convertJML(that.init);
                if (init != null) init = addImplicitConversion(init.pos(),that.type,init);
                
                JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,init);
                stat.ident = newident;
                JCExpression nn = null;
                if (init != null && !init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
                    nn = treeutils.makeNeqObject(init.pos, init, treeutils.nullLit);
                    if (init instanceof JCLiteral) {
                        // FIXME - potential optimizations, but they need testing, particularly the second one
                        if (init.type.tag == TypeTags.BOT) nn = treeutils.falseLit;
                        else if (init.type.tag == TypeTags.CLASS) nn = treeutils.trueLit;
                    } 
                    // FIXME - should have an associated position in assert
                }
                if (nn != null) addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,that.name);
                if (esc && !that.type.isPrimitive()) {
                    addAssume(that.pos(),Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeEquality(that.pos(), 
                        treeutils.makeIdent(that.pos, that.sym), 
                        that.type));
                }

                if (inClassDecl) {
                    JCBlock bl = popBlock(that.mods.flags & Flags.STATIC,that.pos());
                    classDefs.add(stat);
                    classDefs.add(bl);
                } else {
                    addStat(stat);
                }
                result = stat;
            } catch (JmlNotImplementedException e) {
                notImplemented("ghost declaration containing ",e);
            }
        } else if (that.init == null) {
            JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,that.init);
            stat.ident = newident;
            // type, vartype, sym, name, mods, init are filled in
            stat.mods = that.mods;
            stat.sourcefile = that.sourcefile;
            stat.docComment = that.docComment;
            stat.fieldSpecs = that.fieldSpecs;  // TOOD: copy?
            stat.fieldSpecsCombined = that.fieldSpecsCombined;// TODO: copy?
            stat.specsDecl = that.specsDecl; // TODO: copy? translate reference?
            if (!pureCopy) {
                if (currentStatements == null) classDefs.add(stat);
                else addStat(stat);
            }
            if (esc && !that.type.isPrimitive()) {
                addAssume(that.pos(),Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeEquality(that.pos(), 
                    treeutils.makeIdent(that.pos, that.sym), 
                    that.type));
            }

            result = stat;
        } else {
            // FIXME - are these regular Java declarations?  what about model decls?

            // FIXME - need to make a unique symbol; what if the decl is final?
            JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,null);
            stat.ident = newident;
            // type, vartype, sym, name, mods, init are filled in
            stat.mods = that.mods;
            stat.sourcefile = that.sourcefile;
            stat.docComment = that.docComment;
            stat.fieldSpecs = that.fieldSpecs;
            stat.fieldSpecsCombined = that.fieldSpecsCombined;
            stat.specsDecl = that.specsDecl;

            pushBlock();
            
            if (statementStack.get(0) == null && methodDecl == null) {
                long flags = that.mods.flags & Flags.STATIC;
                // We are in an initializer block
                // We need a method symbol to be the owner of declarations 
                // (otherwise they will have the class as owner and be thought to
                // be fields)
                MethodSymbol msym = new MethodSymbol(
                        flags, 
                        classDecl.name, 
                        null, 
                        classDecl.sym);
                methodDecl = //M.MethodDef(msym, null,null);
                        new JmlMethodDecl(
                                M.Modifiers(flags, M.Annotations(List.<com.sun.tools.javac.code.Attribute.Compound>nil())),
                                classDecl.name,
                                null,
                                null,
                                null,
                                null,
                                null, //body,
                                null,
                                msym);

            }
            
            JCExpression init = convertExpr(that.init);
            if (init != null) init = addImplicitConversion(init.pos(),that.type,init);
            
            JCExpression nn = null;
            if (init != null && !init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
                nn = treeutils.makeNeqObject(init.pos, init, treeutils.nullLit);
                if (init instanceof JCLiteral) {
                    // FIXME - potential optimizations, but they need testing, particularly the second one
                    if (init.type.tag == TypeTags.BOT) nn = treeutils.falseLit;
                    else if (init.type.tag == TypeTags.CLASS) nn = treeutils.trueLit;
                } 
                // FIXME - should have an associated position
            }
            

            if (statementStack.get(0) == null) {
                // Class definition
                if (currentStatements.isEmpty() && nn == null) {
                    // Just a simple initialization since there is no nonnull check
                    // and the init expression did not create any new statements
                    popBlock(0,null); // Nothing present - just ignore the empty block
                    stat.init = init;
                    this.classDefs.add(stat);
                    if (esc && !that.type.isPrimitive()) {
                        addAssume(that.pos(),Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeEquality(that.pos(), 
                            treeutils.makeIdent(that.pos, that.sym), 
                            that.type));
                    }
                } else {
                    long flags = that.mods.flags & Flags.STATIC;

                    // Create a initializer block
                    if (nn != null) addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,that.name);
                    addStat(treeutils.makeAssignStat(that.pos, treeutils.makeIdent(that.pos, stat.sym), init));
                    if (esc && !that.type.isPrimitive()) {
                        addAssume(that.pos(),Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeEquality(that.pos(), 
                            treeutils.makeIdent(that.pos, that.sym), 
                            that.type));
                    }
                    JCBlock bl = popBlock(flags,that.pos());
                    this.classDefs.add(stat);
                    this.classDefs.add(bl);
                }
                methodDecl = null;
            } else {
                // Regular method body
                JCBlock bl = popBlock(0,that.pos());
                currentStatements.addAll(bl.stats);
                if (nn != null) addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,that.name);
                stat.init = init;
                addStat(stat);
                if (esc && !that.type.isPrimitive()) {
                    addAssume(that.pos(),Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeEquality(that.pos(), 
                        treeutils.makeIdent(that.pos, that.sym), 
                        that.type));
                }
            }
            result = stat;
        }
        
    }
    
    protected boolean inClassDecl() {
        return currentStatements == null;
    }
    
    // OK
    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        if (pureCopy) {
            JCExpression e = convertExpr(that.cond);
            JmlWhileLoop loop = M.at(that.pos()).WhileLoop(e,null);
            try {
                treeMap.put(that, loop);
                JCStatement bl = convert(that.body);
                loop.body = bl;
                loop.setType(that.type);
                loop.loopSpecs = convertCopy(that.loopSpecs); 
                result = loop;
            } finally {
                treeMap.remove(that);
            }
            return;
        }
        
        /*   loop_invariant INV
         *   loop_variant  VAR
         *   label: while (COND) {
         *     BODY
         *   }
         * becomes
         *   {
         *      assert INV
         *      label: while (true) {
         *         havoc
         *         assume INV
         *         TEMP = VAR
         *         ... statements from COND
         *         if (!COND') {
         *             assert INV;
         *             break;
         *         }
         *         assert 0 <= TEMP
         *         loop_bodyN: {
         *            ... statements from BODY
         *            ... continue --> break loop_bodyN;
         *            ... break --> break;
         *         }
         *         assert INV
         *         TEMP2 = VAR
         *         assert TEMP2 < TEMP
         *      }
         *      // FIXME - if break exits still have to satisfy invariant, put the check here
         *   }
         *         
         */
        
        // FIXME - need label for loop if any and the target mapping
        
        // Outer block to restrict scopes of temporaries
        pushBlock();

        JCVariableDecl indexDecl = loopHelperDeclareIndex(that.pos());;

        java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

        // Create this early so it is available as a target
        JmlWhileLoop loop = M.at(that.pos()).WhileLoop(treeutils.trueLit,null);
        treeMap.put(that, loop);

        // Test that invariants hold before entering loop
        loopHelperInitialInvariant(that.loopSpecs);

        // New loop body
        pushBlock();
        
        // Havoc all items that might be changed in the loop
        if (esc) {
            loopHelperHavoc(that.body.pos(),that.body,that.cond);
        }
        
        loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that);
        
        // Compute the condition, recording any side-effects
        {
            
            addTraceableComment(that.cond,that.cond,"Loop test");
            JCExpression cond = convertExpr(that.cond);

            // The exit block tests the condition; if exiting, it tests the
            // invariant and breaks.
            loopHelperMakeBreak(that.loopSpecs, cond, loop, that.pos());
        }
        
        // Now in the loop, so check that the variants are non-negative
        loopHelperCheckNegative(decreasesIDs, that.pos());
        
        // Then translate the original loop body
        // Have to do some footwork to get the Block object before constructing its contents
        loopHelperMakeBody(that.body);
        
        // increment the index
        loopHelperIncrementIndex(indexDecl);
        
        // After the loop, check the invariants and check that the variants have decreased
        loopHelperAssertInvariants(that.loopSpecs,decreasesIDs);
        
        // Finish up the new loop body
        // Finish up the output block
        loopHelperFinish(loop,that);
    }
    
    public static class PositionChecker extends JmlTreeScanner {
        int lo;
        int hi;
        Log log;
        Map<JCTree,Integer> table;
        
        public void check(Log log, JCTree tree) {
            lo = 0;
            hi = Integer.MAX_VALUE;
            this.log = log;
            table = log.currentSource().getEndPosTable();
            scan(tree);
        }
        
        public void scan(JCTree tree) {// FIXME - we see a bad end position for JC/JmlMethodDecl, JCModifiers, JCPrimitiveTYpeTree
            if (tree == null) return;
            int sp = tree.getStartPosition();
            int pp = tree.getPreferredPosition();
            int ep = tree.getEndPosition(table);
            log.noticeWriter.println(" POSITIONS: " + lo + " " + sp + " " + pp + " " + tree.pos + " " + ep + " " + hi + " " + tree);
            if (!(lo <= sp && sp <= pp && pp == tree.pos && pp <= ep && ep <= hi)
            		&& !(tree instanceof JCModifiers && sp == -1 && ep == -1)) {
                log.noticeWriter.println("BAD POSITIONS: " + lo + " " + sp + " " + pp + " " + tree.pos + " " + ep + " " + hi + " " + tree);
                sp = sp;
            }
            int savedlo = this.lo;
            int savedhi = this.hi;
            this.lo = sp;
            this.hi = ep;
            super.scan(tree);
            this.lo = savedlo;
            this.hi = savedhi;
            
        }
    }
}

