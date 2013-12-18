/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;


import java.io.PrintWriter;
import java.io.StringWriter;
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
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
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
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.Env;
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
import com.sun.tools.javac.util.*;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

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

    static final public String preconditionAssumeCheckDescription = "end of preconditions";
    
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
    
    /** If true, we are making a pure copy (!esc && !rac)*/
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
    
    /** An expression to be used for \result (instead of resultSym), if non-null */
    protected JCExpression resultExpr = null;
    
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
    protected JCExpression currentThisExpr;
    protected Symbol enclosingMethod;
    protected Symbol enclosingClass;
    
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
     * the code under current consideration. 0th element is the currently innermost scope
     */
    protected java.util.List<JCVariableDecl> indexStack = new LinkedList<JCVariableDecl>();
    
    /** true when translating JML constructs, false when translating Java constructs.
     * This is set and manipulated by the visitor methods 
     */
    protected boolean translatingJML = false;
    protected boolean splitExpressions = true;
    protected boolean convertingAssignable = false;
    
    /** Contains an expression that is used as a guard in determining whether expressions
     * are well-defined. For example, suppose we are translating the expression 
     * a != null && a[i] == 0. Then condition is 'true' when a!=null is translated.
     * But when a[i] is translated, 'condition' will be a != null. The well-definedness
     * check for a[i] will then be (a != null) ==> (a != null && i >= 0 && i < a.length).
     * So the full expression is well-defined only if that implication can be proved given 
     * other pre-conditions.
     */
    protected JCExpression condition;
    
    // FIXME - dcoument
    protected java.util.List<JmlStatementExpr> wellDefinedConditions = new java.util.LinkedList<JmlStatementExpr>();
    
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
    protected JCIdent preLabel;
    
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
    
    public int heapCount = 0;
    
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
        this.showRacSource = JmlOption.isOption(context,JmlOption.RAC_SHOW_SOURCE);
        this.racCheckAssumeStatements = JmlOption.isOption(context,JmlOption.RAC_CHECK_ASSUMPTIONS);
        this.javaChecks = esc || (rac && JmlOption.isOption(context,JmlOption.RAC_JAVA_CHECKS));
        this.count = 0;
        this.assertCount = 0;
        this.precount = 0;
        this.preparams.clear();
        this.preconditions.clear();
        //this.labels.clear();
        this.pureCopy = !(esc||rac);
        this.treeMap.clear();
        this.oldenv = null;
        this.heapCount = 0;
        racMessages.clear();
        escMessages.clear();
        assumptionChecks.clear();
        assumptionCheckStats.clear();
    }
    
    public void initialize2(long flags) {


        MethodSymbol msym;
        if (methodDecl != null) {
            msym = methodDecl.sym;
        } else {
            // We are in an initializer block
            // We need a method symbol to be the owner of declarations 
            // (otherwise they will have the class as owner and be thought to
            // be fields)
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
        if (!pureCopy) {
            JCVariableDecl d = treeutils.makeVarDef(syms.exceptionType,exceptionName,msym,
                    treeutils.makeNullLiteral(methodDecl.pos));
            exceptionSym = d.sym;
            exceptionSymbols.put(methodDecl,exceptionSym);
            currentStatements.add(d);
        }

        if (!pureCopy) {
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
    
    Name defaultOldLabel = null;

    /** Internal method to do the method body conversion */
    protected JCBlock convertMethodBodyNoInit(JmlMethodDecl pmethodDecl, JmlClassDecl pclassDecl) {
        int prevAssumeCheckCount = assumeCheckCount;
        JmlMethodDecl prev = this.methodDecl;
        JmlClassDecl prevClass = this.classDecl;
        JCIdent savedThisId = this.currentThisId;
        JCExpression savedThisExpr = this.currentThisExpr;
        Symbol savedExceptionSym = this.exceptionSym;
        Symbol savedEnclosingMethod = this.enclosingMethod;
        Symbol savedEnclosingClass = this.enclosingClass;
        Symbol savedResultSym = this.resultSym;
        Symbol savedTerminationSym = this.terminationSym;
        ListBuffer<JCStatement> prevStats = initialStatements;
        ListBuffer<JCStatement> savedOldStatements = oldStatements;
        JavaFileObject prevSource = log.useSource(pmethodDecl.source());
        Map<Symbol,JCExpression> savedParamActuals = paramActuals;
        java.util.List<Symbol> savedCompletedInvariants = this.completedInvariants;
        Set<Symbol> savedInProcessInvariants = this.inProcessInvariants;
        Name savedOldLabel = defaultOldLabel;
        boolean isModel = isModel(pmethodDecl.sym);
        if (!isModel) addAxioms(-1,null);
        
        try {
            enclosingMethod = pmethodDecl.sym;
            enclosingClass = pmethodDecl.sym.owner;
            if (isModel && (pmethodDecl.mods.flags & Flags.SYNTHETIC) != 0) {
                return convertMethodBodyNoInitModel(pmethodDecl, pclassDecl);
            }
            assumeCheckCount = 0;
            this.methodDecl = pmethodDecl;
            this.classDecl = pclassDecl != null ? pclassDecl : utils.getOwner(methodDecl) ;
            this.initialStatements = new ListBuffer<JCStatement>();
            ListBuffer<JCStatement> outerFinalizeStats = new ListBuffer<JCStatement>();
            boolean isConstructor = methodDecl.sym.isConstructor();
            oldStatements = initialStatements;
            currentStatements = initialStatements;
            JCLabeledStatement mark = M.Labelled(preLabel.name, M.Block(0L, List.<JCStatement>nil()));
            markLocation(preLabel.name,initialStatements,mark);
            
            if (isConstructor) {
                JCVariableDecl d = treeutils.makeVarDef(classDecl.type,resultName,methodDecl.sym,
                        treeutils.makeZeroEquivalentLit(methodDecl.pos,classDecl.type));
                resultSym = d.sym;
                initialStatements.add(d);
            } else if (methodDecl.restype.type.tag != TypeTags.VOID) {
                // The compiler complains that the result variable might not be
                // initialized on every path, even in programs in which it appears
                // obvious that it is. So we initialize it here to a null-like value.
                JCVariableDecl d = treeutils.makeVarDef(methodDecl.restype.type,resultName,methodDecl.sym,
                        treeutils.makeZeroEquivalentLit(methodDecl.pos,methodDecl.restype.type));
                resultSym = d.sym;
                initialStatements.add(d);
            } else {
                resultSym = null;
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
//                    VarSymbol THISSym = treeutils.makeVarSymbol(Flags.STATIC,names.fromString(Strings.thisName),classDecl.sym.type, Position.NOPOS);
//                    THISSym.owner = classDecl.sym;
//                    this.currentThisId = treeutils.makeIdent(classDecl.pos,THISSym);
//                    this.thisIds.put(classDecl.sym, this.currentThisId);
//                    exprBiMap.put(this.currentThisId, this.currentThisId);
                    this.currentThisId = makeThisId(classDecl.pos,classDecl.sym);
                    this.currentThisExpr = this.currentThisId;
                } else { // rac
                    // For RAC we use the actual 'this'   FIXME - not sure about this design - perhaps just need to be cautious about what is translated and what is not
                    this.currentThisId = treeutils.makeIdent(classDecl.pos, classDecl.thisSymbol);
                    this.currentThisExpr = this.currentThisId;
                    this.thisIds.put(classDecl.sym, currentThisId);
                }
            }
            if (esc && (isConstructor || !utils.isJMLStatic(methodDecl.sym))) {
                currentStatements = initialStatements;
                JCExpression e = treeutils.makeNeqObject(methodDecl.pos,currentThisExpr,treeutils.nullLit);
                addAssume(methodDecl,Label.IMPLICIT_ASSUME,e);
                addAssume(classDecl,Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeInEquality(classDecl,currentThisExpr,classDecl.type));
            }
            
            boolean callingSuper = false;
            boolean callingThis = false;
            Iterator<JCStatement> iter = null;
            if (methodDecl.body != null) {
                iter = methodDecl.body.stats.iterator();
                if (iter.hasNext()) {
                    JCStatement st = methodDecl.body.stats.get(0);
                    if (st instanceof JCExpressionStatement && 
                            ((JCExpressionStatement)st).expr instanceof JCMethodInvocation) {
                        JCMethodInvocation mi = (JCMethodInvocation)((JCExpressionStatement)st).expr;
                        if (mi.meth instanceof JCIdent) {
                            JCIdent id = (JCIdent)mi.meth;
                            if (id.name.equals(names._this)) callingThis = true;
                            else if (id.name.equals(names._super)) callingSuper = true;
                        }
                    }
                }
            }


            if (isConstructor && rac) {
                pushBlock();
                if (callingThis || callingSuper) {
                    convertCopy(iter.next());
                }
                JCBlock bl = popBlock(0,methodDecl);
                
                if (!pureCopy) addPrePostConditions(initialStatements,outerFinalizeStats);
                // FIXME - need to fix RAC So it can check preconditions etc.
                pushBlock();
                JCBlock newMainBody = null;
                try {
                    while (iter.hasNext()) {
                        convert(iter.next());
                    }
                } finally {
                    newMainBody = popBlock(0,methodDecl.body == null ? methodDecl: methodDecl.body);
                }
                
                // The outerTryStatement just has a finally clause in which the
                // postconditions and exceptional postconditions are checked.
                JCCatch c;
                {
                    // global catch block
                    JCVariableDecl ex = treeutils.makeVarDef(syms.exceptionType,names.fromString("_JML__ex"),methodDecl.sym,methodDecl.pos);
                    pushBlock();
                    addStat(treeutils.makeAssignStat(methodDecl.pos, treeutils.makeIdent(methodDecl.pos,exceptionSym), treeutils.makeIdent(methodDecl.pos, ex.sym)));
                    addStat(M.at(methodDecl.pos).Throw(treeutils.makeIdent(methodDecl.pos, ex.sym)));
                    JCBlock bbl = popBlock(0,methodDecl);
                    c = M.at(methodDecl.pos).Catch(ex, bbl);
                }
                JCTry outerTryStatement = M.at(methodDecl).Try(
                                newMainBody,
                                esc ? List.<JCCatch>nil() : List.<JCCatch>of(c),
                                M.Block(0, outerFinalizeStats.toList()));
                
                initialStatements.add(outerTryStatement);
                bl.stats = bl.stats.appendList(initialStatements);
                return M.at(methodDecl.body).Block(methodDecl.body.flags,bl.stats);
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
            pushBlock(); // FIXME - should we have a try block?
            if (!pureCopy) {

                outerFinalizeStats.add( comment(methodDecl,"Check Postconditions"));
                addPrePostConditions(initialStatements, outerFinalizeStats);

                pushBlock();
                addAssumeCheck(methodDecl,currentStatements,preconditionAssumeCheckDescription); // FIXME - use a smaller highlight range than the whole method - perhaps the specs?
                JCStatement preconditionAssumeCheck = popBlock(0,methodDecl);
                addStat(initialStatements,preconditionAssumeCheck);
                
            }

            
            addStat( comment(methodDecl,"Method Body"));
            if (methodDecl.body != null) {
                if (callingThis || callingSuper) {
                    convert(iter.next());
                } else if (isConstructor && esc) {
                    // FIXME - need assumptions from default super constructor
                }
                if (isConstructor && esc && !callingThis) {
                    addInstanceInitialization();
                }
                while (iter.hasNext()) {
                    convert(iter.next());
                }
            }
            JCBlock newMainBody = popBlock(0,methodDecl.body == null ? methodDecl: methodDecl.body);
            
            
            // The outerTryStatement just has a finally clause in which the
            // postconditions and exceptional postconditions are checked.
            if (esc && (JmlOption.value(context,JmlOption.FEASIBILITY).equals("all") ||
                    JmlOption.value(context,JmlOption.FEASIBILITY).equals("exit"))) {
                addAssumeCheck(methodDecl,outerFinalizeStats,"at program exit");
            }
            JCCatch c;
            {
                // global catch block
                JCVariableDecl ex = treeutils.makeVarDef(syms.exceptionType,names.fromString("_JML__ex"),methodDecl.sym,methodDecl.pos);
                pushBlock();
                addStat(treeutils.makeAssignStat(methodDecl.pos, treeutils.makeIdent(methodDecl.pos,exceptionSym), treeutils.makeIdent(methodDecl.pos, ex.sym)));
                addStat(M.at(methodDecl.pos).Throw(treeutils.makeIdent(methodDecl.pos, ex.sym)));
                JCBlock bl = popBlock(0,methodDecl);
                c = M.at(methodDecl.pos).Catch(ex, bl);
            }
            JCTry outerTryStatement = M.at(methodDecl).Try(
                            newMainBody,
                            esc ? List.<JCCatch>nil() : List.<JCCatch>of(c),
                            M.Block(0, outerFinalizeStats.toList()));
            
            initialStatements.add(outerTryStatement);
            return M.at(methodDecl).Block(0,initialStatements.toList());
        } catch (JmlNotImplementedException e) {
            throw e;
        } catch (JmlInternalAbort e) {
        	return null;
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
            this.currentThisExpr = savedThisExpr;
            this.resultSym = savedResultSym;
            this.exceptionSym = savedExceptionSym;
            this.terminationSym = savedTerminationSym;
            this.oldStatements = savedOldStatements;
            this.currentStatements = null;
            this.paramActuals = savedParamActuals;
            log.useSource(prevSource);
            this.completedInvariants = savedCompletedInvariants;
            this.inProcessInvariants = savedInProcessInvariants;
            this.enclosingMethod = savedEnclosingMethod;
            this.enclosingClass = savedEnclosingClass;
            this.defaultOldLabel = savedOldLabel;
        }
    }
    
    /** Internal method to do the method body conversion */
    protected JCBlock convertMethodBodyNoInitModel(JmlMethodDecl pmethodDecl, JmlClassDecl pclassDecl) {
            assumeCheckCount = 0;
            this.methodDecl = pmethodDecl;
            this.classDecl = pclassDecl != null ? pclassDecl : utils.getOwner(methodDecl) ;
            this.initialStatements = new ListBuffer<JCStatement>();
            ListBuffer<JCStatement> outerFinalizeStats = new ListBuffer<JCStatement>();
            boolean isConstructor = methodDecl.sym.isConstructor();
            oldStatements = initialStatements;
            currentStatements = initialStatements;
            
            if (methodDecl.restype.type.tag != TypeTags.VOID) {
                // The compiler complains that the result variable might not be
                // initialized on every path, even in programs in which it appears
                // obvious that it is. So we initialize it here to a null-like value.
                JCVariableDecl d = treeutils.makeVarDef(methodDecl.restype.type,resultName,methodDecl.sym,
                        treeutils.makeZeroEquivalentLit(methodDecl.pos,methodDecl.restype.type));
                resultSym = d.sym;
                initialStatements.add(d);
            }
            initialize2(0L);
//            if (allocSym == null) {
//                allocSym = treeutils.makeVarSymbol(0, names.fromString(Strings.allocName), syms.intType, classDecl.pos);
//                allocSym.owner = classDecl.sym;
//                isAllocSym = treeutils.makeVarSymbol(0, names.fromString(Strings.isAllocName), syms.booleanType, classDecl.pos);;
//                isAllocSym.owner = classDecl.sym;
//
//                if (esc) {
//                    // THIS is an id that is a proxy for the this object on which a method is called;
//                    // we need to distinguish it from uses of 'this' in the text
//                    // FIXME - should make this NonNull
////                    VarSymbol THISSym = treeutils.makeVarSymbol(Flags.STATIC,names.fromString(Strings.thisName),classDecl.sym.type, Position.NOPOS);
////                    THISSym.owner = classDecl.sym;
////                    this.currentThisId = treeutils.makeIdent(classDecl.pos,THISSym);
////                    this.thisIds.put(classDecl.sym, this.currentThisId);
////                    exprBiMap.put(this.currentThisId, this.currentThisId);
//                    this.currentThisId = makeThisId(classDecl.pos,classDecl.sym);
//                    this.currentThisExpr = this.currentThisId;
//                } else { // rac
//                    // For RAC we use the actual 'this'   FIXME - not sure about this design - perhaps just need to be cautious about what is translated and what is not
//                    this.currentThisId = treeutils.makeIdent(classDecl.pos, classDecl.thisSymbol);
//                    this.currentThisExpr = this.currentThisId;
//                    this.thisIds.put(classDecl.sym, currentThisId);
//                }
//            }
//            if (esc && (isConstructor || !utils.isJMLStatic(methodDecl.sym))) {
//                currentStatements = initialStatements;
//                JCExpression e = treeutils.makeNeqObject(methodDecl.pos,currentThisExpr,treeutils.nullLit);
//                addAssume(methodDecl,Label.IMPLICIT_ASSUME,e);
//                addAssume(classDecl,Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeInEquality(classDecl,currentThisExpr,classDecl.type));
//            }

            
            pushBlock(); // FIXME - should we have a try block
//            if (!pureCopy) {
//
//                outerFinalizeStats.add( comment(methodDecl,"Check Postconditions"));
//                addPrePostConditions(initialStatements, outerFinalizeStats);
//
//                pushBlock();
//                addAssumeCheck(methodDecl,currentStatements,preconditionAssumeCheckDescription); // FIXME - use a smaller highlight range than the whole method - perhaps the specs?
//                JCStatement preconditionAssumeCheck = popBlock(0,methodDecl);
//                addStat(initialStatements,preconditionAssumeCheck);
//                
//            }

            
            addStat( comment(methodDecl,"Method Body"));
            if (methodDecl.body != null) {
                Iterator<JCStatement> iter = methodDecl.body.stats.iterator();
                while (iter.hasNext()) {
                    scan(iter.next());
                }
            }
            JCBlock newMainBody = popBlock(0,methodDecl.body == null ? methodDecl: methodDecl.body);
            
            
            JCCatch c;
            {
                // global catch block
                JCVariableDecl ex = treeutils.makeVarDef(syms.exceptionType,names.fromString("_JML__ex"),methodDecl.sym,methodDecl.pos);
                pushBlock();
                addStat(treeutils.makeAssignStat(methodDecl.pos, treeutils.makeIdent(methodDecl.pos,exceptionSym), treeutils.makeIdent(methodDecl.pos, ex.sym)));
                addStat(M.at(methodDecl.pos).Throw(treeutils.makeIdent(methodDecl.pos, ex.sym)));
                JCBlock bl = popBlock(0,methodDecl);
                c = M.at(methodDecl.pos).Catch(ex, bl);
            }
            JCTry outerTryStatement = M.at(methodDecl).Try(
                            newMainBody,
                            esc ? List.<JCCatch>nil() : List.<JCCatch>of(c),
                            M.Block(0, outerFinalizeStats.toList()));
            
            initialStatements.add(outerTryStatement);
            return M.at(methodDecl).Block(0,initialStatements.toList());
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

        exprBiMap.put(tree, result);

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
    protected @Nullable JCExpression convertAssignable(@Nullable JCExpression tree, VarSymbol receiver) {
        eresult = null; // Just so it is initialized in case assignment is forgotten
        boolean savedT = translatingJML;
        boolean savedS = splitExpressions;
        JCExpression savedC = condition;
        JCExpression savedThis = currentThisExpr;
        JCIdent savedId = currentThisId;
        try {
            translatingJML = true;
            condition = treeutils.trueLit;
            splitExpressions = false;
            convertingAssignable = true;
            currentThisExpr = currentThisId = receiver == null ? null : treeutils.makeIdent(tree.pos,receiver);
            if (tree != null) {
                super.scan(tree);
                if (rac && eresult != null && eresult.type != null && jmltypes.isJmlType(eresult.type)) eresult.type = jmltypes.repSym((JmlType)eresult.type).type;
                exprBiMap.put(tree,eresult);
            }
        } finally {
            translatingJML = savedT;
            splitExpressions = savedS;
            convertingAssignable = false;
            condition = savedC;
            currentThisExpr = savedThis;
            currentThisId = savedId;
        }
        return eresult;
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
        boolean savedSplit = splitExpressions;
        try {
            pureCopy = true;
            splitExpressions = false;
            return convert(tree);
        } finally {
            pureCopy = savedCopy;
            splitExpressions = savedSplit;
        }
    }

    /** Does a pure copy of the list of trees */
    protected  <T extends JCTree> List<T> convertCopy(List<T> trees) {
        if (trees == null) return null;
        boolean savedCopy = pureCopy;
        boolean savedSplit = splitExpressions;
        try {
            pureCopy = true;
            splitExpressions = false;
            pushBlock();
            ListBuffer<T> newlist = new ListBuffer<T>();
            for (T t: trees) {
                newlist.add(convert(t));
            }
            popBlock();
            return newlist.toList();
        } finally {
            pureCopy = savedCopy;
            splitExpressions = savedSplit;
        }
    }

    /** Does a pure copy of the list of trees */
    protected  <T extends JCTree> java.util.List<T> convertCopy(java.util.List<T> trees) {
        boolean savedCopy = pureCopy;
        boolean savedSplit = splitExpressions;
        try {
            pureCopy = true;
            splitExpressions = false;
            java.util.List<T> newlist = new java.util.LinkedList<T>();
            for (T t: trees) {
                newlist.add(convert(t));
            }
            return newlist;
        } finally {
            pureCopy = savedCopy;
            splitExpressions = savedSplit;
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
        boolean savedSplit = this.splitExpressions;
        JCExpression savedc = this.condition;
        try {
            this.isPostcondition = isPostcondition;
            this.condition = condition;
            this.translatingJML = true;
            this.splitExpressions = rac;
            return convertExpr(that);
        } finally {
            this.isPostcondition = savedp;
            this.translatingJML = savedt;
            this.splitExpressions = savedSplit;
            this.condition = savedc;
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
        try {
            scan(block.stats);
        } finally {
            return popBlock(block.flags,block);
        }
    }

    /** Translates a list of statements, returning a block containing the translations */
    protected JCBlock convertIntoBlock(DiagnosticPosition pos, List<JCStatement> stats) {
        pushBlock();
        try {
            scan(stats);
        } finally {
            return popBlock(0,pos);
        }
    }

    /** Translates one statement, returning a block containing the translation
     * (including any statements it spawns); if the statement is a block, then
     * the block's statements are translated, so there is not an excess nested
     * block. */
    protected JCBlock convertIntoBlock(DiagnosticPosition pos, JCStatement stat) {
        pushBlock();
        try {
            if (stat instanceof JCBlock) scan(((JCBlock)stat).stats); else scan(stat);
        } finally {
            return popBlock(0,pos);
        }
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
    
    protected LinkedList<ListBuffer<JCStatement>> markBlock() {
        LinkedList<ListBuffer<JCStatement>> temp = new LinkedList<ListBuffer<JCStatement>>();
        temp.addAll(statementStack);
        temp.add(0,currentStatements);
        return temp;
    }
    
    protected boolean checkBlock(LinkedList<ListBuffer<JCStatement>> temp) {
        Iterator<ListBuffer<JCStatement>> iter = temp.iterator();
        ListBuffer<JCStatement> t = iter.next();
        if (t != currentStatements) return false;
        Iterator<ListBuffer<JCStatement>> iter2 = statementStack.iterator();
        while (iter2.hasNext() && iter.hasNext()) {
            if (iter2.next() != iter.next()) return false;
        }
        return !iter2.hasNext() && !iter.hasNext();
    }
    /** Pop and ignore the content of currentStatements. */
    protected void popBlock() {
        currentStatements = statementStack.removeFirst();
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
        if (s.contains("\n") || s.contains("\r")) {
            s = s.replace("\r\n"," ").replace('\r', ' ').replace('\n', ' ');
        }
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
        return comment(t,s);
    }
    
    /** Issue an internal error message and throw an exception. */
    protected void error(DiagnosticPosition pos, String msg) {
        log.error(pos, "esc.internal.error", msg);
        throw new JmlInternalError(msg);
    }
    
    /** Issue an internal warning message and throw an exception. */
    protected void warning(DiagnosticPosition pos, String key, Object ...  msg) {
        log.warning(pos, key, msg);
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
    
    protected void notImplemented(String location, JmlNotImplementedException source, JavaFileObject file) {
        String message = location + source.getMessage();
        String key = source.pos.getPreferredPosition() + message;
        JavaFileObject prev = file == null ? null : log.useSource(file);
        if (rac ? racMessages.add(key) : escMessages.add(key)) {
            log.note(source.pos, 
                    rac ? "rac.not.implemented" : "esc.not.implemented", 
                            message);
        }
        if (file != null) log.useSource(prev);
    }
    
    /** Issues a diagnostic message (note) containing the given message.
     */
    protected void notImplemented(DiagnosticPosition pos, String message, JavaFileObject source) {
        String key = pos.getPreferredPosition() + message;
        if (rac ? !racMessages.add(key) : !escMessages.add(key)) return;
        JavaFileObject prev = log.useSource(source);
        log.note(pos, 
                rac ? "rac.not.implemented" : "esc.not.implemented", 
                        message);
        log.useSource(prev);
    }
    
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
            boolean trace,
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
        if (associatedPos != null) {
            if (nowarns.suppress(associatedSource == null ? log.currentSourceFile() : associatedSource,
                    associatedPos.getPreferredPosition(), label.toString())) return null;
        }
        String assertID = Strings.assertPrefix + (++assertCount);
        Name assertname = names.fromString(assertID);
        JavaFileObject dsource = log.currentSourceFile();
        JCVariableDecl assertDecl = treeutils.makeVarDef(syms.booleanType,assertname,methodDecl == null? classDecl.sym : methodDecl.sym,translatedExpr);
        assertDecl.mods.flags |= Flags.FINAL;
        assertDecl.sym.flags_field |= Flags.FINAL;
        if (esc) {

            String extra = Strings.empty;
            for (Object o: args) {
                extra = extra + " " + o.toString();
            }
            
            JmlStatementExpr st = treeutils.makeAssert(codepos,label,treeutils.makeIdent(translatedExpr.pos,assertDecl.sym));
            st.source = dsource;
            st.associatedPos = associatedPos == null ? Position.NOPOS : associatedPos.getPreferredPosition();
            st.associatedSource = associatedSource;
            st.optionalExpression = info;
            st.id = assertID;
            st.description = null; // FIXME - include this, but need to change tests: extra.isEmpty() ? null : extra;
            treeutils.copyEndPosition(st.expression, translatedExpr);
            treeutils.copyEndPosition(st, translatedExpr); // Note that the position of the expression may be that of the associatedPos, not of the original assert, if there even is one

            if (trace) {
                JCExpression newexpr = convertCopy(translatedExpr);
                assertDecl.init = newexpr;
                addTraceableComment(st,translatedExpr,label + " assertion: " + translatedExpr.toString());
            }

            currentStatements.add(assertDecl);
            currentStatements.add(st);
            return st;
        } 
        if (rac) {
            JCExpression racarg = null;
            if (args != null && args.length > 0 && args[0] instanceof JCExpression) { racarg = (JCExpression)args[0]; args = new Object[0]; }
            JCDiagnostic diag = JCDiagnostic.Factory.instance(context).warning(log.currentSource(), codepos, "rac." + label, args);
            String msg = (showRacSource? diag.toString() : diag.noSource()).replace("warning: ", "");
            JCExpression emsg;
            if (racarg != null) {
                int k = msg.indexOf(JmlTree.eol);
                if (k < 0) k = msg.indexOf('\n');
                if (k >= 0) {
                    String m1 = msg.substring(0,k);
                    String m2 = msg.substring(k);
                    emsg = treeutils.makeStringLiteral(translatedExpr.pos,m1 + ": ");
                    emsg = treeutils.makeUtilsMethodCall(racarg.pos, "concat", emsg, racarg);
                    emsg = treeutils.makeUtilsMethodCall(racarg.pos, "concat", emsg, treeutils.makeStringLiteral(translatedExpr.pos,m2));
                } else {
                    emsg = treeutils.makeStringLiteral(translatedExpr.pos,msg + ": ");
                    emsg = treeutils.makeUtilsMethodCall(racarg.pos, "concat", emsg, racarg);
                }
            } else {
                emsg = treeutils.makeStringLiteral(translatedExpr.pos,msg);
            }
            if (associatedPos != null) {
                diag = JCDiagnostic.Factory.instance(context).warning(
                        new DiagnosticSource(associatedSource != null ? associatedSource : log.currentSourceFile(),null), 
                        associatedPos, 
                        Utils.testingMode || !showRacSource ? "jml.associated.decl" : "jml.associated.decl.cf",
                                utils.locationString(codepos.getPreferredPosition()));
                String msg2 = JmlTree.eol + (showRacSource? diag.toString() : diag.noSource()).replace("warning: ", "");
                emsg = treeutils.makeUtilsMethodCall(emsg.pos, "concat", emsg, treeutils.makeStringLiteral(translatedExpr.pos,msg2));
            }
            JCStatement st;
            if (JmlOption.isOption(context, JmlOption.RAC_COMPILE_TO_JAVA_ASSERT)) {
                st = M.at(codepos).Assert(translatedExpr, emsg);
            } else {
                if (info != null) {
                    emsg = info;
                }
                st = assertFailure(emsg,codepos,label);
                if (!isFalse) st = M.at(codepos).If(
                        treeutils.makeNot(codepos == null ? Position.NOPOS : codepos.getPreferredPosition(), treeutils.makeIdent(translatedExpr.pos,assertDecl.sym)), 
                        st, null);
            }
            addStat(comment(translatedExpr,label + " assertion: " + translatedExpr.toString()));
            currentStatements.add(assertDecl);
            currentStatements.add(st);
            return st;
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
        return addAssert(true,codepos,label,expr,null,null,null,args);
    }
    
    /** Creates a statement at which we can check feasibility */
    protected void addAssumeCheck(JCTree item, ListBuffer<JCStatement> list, String description) {
        addAssumeCheck(item,list,description,treeutils.trueLit);
    }
    
    /** Creates a statement at which we can check feasibility */
    protected void addAssumeCheck(JCTree item, ListBuffer<JCStatement> list, String description, JCExpression predicate) {
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
        if (!treeutils.isTrueLit(predicate)) bin = treeutils.makeImplies(item.pos, predicate, bin);
        ListBuffer<JCStatement> prev = currentStatements;
        currentStatements = list;
        JmlStatementExpr a = (JmlStatementExpr)addAssert(item, Label.ASSUME_CHECK, bin);
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
        return addAssert(true,codepos,label,expr,associatedPos,associatedSource,null,args);
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

    protected JCStatement assertFailure(JCExpression sp, DiagnosticPosition pos, Label label, JCExpression arg) {
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
        return addAssume(pos,label,ex,null,null,null,"");
    }
    
    /** Creates an assumption with an associated declaration (perhaps in a different file), 
     * adding it to 'currentStatements' (does nothing if esc and rac are false)*/
    protected JmlStatementExpr addAssume(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression ex, 
            @Nullable DiagnosticPosition associatedPos, 
            @Nullable JavaFileObject associatedSource,
            Object ... args) {
        return addAssume(pos,label,ex,associatedPos,associatedSource,null,args);
    }
    
    /** Creates an assumption with an associated declaration (perhaps in a 
     * different file), adding it to 'currentStatements' */
    protected JmlStatementExpr addAssume(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression translatedExpr, 
            @Nullable DiagnosticPosition associatedPosition, 
            @Nullable JavaFileObject associatedSource, 
            @Nullable JCExpression info,
            Object ... args) {
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
            addAssert(true,pos,label,translatedExpr,associatedPosition,associatedSource,info,args);
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

    protected JCVariableDecl newTempDecl(DiagnosticPosition pos, Type t) {
        Name n = M.Name(Strings.tmpVarString + (++count));
        JCVariableDecl d = treeutils.makeVarDef(t, n, esc ? null : methodDecl.sym , esc ? Position.NOPOS : pos.getPreferredPosition()); // FIXME - see note below
        return d;
    }
    
    /** Creates a declaration for a unique temporary name with the given type and position,
     * with no initialization, adds it to currentStatements and returns an Ident
     * for the new symbol. */
    protected JCIdent newTemp(DiagnosticPosition pos, Type t) {
        JCVariableDecl d = newTempDecl(pos,t); // FIXME - see note below
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
        JmlVariableDecl d = (JmlVariableDecl)treeutils.makeVarDef(
                expr.type.tag == TypeTags.BOT ? syms.objectType : expr.type, 
                n, 
                esc ? null : methodDecl != null ? methodDecl.sym : classDecl.sym, 
                expr); 
//        d.sym.flags_field |= Flags.FINAL;
//        d.mods.flags |= Flags.FINAL;
        d.pos = pos;
        d.sym.pos = Position.NOPOS; // We set the position to NOPOS so that the temporary name is not further encoded
        d.ident = treeutils.makeIdent(pos, d.sym);
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
    
    /** Returns true if the given symbol has a Pure annotation */
    public boolean isPure(Symbol symbol) {
        return symbol.attribute(attr.tokenToAnnotationSymbol.get(JmlToken.PURE))!=null;

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
        // FIXME - this report needs a position of clause and name of method
        boolean quiet = utils.jmlverbose == 0; 
        JCCatch catcher1;
        vd = treeutils.makeVarDef(utils.createClassSymbol("java.lang.NoSuchMethodError").type, names.fromString("noSuchMethodError"), methodDecl.sym, p);
        if (quiet) {
            catcher1 = M.at(pos).Catch(vd,  M.Block(0L, List.<JCStatement>nil()));
        } else {
            JCExpression id = treeutils.makeIdent(pos.getPreferredPosition(),vd.sym);
            JCMethodInvocation m = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(),"reportNoSuchMethod",id);
            catcher1 = M.at(pos).Catch(vd,  M.Block(0L, List.<JCStatement>of(M.at(pos.getPreferredPosition()).Exec(m))));
        }
        return M.at(pos).Try(block,List.<JCCatch>of(catcher,catcher1),null);
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
    
//    protected void addInvariantsForAllFormals(DiagnosticPosition pos, MethodSymbol methodSym, TypeSymbol basecsym, JCIdent receiver, ListBuffer<JCStatement> stats, 
//            boolean includeAxioms, boolean isPost, boolean assume, Label invariantLabel) {
//        
//    }
    
//    protected boolean isFinal(Symbol sym) {
//        return (sym.flags() & Flags.FINAL) != 0;
//    }
    

    /** Adds invariants, constraints and initially clauses from a given class and its parents.
     * This is used for pre and post conditions, in which case the invariants from a 
     * meethod's own class (and its parents) are used; it is also used for other 
     * relevant classes, such as the classes of method parameters. The value of
     * 'methodDecl' (and 'classDecl') is the method for which a logical encoding
     * is being constructed, but is not necessarily the callee class which is causing
     * the invariants to be loaded.
     * 
     * @param pos       the code position which occasioned needing the invariants
     * @param isConstructor whether the callee (or the method itself if there is no callee) is a contructor
     * @param isSuper   true if the callee method is a super() call 
     * @param basecsym  the base TypeSymbol from which to take invariants (this may
     *                  or may not be the class containing the methodDecl)
     * @param receiver  the THIS object to use when translating the invariants -
     *                  this is either the receiver for the original method call
     *                  or is the parameter or return value for which invariants
     *                  are being loaded. This parameter is null iff the base method
     *                  is static and not a constructor; if it is a constructor the 
     *                  value is the object being produced by the constructor.
     * @param stats     the statement list into which to add the invariants
     * @param isHelper  whether the callee or base method is a helper method (whichever one the invariants are for)
     * @param prepost   true if we are inserting invariants as pre or post conditions (rather than on behalf of a called procedure)
     * @param isPost    whether we are adding clauses after (post) or before the method
     * @param assume    whether clauses are assumed or asserted
     * @param invariantLabel the cause of needing the invariant
     */
    protected void addInvariants(DiagnosticPosition pos, TypeSymbol basecsym, JCExpression receiver, ListBuffer<JCStatement> stats, boolean prepost, boolean isConstructor, boolean isSuper,
            boolean isHelper, boolean isPost, boolean assume, Label invariantLabel, Object ... invariantDescription) {
        if (basecsym.type.isPrimitive()) return;
        if (!translatingJML) clearInvariants();
        if (startInvariants(basecsym,pos)) return;
//        System.out.println("STARTING " + basecsym);
        java.util.List<ClassSymbol> parents = utils.parents(basecsym);
//        boolean isConstructedObject = isConstructor && receiver.sym == currentThisId.sym;
        boolean self = basecsym == methodDecl.sym.owner; // true if we are inserting invariants for the base method, either as pre and post conditions or prior to calling a callee
        boolean contextIsStatic = receiver == null; // && !methodDecl.sym.isConstructor(); //|| (self && utils.isJMLStatic(methodDecl.sym));
        
        // Iterate through parent classes and interfaces, assuming relevant axioms and invariants
        // These are checked prior to calling the callee
        ListBuffer<JCStatement> prevStats = currentStatements;
        JCIdent prevThisId = currentThisId;
        JCExpression prevThisExpr = currentThisExpr;
        try {
            ListBuffer<JCStatement> staticStats = stats;
            
            currentThisId = (JCIdent)receiver;
            currentThisExpr = receiver;
            
            for (ClassSymbol csym: parents) {
                pushBlock();
                ListBuffer<JCStatement> instanceStats = currentStatements;
                try {

                    JmlSpecs.TypeSpecs tspecs = specs.get(csym);
                    if (tspecs == null) continue; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

                    if (prepost && !isPost && !methodDecl.sym.isConstructor()) {
                        // Adding in invariant about final fields
                        instanceStats.add(comment(pos,(assume? "Assume" : "Assert") + " final field invariants for " + csym));
                        JCExpression conj = null;
                        //JCExpression staticconj = null;
                        for (Symbol s : csym.getEnclosedElements()) {
                            if (s instanceof VarSymbol) {
                                VarSymbol v = (VarSymbol)s;
                                Object o = v.getConstantValue();
                                if (o != null) {
                                    JCIdent id = treeutils.makeIdent(v.pos,v);
                                    JCLiteral val = treeutils.makeLit(v.pos,v.type,o);
                                    JCExpression e = treeutils.makeEquality(v.pos, id, val);
                                    if (utils.isJMLStatic(s)) {
                                        //staticconj = staticconj == null ? e : treeutils.makeAnd(v.pos, staticconj, e);
                                    } else {
                                        conj = conj == null ? e : treeutils.makeAnd(v.pos, conj, e);
                                    }
                                }
                            }
                        }
                        if (conj != null) {
                            currentStatements = instanceStats;
                            conj = convertJML(conj);
                            if (assume) addAssume(pos,invariantLabel,conj);
                            else  addAssert(pos,invariantLabel,conj);
                        }
//                        if (staticconj != null) {
//                            currentStatements = staticStats;
//                            staticconj = convertJML(staticconj);
//                            if (assume) addAssume(pos,invariantLabel,staticconj);
//                            else  addAssert(pos,invariantLabel,staticconj);
//                        }
                    }
                    
                    staticStats.add(comment(pos,(assume? "Assume" : "Assert") + " invariants for " + csym));
                    for (JmlTypeClause clause : tspecs.clauses) {
                        if (!utils.visible(classDecl.sym, csym, clause.modifiers.flags/*, methodDecl.mods.flags*/)) continue;
                        JmlTypeClauseExpr t;
                        DiagnosticPosition cpos = clause;
                        boolean clauseIsStatic = utils.isJMLStatic(clause.modifiers,csym);
                        currentStatements = clauseIsStatic? staticStats : instanceStats;
                        try {
                            // FIXME - guard against the receiver being null for non-static invariants
                            switch (clause.token) {
                                // invariants on both pre and post for all classes of parameters and return value
                                // Pre and post conditions:
                                //      helper - no invariants for class of method
                                //      non-helper constructor - invariants only on post
                                //      non-helper method - invariants on pre and post
                                // Calling a method - caller invariants
                                //      same as pre and postconditions, except
                                //      when a constructor is calling super(), no invariants of containing class are assumed in post
                                // Calling a method - callee invariants
                                //      callee is helper - no invariants in pre or post for class containing method
                                //      callee is super() - invariants of super class on post
                                //      callee is constructor - invariants on post
                                //      callee is method - invariants on pre and post
                                case INVARIANT:
                                    if (contextIsStatic && !clauseIsStatic) break;
                                    if (isHelper) break;
                                    if (isSuper) break;
                                    boolean doit = false;
                                    if (!isConstructor || isPost) doit = true; // pre and postcondition case
                                    if (isConstructor && clauseIsStatic) doit = true;
                                    if (doit) {
                                        t = (JmlTypeClauseExpr)convertCopy(clause);
                                        addTraceableComment(t.expression,clause.toString());
                                        JCExpression e = convertJML(t.expression,treeutils.trueLit,isPost);
                                        // FIXME - be nice to record where called from, not just the location of the invariant declaration
                                        if (assume) addAssume(pos,invariantLabel,
                                                e,
                                                cpos,clause.source, invariantDescription);
                                        else  addAssert(pos,invariantLabel,
                                                e,
                                                cpos,clause.source, invariantDescription);
//                                        JavaFileObject source = log.useSource(clause.source);
//                                        if (assume) addAssume(cpos,invariantLabel,
//                                                e,
//                                                cpos,clause.source, invariantDescription);
//                                        else  addAssert(cpos,invariantLabel,
//                                                e,
//                                                invariantDescription);
//                                        log.useSource(source);
                                    }
                                    break;
                                default:
                                    // Skip

                            }
                        } catch (NoModelMethod e) {
                            // FIXME - what to do.
                        } catch (JmlNotImplementedException e) {
                            notImplemented(clause.token.internedName() + " clause containing ", e, clause.source());
                        }
                    }
                } finally {
                    currentStatements = instanceStats;
                    JCBlock bl = popBlock(0,pos);
                    if (!onlyComments(bl.stats)) {
                        if (contextIsStatic) {
                            staticStats.add(bl);
                        } else {
                            JCExpression ex = treeutils.makeNeqObject(pos.getPreferredPosition(),receiver,treeutils.nullLit);
                            JCStatement st = M.at(pos).If(ex, bl, null);
                            staticStats.add(st);
                        }
                    }
                }
                
            }
        } finally {
            endInvariants(basecsym);
            if (!translatingJML) clearInvariants();
//            System.out.println("ENDING " + basecsym + " " + inProcessInvariants.contains(basecsym) + " " + completedInvariants.contains(basecsym));
            currentStatements = prevStats;
            currentThisId = prevThisId;
            currentThisExpr = prevThisExpr;
        }

    }
    
    protected void assertInvariants(JCExpression expr, JCExpression currentThis) {
        JCExpression saved = currentThisExpr;
        currentThisExpr = currentThis;
        pushBlock();
        try {
            for (JmlTypeClause t: specs.getSpecs((ClassSymbol)expr.type.tsym).clauses) {
                if (t.token != JmlToken.INVARIANT) continue;
                JavaFileObject prev = log.useSource(t.source);
                try {
                    JCExpression e = convertJML(convertCopy((JmlTypeClauseExpr)t).expression);
                    addAssert(t,Label.INVARIANT,e); // FIXME - CHnage the position to point to end point of method, and associated position to invariant
                } finally {
                    log.useSource(prev);
                }
            }
        } finally {
            JCBlock bl = popBlock(0L,expr);
            if (!bl.stats.isEmpty()) {
                JCExpression nn = treeutils.makeNeqObject(expr.pos, expr, treeutils.nullLit);
                JCStatement st = M.at(expr.pos).If(nn, bl, null);
                addStat(st);
            }
            currentThisExpr = saved;
        }        
    }
    
    protected void addInvariants(boolean assume, JCVariableDecl d, JCExpression currentThis) {
        JCExpression saved = currentThisExpr;
        currentThisExpr = currentThis;
        ClassSymbol csym = (ClassSymbol)d.sym.type.tsym;
        pushBlock();
        try {
            for (JmlTypeClause t: specs.getSpecs(csym).clauses) {
                if (t.token != JmlToken.INVARIANT) continue;
                JavaFileObject prev = log.useSource(t.source);
                JCExpression e = convertJML( convertCopy((JmlTypeClauseExpr)t).expression);
                if (assume) addAssume(t,Label.INVARIANT,e);
                else addAssert(t,Label.INVARIANT,e);
                log.useSource(prev);
            }
        } finally {
            JCBlock bl = popBlock(0L,d);
            if (!bl.stats.isEmpty()) {
                if (utils.isJMLStatic(d.sym)) {
                    addStat(bl);
                } else {
                    JCExpression nn = treeutils.makeNeqObject(d.pos, convertCopy(currentThisExpr), treeutils.nullLit);
                    JCStatement st = M.at(d.pos).If(nn, bl, null);
                    addStat(st);
                }
            }
            currentThisExpr = saved;
        }
    }

    protected void addConstraintInitiallyChecks(DiagnosticPosition pos, TypeSymbol basecsym, JCExpression receiver, ListBuffer<JCStatement> stats, boolean prepost, boolean isConstructor, boolean isSuper,
            boolean isHelper, boolean isPost, boolean assume, Label invariantLabel, Object ... invariantDescription) {
        if (basecsym.type.isPrimitive()) return;
//        if (!translatingJML) clearInvariants();
        java.util.List<ClassSymbol> parents = utils.parents(basecsym);
//        boolean isConstructedObject = isConstructor && receiver.sym == currentThisId.sym;
        boolean self = basecsym == methodDecl.sym.owner; // true if we are inserting invariants for the base method, either as pre and post conditions or prior to calling a callee
        boolean contextIsStatic = receiver == null ; //|| (self && utils.isJMLStatic(methodDecl.sym));
        
        // Iterate through parent classes and interfaces, assuming relevant axioms and invariants
        // These are checked prior to calling the callee
        ListBuffer<JCStatement> prevStats = currentStatements;
        JCIdent prevThisId = currentThisId;
        JCExpression prevThisExpr = currentThisExpr;
        try {
            ListBuffer<JCStatement> staticStats = stats;
            
            currentThisId = (JCIdent)receiver;
            currentThisExpr = receiver;
            
            for (ClassSymbol csym: parents) {
                pushBlock();
                ListBuffer<JCStatement> instanceStats = currentStatements;
                try {

                    JmlSpecs.TypeSpecs tspecs = specs.get(csym);
                    if (tspecs == null) continue; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

                    staticStats.add(comment(pos,(assume? "Assume" : "Assert") + " constraints for " + csym));
                    for (JmlTypeClause clause : tspecs.clauses) {
                        if (!utils.visible(classDecl.sym, csym, clause.modifiers.flags/*, methodDecl.mods.flags*/)) continue;
                        JmlTypeClauseExpr t;
                        DiagnosticPosition cpos = clause;
                        boolean clauseIsStatic = utils.isJMLStatic(clause.modifiers,csym);
                        currentStatements = clauseIsStatic? staticStats : instanceStats;
                        try {
                            // FIXME - guard against the receiver being null for non-static invariants
                            switch (clause.token) {
                                case CONSTRAINT:
                                    if (contextIsStatic && !clauseIsStatic) break;
                                    //if (!prepost) break;
                                    if (!isPost) break;
                                    // FIXME - need to check the list of method signatures
                                    // FIXME - what about static vs. instance for clauses in interfaces
                                    // constraints are used when
                                    //   the constraint is static OR
                                    //   the method is not static and not a constructor
                                    //if ((!isConstructor && !contextIsStatic) || clauseIsStatic) {
                                    if (!isConstructor) {
                                        pushBlock();
                                        try {
                                            JmlTypeClauseConstraint tt = (JmlTypeClauseConstraint)clause;
                                            addTraceableComment(tt.expression,clause.toString());
                                            JCExpression e = convertJML(tt.expression);
                                            if (assume) addAssume(pos,Label.CONSTRAINT,
                                                    e,
                                                    cpos,
                                                    clause.source);
                                            else addAssert(pos,Label.CONSTRAINT,
                                                    e,
                                                    cpos,
                                                    clause.source);
                                        } finally {
                                            addStat( popBlock(0,clause));
                                        }
                                    }
                                    break;
                                case INITIALLY:
                                    if (isPost && isConstructor) {
                                        pushBlock();
                                        try {
                                            t = (JmlTypeClauseExpr)clause;
                                            addTraceableComment(t.expression,clause.toString());
                                            JCExpression e = convertJML(t.expression);
                                            if (assume) addAssume(pos,Label.INITIALLY,
                                                    e,
                                                    cpos,clause.source);
                                            else addAssert(pos,Label.INITIALLY,
                                                    e,
                                                    cpos,clause.source);
                                        } finally {
                                            addStat( popBlock(0,cpos));
                                        }
                                    }
                                    break;
                                default:
                                    // Skip

                            }
                        } catch (NoModelMethod e) {
                            // FIXME - what to do.
                        } catch (JmlNotImplementedException e) {
                            notImplemented(clause.token.internedName() + " clause containing ", e, clause.source());
                        }
                    }
                } finally {
                    currentStatements = instanceStats;
                    JCBlock bl = popBlock(0,pos);
                    if (!onlyComments(bl.stats)) {
                        if (contextIsStatic) {
                            staticStats.add(bl);
                        } else {
                            JCExpression ex = treeutils.makeNeqObject(pos.getPreferredPosition(),receiver,treeutils.nullLit);
                            JCStatement st = M.at(pos).If(ex, bl, null);
                            staticStats.add(st);
                        }
                    }
                }
                
            }
        } finally {
            currentStatements = prevStats;
            currentThisId = prevThisId;
            currentThisExpr = prevThisExpr;
        }

    }

    protected void addAxioms(DiagnosticPosition pos, TypeSymbol basecsym, ListBuffer<JCStatement> stats, JCExpression receiver) {
        if (rac) return;
        java.util.List<ClassSymbol> parents = utils.parents(basecsym);
        
        // Iterate through parent classes and interfaces, assuming relevant axioms
        ListBuffer<JCStatement> prevStats = currentStatements;
        JCIdent prevThisId = currentThisId;
        JCExpression prevThisExpr = currentThisExpr;
        try {
            currentStatements = stats;
            currentThisId = (JCIdent)receiver;
            currentThisExpr = receiver;
            for (ClassSymbol csym: parents) {
                if (!addAxioms(heapCount,csym)) continue;
                JmlSpecs.TypeSpecs tspecs = specs.get(csym);
                if (tspecs == null) continue; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

                for (JmlTypeClause clause : tspecs.clauses) {
                    DiagnosticPosition cpos = clause;
                    try {
                        // FIXME - guard against the receiver being null for non-static invariants
                        switch (clause.token) {
                            case AXIOM:
                                // Axioms are included only when assuming the preconditions
                                // for a method body - both the main procedure and
                                // any axioms for the classes of the parameters and return values
                                if (rac) {
                                    notImplemented(clause, "axiom clause", clause.source());
                                } else if (esc) {
                                    addStat(comment(clause));
                                    JmlTypeClauseExpr t = (JmlTypeClauseExpr)clause;
                                    JCExpression e = convertJML(t.expression);
                                    addAssume(pos,Label.AXIOM,
                                            e,
                                            cpos,clause.source);
                                }
                                break;
                            default:
                                // Skip

                        }
                    } catch (NoModelMethod e) {
                        // FIXME - what to do.
                    } catch (JmlNotImplementedException e) {
                        notImplemented(clause.token.internedName() + " clause containing ", e, clause.source());
                    }
                }
            }
        } finally {
            currentStatements = prevStats;
            currentThisId = prevThisId;
            currentThisExpr = prevThisExpr;
        }

    }
    
    protected void addInvariantsForVar(JCExpression thisExpr) {
        assertInvariants(thisExpr,thisExpr);
    }
    
    protected boolean addNullnessAllocationTypeCondition(JCVariableDecl d, boolean instanceBeingConstructed) {
        boolean nnull = true;
        if (!d.sym.type.isPrimitive()) {
            JCExpression id = treeutils.makeIdent(d.pos, d.sym);
            id = convertJML(id);
            JCExpression e2 = treeutils.makeSelect(d.pos, id, isAllocSym);
            JCExpression e3 = treeutils.makeDynamicTypeEquality(d,  // FIXME - should be inequality in general
                    id, 
                    d.type);
            Symbol own = d.sym.owner;
            if (own instanceof MethodSymbol) own = own.owner;
            boolean nn = specs.isNonNull(d.sym, (Symbol.ClassSymbol)own) &&
                    !instanceBeingConstructed;
            nnull = nn;
            if (nn) {
                // assume id != null
                addAssume(d,Label.NULL_CHECK,treeutils.makeNeqObject(d.pos, id, treeutils.makeNullLiteral(d.pos)));
                // assume id.isAlloc
                addAssume(d,Label.IMPLICIT_ASSUME,e2);
                // assume type information
                addAssume(d,Label.IMPLICIT_ASSUME,e3);                   
            } else {
                JCExpression e1 = treeutils.makeEqObject(d.pos,id, treeutils.makeNullLiteral(d.pos));
                // assume id == null || id.isAlloc
                addAssume(d,Label.IMPLICIT_ASSUME,treeutils.makeOr(d.pos, e1, e2));
                // assume id == null || type information
                addAssume(d,Label.IMPLICIT_ASSUME,treeutils.makeOr(d.pos, e1, e3));
            }
        }
        return nnull;
    }
    
    
    /** Add all axioms from listed classes and their parents */
    public void addForClasses(java.util.Collection<ClassSymbol> classes, IClassOp op) {
        Set<ClassSymbol> done = new HashSet<ClassSymbol>();
        for (ClassSymbol csym: classes) {
            for (ClassSymbol cs: utils.parents(csym)) {
                if (done.add(cs)) op.classOp(cs);
            }
        }
        done.clear();
    }
    
    /** Add all axioms from this specific class */
    protected void addClassAxioms(ClassSymbol csym) {
        if (!addAxioms(heapCount,csym)) return;
        JmlSpecs.TypeSpecs tspecs = specs.get(csym);
        if (tspecs == null) return; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

        for (JmlTypeClause clause : tspecs.clauses) {
            DiagnosticPosition cpos = clause;
            try {
                // Note: axioms have no modifiers but nonetheless must always be effectively static
                if (clause.token == JmlToken.AXIOM) {
                        addStat(comment(clause));
                        JmlTypeClauseExpr t = (JmlTypeClauseExpr)clause;
                        JCExpression e = convertJML(t.expression);
                        addAssume(cpos,Label.AXIOM,
                                e,
                                cpos,clause.source);
                }
            } catch (NoModelMethod e) {
                // FIXME - what to do.
            } catch (JmlNotImplementedException e) {
                notImplemented(clause.token.internedName() + " clause containing ", e, clause.source());
            }
        }
    }

    /** Add all constant final static fields from this specific class */
    protected void addFinalStaticFields(ClassSymbol csym) {
        Env<AttrContext> enva = Enter.instance(context).getEnv(csym);
        if (enva == null) return;
        JmlClassDecl decl = (JmlClassDecl)enva.tree;
        if (decl == null) return;
        for (JCTree def : decl.defs) {
            if (def instanceof JmlVariableDecl) {
                JmlVariableDecl vd = (JmlVariableDecl)def;
                if (!utils.jmlvisible(vd.sym, methodDecl.sym.owner, csym, vd.mods.flags, methodDecl.mods.flags)) continue;

                if ((vd.sym.flags() & (Flags.FINAL|Flags.STATIC)) == (Flags.FINAL|Flags.STATIC)) {
                    JCExpression e = vd.init;
                    if (e != null) {
                        Object constValue = e.type.constValue();
                        if (constValue == null) continue;
                        JCExpression lit = treeutils.makeLit(e.pos, e.type, constValue);
                        lit = addImplicitConversion(e,vd.type,lit);
//                        addStat(treeutils.makeVariableDecl(vd.sym, lit));
                        vd.init = lit;
                        vd.sym.owner = null; // This null makes the identifier not subject to havoc
                        addStat(vd);
                    }
                }
            }
        }
        JmlSpecs.TypeSpecs tspecs = specs.get(csym);
        if (tspecs == null) return; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

        for (JmlTypeClause clause : tspecs.clauses) {
            try {
                if (!(clause instanceof JmlTypeClauseDecl)) continue;
                JmlTypeClauseDecl tdecl = (JmlTypeClauseDecl)clause;
                if (!(tdecl.decl instanceof JmlVariableDecl)) continue;
                JmlVariableDecl vdecl = (JmlVariableDecl)tdecl.decl;
                if (vdecl.init == null) continue;
                if (!utils.jmlvisible(null, methodDecl.sym.owner, csym, vdecl.mods.flags, methodDecl.mods.flags)) continue;
                if ((vdecl.sym.flags() & (Flags.FINAL | Flags.STATIC)) != (Flags.FINAL|Flags.STATIC)) continue;
                Object constValue = vdecl.init.type.constValue();
                if (constValue == null) continue;
                addStat(vdecl);
            } catch (JmlNotImplementedException e) {
                notImplemented(clause.token.internedName() + " clause containing ", e, clause.source());
            }
        }
    }
    
    protected void assumeStaticInvariants(ClassSymbol csym) {
        if (startInvariants(csym,methodDecl)) return;
        JmlSpecs.TypeSpecs tspecs = specs.get(csym);
        if (tspecs == null) return; // FIXME - why might this happen - see racnew.testElemtype & Cloneable
        for (JmlTypeClause t : tspecs.clauses) {
            if (t.token != JmlToken.INVARIANT) continue; 
            if (!utils.isJMLStatic(t.modifiers,csym)) continue;
            if (!utils.jmlvisible(null, methodDecl.sym.owner, csym, t.modifiers.flags, methodDecl.mods.flags)) continue;
            addAssume(methodDecl,Label.INVARIANT_ENTRANCE,
                    convertJML( convertCopy((JmlTypeClauseExpr)t).expression),
                    t,t.source(),
                    utils.qualifiedMethodSig(methodDecl.sym));
        }
        endInvariants(csym);
    }

    public interface IClassOp {
        public void classOp(ClassSymbol csym);
    }
    
    public final IClassOp axiomAdder = new IClassOp() { public void classOp(ClassSymbol cs) { addClassAxioms(cs); }};
    public final IClassOp finalStaticFieldAdder = new IClassOp() { public void classOp(ClassSymbol cs) { addFinalStaticFields(cs); }};
    public final IClassOp staticInvariantAdder = new IClassOp() { public void classOp(ClassSymbol cs) { assumeStaticInvariants(cs); }};
    

    /** Computes and adds checks for all the pre and postcondition clauses. */
    // FIXME - review this
    protected void addPrePostConditions( 
            ListBuffer<JCStatement> initialStats, 
            ListBuffer<JCStatement> finalizeStats
            ) {
        
        JCMethodDecl methodDecl = this.methodDecl;
        boolean isConstructor = methodDecl.sym.isConstructor();
        ListBuffer<JCStatement> savedCurrentStatements = currentStatements;
        currentStatements = initialStats;
        
        // Add a precondition that the parameter != null on each formal parameter, if needed
        // Not adding these because the nonnull conditions are part of the deNestedSpecs.
        // However it would be nice to use these and leave them out of the  combinedPrecondition
        // because we get more accurate error messages.
        // Added  back - appears to be needed for ESC - FIXME - review all this
        
        // Assume all static invariants and axioms of classes mentioned in the target method
            // Collect all classes that are mentioned in the method
        ClassCollector collector = ClassCollector.collect(this.classDecl,this.methodDecl);
        if (esc) {
            addStat(comment(methodDecl,"Assume axioms"));
            addForClasses(collector.classes, axiomAdder);
            addStat(comment(methodDecl,"Assume static final constant fields"));
            addForClasses(collector.classes, finalStaticFieldAdder);
            //addStat(comment(methodDecl,"Static initialization"));
            //if (isConstructor) addStaticInitialization((ClassSymbol)methodDecl.sym.owner);
        }


//        pushBlock();
//        try {
//            addStat(comment(methodDecl,"Assume static invariants of collected classes"));
//            clearInvariants();
//            addForClasses(collector.classes, staticInvariantAdder);
//            clearInvariants();
//        } finally {
//            JCBlock bl = popBlock(0,methodDecl);
//            if (rac) {
//                addStat( wrapRuntimeException(methodDecl, bl, 
//                        "JML runtime exception while evaluating static invariants",
//                        null));
//
//            } else{
//                addStat(bl);
//            }
//        }
        if (esc) { // FIXME - what about inherited fields? fields of parameters? fields of anything else?
            addStat(comment(methodDecl,"Assume field type, allocation, and nullness"));
            // For Java fields
            for (JCTree dd: classDecl.defs) {
                if (!(dd instanceof JCVariableDecl)) continue;
                JCVariableDecl d = (JCVariableDecl)dd;
                addNullnessAllocationTypeCondition(d, isConstructor && !utils.isJMLStatic(d.sym));
            }
            // For JML fields
            for (JCTree dd: classDecl.typeSpecs.clauses) {
                if (!(dd instanceof JmlTypeClauseDecl)) continue;
                JCTree t = ((JmlTypeClauseDecl)dd).decl;
                if (!(t instanceof JCVariableDecl)) continue;
                JCVariableDecl d = (JCVariableDecl)t;
                if (d.sym == null) continue; // FIXME - model fields, at least, can have null symbols, I think
                if (isConstructor && !utils.isJMLStatic(d.sym)) continue;
                addNullnessAllocationTypeCondition(d,isConstructor && !utils.isJMLStatic(d.sym));
            }
            // For the parameters of the method
            addStat(comment(methodDecl,"Assume parameter type, allocation, and nullness"));
            boolean varargs = (methodDecl.sym.flags() & Flags.VARARGS) != 0;
            boolean nn = true;
            for (JCVariableDecl d: methodDecl.params) {
                nn = addNullnessAllocationTypeCondition(d,false);
            }
            if (varargs && !nn) {
                JCVariableDecl d = methodDecl.params.last();
                JCIdent id = treeutils.makeIdent(d.pos,d.sym);
                JCExpression nnex = treeutils.makeNeqObject(d.pos,id,treeutils.nullLit);
                addAssume(d.pos(),Label.IMPLICIT_ASSUME,nnex);
            }
            
            int pos = methodDecl.pos;
            
            // FIXME - for the isConstructor case, it should be newly allocated
            if (isConstructor) {
            } else if (!utils.isJMLStatic(methodDecl.sym)){
                // Assume that 'this' is allocated
                JCFieldAccess fa = treeutils.makeSelect(pos, convertCopy(currentThisExpr), isAllocSym);
                addAssume(methodDecl,Label.IMPLICIT_ASSUME,fa);

                fa = treeutils.makeSelect(pos, convertCopy(currentThisExpr), allocSym);
                JCExpression comp = treeutils.makeBinary(pos,JCTree.EQ,treeutils.inteqSymbol,fa,treeutils.makeIntLiteral(pos, 0));
                addAssume(methodDecl,Label.IMPLICIT_ASSUME,comp);
            }

        }
        
        /* Declare new variables, initialized to the values of the formal 
         * parameters, so that they can be referred to in postconditions. 
         */
        if (!methodDecl.params.isEmpty()) addStat(comment(methodDecl,"Declare pre-state value of formals"));
        for (JCVariableDecl d: methodDecl.params) {
            JCVariableDecl dd = treeutils.makeVarDef(d.type,M.Name(Strings.formalPrefix+d.name.toString()),  
                    d.sym.owner, M.Ident(d.sym));
            dd.pos = dd.sym.pos = d.sym.pos;
            preparams.put(d.sym,dd);
            if (esc) dd.sym.owner = null; // FIXME - can get these straight from the labelmaps - do we need this?
            addStat(dd);
        }
        
        ListBuffer<JCStatement> preStats = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> ensuresStats = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> exsuresStats = new ListBuffer<JCStatement>();
        
        // Construct a condition, to be used later, that the method has not thrown an exception
        DiagnosticPosition methodPos = methodDecl;
        JCExpression noException = treeutils.makeEqObject(methodPos.getPreferredPosition(),
                treeutils.makeIdent(methodPos.getPreferredPosition(), exceptionSym), treeutils.nullLit);
        
        // FIXME - what if the owning class is a TypeSymbol because it is a TypeVar
        TypeSymbol owner = (TypeSymbol)methodDecl.sym.owner;
        
        JCExpression receiver = utils.isJMLStatic(methodDecl.sym) ? null : currentThisExpr;
        
        // Assuming  invariants
        addInvariants(methodDecl,owner,receiver,preStats,true,methodDecl.sym.isConstructor(),false,isHelper(methodDecl.sym),false,true,Label.INVARIANT_ENTRANCE,
                utils.qualifiedMethodSig(methodDecl.sym) );
        // Assume invariants for the class of each parameter
        for (JCVariableDecl v: methodDecl.params) {
            if (v.type.isPrimitive()) continue;
            JCVariableDecl d = preparams.get(v.sym);
            if (owner.type.tsym == v.type.tsym && methodDecl.sym.isConstructor()) {
                JCIdent id = treeutils.makeIdent(v.pos,d.sym);
                addAssume(v,Label.IMPLICIT_ASSUME,
                        treeutils.makeNeqObject(v.pos, id, currentThisExpr));
            }
            JCIdent id = treeutils.makeIdent(v.pos,d.sym);
            //addAxioms( methodDecl, v.type.tsym, preStats, id);
            addInvariants(v,v.type.tsym,id,preStats,true,false,false,false,false,true,Label.INVARIANT_ENTRANCE,
                    utils.qualifiedMethodSig(methodDecl.sym) + " (parameter " + v.name + ")");
        }

        // Assume invariants for the class of each field of the owning class
        JCExpression savedThis = currentThisExpr;
        for (JCTree dd: classDecl.defs) {
            if (!(dd instanceof JCVariableDecl)) continue;
            JCVariableDecl d = (JCVariableDecl)dd;
            if (d.sym.type.isPrimitive()) continue;
            
            JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
            addInvariants(true,d,fa);
        }
        currentThisExpr = savedThis;
        for (JCTree dd: specs.get(classDecl.sym).clauses) {
            if (!(dd instanceof JmlTypeClauseDecl)) continue;
            JCTree tt = ((JmlTypeClauseDecl)dd).decl;
            if (!(tt instanceof JCVariableDecl)) continue;
            JCVariableDecl d = (JCVariableDecl)tt;
            if (d.sym.type.isPrimitive()) continue;
            
            JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
            addInvariants(true,d,fa);
        }
        currentThisExpr = savedThis;

        // FIXME Don't replicate the invariants in ensures and exsuresStats
        
        // Accumulate the invariants to be checked after the method returns
        clearInvariants();
        addInvariants(methodDecl,owner,receiver,ensuresStats,true,methodDecl.sym.isConstructor(),false,isHelper(methodDecl.sym),true,false,Label.INVARIANT_EXIT,
                utils.qualifiedMethodSig(methodDecl.sym));
        addConstraintInitiallyChecks(methodDecl,owner,receiver,ensuresStats,true,methodDecl.sym.isConstructor(),false,isHelper(methodDecl.sym),true,false,null,
                utils.qualifiedMethodSig(methodDecl.sym));
        for (JCVariableDecl v: methodDecl.params) {
            if (v.type.isPrimitive()) continue;
            JCVariableDecl d = preparams.get(v.sym);
            JCIdent id = treeutils.makeIdent(v.pos,d.sym);
            addInvariants(v,v.type.tsym,id,ensuresStats,true,false,false,false,true,false,Label.INVARIANT_EXIT,
                    utils.qualifiedMethodSig(methodDecl.sym) + " (parameter " + v.name + ")");
        }
        clearInvariants();
        if (resultSym != null && !resultSym.type.isPrimitive() && !methodDecl.sym.isConstructor()) {
            JCIdent resultId = treeutils.makeIdent(methodDecl.pos, resultSym);
            addInvariants(methodDecl,resultSym.type.tsym,resultId,ensuresStats,false,false,false,false,true,false,Label.INVARIANT_EXIT,
                    utils.qualifiedMethodSig(methodDecl.sym) + " (for result type)");
        }
        addInvariants(methodDecl,owner,receiver,exsuresStats,true,methodDecl.sym.isConstructor(),false,isHelper(methodDecl.sym),true,false,Label.INVARIANT_EXIT,
                utils.qualifiedMethodSig(methodDecl.sym));
        addConstraintInitiallyChecks(methodDecl,owner,receiver,exsuresStats,true,methodDecl.sym.isConstructor(),false,isHelper(methodDecl.sym),true,false,null,
                utils.qualifiedMethodSig(methodDecl.sym));
        for (JCVariableDecl v: methodDecl.params) {
            if (v.type.isPrimitive()) continue;
            JCVariableDecl d = preparams.get(v.sym);
            JCIdent id = treeutils.makeIdent(v.pos,d.sym);
            addInvariants(v,v.type.tsym,id,exsuresStats,false,false,false,false,true,false,Label.INVARIANT_EXIT,
                    utils.qualifiedMethodSig(methodDecl.sym) + " (parameter " + v.name + ")");
            addConstraintInitiallyChecks(v,v.type.tsym,id,exsuresStats,false,false,false,false,true,false,null,
                    utils.qualifiedMethodSig(methodDecl.sym) + " (parameter " + v.name + ")");
        }

        // Invariants for fields
        savedThis = currentThisExpr;
        for (JCTree dd: classDecl.defs) {
            if (!(dd instanceof JCVariableDecl)) continue;
            JCVariableDecl d = (JCVariableDecl)dd;
            if (d.sym.type.isPrimitive()) continue;
            
            JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
            addInvariants(false,d,fa);
        }
        currentThisExpr = savedThis;
        for (JCTree dd: specs.get(classDecl.sym).clauses) {
            if (!(dd instanceof JmlTypeClauseDecl)) continue;
            JCTree tt = ((JmlTypeClauseDecl)dd).decl;
            if (!(tt instanceof JCVariableDecl)) continue;
            JCVariableDecl d = (JCVariableDecl)tt;
            if (d.sym.type.isPrimitive()) continue;
            
            JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
            addInvariants(false,d,fa);
        }
        currentThisExpr = savedThis;
        JCExpression combinedPrecondition = null;
        preStats.add( comment(methodDecl,"Assume Preconditions"));
        
        // Iterate over all methods that methodDecl overrides, collecting specs
        boolean sawSomeSpecs = false;
        for (MethodSymbol msym: utils.parents(methodDecl.sym)) {
            if (msym.params == null) continue; // FIXME - we should do something better? or does this mean binary with no specs?
            JmlMethodSpecs denestedSpecs = JmlSpecs.instance(context).getDenestedSpecs(msym);
            ensuresStats.add(comment(methodDecl,"Asserting postconditions for " + utils.qualifiedMethodSig(msym)));
            exsuresStats.add(comment(methodDecl,"Asserting exceptional postconditions for " + utils.qualifiedMethodSig(msym)));
            // Set up the map from parameter symbol of the overridden method to 
            // corresponding parameter of the target method.
            // We need this even if names have not changed, because the parameters 
            // will have been attributed with different symbols.
            if (denestedSpecs.decl != null) {
                Iterator<JCVariableDecl> iter = denestedSpecs.decl.params.iterator();
                paramActuals = new HashMap<Symbol,JCExpression>();
                for (JCVariableDecl dp: methodDecl.params) {
                    JCVariableDecl newdecl = iter.next();
                    paramActuals.put(newdecl.sym,treeutils.makeIdent(dp.pos, dp.sym));
                }
            } else { // FIXME - why should denestedSpecs ever not have a declaration if there are any specs to use
                Iterator<VarSymbol> iter = msym.params.iterator();
                paramActuals = new HashMap<Symbol,JCExpression>();
                for (JCVariableDecl dp: methodDecl.params) {
                    VarSymbol newsym = iter.next();
                    paramActuals.put(newsym,treeutils.makeIdent(dp.pos, dp.sym));
                }
            }


            for (JmlSpecificationCase scase : denestedSpecs.cases) {
                sawSomeSpecs = true;
                if (!utils.visible(classDecl.sym, msym.owner, scase.modifiers.flags/*, methodDecl.mods.flags*/)) continue;
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
                        notImplemented("requires clause containing ",e); // FIXME - needs source
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
                                try {
                                    JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                                    addTraceableComment(ex,clause.toString());
                                    ex = convertJML(ex,preident,true);
                                    ex = treeutils.makeImplies(clause.pos, preident, ex);
                                    // FIXME - if the clause is synthetic, the source file may be null, and for signals clause
                                    addAssert(false,methodDecl,Label.POSTCONDITION,ex,clause,clause.sourcefile,null);
                                } finally {
                                    addStat(popBlock(0,clause));
                                }
                                break;
                            }

                            case SIGNALS: // FIXME - need to check exception type of the exception
                            {
                                currentStatements = exsuresStats;
                                JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionSym);
                                {
                                    JCIdent nid = convertCopy(exceptionId);
                                    exprBiMap.put(nid, exceptionId);
                                    addTraceableComment(clause,nid,"Terminated with exception");
                                }
                                JCVariableDecl vd = ((JmlMethodClauseSignals)clause).vardef;
                                JCExpression ex = ((JmlMethodClauseSignals)clause).expression;
                                addTraceableComment(ex,clause.toString());

                                JCExpression test = vd == null ? null :
                                        treeutils.makeInstanceOf(clause.pos,exceptionId,vd.type);
                                pushBlock();
                                try {
                                    if (vd != null) {
                                        JCTypeCast tc = M.at(clause).TypeCast(vd.type, exceptionId);
                                        vd.init = esc ? exceptionId : tc;
                                        addStat(vd);
                                    }

                                    ex = convertJML(ex,preident,true);                                
                                    ex = treeutils.makeImplies(clause.pos, preident, ex);
                                    addAssert(methodDecl,Label.SIGNALS,ex,clause,clause.sourcefile);
                                } finally {
                                    JCBlock block = popBlock(0,clause);
                                    if (test != null) addStat(M.at(clause.pos).If(test, block, null));
                                    else addStat(block);
                                }
                                break;
                            }

                            case SIGNALS_ONLY:
                            {
                                sawSignalsOnly = true;
                                {
                                    currentStatements = exsuresStats;
                                    pushBlock();
                                    try {
                                        JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionSym);
                                        JCExpression condd = treeutils.falseLit;
                                        for (JCExpression t: ((JmlMethodClauseSignalsOnly)clause).list) {
                                            JCExpression tc = M.at(t).TypeTest(exceptionId, t).setType(syms.booleanType);
                                            condd = treeutils.makeOr(clause.pos, condd, tc);
                                        }
                                        condd = treeutils.makeImplies(clause.pos, preident, condd);
                                        addAssert(methodDecl,Label.SIGNALS_ONLY,condd,clause,clause.sourcefile,
                                                treeutils.makeUtilsMethodCall(clause.pos,"getClassName",exceptionId));
                                    } finally {
                                        addStat(popBlock(0,methodDecl));
                                    }
                                }
                                break;
                            }

                            case DIVERGES:
                            {
                                // FIXME _ implement
                                currentStatements = ensuresStats;
                                pushBlock();
                                try {
                                    JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                                    addTraceableComment(ex,clause.toString());
                                    ex = convertJML(ex,preident,true);
                                    ex = treeutils.makeImplies(clause.pos, preident, ex);
                                    //addAssert(methodDecl,Label.SIGNALS,ex,currentStatements,clause,clause.sourcefile);
                                } finally {
                                    popBlock(0,clause);
                                }
                                notImplemented(clause,clause.token.internedName() + " clause", clause.source());
                                break;
                            }

                            case DURATION:
                            case WORKING_SPACE:
                            {
                                // FIXME - implement
                                currentStatements = ensuresStats;
                                pushBlock();
                                try {
                                    JCExpression ex = ((JmlMethodClauseConditional)clause).expression;
                                    ex = convertJML(ex,preident,true);
                                    ex = treeutils.makeImplies(clause.pos, preident, ex);
                                    //addAssert(methodDecl,Label.SIGNALS,ex,currentStatements,clause,clause.sourcefile);
                                } finally {
                                    popBlock(0,clause);
                                }
                                notImplemented(clause,clause.token.internedName() + " clause", clause.source());
                                break;
                            }


                            // FIXME - more clauses to implement?

                            case REQUIRES:
                                break;
                            default:
                        }
                    } catch (NoModelMethod e) {
                        JavaFileObject orig = log.useSource(clause.source());
                        warning(clause,"jml.skipping.no.model",""); // FIXME - can we tell which field is not implemented?
                        log.useSource(orig);
                        // continue - ignore any clause containing a model field that is not represented
                    } catch (JmlNotImplementedException e) {
                        notImplemented(clause.token.internedName() + " clause containing ",e, clause.source());
                        continue;
                    }
                    
                }
                if (!sawSignalsOnly) {
                    sawSomeSpecs = true;
                    currentStatements = exsuresStats;
                    pushBlock();
                    try {
                        JCIdent exceptionId = treeutils.makeIdent(scase.pos,exceptionSym);
                        DiagnosticPosition pos = null;
                        JCExpression condd = treeutils.makeThrownPredicate(scase, exceptionId, methodDecl);
                        addAssert(methodDecl,Label.SIGNALS_ONLY,condd,pos == null ? methodDecl : pos, log.currentSourceFile(),
                                treeutils.makeUtilsMethodCall(methodDecl.pos,"getClassName",exceptionId));
                    } finally {
                        addStat(popBlock(0,methodDecl));
                    }
                }
            }
            if (!sawSomeSpecs) {
                currentStatements = exsuresStats;
                pushBlock();
                try {
                    JCIdent exceptionId = treeutils.makeIdent(methodDecl.pos,exceptionSym);
                    JCExpression rex = treeutils.makeType(methodDecl.pos,syms.runtimeExceptionType);
                    JCExpression condd = M.at(methodDecl).TypeTest(exceptionId, rex).setType(syms.booleanType);
                    DiagnosticPosition pos = null;
                    for (JCExpression ex: methodDecl.thrown) {
                        if (pos == null) pos = ex;
                        JCExpression tc = M.at(ex).TypeTest(exceptionId, ex).setType(syms.booleanType);
                        condd = treeutils.makeOr(ex.pos, condd, tc);
                    }
                    addAssert(methodDecl,Label.SIGNALS_ONLY,condd,pos == null ? methodDecl : pos, log.currentSourceFile(),
                            treeutils.makeUtilsMethodCall(methodDecl.pos,"getClassName",exceptionId));
                } finally {
                    addStat(popBlock(0,methodDecl));
                }
            }

        }


        methodPos = methodDecl;

        // If combinedPrecondition is null then there were no specs, so the implicit precondition is true and does not
        // need to be checked
        if (combinedPrecondition != null) {
            currentStatements = preStats;
            // FIXME - associated location? where?
            addAssume(combinedPrecondition,Label.PRECONDITION,combinedPrecondition);
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
                JCStatement st = methodCallUtilsStatement(methodDecl,"reportException",str,ex);
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
                JCStatement st = methodCallUtilsStatement(methodDecl,"reportException",str,ex);
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
                JCStatement st = methodCallUtilsStatement(methodDecl,"reportException",str,ex);
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
        clearInvariants();
        
        // This empty block with a null label marks the end of the pre-state
        if (esc) {
            addStat(comment(methodDecl,"End of pre-state"));
            JCBlock bl = M.Block(0L, List.<JCStatement>nil());
            JCStatement st = M.Labelled(null, bl);
            addStat(st);
        }
    }
    
    protected void addInstanceInitialization() {
        JmlSpecs.TypeSpecs tspecs = specs.get(classDecl.sym);
        
        // If there is an initializer, use it
        if (tspecs != null) {
            for (JmlTypeClause tc: tspecs.clauses) {
                if (tc instanceof JmlTypeClauseInitializer && 
                        (tc.modifiers.flags & Flags.STATIC) == 0) {
                    JmlTypeClauseInitializer tci = (JmlTypeClauseInitializer)tc;
                    addStat( comment(methodDecl,"Instance initializer"));
                    for (JmlSpecificationCase cs: tci.specs.cases) {
                        JCExpression pre = null;
                        JCExpression post = null;
                        for (JmlMethodClause clause: cs.clauses) {
                            if (clause.token == JmlToken.REQUIRES) {
                                JCExpression p = convertJML(((JmlMethodClauseExpr)clause).expression);
                                pre = pre == null ? p : treeutils.makeAnd(clause.pos, pre, p);
                            } else if (clause.token == JmlToken.ENSURES) {
                                JCExpression p = convertJML(((JmlMethodClauseExpr)clause).expression);
                                post = post == null ? p : treeutils.makeAnd(clause.pos, post, p);
                            } else {
                                notImplemented(clause,"Clause not implemented in an initializer: " + clause.token.internedName());
                            }
                        }
                        if (post == null) post = treeutils.trueLit;
                        addAssume(tc,Label.POSTCONDITION,post);
                    }
                    return; // There must be at most one initializer
                }
            }
        }
        addStat( comment(methodDecl,"Class fields for constructor"));
        // First pass sets everything to zero-equivalent
        java.util.List<JCVariableDecl> redo = new LinkedList<JCVariableDecl>();
        for (JCTree t: classDecl.defs) {
            if (!(t instanceof JCVariableDecl)) continue;
            JCVariableDecl vd = (JCVariableDecl)t;
            if (vd.sym.isStatic()) continue; // FIXME - static fields have to be created sooner
            JCExpression receiver;
            receiver = treeutils.makeIdent(vd.pos, vd.sym);
            receiver = convertJML(receiver);
            JCExpression z = treeutils.makeZeroEquivalentLit(vd.pos,vd.type);
            addStat(treeutils.makeAssignStat(vd.pos, receiver, z));
            if (vd.init != null) redo.add(vd);
        }
        for (JmlTypeClause t: specs.get(classDecl.sym).clauses) {
            if (!(t instanceof JmlTypeClauseDecl)) continue;
            JmlTypeClauseDecl vdj = (JmlTypeClauseDecl)t;
            if (!(vdj.decl instanceof JCVariableDecl)) continue;
            JCVariableDecl vd = (JCVariableDecl)vdj.decl;
            if (isModel(vd.sym)) continue;
            JCExpression receiver;
            receiver = treeutils.makeIdent(vd.pos, vd.sym);
            receiver = convertJML(receiver);
            JCExpression z = treeutils.makeZeroEquivalentLit(vd.pos,vd.type);
            addStat(treeutils.makeAssignStat(vd.pos, receiver, z));
            if (vd.init != null) redo.add(vd);
        }
        // Second pass computes the initialized result
        for (JCVariableDecl vd: redo) {
            JCExpression receiver;
            receiver = treeutils.makeIdent(vd.pos, vd.sym);
            receiver = convertJML(receiver);
            JCExpression e = convertExpr(vd.init);
            e = addImplicitConversion(e, vd.type, e);
            addStat(treeutils.makeAssignStat(vd.pos, receiver, e));
        }
    }
    
    protected void addStaticInitialization(ClassSymbol csym) {
        JmlSpecs.TypeSpecs tspecs = specs.get(csym);
        
        // If there is a static initializer, use it
        if (tspecs != null) {
            for (JmlTypeClause tc: tspecs.clauses) {
                if (tc instanceof JmlTypeClauseInitializer && 
                        (tc.modifiers.flags & Flags.STATIC) != 0) {
                    JmlTypeClauseInitializer tci = (JmlTypeClauseInitializer)tc;
                    for (JmlSpecificationCase cs: tci.specs.cases) {
                        JCExpression pre = null;
                        JCExpression post = null;
                        for (JmlMethodClause clause: cs.clauses) {
                            if (clause.token == JmlToken.REQUIRES) {
                                JCExpression p = convertJML(((JmlMethodClauseExpr)clause).expression);
                                pre = pre == null ? p : treeutils.makeAnd(clause.pos, pre, p);
                            } else if (clause.token == JmlToken.ENSURES) {
                                JCExpression p = convertJML(((JmlMethodClauseExpr)clause).expression);
                                post = post == null ? p : treeutils.makeAnd(clause.pos, post, p);
                            } else {
                                notImplemented(clause,"Clause not implemented in an initializer: " + clause.token.internedName());
                            }
                        }
                        if (post == null) post = treeutils.trueLit;
                        addAssume(tc,Label.POSTCONDITION,post);
                    }
                    return; // There must be at most one static initializer
                }
            }
        }
        
//        // Otherwise we construct it from the static fields
//
//        Env<AttrContext> enva = Enter.instance(context).getEnv(csym);
//        if (enva == null) return;
//        JmlClassDecl decl = (JmlClassDecl)enva.tree;
//        if (decl == null) return;
//
//        for (JCTree t: decl.defs) {
//            if (t instanceof JmlVariableDecl) {
//                JmlVariableDecl d = (JmlVariableDecl)t;
//                if (!d.sym.isStatic()) continue;
//                JCIdent id = treeutils.makeIdent(d.pos, d.sym);
//                JCExpression z = treeutils.makeZeroEquivalentLit(d.pos,d.type);
//                addStat(treeutils.makeAssignStat(d.pos, id, z));
//            }
//        }
//        
//        for (JCTree t: decl.defs) {
//            if (t instanceof JmlVariableDecl) {
//                JmlVariableDecl d = (JmlVariableDecl)t;
//                if (!d.sym.isStatic()) continue;
//                if (d.init == null) continue;
//                JCIdent id = treeutils.makeIdent(d.pos, d.sym);
//                JCExpression z = addImplicitConversion(d, d.type, convertExpr(d.init));
//                addStat(treeutils.makeAssignStat(d.pos, id, z));
//            }
//        }
        
    }
    

    // VISITOR METHODS
    
    // OK
    @Override
    public void visitTopLevel(JCCompilationUnit that) {
        // OpenJML should never call this, because JCCompilationUnit nodes should be
        // replaced by JmlCompilationUnit nodes. We implement this just in case, but
        // always produce a JmlCompilationUnit node
        if (pureCopy) {
          JmlCompilationUnit n = M.at(that).TopLevel(that.packageAnnotations,that.pid,convert(that.defs));
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
            error(that,"Unexpected call of JmlAssertionAdder.visitTopLevel while translating JML: " + that.getClass());
            return;
        }
        error(that,"Unexpected call of JmlAssertionAdder.visitTopLevel: " + that.getClass());
    }

    // OK
    @Override
    public void visitImport(JCImport that) {
        // OpenJML should never call this, because JCImport nodes should be
        // replaced by JmlImport nodes. We implement this just in case, but
        // always produce a JmlImport node
        
        JCTree qualid = that.qualid;
        if (fullTranslation) qualid = convert(qualid);
        result = M.at(that).Import(qualid, that.staticImport);
    }

    // OK
    @Override
    public void visitClassDef(JCClassDecl that) {
        // OpenJML should never call this, because JCClassDecl nodes should be
        // replaced by JmlClassDecl nodes. We implement this just in case, but
        // always produce a JmlClassDecl node.

        if (pureCopy) {
            JmlClassDecl d = M.at(that).ClassDef(
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
        } else if (translatingJML) {
            error(that,"Unexpected call of JmlAssertionAdder.visitClassDef while translating JML: " + that.getClass());
        } else {
            error(that, "Unexpectedly calling JmlAssertionAdder.visitClassDef: " + that.getClass());
        }
        return;
    }

    // OK
    @Override
    public void visitMethodDef(JCMethodDecl that) {
        // In OpenJML, we expect to always have JmlMethodDecl nodes, and so 
        // never to call this visit class
        // However, just in case a user creates one, we translate it
        if (pureCopy) {
            JmlMethodDecl m = M.at(that).MethodDef(
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
            //m.owner = that.owner;
            m.sourcefile = null;
            m.specsDecl = null;
            result = m;
            methodBiMap.put((JmlMethodDecl)that,m);
        } else if (translatingJML) {
            error(that,"Unexpected call of JmlAssertionAdder.visitMethodDef while translating JML: " + that.getClass());
        } else {
            error(that,"Unexpected visit call in JmlAssertionAdder.visitMethodDef: " + that.getClass());
        }
        return;
    }

    // OK
    @Override
    public void visitVarDef(JCVariableDecl that) {
        if (pureCopy) {
            JmlVariableDecl v = M.at(that).VarDef(
                    convert(that.mods),
                    that.name,
                    convert(that.vartype),
                    convert(that.init));
            v.setType(that.type);
            v.sym = that.sym; // Keep same sym, or else we have to map them 
            v.docComment = null;
            v.fieldSpecs = null;
            v.fieldSpecsCombined = null;
            v.sourcefile = null;
            v.specsDecl = null;
            result = v;
        } else if (translatingJML) {
            error(that,"Unexpected call of JmlAssertionAdder.visitVarDef while translating JML: " + that.getClass());
        } else {
            error(that,"Unexpected visit call in JmlAssertionAdder.visitVarDef: " + that.getClass());
        }
        return;
    }

    //OK
    @Override
    public void visitSkip(JCSkip that) {
        if (!pureCopy) addTraceableComment(that);
        result = addStat(M.at(that).Skip());
        // Caution - JML statements are subclasses of JCSkip
    }
    
    /** Produces a MethodSym for an initialization block; any variables 
     * declared within an initialization block need a 'method' as an owner
     * rather than a class, or they will be interpreted as class fields.
     */
    protected JmlMethodDecl methodSymForInitBlock(DiagnosticPosition pos, long flags, JCClassDecl classDecl) {
        MethodSymbol msym = new MethodSymbol(
                flags, 
                classDecl.name, 
                null, 
                classDecl.sym);
        methodDecl = M.MethodDef(
                M.Modifiers(flags, M.Annotations(List.<com.sun.tools.javac.code.Attribute.Compound>nil())),
                classDecl.name,
                null,
                null,
                null,
                null,
                null, //body,
                null);
        methodDecl.pos = pos.getPreferredPosition();
        methodDecl.sourcefile = Log.instance(context).currentSourceFile();
        methodDecl.docComment = null;
        methodDecl.cases = null;
        methodDecl.methodSpecsCombined = null;
        methodDecl.sym = msym;
        methodDecl.type = null;
        return methodDecl;
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
            methodDecl = methodSymForInitBlock(that, that.flags, classDecl);

        }
        pushBlock();
        try {
            if (exceptionSym == null) {
                initialize2(that.flags & Flags.STATIC);
            }
            scan(that.stats);
        } finally {
            JCBlock bl = popBlock(that.flags,that);
            if (currentStatements == null) { // FIXME - need a better way to tell which kind of block we are in
                classDefs.add(bl);
            } else {
                addStat(bl);
            }
            methodDecl = prev;
            result = bl;
        }
    }

    // OK - should call visitJmlDoWhileLoop instead
    @Override
    public void visitDoLoop(JCDoWhileLoop that) {
        error(that,"Unexpected visit call in JmlAssertionAdder.visitDoLoop: " + that.getClass());
    }

    // OK - should call visitJmlWhileLoop instead
    @Override
    public void visitWhileLoop(JCWhileLoop that) {
        error(that,"Unexpected visit call in JmlAssertionAdder.visitWhileLoop: " + that.getClass());
    }

    // OK - should call visitJmlForLoop instead
    @Override
    public void visitForLoop(JCForLoop that) {
        error(that,"Unexpected visit call in JmlAssertionAdder.visitForLoop: " + that.getClass());
    }

    // OK - should call visitJmlEnhancedForLoop instead
    @Override
    public void visitForeachLoop(JCEnhancedForLoop that) {
        error(that,"Unexpected visit call in JmlAssertionAdder.visitForeachLoop: " + that.getClass());
    }
    
    /** This map contains an entry for all labels that are in scope. It is used
     * when an \old expression appears that references the label: in RAC mode we
     * need to insert a computation of the desired quantity.
     */ // FIXME - determine if these need to be two separate lists. The difference at present is that those in the active list are not yet closed.
    protected
    Map<Name,ListBuffer<JCStatement>> labelActiveOldLists = new HashMap<Name,ListBuffer<JCStatement>>();
    protected
    Map<Name,ListBuffer<JCStatement>> labelOldLists = new HashMap<Name,ListBuffer<JCStatement>>();

    //OK
    @Override
    public void visitLabelled(JCLabeledStatement that) {
        if (!pureCopy) addStat(comment(that,"label:: " + that.label + ": ..."));
        // Note that the labeled statement will turn into a block
        // Since declarations may not be labelled statements, there are no
        // declarations in the labelled statement that need to be in scope after
        // the labelled statement.
        JCLabeledStatement stat = M.at(that).Labelled(that.label, null);
        markLocation(that.label,currentStatements,stat);
        treeMap.put(that, stat); // we store the mapping from old to new so that we can appropriately translate the targets of break and continue statements
        labelActiveOldLists.put(that.label, currentStatements);
        JCBlock block;
        try {
            block = convertIntoBlock(that,that.body);
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
        JCExpression switchExpr = that.selector;
        if (!pureCopy) {
            addStat(traceableComment(that,that,"switch " + that.getExpression() + " ...","Selection"));
        }
        try {
            JCExpression selector = convertExpr(switchExpr);
            if (!pureCopy) {
                if (that.selector.type.equals(syms.stringType)) {
                    if (javaChecks) {
                        JCExpression e = treeutils.makeNeqObject(switchExpr.pos, selector, treeutils.nullLit);
                        addAssert(that.selector, Label.POSSIBLY_NULL_VALUE, e);
                    }
                } else if ((that.selector.type.tsym.flags_field & Flags.ENUM) != 0) {
                    if (javaChecks) {
                        JCExpression e = treeutils.makeNeqObject(switchExpr.pos, selector, treeutils.nullLit);
                        addAssert(switchExpr, Label.POSSIBLY_NULL_VALUE, e);
                    }
                } else {
                    selector = addImplicitConversion(switchExpr,syms.intType,selector);
                }
            }
            JCSwitch sw = M.at(that).Switch(selector, null);
            // record the translation from old to new AST before translating the body
            treeMap.put(that,sw);
            ListBuffer<JCCase> cases = new ListBuffer<JCCase>();
            for (JCCase c: that.cases) {
                JCExpression pat = convertExpr(c.pat);
                JCBlock b = convertIntoBlock(c,c.stats);
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
        error(that,"JmlAssertionAdder.visitCase should not be called");
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
            addAssert(that.lock, Label.POSSIBLY_NULL_VALUE, e);
        }
        JCBlock block = convertBlock(that.body);
        result = addStat(M.at(that).Synchronized(lock, block).setType(that.type));
        // FIXME - need to add concurrency checks
    }

    // OK
    // FIXME - review and cleanup for both esc and rac
    @Override
    public void visitTry(JCTry that) {
        if (!pureCopy) addStat(comment(that,"try ...")); // Don't need to trace the try keyword
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
                JmlVariableDecl decl = M.at(odecl).VarDef(odecl.sym,  null); // Catcher declarations have no initializer
                JCCatch ncatcher = M.at(catcher).Catch(decl,block);
                ncatcher.setType(catcher.type);
                ncatchers.add(ncatcher);
            }
            catchers = ncatchers.toList();
        }
        JCBlock finalizer = convertBlock(that.finalizer);
        List<JCTree> newResources = convertCopy(that.resources);
        // FIXME - no checks implemented on the resources
        JCTry st =  M.at(that).Try(newResources, body, catchers, finalizer);
        st.setType(that.type);
        result = addStat(st);
        return;
    }

    // OK
    @Override
    public void visitCatch(JCCatch that) {
        // Catch statements are handled along with Try
        error(that,"JmlAssertionAdder.visitCatch should not be called");
    }
    
    // FIXME - these are not fully developed yet
    protected void adjustWellDefinedConditions(JCExpression cond) {
        adjustWellDefinedConditions(cond,wellDefinedConditions);
    }
    protected void adjustWellDefinedConditions(JCExpression cond, java.util.List<JmlStatementExpr> conds) {
        for (JmlStatementExpr st: conds) {
            st.expression = treeutils.makeImplies(st.expression.pos, cond, st.expression);
        }
    }

    // OK
    @Override
    public void visitConditional(JCConditional that) {
        if (!pureCopy) addStat(comment(that," ... conditional ..."));

        JCExpression cond = convertExpr(that.cond);
        if (pureCopy) {
            JCExpression truepart = convertExpr(that.truepart);
            JCExpression falsepart = convertExpr(that.falsepart);
            result = eresult = M.at(that).Conditional(cond,truepart,falsepart).setType(that.type);
        } else if (!splitExpressions) {
            JCExpression prev = condition;
            try {
                java.util.List<JmlStatementExpr> listf = new java.util.LinkedList<JmlStatementExpr>();
                listf.addAll(wellDefinedConditions);

                cond = addImplicitConversion(cond,syms.booleanType,cond);
                condition = treeutils.makeAnd(that.pos, prev, cond);
                JCExpression truepart = convertExpr(that.truepart);
                truepart = addImplicitConversion(that.truepart,that.type,truepart);
                adjustWellDefinedConditions(cond);                
                condition = treeutils.makeAnd(that.pos, prev, treeutils.makeNot(that.falsepart.pos, cond));
                JCExpression falsepart = convertExpr(that.falsepart);
                falsepart = addImplicitConversion(that.falsepart,that.type,falsepart);
                adjustWellDefinedConditions(cond,listf);
                wellDefinedConditions.addAll(listf);
                result = eresult = M.at(that).Conditional(cond,truepart,falsepart).setType(that.type);
            } finally {
                condition = prev;
            }
        } else {
            cond = addImplicitConversion(cond,syms.booleanType,cond);

            Name resultname = names.fromString(Strings.conditionalResult + (++count));
            JCVariableDecl vdecl = treeutils.makeVarDef(that.type, resultname, esc? null : methodDecl.sym, that.pos);
            addStat(vdecl);

            pushBlock();
            JCBlock trueblock = null;
            try {
                JCExpression tres = convertExpr(that.truepart);
                tres = addImplicitConversion(that.truepart,that.type,tres);
                JCIdent id = treeutils.makeIdent(that.truepart.pos, vdecl.sym);
                addStat( treeutils.makeAssignStat(that.truepart.pos, id, tres));
            } finally {
                trueblock = popBlock(0,that.truepart);
            }

            pushBlock();
            JCBlock falseblock = null;
            try {
                JCExpression fres = convertExpr(that.falsepart);
                fres = addImplicitConversion(that.falsepart,that.type,fres);
                JCIdent id = treeutils.makeIdent(that.falsepart.pos, vdecl.sym);
                addStat( treeutils.makeAssignStat(that.falsepart.pos, id, fres));
            } finally {
                falseblock = popBlock(0,that.falsepart);
            }

            JCStatement stat = M.at(that).If(cond, trueblock, falseblock);

            addStat(stat);
            result = eresult = treeutils.makeIdent(that.pos, vdecl.sym);
        }
    }

    // OK
    @Override
    public void visitIf(JCIf that) {
        JCExpression cond = convertExpr(that.cond);
        if (pureCopy) {
            JCStatement thenpart = convert(that.thenpart);

            JCStatement elsepart = convert(that.elsepart);

            JCStatement st = M.at(that).If(cond,thenpart,elsepart).setType(that.type);
            result = addStat( st );
        }
        else {
            addStat(traceableComment(that,that,"if " + that.getCondition() + " ...", "Condition"));
            cond = addImplicitConversion(that.cond,syms.booleanType,cond);

            // The scanned result of the then and else parts must always be a block
            // because multiple statements might be produced, even from a single
            // statement in the branch.

            JCBlock thenpart = convertIntoBlock(that.thenpart,that.thenpart);

            JCBlock elsepart = that.elsepart == null ? null :
                convertIntoBlock(that.elsepart, that.elsepart);

            JCStatement st = M.at(that).If(cond,thenpart,elsepart).setType(that.type);
            result = addStat( st );
        }
    }
    
    // FIXME - document these
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

    /** Create a comment that is used for tracing; the value of the given expression (and subexpressions)
     * is printed as part of the trace.
     * @param t the source location to cite for the comment
     * @param expr the expression to trace
     * @param description the description of the expression to give (typically a string representation of the symbolic expression)
     * @param info additional information to be provided with the comment
     * @return
     */
    protected JCStatement traceableComment(JCTree t, JCTree expr, String description, String info) {
        JmlStatementExpr c = comment(t,description);
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
            result = addStat( M.at(that).Exec(arg).setType(that.type) );
        }
    }

    // OK
    @Override
    public void visitBreak(JCBreak that) {
        if (!pureCopy) {
            addTraceableComment(that);
        }
        JCBreak st = M.at(that).Break(that.label);
        st.target = treeMap.get(that.target);
        if (st.target == null) {
            error(that,"Unknown break target");
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
            JCBreak st = M.at(that).Break(null);
            st.setType(that.type);
            st.label = continueStack.peek().getLabel();
            st.target = continueStack.peek();
            result = addStat(st);
        } else {
            JCContinue st = M.at(that).Continue(that.label);
            st.setType(that.type);
            st.target = treeMap.get(that.target);
            if (st.target == null) {
                error(that,"Unknown continue target");
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
            int p = that.pos;
            if (retValue != null) {
                retValue = addImplicitConversion(that,methodDecl.restype.type,retValue);
                JCIdent resultid = treeutils.makeIdent(p,resultSym);
                JCStatement stat = treeutils.makeAssignStat(p,resultid,retValue);
                addStat(stat);
                retValue = treeutils.makeIdent(p,resultSym);
            }
            
            // Record the value of the termination location
            JCIdent id = treeutils.makeIdent(p,terminationSym);
            JCLiteral intlit = treeutils.makeIntLiteral(p,that.pos);
            JCStatement stat = treeutils.makeAssignStat(p,id,intlit);
            addStat(stat);
            
            // If the return statement is in a finally block, there may have been an exception
            // in the process of being thrown - so we set EXCEPTION to null.
            id = treeutils.makeIdent(p,exceptionSym);
            stat = treeutils.makeAssignStat(p,id,treeutils.nullLit);
            addStat(stat);
        }
        
        result = addStat( M.at(that).Return(retValue).setType(that.type) );
    }

    // OK
    // FIXME - review for esc
    @Override
    public void visitThrow(JCThrow that) {
        if (pureCopy) {
            JCExpression expr = convertExpr(that.getExpression());
            result = addStat(M.at(that).Throw(expr).setType(that.type));
            
//        } else if (rac) {
//            addTraceableComment(that);
//
//            JCExpression expr = convertExpr(that.getExpression());
//            JCIdent id = treeutils.makeIdent(that.pos,exceptionSym);
//            addStat( treeutils.makeAssignStat(that.pos,id,expr) );
//            JCExpression e = treeutils.makeNeqObject(that.expr.pos, expr, treeutils.makeNullLiteral(that.expr.getEndPosition(log.currentSource().getEndPosTable())));
//            if (javaChecks) addAssert(e, Label.POSSIBLY_NULL_VALUE, e);
//            result = addStat(M.at(that).Throw(expr).setType(that.type));
            
        } else {
        
            addTraceableComment(that);
            pushBlock();
            try {
                JCExpression exceptionExpr = convertExpr(that.expr);
                // assert expr != null;
                JCExpression e = treeutils.makeNeqObject(that.expr.pos, exceptionExpr, treeutils.makeNullLiteral(that.expr.getEndPosition(log.currentSource().getEndPosTable())));
                if (javaChecks) addAssert(e, Label.POSSIBLY_NULL_VALUE, e);

                if (that.expr.type.tag != TypeTags.BOT) {
                    // Declare a local variable of the type of the exception expression, initialized to the expression
                    Name local = names.fromString(Strings.exceptionLocalVarString + that.pos);
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
                    JCStatement term = treeutils.makeAssignStat(that.pos, tid, treeutils.makeIntLiteral(that.pos,-that.pos));
                    addStat(term);

                    // throw the local expression value
                    localid = treeutils.makeIdent(that.pos,decl.sym);
                    exceptionExpr = localid;
                }
                JCThrow thrw = M.at(that).Throw(exceptionExpr);
                addStat(thrw);
            } finally {
                JCBlock block = popBlock(0,that);
                result = addStat(block);
            }
        }
        return;
    }

    // OK - this is a Java assert statement
    @Override
    public void visitAssert(JCAssert that) {
        // FIXME - in esc we may want to treat this as an exception throwing Java statement
        
        // ESC will eventually convert this to a Jml assertion, but RAC wants
        // it left as a Java assertion statement
        if (!pureCopy) addTraceableComment(that);
        
        JCExpression cond = convertExpr(that.getCondition());
        
        JCExpression opt = that.getDetail();
        JCExpression info = // We don't convert literals to avoid bloat when the literal is an explicit null or constant String
            !(opt instanceof JCLiteral) ? convertExpr(opt) :
            fullTranslation ? treeutils.makeDuplicateLiteral(opt.pos, (JCLiteral)opt) :
                opt;
        
        if (pureCopy || rac) {
            result = addStat( M.at(that).Assert(cond, info).setType(that.type) );
        } else { // esc
            result = addAssert(true,that,Label.EXPLICIT_ASSERT,cond,null,null,info);
            if (info != null) newTemp(info); // The detail expression is evaluated but not used anywhere
        }
    }
    
    // FIXME - review all the assignable checks for appropriate use of translations and this
    /** Returns true if x is contained in the datagroup y */
    protected
    boolean isContainedIn(VarSymbol x, VarSymbol y) {
        if (x == y) return true;
        if (x == classDecl.thisSymbol && y == currentThisId.sym) return true;
        FieldSpecs fs = specs.getSpecs(x);
        if (fs == null) {
            // null can happen for a private field of a class without source
            // and without a declaration in the corresponding jml file
            return false;
        }
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
    JCExpression accessAllowed(JmlStoreRefKeyword storeref, JCExpression pstoreref) {
        DiagnosticPosition pos = storeref;
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
    JCExpression accessAllowed(JCIdent id, JCExpression pstoreref, VarSymbol baseThisSym, VarSymbol targetThisSym) {
        if (id.sym.owner.kind == Kinds.MTH) return treeutils.trueLit; // Local variable // FIXME - I thought this was already checked somewhere
        DiagnosticPosition pos = id;
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            JCIdent pid = (JCIdent)pstoreref;
            // Presumes any class fields are qualified
            return id.sym == pid.sym ? treeutils.trueLit : treeutils.falseLit;
//            if (id.sym == pid.sym) {
//                if (baseThisSym == targetThisSym) return treeutils.trueLit;
//                JCExpression id1 = treeutils.makeIdent(id.pos, targetThisSym);
//                JCExpression id2 = treeutils.makeIdent(pstoreref.pos, baseThisSym);
//                return treeutils.makeEqObject(id.pos, id1, id2);
//            }
//            else return treeutils.falseLit;

        } else if (pstoreref instanceof JCFieldAccess) {
            JCFieldAccess pfa = (JCFieldAccess)pstoreref;
            if (pfa.name == null) {
                log.error(pstoreref, "jml.internal", "A field wildcard expression should not be present here");
                return treeutils.falseLit;
            }
            // FIXME - check the following - use isContainedIn
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
                boolean st = utils.isJMLStatic(id.sym);
                if (id.sym != pfa.sym && pfa.sym != null) return treeutils.falseLit;
                if (st  && pfa.sym != null) return treeutils.trueLit;
                if (st  && pfa.sym == null && s0 == classDecl.sym) return treeutils.trueLit;
                if (st  && pfa.sym == null && s0 != classDecl.sym) return treeutils.falseLit;
                if (!st && pfa.sym == null) {
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
    JCExpression accessAllowed(JCFieldAccess fa, JCExpression pstoreref, VarSymbol baseThisSym, VarSymbol targetThisSym) {
        if (fa.name == null) {
            log.error(pstoreref, "jml.internal", "A field wildcard expression should not be present here");
            return treeutils.falseLit;
        }

        DiagnosticPosition pos = fa;
        int posp = pos.getPreferredPosition();
        JCExpression pfac = convertAssignable(pstoreref,targetThisSym);
        if (pfac instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pfac).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pfac instanceof JCIdent) {
            JCIdent pid = (JCIdent)pfac;
            if (!isContainedIn((VarSymbol)fa.sym,(VarSymbol)pid.sym)) return treeutils.falseLit;
            if (utils.isJMLStatic(pid.sym)) return treeutils.trueLit;
            JCExpression idthis = treeutils.makeOld(pos,treeutils.makeIdent(posp, baseThisSym));
            if (rac) idthis = convertJML(idthis);
            JCExpression result = treeutils.makeEqObject(posp, idthis, 
                     convertJML(fa.selected));

            return result; 

        } else if (pfac instanceof JCFieldAccess) {
            JCFieldAccess pfa = (JCFieldAccess)pfac;
            if (pfa.name == null) {
                JCExpression or = treeutils.falseLit;
                for (Symbol s: utils.listJmlVisibleFields(pfa.selected.type.tsym, methodDecl.mods.flags&Flags.AccessFlags, treeutils.isATypeTree(pfa.selected))) {
                    JCExpression newpfa = M.at(pfa.pos).Select(pfa.selected, s);
                    or = treeutils.makeOr(pfa.pos, or, accessAllowed(fa,newpfa,baseThisSym,targetThisSym));
                }
                return or;
                //log.error(pstoreref, "jml.internal", "A field wildcard expression should not be present here");
                //return treeutils.falseLit;
            }
            boolean contained = isContainedIn((VarSymbol)fa.sym,(VarSymbol)pfa.sym);
            if (!contained) {
                // a.x vs b.y with x != y, so automatically false
                return treeutils.falseLit;
            }
            if (contained && !utils.isJMLStatic(pfa.sym)) {
                // a.x vs. b.x  with x not static, so result is (a == b)
                JCExpression result = treeutils.makeEqObject(posp, convertJML(fa.selected), convertJML(pfa.selected));
                return result;
            }
            if (contained && utils.isJMLStatic(pfa.sym)) {
                // a.x vs. b.x  with x static, so result is true - a and b have to be the same type
                return treeutils.trueLit;
            }
//            if (pfa.sym == null) {  // FIXME - review this
//                // a.x vs b.* (x may be *, a,b may be expressions or types)
//                // Note: this.* does not include static fields, and only include jmlvisible fields and data groups
//                
//                JCExpression expr = fa.selected;
//                Symbol fs = expr instanceof JCIdent ? ((JCIdent)expr).sym :
//                    expr instanceof JCFieldAccess ? ((JCFieldAccess)expr).sym :
//                        null;
//                expr = convertJML(pfa.selected);
//                Symbol pfs = expr instanceof JCIdent ? ((JCIdent)expr).sym :
//                        expr instanceof JCFieldAccess ? ((JCFieldAccess)expr).sym :
//                            null;
//
//                if (fa.sym != null && !utils.jmlvisible(  // FIXME - what should the answer be from a jmlvisibility if we are matching x.* and y.* ?
//                        pfs instanceof TypeSymbol ? pfs : pfs.enclClass(), 
//                        fa.sym.owner, 
//                        fa.sym.flags(), methodDecl.mods.flags)) {
//                    return treeutils.falseLit;
//                }
//                
//                if (fa.sym != null && (pfs instanceof Symbol.TypeSymbol) != utils.isJMLStatic(fa.sym)) return treeutils.falseLit;
//                if (fa.sym == null && (pfs instanceof Symbol.TypeSymbol) != (fs instanceof Symbol.TypeSymbol)) return treeutils.falseLit;
//                
//                // FIXME - this all needs review
//                if (pfs instanceof Symbol.ClassSymbol) {
//                    // ?.x vs X.*
//                    JCExpression result = (fs instanceof Symbol.ClassSymbol) && (fs == pfs) // FIXME - should be fs extends pfs?
//                             ? treeutils.trueLit : treeutils.falseLit;
//                    return result;
//                } else if (fs instanceof Symbol.ClassSymbol) {
//                    // X.x vs e.*
//                    boolean same = fs == pfs;
//                    JCExpression result = same ? treeutils.trueLit : treeutils.falseLit;
//                    return result;
//                } else {
//                    // ee.x vs. e.*
//                    JCExpression result = treeutils.makeEqObject(posp, convertJML(fa.selected), expr);
//                    return result;
//                }
//            }
            
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
    JCExpression accessAllowed(JCArrayAccess aa, JCExpression pstoreref, VarSymbol baseThisSym, VarSymbol targetThisSym) {
        DiagnosticPosition pos = aa;
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
            JCExpression a1 = convertAssignable(aa.indexed, targetThisSym);
            JCExpression e = treeutils.makeOld(pos,paa.indexed);
            if (rac) e = convertAssignable(e, baseThisSym);
            JCExpression result = treeutils.makeEqObject(posp, a1, e);
            if (paa.index == null ) return result;
            if (aa.index == null) return treeutils.falseLit;
            a1 = convertJML(aa.index);
            result = treeutils.makeAnd(posp,result,
                    treeutils.makeBinary(posp,JCTree.EQ,treeutils.inteqSymbol,a1,convertJML(paa.index)));
            return result;
            
        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange paa = (JmlStoreRefArrayRange)pstoreref;
            JCExpression a1 = convertJML(aa.indexed);
            JCExpression arrayConverted = treeutils.makeOld(pos,convertJML(paa.expression));
            if (rac) arrayConverted = convertJML(arrayConverted);
            JCExpression result = treeutils.makeEqObject(posp, a1, arrayConverted);
            if (aa.index == null) {
                if (paa.lo == null && paa.hi == null) return result;
                if (paa.hi == null) return treeutils.makeAnd(posp, result, treeutils.makeBinary(pos.getPreferredPosition(), JCTree.EQ, treeutils.inteqSymbol, convertJML(paa.lo),treeutils.zero));
                
                // FIXME - compare paa.hi to array.length, paa.lo to zero if not null
                return treeutils.falseLit;
            } else {
                JCExpression aat = convert(aa.index);
                result = treeutils.makeAnd(posp,result,
                        treeutils.makeAnd(posp,
                                treeutils.makeBinary(posp,JCTree.LE,treeutils.intleSymbol,
                                        paa.lo == null ? treeutils.zero : convertJML(paa.lo),aat),
                                paa.hi == null ? treeutils.makeBinary(posp, JCTree.LT,treeutils.intltSymbol,
                                                aat, treeutils.makeLength(paa,arrayConverted) )
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
    JCExpression accessAllowed(JmlStoreRefArrayRange aa, JCExpression pstoreref, VarSymbol baseThisSym, VarSymbol targetThisSym) {
        DiagnosticPosition pos = aa;
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
            JCExpression e = treeutils.makeOld(pos,(paa.indexed));
            e = convertAssignable(e,baseThisSym);
            JCExpression result = treeutils.makeEqObject(posp, convertAssignable(aa.expression,targetThisSym), e);
            if (paa.index == null) return result;
            JCExpression paat = convertJML(paa.index);
            result = treeutils.makeAnd(posp, result, treeutils.makeBinary(posp,JCTree.EQ,treeutils.inteqSymbol, 
                    aa.lo == null ? treeutils.zero : convertJML(aa.lo), paat));
//            result = treeutils.makeAnd(pos, result, treeutils.makeBinary(pos,JCTree.EQ,treeutils.inteqSymbol, 
//                    aa.hi == null ? /* FIXME - array length -1 */ : jmlrewriter.translate(aa.hi), paat));
            return result;
        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange paa = (JmlStoreRefArrayRange)pstoreref;
            JCExpression e = treeutils.makeOld(pos,(paa.expression));
            e = convertAssignable(e,baseThisSym);
            JCExpression result = treeutils.makeEqObject(posp, convertAssignable(aa.expression,targetThisSym), e);
            JCExpression a1 = aa.lo == null ? treeutils.zero : convertJML(aa.lo);
            JCExpression a2 = paa.lo == null ? treeutils.zero : convertJML(paa.lo);
            result = treeutils.makeAnd(posp, result, treeutils.makeBinary(posp,JCTree.LE,treeutils.intleSymbol, 
                    a2, a1));

            JCIdent savedId = currentThisId;
            JCExpression savedExpr = currentThisExpr;
            try {
                currentThisExpr = currentThisId = targetThisSym == null ? null : treeutils.makeIdent(aa.expression.pos, targetThisSym);
                a1 = aa.hi != null ? convertJML(aa.hi) : treeutils.makeBinary(posp, JCTree.MINUS, treeutils.makeLength(pos, convertJML(aa.expression)), treeutils.one);
                currentThisExpr = currentThisId = baseThisSym == null ? null : treeutils.makeIdent(aa.expression.pos, baseThisSym);
                a2 = paa.hi != null ? convertJML(paa.hi) :  treeutils.makeBinary(posp, JCTree.MINUS, treeutils.makeLength(pos, convertJML(paa.expression)), treeutils.one);
            } finally {
                currentThisId = savedId;
                currentThisExpr = savedExpr;
            }
            result = treeutils.makeAnd(posp, result, treeutils.makeBinary(pos.getPreferredPosition(),JCTree.LE,treeutils.intleSymbol, 
                    a1, a2));

            return result;
        }
        
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + aa + " vs. " + pstoreref);
        return treeutils.falseLit;
    }

    /** Check that the given storeref is a subset of the given 
     * pstoreref, returning the condition under which the storeref
     * is allowed. storeref may not be a field wildcard.
     * pstoreref is presumed to refer to the enclosing methodDecl.
     */
    protected 
    JCExpression accessAllowed(JCExpression storeref, JCExpression pstoreref,
            VarSymbol baseThisSym, VarSymbol targetThisSym) {
        if (storeref instanceof JmlStoreRefKeyword) {
            return accessAllowed((JmlStoreRefKeyword)storeref,pstoreref);

        } else if (storeref instanceof JCIdent) {
            return accessAllowed((JCIdent)storeref,pstoreref,baseThisSym,targetThisSym);
            
        } else if (storeref instanceof JCFieldAccess) {
//            JCFieldAccess fa = (JCFieldAccess)storeref;
//            if (fa.name == null) {
//                JCExpression or = treeutils.falseLit;
//                for (Symbol s: utils.listJmlVisibleFields(fa.selected.type.tsym, methodDecl.mods.flags&Flags.AccessFlags, utils.isJMLStatic(methodDecl.sym))) {
//                    JCExpression newfa = M.at(fa.pos).Select(fa.selected, s);
//                    or = treeutils.makeOr(fa.pos, or, assignmentAllowed(newfa,pstoreref,baseThisSym,targetThisSym));
//                }
//                return or;
//            } else {
                return accessAllowed((JCFieldAccess)storeref,pstoreref,baseThisSym,targetThisSym);
//            }
            
        } else if (storeref instanceof JCArrayAccess) {
            return accessAllowed((JCArrayAccess)storeref,pstoreref,baseThisSym,targetThisSym);
            
        } else if (storeref instanceof JmlStoreRefArrayRange) {
            return accessAllowed((JmlStoreRefArrayRange)storeref,pstoreref,baseThisSym,targetThisSym);
            
        }
        
        log.error(storeref.pos,"esc.not.implemented", "Assignability comparison: " + storeref + " vs. " + pstoreref);
        return treeutils.falseLit;
    }
    
    protected boolean recursiveCall = false;
    /** Add assertions that the lhs is allowed to be written to or read from.
     * 
     * @param assignPosition the position of the generation assertion
     * @param mdecl the method in which the assignment takes place and whose assignable clauses are to be checked
     * @param lhs the target to be checked if it may be assigned to (must not be a field wildcard)
     * @param baseThisSym
     * @param targetThisSym
     */
    protected void checkAccess(JmlToken token, DiagnosticPosition assignPosition, JCExpression lhs,
            VarSymbol baseThisSym, VarSymbol targetThisSym) {
        if (rac) return; // FIXME - turn off checking assignable until we figure out how to handle fresh allocations in rac
        if (recursiveCall) return;
        Symbol sym = treeutils.getSym(lhs);
        if (sym != null && !(sym instanceof VarSymbol)) return;
        recursiveCall = true;
        boolean noSpecCases = true;
        for (JmlSpecificationCase c: specs.getDenestedSpecs(methodDecl.sym).cases) {
            noSpecCases = false;
            JCExpression check = checkAccess(token,assignPosition, lhs,c,baseThisSym,targetThisSym);
            if (!treeutils.isTrueLit(check)) {
                // The access is not allowed if it is nowhere in the
                // assignable/accessible clauses; we point to the first one. If there are
                // none the default is \everything, which is always allowed 
                // (constructor default handled below)
                DiagnosticPosition cpos = c;
                for (JmlMethodClause m : c.clauses) {
                    if (m.token == token) { cpos = m; break; }
                }
                addAssert(assignPosition,
                        token == JmlToken.ASSIGNABLE ? Label.ASSIGNABLE : Label.ACCESSIBLE,
                        check,cpos,c.sourcefile,lhs.toString());
            }
        }
        if (noSpecCases) {
            // Constructor default is handled within the call below
            JCExpression check = checkAccess(token,assignPosition, lhs,M.at(methodDecl.pos).JmlSpecificationCase(null, false, null, null, List.<JmlMethodClause>nil()),currentThisId.sym,currentThisId.sym);
            if (!treeutils.isTrueLit(check)) {
                addAssert(assignPosition,
                        token == JmlToken.ASSIGNABLE ? Label.ASSIGNABLE : Label.ACCESSIBLE,
                        check,methodDecl.pos,methodDecl.sourcefile,lhs.toString());
            }
        }
        recursiveCall = false;
    }

    /** This method checks a store-ref of a callee against the caller's assignable clauses.
     * Both the callee and the caller are expected to have field wildcards expanded.
     * 
     * @param callPosition the position of the call
     * @param scannedItem  the store-ref of the callee
     * @param precondition the callee precondition under which the store-ref might be assigned
     * @param baseThisId   the thisId of the caller
     * @param targetThisId the thisId of the callee
     */
    protected void checkAgainstCallerSpecs(JmlToken token, DiagnosticPosition callPosition, JCExpression scannedItem, JCExpression precondition,
            JCIdent baseThisId, /*@nullable*/ JCIdent targetThisId) {
        if (rac) return; // FIXME - turn off checking assignable until we figure out how to handle fresh allocations
        JmlMethodSpecs mspecs = specs.getDenestedSpecs(methodDecl.sym); // FIXME - does this contain all inherited specs? it should
        if (mspecs == null) return; // FIXME - why would this happen?
        JCExpression sc;
        {
            sc = convertAssignable(scannedItem,targetThisId == null ? null : (VarSymbol)targetThisId.sym);
        }
        for (JmlSpecificationCase c : mspecs.cases) {
            JCExpression condition = checkAccess(token,callPosition, sc, c, baseThisId.sym,targetThisId == null ? null : targetThisId.sym);
            if (condition != treeutils.trueLit) {
                condition = treeutils.makeImplies(scannedItem.pos, precondition, condition);
                addAssert(callPosition,token == JmlToken.ASSIGNABLE ? Label.ASSIGNABLE : Label.ACCESSIBLE,condition,c,c.sourcefile,scannedItem.toString());
                // FIXME - do we also want to identify the position or identity of the scannedItem?
            }
        }
        // FIXME - do we need a default if there are no spec cases in the enclosing method?
    }
    

    /** Check that the given storeref is allowed by the given 
     * specification case, returning the condition under which the storeref
     * is allowed.
     * 
     * @param assignPosition the position of the generated expression
     * @param storeref the target to be checked if it may be assigned to (must not be a field wildcard)
     * @param specCase the specification case of the containing method against which to check
     * @param baseThisSym
     * @param targetThisSym
     */
    protected @Nullable
    JCExpression checkAccess(JmlToken token, DiagnosticPosition assignPosition, JCExpression storeref, JmlSpecificationCase specCase, Symbol baseThisSym, Symbol targetThisSym) {
        // If the storeref is a local identifier, then assignment is allowed
        if ((storeref instanceof JCIdent) && ((JCIdent)storeref).sym.owner instanceof Symbol.MethodSymbol) return treeutils.trueLit; 
        if (currentFresh != null && (storeref instanceof JCFieldAccess) && ((JCFieldAccess)storeref).sym == currentFresh.sym) return treeutils.trueLit; 

        JCIdent pre = preconditions.get(specCase);
        pre = pre == null ? null : treeutils.makeIdent(pre.pos, pre.sym); // a new id for the same symbol
        boolean anyAccessClauses = false;
        JmlMethodClause anyAssignableClause = null;
        JCExpression asg = treeutils.falseLit;
        asg = isFreshlyAllocated(assignPosition,storeref); // convertAssignable(storeref,(VarSymbol)baseThisSym)); // FIXME _ base or target
        for (JmlMethodClause mclause : specCase.clauses) {
            try {
                // FIXME - do we have to satisfy each assignable clause individually, or the union?
                if (mclause.token == token) {
                        // Is storeref allowed by some item in the parent method's list?
                        List<JCExpression> pstorerefs = ((JmlMethodClauseStoreRef)mclause).list;
                        for (JCExpression pstoreref: pstorerefs) {
                            JCExpression nasg = accessAllowed(storeref,pstoreref,(VarSymbol)baseThisSym,(VarSymbol)targetThisSym);
                            // optimizing asg = asg || nasg
                            asg = nasg == treeutils.trueLit ? nasg :
                                asg == treeutils.falseLit ? nasg :
                                    nasg == treeutils.falseLit ? asg :
                                        asg == treeutils.trueLit ? asg :
                                            treeutils.makeOr(storeref.pos,asg,nasg);
                        }
                        anyAccessClauses = true;
                }
                if (mclause.token == JmlToken.ASSIGNABLE && anyAssignableClause== null) anyAssignableClause = mclause;
            } catch (JmlNotImplementedException e) {
                notImplemented("assignable/accessible clause containing ",e); // FIXME - clause source
            }
        }
        // If there are no assignable clauses at all, 
        // then we use a default assignable clause;
        if (!anyAccessClauses) {
            List<JCExpression> pstorerefs;
            if (token == JmlToken.ACCESSIBLE && anyAssignableClause != null) {
                pstorerefs = ((JmlMethodClauseStoreRef)anyAssignableClause).list;
            } else if (methodDecl.sym.isConstructor()) {
                pstorerefs = defaultStoreRefs(specCase, methodDecl.sym);
            } else {
                pstorerefs = List.<JCExpression>of(M.JmlStoreRefKeyword(JmlToken.BSEVERYTHING));
            }
            try {
                for (JCExpression pstoreref: pstorerefs) {
                    JCExpression nasg = accessAllowed(storeref,pstoreref,(VarSymbol)baseThisSym,(VarSymbol)targetThisSym);
                    // optimizing asg = asg || nasg
                    asg = nasg == treeutils.trueLit ? nasg :
                        asg == treeutils.falseLit ? nasg :
                            nasg == treeutils.falseLit ? asg :
                                asg == treeutils.trueLit ? asg :
                                    treeutils.makeOr(storeref.pos,asg,nasg);
                }
            } catch (JmlNotImplementedException e) {
                notImplemented("assignable/accessible clause containing ",e); // FIXME - clause source
            }
        }
        if (asg != treeutils.trueLit && pre != null) {
            return treeutils.makeImplies(storeref.pos, pre, asg);
        } else {
            return asg;
        }
    }
    
    /** Returns an expression indicating whether the object being dereferenced in the storeref
     * is allocated now but was not in the prestate.
     */
    protected JCExpression isFreshlyAllocated(DiagnosticPosition pos, JCExpression storeref) {
        if (rac) return treeutils.falseLit; // FIXME - how do we handle this aspect of assignment checking in RAC.
//        if (storeref instanceof JmlStoreRefKeyword) return treeutils.falseLit;
//        if (storeref.type.tag == TypeTags.BOT || storeref.type.isPrimitive()) return treeutils.falseLit;
        
        JCExpression obj = null;
        if (storeref instanceof JCFieldAccess && !((JCFieldAccess)storeref).sym.isStatic()) obj = ((JCFieldAccess)storeref).selected;
        else if (storeref instanceof JCArrayAccess) obj = ((JCArrayAccess)storeref).indexed;
        else if (storeref instanceof JmlStoreRefArrayRange) obj = ((JmlStoreRefArrayRange)storeref).expression;
        else if (storeref instanceof JCIdent) obj = storeref;
        if (obj == null) return treeutils.falseLit;
        obj = convertJML(obj);  // FIXME - in some cases at least this is a second conversion
        obj = newTemp(obj);
        // FIXME - don't bother with the following if obj is 'this'
        JCExpression allocNow = M.at(pos).Select(obj, isAllocSym).setType(syms.booleanType);
        JCExpression allocOld = treeutils.makeOld(pos,M.at(pos).Select(convertCopy(obj), isAllocSym).setType(syms.booleanType));
        return treeutils.makeAnd(pos.getPreferredPosition(),allocNow,treeutils.makeNot(pos.getPreferredPosition(), allocOld));
    }

    /** Returns an expression indicating whether an object is allocated in the current state.
     */
    protected JCFieldAccess isAllocated(DiagnosticPosition pos, JCExpression obj) {
        //if (rac) return treeutils.falseLit; // FIXME - how do we handle this aspect of assignment checking in RAC.
        obj = convertJML(obj);
        return (JCFieldAccess)M.at(pos).Select(obj, isAllocSym).setType(syms.booleanType);
    }


    /** Expands any store-ref wildcard items, since they depend on the base location and visibility */
    // FIXME - should we expand data groups?
    protected List<JCExpression> expandStoreRefList(List<JCExpression> list, MethodSymbol base) {
        ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
        for (JCExpression item: list) {
            if (item instanceof JCFieldAccess && ((JCFieldAccess)item).name == null) {
                JCFieldAccess fa = (JCFieldAccess)item;
                // FIXME - use jml visibility (spec_public and spec_protected?)
                for (VarSymbol vsym : utils.listJmlVisibleFields((TypeSymbol)base.owner, base.flags() & Flags.AccessFlags, treeutils.isATypeTree(((JCFieldAccess)item).selected))) {
                    newlist.add(M.at(item).Select(fa.selected, vsym));
                }
            } else {
                newlist.add(item);
            }
        }
        return newlist.toList();
    }

    /** Returns the list of store-ref items corresponding to this.*  */
    // FIXME - should we expand data groups?
    protected List<JCExpression> defaultStoreRefs(DiagnosticPosition pos, MethodSymbol base) {
        ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
        for (VarSymbol vsym : utils.listJmlVisibleFields((TypeSymbol)base.owner, base.flags() & Flags.AccessFlags, utils.isJMLStatic(base))) {
            newlist.add(M.at(pos).Select(currentThisExpr, vsym));
        }
        return newlist.toList();
    }

    // FIXME - needs work
    @Override
    public void visitApply(JCMethodInvocation that) {
        //System.out.println("APPLY ENTER " + statementStack.size());
        // FIXME - needs result set - needs proper handling of pure methods etc.
        if (that.meth.toString().startsWith("System.out.")) {
            // We handle System.out.println specially. It is essentially pure and
            // does not depend on any class invariants, so we can safely just call it
            // after translating the arguments. This avoids bloat caused by putting
            // in debug statements. 
            List<JCExpression> args = convertExprList(that.args);
            JCMethodInvocation app = M.at(that).Apply(that.typeargs, that.meth, args).setType(that.type);
            app.varargsElement = that.varargsElement; // a Type
            result = eresult = app;
            return;
        }
//        if (inOldEnv && rac) {
//            String msg = "RAC does not currently implement method calls in \\old expressions: " + treeutils.getSym(that.meth);
//            notImplemented(that,msg);
//            throw new JmlNotImplementedException(that,msg);
//        }
        
        if (!translatingJML && !pureCopy) checkThatMethodIsCallable(that, treeutils.getSym(that.meth));
        if ((translatingJML && rac) || pureCopy) {
            // FIXME - need to check definedness by testing preconditions
            List<JCExpression> typeargs = convertExprList(that.typeargs);
            JCExpression meth = convertExpr(that.meth);
            List<JCExpression> args = convertExprList(that.args);
            JCMethodInvocation app = M.at(that).Apply(typeargs, meth, args).setType(that.type);
            app.varargsElement = that.varargsElement; // a Type
            result = eresult = app;
            return;
        }
        applyHelper(that);
    }
    
    protected void checkThatMethodIsCallable(DiagnosticPosition pos, Symbol sym) {
        // Method might be called in an initializer??? FIXME - what do we do then?
        // FIXME - not sure how to detect this
        if (methodDecl.body == null) return;
        
        // If there are no specification cases, then the default is that 
        // everything is callable
        for (JmlSpecificationCase specCase: specs.getDenestedSpecs(methodDecl.sym).cases) {
            JCIdent pre = preconditions.get(specCase);
            pre = pre == null ? null : treeutils.makeIdent(pre.pos, pre.sym); // a new id for the same symbol
            for (JmlMethodClause mclause : specCase.clauses) {
                try {
                    // We have to satisfy each callable clause individually
                    JCExpression asg = null;
                    if (mclause.token == JmlToken.CALLABLE) {
                        JmlMethodClauseCallable c = (JmlMethodClauseCallable)mclause;
                        if (c.keyword != null) {
                            if (c.keyword.token == JmlToken.BSNOTHING) {
                                asg = treeutils.falseLit;
                            } else if (c.keyword.token == JmlToken.BSEVERYTHING) {
                                asg = null;
                            }
                        } else {
                            asg = treeutils.falseLit;
                            for (JmlMethodSig sig: c.methodSignatures) {
                                if (sig.methodSymbol != sym) continue;
                                asg = null;
                                break;
                            }
                        }
                    }
                    // If there are no assignable clauses at all, 
                    // then we use a default assignable clause.
                    if (asg == null) {
                        // OK
                    } else { // asg is false
                        asg = treeutils.makeNot(mclause.pos, pre);
                        addAssert(pos,Label.CALLABLE,asg,mclause,specCase.sourcefile);
                    }
                } catch (JmlNotImplementedException e) {
                    notImplemented("callable clause containing ",e); // FIXME - clause source
                }
            }
        }
    }
    
    protected List<JCExpression> convertArgs(DiagnosticPosition pos, List<JCExpression> args, List<Type> argtypes, boolean hasVarArgs) {
        // Note: because the declaration may have a last varargs element,
        // args.size() may be greater than argtypes.size() But since everything
        // has typechecked OK, it is OK to implicitly use the last element of
        // argtypes for any additional args.
        ListBuffer<JCExpression> out = new ListBuffer<JCExpression>();
        Iterator<Type> iter = argtypes.iterator();
        boolean last = false;
        Type currentArgType = null;
        boolean usedVarArgs = args.size() == 0 && argtypes.size() != 0 && hasVarArgs;
        for (JCExpression a: args) {
            a = convertExpr(a);
            if (iter.hasNext()) currentArgType = iter.next(); // handles varargs
            last = !iter.hasNext();
            if (last && hasVarArgs && !(a.type instanceof Type.ArrayType)) {
                currentArgType = ((Type.ArrayType)argtypes.last()).getComponentType();
                a = addImplicitConversion(a,currentArgType,a);
                usedVarArgs = true;
            } else {
                a = addImplicitConversion(a,currentArgType,a);
            }
            if (useMethodAxioms && translatingJML) {
            } else if ((a instanceof JCIdent) && ((JCIdent)a).name.toString().startsWith(Strings.tmpVarString)) {
            } else if ((a instanceof JCIdent) && localVariables.containsKey(((JCIdent)a).sym)) {
            } else if (!localVariables.isEmpty()) {
            } else {
                // This check is a hack and a bit expensive. It makes sure that
                // every argument is represented by a temporary variable. 
                // Without this an argument that is just an Ident or a Literal
                // and is not used ends up without its value captured for
                // tracing
                a = newTemp(a);
            }
            out.add(a);
        }
        if (usedVarArgs) {
            ListBuffer<JCExpression> newout = new ListBuffer<JCExpression>();
            int n = argtypes.length() - 1;
            while (--n >= 0) {
                newout.add(out.remove());
            }
            // create an array with the rest
            currentArgType = ((Type.ArrayType)argtypes.last()).getComponentType();
            List<JCExpression> dims = List.<JCExpression>nil(); // FIXME - what if the array is multi-dimensional
            int p = pos.getPreferredPosition();
            JCExpression t = treeutils.makeType(p,currentArgType);
            JCExpression e = M.at(p).NewArray(t, dims, out.toList());
            e.type = argtypes.last();
            if (esc) e = convertExpr(e);
            newout.add(newTemp(e)); // FIXME - see comment above about newTemp
            out = newout;
        }
        return out.toList();
    }
    
    static public boolean useMethodAxioms = false;

    public java.util.List<Symbol> completedInvariants = new LinkedList<Symbol>();
    public java.util.Set<Symbol> inProcessInvariants = new HashSet<Symbol>();
    
    protected boolean startInvariants(Symbol csym, DiagnosticPosition pos) {
        if (completedInvariants.contains(csym)) return true; // skip processing
        if (inProcessInvariants.add(csym)) return false; // ok to do processing
        log.error(pos, "jml.recursive.invariants", csym.getQualifiedName());
        return true; // skip processing
    }
    
    protected boolean startInvariantsNoError(Symbol csym, DiagnosticPosition pos) {
        if (completedInvariants.contains(csym)) return true; // skip processing
        if (inProcessInvariants.add(csym)) return false; // ok to do processing
        return true; // skip processing
    }
    
    protected void endInvariants(Symbol csym) {
        inProcessInvariants.remove(csym);
        completedInvariants.add(csym);
    }
    
    protected void clearInvariants() {
        completedInvariants.clear();
        inProcessInvariants.clear();
    }
    
    protected void changeState() {
        ++heapCount;
        clearInvariants();
    }
    
    protected JCIdent currentFresh = null;
    
    /** Helper method to do the work of visitApply and visitNewObject */
    protected void applyHelper(JCExpression that) {
        
        JCExpression savedCondition = condition; // This is the logical context in which this method is called - only used for JML expressions
        /*@ nullable */ Symbol savedSym = resultSym; // This is the symbol of the JCIdent representing the result of the method call, null if the method is void
        /*@ nullable */ Symbol savedExceptionSym = exceptionSym; // The symbol that holds the actifve exception (or null) // FIXME - doesnot get changed so why save it?
        /*@ nullable */ JCIdent savedThisId = currentThisId; // The JCIdent holding what 'this' means in the current context
        /*@ nullable */ JCExpression savedThisExpr = currentThisExpr; // The JCIdent holding what 'this' means in the current context
        Map<Symbol,JCExpression> savedParamActuals = paramActuals; // Mapping from formal parameter symbols to the actual arguments
          // A map in which to save paramActuals for each overridden method
        Map<Symbol,Map<Symbol,JCExpression>> mapParamActuals = new HashMap<Symbol,Map<Symbol,JCExpression>>();
        Map<Symbol,JCVariableDecl> savedpreparams = preparams;
        ListBuffer<JCStatement> savedOldStatements = oldStatements;
        JCIdent savedFresh = currentFresh;
        JCIdent savedPreLabel = preLabel;
        Symbol savedEnclosingMethod = enclosingMethod;
        Symbol savedEnclosingClass = enclosingClass;
        
        boolean isSuper = false;
        
        if (methodDecl.sym.toString().contains("defaultValues") && that.toString().contains("add")) Utils.print("");
        
        /*@ nullable */ JCVariableDecl exceptionDeclCall = 
                translatingJML && esc? null : treeutils.makeVarDef(syms.exceptionType, exceptionNameCall, methodDecl.sym, that.pos);
        
        
        try {
            // Translate the method name, and determine the thisid for the
            // method call
            
            JCIdent newThisId = null; // The translated receiver
            JCExpression newThisExpr = null; // The translated receiver
            List<JCExpression> trArgs; // The translated arguments
            List<JCExpression> typeargs; // The translated type arguments
            /*@ nullable*/ JCExpression meth = null; // the qualified method name, if this is a method call
            /*@ nullable*/ JCMethodInvocation apply = null; // non-null if this is a method call
            /*@ nullable*/ JCNewClass newclass = null; // non-null if this a new object call
            
            MethodSymbol calleeMethodSym = null; // The method symbol of the callee method or constructor
            
            if (that instanceof JCMethodInvocation) {
                apply = (JCMethodInvocation)that;
                meth = apply.meth;
                trArgs = apply.args;
                typeargs = apply.typeargs;
            } else if (that instanceof JCNewClass) {
                newclass = (JCNewClass) that;
                trArgs = newclass.args;
                typeargs = newclass.typeargs;
            } else {
                error(that,"Invalid argument type for JmlAssertionAdder.applyHelper");
                return;
            }

            // FIXME - do we need to convert the varargsElement or its associated expressions
            // Convert all the expressions
            // There is duplicate code because we have to be sure to evaluate everything in order
            JCExpression trExpr = null; // Holds the translated method call (for RAC)
            
            if (meth instanceof JCIdent) {
                JCIdent id = (JCIdent)meth; // There is no conversion for method names
                if (utils.isJMLStatic(id.sym)) meth = convertExpr(meth); 
                isSuper = id.name.equals(names._super);
                
                typeargs = convert(typeargs);
                trArgs = convertArgs(that, trArgs,meth.type.asMethodType().argtypes, (id.sym.flags() & Flags.VARARGS) != 0 );

                calleeMethodSym = (MethodSymbol)id.sym;

                JCMethodInvocation mExpr = M.at(that).Apply(typeargs,meth,trArgs);
                mExpr.setType(that.type);
                mExpr.varargsElement = null; // We have combined the arargs elements into an array
                trExpr = mExpr;
                newThisExpr = newThisId = utils.isJMLStatic(id.sym) ? null : newTemp(currentThisExpr);
                enclosingMethod = id.sym;
                enclosingClass = id.sym.owner;
                
            } else if (meth instanceof JCFieldAccess) {
                JCFieldAccess fa = (JCFieldAccess)meth;
                JCExpression convertedReceiver = convertExpr(fa.selected);
                if (!utils.isJMLStatic(fa.sym)) {
                    if (translatingJML && (fa.selected instanceof JCIdent && localVariables.containsKey(((JCIdent)fa.selected).sym))) {
                        // Local variables are presumed non-null
                        newThisExpr = newTemp(convertedReceiver);
                        newThisId = (JCIdent)newThisExpr;
                    } else {
                        newThisExpr = newTemp(convertedReceiver);
                        newThisId = (JCIdent)newThisExpr;
                        if (javaChecks) {
                            // Check that receiver is not null
                            JCExpression e = treeutils.makeNeqObject(fa.selected.pos,newThisExpr,treeutils.nullLit);
                            addAssert(fa,
                                    translatingJML? Label.UNDEFINED_NULL_DEREFERENCE : Label.POSSIBLY_NULL_DEREFERENCE,e);
                        }
                    }
                }

                typeargs = convert(typeargs);
                trArgs = convertArgs(that, trArgs,meth.type.asMethodType().argtypes,  (fa.sym.flags() & Flags.VARARGS) != 0);

                JCFieldAccess fameth = (JCFieldAccess)M.at(meth.pos).Select(
                        !utils.isJMLStatic(fa.sym) ? newThisExpr : convertedReceiver, fa.sym);
                calleeMethodSym = (MethodSymbol)fa.sym;
                
                JCMethodInvocation mExpr = M.at(that).Apply(typeargs,fameth,trArgs);
                mExpr.setType(that.type);
                mExpr.varargsElement = null; // We have combined the arargs elements into an array
                trExpr = mExpr; // rewritten expression - for RAC
                enclosingMethod = fa.sym;
                enclosingClass = fa.sym.owner;
                
            } else if (newclass != null) {
                
                // FIXME - this does not handle quantified constructors of inner classes
                
                calleeMethodSym = (MethodSymbol)newclass.constructor;
                enclosingMethod = calleeMethodSym;
                enclosingClass = calleeMethodSym.owner;
                
                JCExpression convertedReceiver = convertExpr(newclass.encl);
                if (javaChecks && convertedReceiver != null && !treeutils.isATypeTree(convertedReceiver)) {
                    // Check that receiver is not null
                    JCExpression e = treeutils.makeNeqObject(newclass.encl.pos,convertedReceiver,treeutils.nullLit);
                    addAssert(newclass.encl,
                            translatingJML? Label.UNDEFINED_NULL_DEREFERENCE : Label.POSSIBLY_NULL_DEREFERENCE,e);
                }

                typeargs = convert(typeargs);
                trArgs = convertArgs(that, trArgs,calleeMethodSym.type.asMethodType().argtypes,  (calleeMethodSym.flags() & Flags.VARARGS) != 0);

                JCNewClass expr = M.at(that).NewClass(
                        convertedReceiver,
                        typeargs, 
                        convert(newclass.clazz), 
                        trArgs, 
                        convert(newclass.def));
                expr.constructor = newclass.constructor;
                expr.constructorType = newclass.constructorType;
                expr.varargsElement =  null; // We have combined the arargs elements into an array
                expr.setType(that.type);
                trExpr = expr;
                
                // newThisId, newThisExpr are assigned the resultId later - can only be used in post-conditions
            } else {
                error(that,"Unknown alternative in interpreting method call");
                return;
            }
            
            java.util.List<MethodSymbol> overridden = utils.parents(calleeMethodSym);
            
            /** We can either try to keep subexpressions as subexpressions, or break
             * them out into statements with temporary variables. Java code is
             * broken into statements so that side-effects can be handled sstraightforwardly.
             * Quantified expressions have to be kept as sub-expressions.
             * Other JML expressions can be handled either way - the 'doTranslations'
             * variable indicates what mode we are in: true means use subexpresions
             * We currently expand non-quantified JML statements because
             * method calls in JML expressions are easier to handle.
             */
            boolean doTranslations = rac || !translatingJML || (!useMethodAxioms &&  localVariables.isEmpty());
            if (!doTranslations) {
                JCExpression heap = treeutils.makeIntLiteral(that.pos,heapCount);
                List<JCExpression> ntrArgs = trArgs;
                if (useMethodAxioms) {
                    if (!utils.isJMLStatic(calleeMethodSym)) {
                        ntrArgs = ntrArgs.prepend(currentThisExpr);
                    }
                    ntrArgs = ntrArgs.prepend(heap); // only if heap dependent
                    addStat(addMethodAxioms(that,calleeMethodSym,overridden));
                    
                    MethodSymbol s = wellDefinedCheck.get(calleeMethodSym);
                    if (s != null && localVariables.isEmpty()) {
                        JCExpression e = treeutils.makeMethodInvocation(that,null,s,ntrArgs);
                        addAssert(that,Label.UNDEFINED_PRECONDITION,e);
                    }
                    
                    MethodSymbol newCalleeSym = pureMethod.get(calleeMethodSym);

                    result = eresult = treeutils.makeMethodInvocation(that,null,newCalleeSym,ntrArgs);
                } else {
                    if (utils.isJMLStatic(calleeMethodSym)) {
                        result = eresult = trExpr;
                    } else {
                        result = eresult = treeutils.makeMethodInvocation(that,newThisExpr,calleeMethodSym,trArgs);
                    }
                }
                
                
                return;
            }


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
                if (esc && !doTranslations) {
                    result = eresult = trExpr; // FIXME - for now skip all the checking of preconditions etc - we are in the middle of a quantified expression
                    return;
                } else if (rac) {
                    resultId = newTempNull(that,resultType); // initialized to null
                    currentFresh = resultId;
                } else if (newclass == null) {
                    resultId = newTemp(that,resultType);
                } else {
                    JCVariableDecl decl = treeutils.makeVarDef(that.type,names.fromString(Strings.newObjectVarString + that.pos), null, that.pos);
                    addStat(decl);
                    resultId = treeutils.makeIdent(that.pos, decl.sym);
                }
            }
            
            resultSym = resultId == null ? null : resultId.sym;
            if (newclass != null) {
                newThisId = resultId;
                newThisExpr = resultId;
                // FIXME - what about newclass.encl
            }
            
            if (esc && newclass != null) {
                addAssume(that,Label.IMPLICIT_ASSUME,treeutils.makeNeqObject(that.pos, convertCopy(resultId), treeutils.nullLit));
//                JCExpression tt = null;
//                for (ClassSymbol sym : utils.parents((ClassSymbol)newclass.type.tsym)) {
//                    JCExpression ttt = M.at(that).TypeTest(convertCopy(resultId), treeutils.makeType(newclass.pos, sym.type));
//                    tt = tt == null ? ttt : treeutils.makeAnd(newclass.pos, tt, ttt);
//                }
//                addAssume(that,Label.IMPLICIT_ASSUME,tt);
                
                JmlMethodInvocation typeof = M.at(that).JmlMethodInvocation(JmlToken.BSTYPEOF, convertCopy(resultId));
                //typeof.type = 
                JmlMethodInvocation stype = M.at(that).JmlMethodInvocation(JmlToken.BSTYPELC, convert(newclass.clazz));
                //stype.type = 
                addAssume(that,Label.IMPLICIT_ASSUME,treeutils.makeEqObject(that.pos, typeof, stype));
                typeof = M.at(that).JmlMethodInvocation(JmlToken.BSTYPEOF, convertCopy(resultId));
                typeof.javaType = true;
                //typeof.type = 
                stype = M.at(that).JmlMethodInvocation(JmlToken.BSTYPELC, convert(newclass.clazz));
                stype.javaType = true;
                //stype.type = 
                addAssume(that,Label.IMPLICIT_ASSUME,treeutils.makeEqObject(that.pos, typeof, stype));

                if (resultId != null && !resultId.type.isPrimitive()) newAllocation1(that,resultId);
            }
            
            // FIXME - don't duplicate what is in visitLabelled
            pushBlock(); // FIXME - needs a try block?
            Name calllabel = null;
            if (!translatingJML) {
                JCBlock bl = M.at(that).Block(0L, List.<JCStatement>nil());
                String label = "_JMLCALL_" + that.pos + "_" + (++count);
                calllabel = names.fromString(label);
                JCLabeledStatement stat = (M.at(that).Labelled(calllabel,bl));
                addStat(stat);
                preLabel = M.at(that).Ident(calllabel);
                
                labelOldLists.put(calllabel,  currentStatements);
                oldStatements = currentStatements;
                defaultOldLabel = calllabel;
                
                markLocation(calllabel,currentStatements,stat);
            }
            
            ListBuffer<JCStatement> saved = currentStatements;
            oldStatements = currentStatements; // FIXME - why twice
            
            if (!isHelper(calleeMethodSym)) {
                addStat(comment(that, "Checking caller invariants before calling method " + utils.qualifiedMethodSig(calleeMethodSym)));
                if (!(meth instanceof JCIdent && ((JCIdent)meth).name.equals(names._super))) {
                    addInvariants(that,savedEnclosingClass.type.tsym,
                            savedEnclosingMethod == null || savedEnclosingMethod.isStatic() || savedEnclosingMethod.isConstructor() ? null : currentThisExpr,
                            currentStatements,
                            false,methodDecl.sym.isConstructor(),isSuper,isHelper(methodDecl.sym),false,false,Label.INVARIANT_EXIT_CALLER,  "(Caller: " + utils.qualifiedMethodSig(methodDecl.sym) + ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");
                            //utils.qualifiedMethodSig(methodDecl.sym) + " " + utils.qualifiedMethodSig(calleeMethodSym)); // FIXME - do we really do post here and below
                }
                // Note that methodDecl.params will be null for initalizer blocks
                if (methodDecl.params != null) for (JCVariableDecl v: methodDecl.params) {
                    if (v.type.isPrimitive()) continue;
                    // FIXME - it is an open question which invariants to check here - in principle all invariants must hold - but which might not? - need the pack/unpack capability
                    // FIXME - for now we check the invariants of the parameters in the prestate
                    JCVariableDecl d = preparams.get(v.sym);
                    JCIdent id = treeutils.makeIdent(v.pos,d.sym);
                    addStat(comment(v, "Checking invariants for caller parameter " + v.sym + " before calling method " + utils.qualifiedMethodSig(calleeMethodSym)));
                    addInvariants(v,v.type.tsym,id,currentStatements,
                            false,false,false,false,false,false,Label.INVARIANT_EXIT_CALLER, "(Parameter: " + v.sym + ", Caller: " + utils.qualifiedMethodSig(methodDecl.sym) + ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");
                }
            }

            ClassSymbol calleeClass = (ClassSymbol)calleeMethodSym.owner;
            JCExpression collectedInvariants = treeutils.trueLit; // FIXME - do we need this - do we include this in the 'condition' ?
            
            if (!isSuper && !isHelper(calleeMethodSym)) {   // Iterate through parent classes and interfaces, adding relevant invariants
                String msg = utils.qualifiedMethodSig(calleeMethodSym) + " from " + utils.qualifiedMethodSig(methodDecl.sym);
                addStat(comment(that, "Checking callee invariants by the caller " + utils.qualifiedMethodSig(methodDecl.sym) + " before calling method " + utils.qualifiedMethodSig(calleeMethodSym)));
                addInvariants(that,calleeClass,newThisExpr,currentStatements,
                        false,calleeMethodSym.isConstructor(),false,isHelper(calleeMethodSym),false,false,Label.INVARIANT_ENTRANCE,msg);
                for (JCExpression arg: trArgs) {
                    if (arg.type.isPrimitive()) continue;
                    currentStatements.add(comment(arg, "Asserting invariants for callee parameter before calling the callee " + utils.qualifiedMethodSig(calleeMethodSym)));
                    JCIdent id = (JCIdent)arg;
                    addInvariants(id,arg.type.tsym,id,currentStatements,
                            false,false,false,false,false,false,Label.INVARIANT_ENTRANCE,msg);
                }
            }
            
            currentThisId = newThisId;
            currentThisExpr = newThisExpr;

            // A map to hold the preconditions, indexed by specification case
            Map<JmlSpecificationCase,JCExpression> preExpressions = new HashMap<JmlSpecificationCase,JCExpression>();
            
            // Collects the complete precondition over all specification cases
            JCExpression combinedPrecondition = treeutils.falseLit;
            
            // Identify the clause to point to as the associated declaration if the precondition fails.
            // The combinedPrecondition may be an OR of many specification cases,
            // each of which may be an AND of clauses - so if the precondition is
            // false, every specification case is false.
            JmlMethodClauseExpr clauseToReference = null;

            boolean anyFound = false;
            for (MethodSymbol mpsym: overridden) {
                JmlMethodSpecs s = specs.getDenestedSpecs(mpsym);
                if (s != null && !s.cases.isEmpty()) {
                    anyFound = true;
                    break;
                }
            }
            if (!anyFound) {
                // No specs - set default

                JmlSpecs.MethodSpecs s = specs.getSpecs(calleeMethodSym);
                if (s == null) {
                    JmlMethodSpecs defaults = JmlSpecs.defaultSpecs(context,methodDecl.sym,methodDecl.pos).cases;
                    s = new JmlSpecs.MethodSpecs(methodDecl.mods,defaults);
                    specs.putSpecs(calleeMethodSym, s);
                    s.cases.deSugared = defaults;  
                } else {
                    JmlMethodSpecs defaults = JmlSpecs.defaultSpecs(context,s.cases.decl.sym,s.cases.decl.pos).cases;
                    s.cases = defaults;
                    s.cases.deSugared = defaults;  
                }
            }
            
            // Iterate over all specs to find preconditions, with the callee
            // method itself last
            {
                addStat(comment(that, "Checking preconditions of callee " + calleeMethodSym + " by the caller"));
                for (MethodSymbol mpsym: overridden) {
                    // This initial logic must match that below for postconditions

                    JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
                    if (calleeSpecs == null) continue; // FIXME - not sure about this - should get a default?

                    paramActuals = new HashMap<Symbol,JCExpression>();
                    mapParamActuals.put(mpsym,paramActuals);
                    
                    if (calleeSpecs.decl != null) {
                        Iterator<JCVariableDecl> iter = calleeSpecs.decl.params.iterator();
                        JCVariableDecl currentDecl = null;
                        for (JCExpression arg: trArgs) {
                            if (iter.hasNext()) currentDecl = iter.next();
                            paramActuals.put(currentDecl.sym, arg);
                        }
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
                        if (typeargs != null && !typeargs.isEmpty()) {
                            Iterator<Symbol.TypeSymbol> tpiter = calleeMethodSym.getTypeParameters().iterator();
                            for (JCExpression tp: typeargs ) {
                                paramActuals.put(tpiter.next(), tp);
                            }
                        }
                    }

                    // FIXME - should this really be before the preconditions computations - it does have to be before the assignable computations.
                    if (esc && (!utils.isPure(calleeMethodSym) || newclass != null) && resultId != null && !resultType.isPrimitive()) {
                        JCTree cs = that;
                        JCFieldAccess x = (JCFieldAccess)M.at(cs.pos).Select(null,isAllocSym);
                        JCStatement havoc = M.at(cs.pos).JmlHavocStatement(List.<JCExpression>of(x));
                        addStat(havoc);  // havoc *.isAllocSym
                        {
                            JCVariableDecl d = newTempDecl(cs, syms.objectType);
                            JCIdent id = treeutils.makeIdent(cs.pos, d.sym);
                            JCExpression eold = treeutils.makeOld(cs.pos, treeutils.makeSelect(cs.pos, id, isAllocSym), 
                                    oldenv);
                            id = convertCopy(id);
                            JCExpression enew = treeutils.makeSelect(cs.pos, id, isAllocSym);
                            JCExpression f = M.at(cs).JmlQuantifiedExpr(JmlToken.BSFORALL, List.<JCVariableDecl>of(d), eold, enew);
                            addAssume(cs,Label.IMPLICIT_ASSUME,f);
                        }
                        newAllocation2(that,resultId);
                    }

                    // For each specification case, we accumulate the precondition
                    // and we create a block that checks the assignable statements
                    for (JmlSpecificationCase cs : calleeSpecs.cases) {
                        if (!utils.visible(classDecl.sym, mpsym.owner, cs.modifiers.flags/*, methodDecl.mods.flags*/)) continue;
                        JCIdent preId = null;
                        if (rac) {
                            preId = newTemp(treeutils.falseLit);
                            pushBlock();
                        }
                        JCExpression pre = translatingJML ? convertCopy(savedCondition) : treeutils.trueLit;
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
                            notImplemented("requires clause containing ",e); // FIXME - clause source
                            pre = treeutils.falseLit;
                        }
                        if (rac) { // FIXME - not sure why this fails for esc (see rac-guarded statements above as well)
                            preId.pos = pre.pos;
                            addStat(treeutils.makeAssignStat(pre.pos,convertCopy(preId),pre));
                            addStat(wrapRuntimeException(pre,popBlock(0L,pre),
                                    "JML undefined precondition - exception thrown",
                                    null));
                            pre = preId;
                        } else {
                            pre = newTemp(pre);
                        }
                        preExpressions.put(cs,pre); // Add to the list of spec cases, in order of declaration
                        combinedPrecondition = combinedPrecondition == treeutils.falseLit ? pre : treeutils.makeOr(pre.pos, combinedPrecondition, pre);
                        if ((!translatingJML || rac) && methodDecl != null && methodDecl.sym != null) {  // FIXME - not quite sure of this guard // FIXME - what should we check for field initializers
                            // Handle assignable & accessible clauses
                            pushBlock(); // A block for assignable and accessible tests
                            boolean anyAssignableClauses = false;
                            boolean anyAccessibleClauses = false;
                            for (JmlMethodClause clause : cs.clauses) {
                                // We iterate over each storeref item in each assignable clause
                                // of each specification case of the callee - for each item we check
                                // that assigning to it (under the appropriate preconditions)
                                // is allowed by each of the specification cases of the caller specs.
                                try {
                                    if (clause.token == JmlToken.ASSIGNABLE) {
                                        List<JCExpression> storerefs = expandStoreRefList(((JmlMethodClauseStoreRef)clause).list,calleeMethodSym);
                                        for (JCExpression item: storerefs) {
                                            addStat(comment(item,"Is " + item + " assignable?"));
                                            checkAgainstCallerSpecs(clause.token, that, item ,pre, savedThisId, newThisId);
                                        }
                                        anyAssignableClauses = true;
//                                    } else if (clause.token == JmlToken.ACCESSIBLE) {
//                                        List<JCExpression> storerefs = expandStoreRefList(((JmlMethodClauseStoreRef)clause).list,calleeMethodSym);
//                                        for (JCExpression item: storerefs) {
//                                            addStat(comment(item,"Is " + item + " accessible?"));
//                                            checkAgainstCallerSpecs(clause.token, that, item ,pre, savedThisId, newThisId);
//                                        }
//                                        anyAccessibleClauses = true;
                                    } else if (clause.token == JmlToken.CALLABLE) {
                                        List<JCExpression> storerefs = expandStoreRefList(((JmlMethodClauseStoreRef)clause).list,calleeMethodSym);
                                        for (JCExpression item: storerefs) {
                                            addStat(comment(item,"Is " + item + " callable?"));
                                            checkThatMethodIsCallable(item, treeutils.getSym(item));
                                        }
                                    }
                                } catch (NoModelMethod e) {
                                    // continue // FIXME - warn?
                                } catch (JmlNotImplementedException e) {
                                    notImplemented(clause.token.internedName() + " clause containing ",e); // FIXME - clause source
                                }
                            }
                            if (!anyAssignableClauses) {
                                // If there are no assignable clauses in the spec case, use a default
                                if (mpsym.isConstructor()) {
                                    // But the default for a constructor call the fields of the constructor
                                    // and the fields of the constructor are allowed to be assigned in any case
                                    // So there is nothing to check
                                    
//                                    for (JCExpression item: defaultStoreRefs(cs,mpsym)) {
//                                        checkAgainstCallerSpecs(that, convertJML(item),pre, savedThisId, newThisId);
//                                    }

                                } else {
                                    // the default is \\everything
                                    checkAgainstCallerSpecs(JmlToken.ASSIGNABLE, that, M.at(cs).JmlStoreRefKeyword(JmlToken.BSEVERYTHING),pre, savedThisId, newThisId);
                                }
                            }
//                            if (!anyAccessibleClauses) {
//                                // If there are no accessible clauses in the spec case, use a default
//                                if (mpsym.isConstructor()) {
//                                    // But the default for a constructor call the fields of the constructor
//                                    // and the fields of the constructor are allowed to be assigned in any case
//                                    // So there is nothing to check
//                                    
////                                    for (JCExpression item: defaultStoreRefs(cs,mpsym)) {
////                                        checkAgainstCallerSpecs(that, convertJML(item),pre, savedThisId, newThisId);
////                                    }
//
//                                } else {
//                                    // the default is \\everything
//                                    checkAgainstCallerSpecs(JmlToken.ACCESSIBLE, that, M.at(cs).JmlStoreRefKeyword(JmlToken.BSEVERYTHING),pre, savedThisId, newThisId);
//                                }
//                            }
                            JCBlock bl = popBlock(0,cs); // Ending the assignable tests block
                            if (!bl.stats.isEmpty()) addStat( M.at(cs).If(pre, bl, null) );
                        }
                    }
                    paramActuals = null;
                }
                if (clauseToReference != null) {
                    pushBlock();
                    if (translatingJML) {
                        //JCExpression conj = treeutils.makeAnd(methodDecl.pos, collectedInvariants, combinedPrecondition);
                        addAssert(that,Label.UNDEFINED_PRECONDITION,
                                treeutils.makeImplies(methodDecl.pos, condition, combinedPrecondition),
                                clauseToReference,clauseToReference.source());

                    } else {
                        addAssert(that,Label.PRECONDITION,
                                combinedPrecondition,
                                clauseToReference,clauseToReference.source());
                    }
                    JCBlock bl = popBlock(0,that);
                    addStat( wrapRuntimeException(that, bl, 
                            "JML undefined precondition - exception thrown",
                            null));
                }
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
                if (apply != null) addStat(comment(apply,"converted method call"));
                if (newclass != null) addStat(comment(newclass,"converted new-object call"));

                JCStatement call;
                if (newclass != null) {
                    addStat(treeutils.makeAssignStat(that.pos, resultId, trExpr));
                    trExpr = resultId;
//                    currentThisId = newThisId = resultId;
//                    currentThisExpr = newThisExpr = resultId;
//                    addAssume(that,Label.IMPLICIT_ASSUME,
//                            treeutils.makeNeqObject(that.pos,resultId,treeutils.nullLit));
                } else if (isVoid) {
                    call = M.at(that).Exec(trExpr);
                    addStat(call);
                } else {
                    call = treeutils.makeAssignStat(that.pos, resultId, trExpr);
                    addStat(call);
                }
                currentStatements = s;
            }

            ensuresStatsOuter.add(comment(that,"Assuming callee normal postconditions"));
            exsuresStatsOuter.add(comment(that,"Assuming callee exceptional postconditions"));

            if (doTranslations) {

                if (exceptionSym != null && exceptionDeclCall != null) {
                    exsuresStatsOuter.add(
                            treeutils.makeAssignStat(
                                    that.pos,
                                    treeutils.makeIdent(that.pos, exceptionSym),
                                    treeutils.makeIdent(that.pos, exceptionDeclCall.sym)));
                }
                
                // TERMINATION
                // The termination symbol will be null if a method call is present in class-level declaration
                // FIXME - not sure what precisely should be done - should we declare a termination symbol in this case? RAC probably needs it.
                if (terminationSym != null) {
                    JCIdent tid = treeutils.makeIdent(that.pos,terminationSym);
                    JCStatement term = treeutils.makeAssignStat(that.pos,tid,treeutils.makeIntLiteral(that.pos,-that.pos));
                    exsuresStatsOuter.add(term);
                }
                
                {
                    // This states the allowed types of any exception according to the
                    // Java declaration
                    if (exceptionSym != null) { // FIXME - what situation has this symbol null?
                        ListBuffer<JCStatement> s = currentStatements;
                        currentStatements = exsuresStatsOuter;
                        if (utils.isPure(calleeMethodSym)) {
                            addAssume(that, Label.IMPLICIT_ASSUME,treeutils.falseLit);
                        } else {
                            JCIdent exceptionId = treeutils.makeIdent(that.pos,exceptionSym);
                            JCExpression expr = treeutils.makeThrownPredicate(that, exceptionId, calleeMethodSym);
                            addAssume(that, Label.IMPLICIT_ASSUME,expr);
                        }
                        currentStatements = s;
                    }
                }
                
            }

            if (esc) {
                // Now we iterate over all specification cases in all parent
                // methods again, this time putting in the assignable havoc statements

                for (MethodSymbol mpsym: overridden) {
                    // This initial logic must match that above for preconditions
                    JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
                    if (calleeSpecs == null) continue; // FIXME - not sure about this

                    paramActuals = mapParamActuals.get(mpsym);

                    // FIXME - we should set condition
                    // Be sure to do assignable (havoc) clauses before the invariant and postcondition clauses
                    for (JmlSpecificationCase cs : calleeSpecs.cases) {
                        if (!utils.visible(classDecl.sym, mpsym.owner, cs.modifiers.flags/*, methodDecl.mods.flags*/)) continue;
                        JCExpression pre = convertCopy(preExpressions.get(cs));
                        if (pre == treeutils.falseLit) continue; // Don't bother with postconditions if corresponding precondition is explicitly false 
                        condition = pre; // FIXME - is this right? what about the havoc statement?
                        pushBlock();
                        boolean useDefault = true;
                        for (JmlMethodClause clause : cs.clauses) {
                            try {
                                JmlToken token = clause.token;
                                switch (token) {
                                    case ASSIGNABLE:
                                        useDefault = false;
                                        addStat(comment(clause));
                                        ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
                                        for (JCExpression location: (((JmlMethodClauseStoreRef)clause).list)) {
                                            location = convertAssignable(location,newThisId == null ? null : (VarSymbol)newThisId.sym);
                                            if (!(location instanceof JCFieldAccess)) { newlist.add(location); continue; }
                                            JCFieldAccess fa = (JCFieldAccess)location;
                                            if (fa.sym == null) {
                                                JCExpression e = fa.selected;
                                                boolean isStatic = treeutils.isATypeTree(e);
                                                for (VarSymbol v: utils.listJmlVisibleFields(e.type.tsym, calleeMethodSym.flags()&Flags.AccessFlags, isStatic)) {
                                                    JCFieldAccess newfa = treeutils.makeSelect(location.pos, e, v);
                                                    JCExpression trfa= convertJML(newfa);
                                                    newlist.add(trfa);
                                                }
                                            } else if (isModel(fa.sym)){
                                                JCExpression e = fa.selected;
                                                boolean isStatic = treeutils.isATypeTree(e);
                                                for (VarSymbol v: utils.listJmlVisibleFields(e.type.tsym, Flags.PRIVATE, isStatic)) {
                                                    if (!isModel(v) && isContainedIn(v,(VarSymbol)fa.sym)) { 
                                                        JCFieldAccess newfa = treeutils.makeSelect(location.pos, e, v);
                                                        JCExpression trfa= convertJML(newfa);
                                                        newlist.add(trfa);
                                                    }
                                                }
                                            } else {
                                                newlist.add(location); 
                                                continue;
                                            }
                                        }
                                        JCStatement havoc = M.at(clause.pos).JmlHavocStatement(newlist.toList());
                                        addStat(havoc);
                                        break;
                                    default:
                                        // skip everything else
                                        break;
                                }
                            } catch (JmlNotImplementedException e) {
                                notImplemented(clause.token.internedName() + " clause containing ",e, clause.source());
                            }
                        }
                        if (useDefault) {
                            if (newclass == null) {
                                // default for non- constructor call is \everything
                                JCStatement havoc = M.at(cs.pos).JmlHavocStatement(List.<JCExpression>of(M.at(cs.pos).JmlStoreRefKeyword(JmlToken.BSEVERYTHING)));
                                addStat(havoc);
                            } else {
                                // default for constructor call is this.*
                                JCStatement havoc = M.at(cs.pos).JmlHavocStatement(defaultStoreRefs(that,(MethodSymbol)newclass.constructor));
                                addStat(havoc);
                            }
                        }

                        JCBlock bl = popBlock(0,cs);
                        JCStatement st = M.at(cs.pos+1).If(pre,bl,null);
                        bl = M.at(cs.pos+1).Block(0,List.<JCStatement>of(st));
                        currentStatements.add( wrapRuntimeException(cs, bl, "JML undefined precondition while checking postconditions - exception thrown", null));

//                        if (esc && (!utils.isPure(calleeMethodSym) || newclass != null) && resultId != null && !resultType.isPrimitive()) {
//                            JCFieldAccess x = (JCFieldAccess)M.at(cs.pos).Select(null,isAllocSym);
//                            JCStatement havoc = M.at(cs.pos).JmlHavocStatement(List.<JCExpression>of(x));
//                            addStat(havoc);  // havoc *.isAllocSym
//                            {
//                                JCVariableDecl d = newTempDecl(cs, syms.objectType);
//                                JCIdent id = treeutils.makeIdent(cs.pos, d.sym);
//                                JCExpression eold = treeutils.makeOld(cs.pos, treeutils.makeSelect(cs.pos, id, isAllocSym), 
//                                        oldenv);
//                                id = convertCopy(id);
//                                JCExpression enew = treeutils.makeSelect(cs.pos, id, isAllocSym);
//                                JCExpression f = M.at(cs).JmlQuantifiedExpr(JmlToken.BSFORALL, List.<JCVariableDecl>of(d), eold, enew);
//                                addAssume(cs,Label.IMPLICIT_ASSUME,f);
//                            }
//                            newAllocation2(that,resultId);
//                        }

                        // FIXME - is that the right statement list?
                    }
                    paramActuals = null;
                }
            }
            if (newclass != null || utils.isPure(methodDecl.sym)) {
                if (inProcessInvariants.isEmpty()) changeState();
            }

            if (doTranslations) {

                pushBlock();

                String msg = utils.qualifiedMethodSig(calleeMethodSym) + ", returning to " + utils.qualifiedMethodSig(methodDecl.sym);
                currentStatements.add(comment(that, "Assuming callee invariants by the caller " + utils.qualifiedMethodSig(methodDecl.sym) + " after exiting the callee " + utils.qualifiedMethodSig(calleeMethodSym)));
                if (!isHelper(calleeMethodSym)) addInvariants(that,calleeClass,newThisExpr,currentStatements,
                        false,calleeMethodSym.isConstructor(),false,isHelper(calleeMethodSym),true,true,Label.INVARIANT_EXIT,
                        msg);
                addConstraintInitiallyChecks(that,calleeClass,newThisExpr,currentStatements,
                        false,calleeMethodSym.isConstructor(),false,isHelper(calleeMethodSym),true,true,null,
                        msg);
                if (!isHelper(calleeMethodSym)) for (JCExpression arg: trArgs) {
                    if (arg.type.isPrimitive()) continue;
                    currentStatements.add(comment(arg, "Assuming invariants for callee parameter after exiting the callee " + utils.qualifiedMethodSig(calleeMethodSym)));
                    JCIdent id = (JCIdent)arg;
                    addInvariants(id,arg.type.tsym,id,currentStatements,
                            false,false,false,false,true,true,Label.INVARIANT_EXIT,msg);
                }
                
                Type retType = calleeMethodSym.getReturnType();
                if (calleeMethodSym.isConstructor()) {
                    // FIXME - invariants for constructor result - already somewhere else?
                } else if (retType.tag != TypeTags.VOID) {
                    // Add invariants on the type of the return value only if normal termination
                    pushBlock();
                    if (esc && !retType.isPrimitive()) {
                        JCExpression nn = treeutils.makeEqObject(that.pos, resultId, treeutils.nullLit);
                        nn = treeutils.makeOr(that.pos, nn, isAllocated(that,resultId));
                        addAssume(that,Label.IMPLICIT_ASSUME,nn);
                        // FIXME - assumption on type? move the above where that is stated?
                    }
                    
                    currentStatements.add(comment(that, "Assuming invariants for the return value by the caller after exiting the callee " + utils.qualifiedMethodSig(calleeMethodSym)));
                    addInvariants(that,retType.tsym,resultId,currentStatements,
                            false,false,false,false,true,true,Label.INVARIANT_EXIT,
                            msg);
                    JCBlock bl = popBlock(0,that);
                    if (exceptionSym == null) {
                        currentStatements.add(bl);
                    } else {
                        JCIdent exceptionId = treeutils.makeIdent(that.pos,exceptionSym);
                        JCExpression e = treeutils.makeEqObject(that.pos,exceptionId,treeutils.nullLit);
                        JCStatement ifstat = M.at(that.pos).If(e,bl,null);
                        currentStatements.add(ifstat);
                    }
                }

                if (!isHelper(calleeMethodSym)) {
                    currentStatements.add(comment(that, "Asserting caller invariants upon reentering the caller " + utils.qualifiedMethodSig(methodDecl.sym) + " after exiting the callee " + utils.qualifiedMethodSig(calleeMethodSym)));
                    addInvariants(that,savedEnclosingClass.type.tsym,
                            savedEnclosingMethod == null || savedEnclosingMethod.isStatic() || savedEnclosingMethod.isConstructor() ? null : savedThisExpr,
                            currentStatements,
                            false,savedEnclosingMethod != null && savedEnclosingMethod.isConstructor(),isSuper,isHelper(methodDecl.sym),false,false,Label.INVARIANT_REENTER_CALLER, "(Caller: " + utils.qualifiedMethodSig(methodDecl.sym) + ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");

                    // Note that methodDecl.params will be null for initalizer blocks
                    if (methodDecl.params != null) for (JCVariableDecl v: methodDecl.params) {
                        if (v.type.isPrimitive()) continue;
                        // FIXME - it is an open question which invariants to check here - in principle all invariants must hold - but which might not? - need the pack/unpack capability
                        // FIXME - for now we check the invariants of the parameters in the prestate
                        JCVariableDecl d = preparams.get(v.sym);
                        JCIdent id = treeutils.makeIdent(v.pos,d.sym);
                        currentStatements.add(comment(that, "Asserting invariants for caller parameter " + id + " upon reentering the caller " + utils.qualifiedMethodSig(methodDecl.sym) + " after exiting the callee " + utils.qualifiedMethodSig(calleeMethodSym)));
                        addInvariants(v,v.type.tsym,id,currentStatements,
                                false,false,false,false,false,false,Label.INVARIANT_REENTER_CALLER, "(Parameter: " + v.sym + ", Caller: " + utils.qualifiedMethodSig(methodDecl.sym) + ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");
                    }
                }
                
                // FIXME - could optimize if the block is empty except comments
                JCBlock invariantBlock = popBlock(0,methodDecl);
                // FIXME - why are these put in different statement lists?
                if (esc) currentStatements.add( wrapRuntimeException(that, invariantBlock, "JML undefined invariant while checking postconditions - exception thrown", null));
                if (rac) ensuresStatsOuter.add( wrapRuntimeException(that, invariantBlock, "JML undefined invariant while checking postconditions - exception thrown", null));
            }

            
            {
                // Now we iterate over all specification cases in all parent
                // methods again, this time putting in the post-condition checks

                for (MethodSymbol mpsym: overridden) {
                    // This initial logic must match that above for preconditions
                    JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
                    if (calleeSpecs == null) continue; // FIXME - not sure about this

                    ensuresStatsOuter.add(comment(methodDecl,"Assuming postconditions for " + utils.qualifiedMethodSig(mpsym)));
                    exsuresStatsOuter.add(comment(methodDecl,"Assuming exceptional postconditions for " + utils.qualifiedMethodSig(mpsym)));

                    paramActuals = mapParamActuals.get(mpsym);

                    // FIXME - we should set condition
                    // Be sure to do assignable (havoc) clauses, then invariants, and then postcondition clauses
                    for (JmlSpecificationCase cs : calleeSpecs.cases) {
                        if (!utils.visible(classDecl.sym, mpsym.owner, cs.modifiers.flags/*, methodDecl.mods.flags*/)) continue;
                        ListBuffer<JCStatement> ensuresStats = new ListBuffer<JCStatement>();
                        ListBuffer<JCStatement> exsuresStats = new ListBuffer<JCStatement>();
                        JCExpression pre = convertCopy(preExpressions.get(cs));
                        if (pre == treeutils.falseLit) continue; // Don't bother with postconditions if corresponding precondition is explicitly false 
                        condition = pre; // FIXME - is this right? what about the havoc statement?
                        for (JmlMethodClause clause : cs.clauses) {
                            try {
                                JavaFileObject clauseSource = clause.sourcefile == null ? log.currentSourceFile() : clause.sourcefile;
                                switch (clause.token) {
                                    case ENSURES:
                                        if (methodDecl.sym.toString().contains("defaultValues") && that.toString().contains("add")) Utils.print("");
                                        currentStatements = ensuresStats;
                                        LinkedList<ListBuffer<JCStatement>> temp = markBlock();
                                        pushBlock();
                                        try {
                                            addStat(comment(clause));
                                            try {
                                                JCExpression e = convertJML(((JmlMethodClauseExpr)clause).expression, condition, false);
                                                addAssume(that,Label.POSTCONDITION,e,clause,clauseSource);
                                            } catch (NoModelMethod e) { // FIXME - need this elsewhere as well, e.g., signals
                                                // continue
                                            }
                                            JCBlock bl = popBlock(0,that);
                                            addStat( wrapRuntimeException(clause, bl, // wrapRuntimeException is a no-op except for rac
                                                    "JML undefined postcondition - exception thrown",
                                                    null));
                                        } catch (JmlNotImplementedException e) {
                                            popBlock(0,that);
                                            notImplemented(clause.token.internedName() + " clause containing ",e, clause.source());
                                        }
                                        if (!checkBlock(temp)) Utils.print("");
                                        break;
                                    case SIGNALS:
                                        // FIXME - review this
                                        currentStatements = exsuresStats;
                                        pushBlock();
                                        try {
                                            addStat(comment(clause));

                                            JCExpression ex = ((JmlMethodClauseSignals)clause).expression;
                                            JCVariableDecl vdo = ((JmlMethodClauseSignals)clause).vardef;
                                            Type vdtype = syms.exceptionType;
                                            if (vdo != null && !treeutils.isFalseLit(ex)) {
                                                JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionDeclCall.sym);
                                                JCExpression tc = M.at(vdo).TypeCast(vdo.type, exceptionId);
                                                JCVariableDecl vd = treeutils.makeVarDef(vdo.type,vdo.name,vdo.sym.owner, esc ? exceptionId : tc);
                                                vdtype = vd.type;
                                                addStat(vd);
                                                paramActuals.put(vdo.sym, treeutils.makeIdent(vd.pos,vd.sym));
                                            }
                                            // Should the condition be augmented with exception not null and of the right type?
                                            JCExpression e = convertJML(ex, condition, false);
                                            ex = treeutils.trueLit;
                                            if (vdo != null && !treeutils.isFalseLit(e)) {
                                                ex = M.at(clause).TypeTest(treeutils.makeIdent(clause.pos, exceptionDeclCall.sym),
                                                        treeutils.makeType(clause.pos, vdtype)).setType(syms.booleanType);
                                                paramActuals.remove(vdo.sym);
                                            }
                                            addAssume(that,Label.SIGNALS,e,clause,clauseSource);
                                            JCStatement st = M.at(clause).If(ex,popBlock(0,that),null);

                                            addStat( wrapRuntimeException(clause, M.at(clause).Block(0,List.<JCStatement>of(st)), 
                                                    "JML undefined exceptional postcondition - exception thrown",
                                                    null));
                                        } catch (JmlNotImplementedException e) {
                                            popBlock(0,that);
                                            notImplemented(clause.token.internedName() + " clause containing ",e, clause.source());
                                        }
                                        break;
                                    case SIGNALS_ONLY:
                                    {
                                        currentStatements = exsuresStats;
                                        if (exceptionDeclCall != null && exceptionSym != null) { // FIXME - why might exceptionSym be null? halndling field initializer?
                                            
                                            JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionSym);
                                            JCExpression condd = treeutils.falseLit;
                                            for (JCExpression t: ((JmlMethodClauseSignalsOnly)clause).list) {
                                                JCExpression tc = M.at(t).TypeTest(exceptionId, t).setType(syms.booleanType);
                                                condd = treeutils.makeOr(clause.pos, condd, tc);
                                            }
                                            addAssume(that,Label.SIGNALS_ONLY,condd,clause,clause.source(),null,
                                                    treeutils.makeUtilsMethodCall(clause.pos,"getClassName",exceptionId));
                                        } else {
                                            // FIXME - I think this should never happen
                                            // FIXME - shouldn'tx we include runtimeException
                                            JCExpression exx = treeutils.makeDuplicateLiteral(clause.pos,treeutils.falseLit);
                                            addAssume(that,Label.SIGNALS_ONLY,exx,clause,clauseSource); // FIXME - which exception
                                        }
                                        break;
                                    }
                                    case REQUIRES: 
                                    case ASSIGNABLE: 
                                    case ACCESSIBLE:
                                    case CALLABLE:
                                        break;
                                    default:
                                        // FIXME - implement others
                                        break;
                                }
                            } catch (JmlNotImplementedException e) {
                                // FIXME - should not need this anymore
                                notImplemented(clause.token.internedName() + " clause containing ",e, clause.source());
                            }
                        }

                        if (!ensuresStats.isEmpty()) {
                            JCBlock ensuresBlock = M.at(cs.pos+1).Block(0, ensuresStats.toList());
                            // The +1 is so that the position of this if statement
                            // and hence the names of the BRANCHT and BRANCHE variables
                            // is different from the if prior to the apply // FIXME - review if this is still needed
                            JCStatement st = M.at(cs.pos+1).If(pre,ensuresBlock,null);
                            JCBlock bl = M.at(cs.pos+1).Block(0,List.<JCStatement>of(st));
                            ensuresStatsOuter.add( wrapRuntimeException(cs, bl, "JML undefined precondition while checking postconditions - exception thrown", null));
                        }
                        if (!exsuresStats.isEmpty()) {
                            JCBlock exsuresBlock = M.at(cs.pos+1).Block(0, exsuresStats.toList());
                            // The +1 is so that the position of this if statement
                            // and hence the names of the BRANCHT and BRANCHE variables
                            // is different from the if prior to the apply // FIXME - review if this is still needed
                            JCStatement st = M.at(cs.pos+1).If(pre,exsuresBlock,null);
                            JCBlock bl = M.at(cs.pos+1).Block(0,List.<JCStatement>of(st));
                            exsuresStatsOuter.add( wrapRuntimeException(cs, bl, "JML undefined precondition while checking exceptional postconditions - exception thrown", null));
                        }
                    }
                    paramActuals = null;
                }
            }
            // FIXME - the source must be handled properly

            preExpressions.clear();
            
            // Get rid of references - this may not really be needed, but it does not hurt
            {
                for (Symbol key: mapParamActuals.keySet()) {
                    mapParamActuals.get(key).clear();
                }
                mapParamActuals.clear();
                mapParamActuals = null;
            }
            
            
            currentStatements = saved;
            
            if (exceptionDeclCall != null) {
                exsuresStatsOuter.add(M.at(that).Throw(treeutils.makeIdent(that.pos, exceptionDeclCall.sym)));
            } else if (rac) {
                System.out.println("DID NOT EXPECT THIS"); // FIXME
            }
            
            JCBlock ensuresBlock = M.at(that).Block(0, ensuresStatsOuter.toList());
            if (rac) {
                JCBlock exsuresBlock = M.at(that).Block(0, exsuresStatsOuter.toList());
                addStat( wrapException(that, ensuresBlock, exceptionDeclCall, exsuresBlock ));
                addStat( popBlock(0,methodDecl) ); // Final outer block
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
                    JCBlock exsuresBlock = M.at(that).Block(0, exsuresStatsOuter.toList());
                    JCStatement st = M.at(that.pos).If(ch, ensuresBlock, exsuresBlock);
                    addStat(st);
                } else {
                    addStat(ensuresBlock);
                }
                addStat( popBlock(0,methodDecl) ); // Final outer block
            }

            if (resultId != null) result = eresult = treeutils.makeIdent(resultId.pos, resultId.sym);
            else result = eresult = null;
            
        } finally {
            paramActuals = savedParamActuals;
            resultSym = savedSym;
            exceptionSym = savedExceptionSym;
            preparams = savedpreparams;
            currentThisId = savedThisId;
            currentThisExpr = savedThisExpr;
            oldStatements = savedOldStatements;
            condition = savedCondition;
            preLabel = savedPreLabel;
            currentFresh = savedFresh;
            enclosingMethod = savedEnclosingMethod;
            enclosingClass = savedEnclosingClass;
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
    protected boolean onlyComments(Iterable<JCStatement> list) {
        for (JCStatement s: list) {
            if (!(s instanceof JmlStatementExpr && ((JmlStatementExpr)s).token == JmlToken.COMMENT)) return false;
        }
        return true;
    }
    
    protected void newAllocation1(DiagnosticPosition pos, JCIdent resultId) {
        int p = pos.getPreferredPosition();
        JCFieldAccess fa = treeutils.makeSelect(p, convertCopy(resultId), isAllocSym);
        addAssume(pos,Label.IMPLICIT_ASSUME,treeutils.makeNot(p, fa));
    }

    protected void newAllocation2(DiagnosticPosition pos, JCIdent resultId) {
        int p = pos.getPreferredPosition();
        JCFieldAccess fa = treeutils.makeSelect(p, convertCopy(resultId), allocSym);
        JCExpressionStatement st = treeutils.makeAssignStat(p, fa, treeutils.makeIntLiteral(p, ++allocCounter));
        addStat( st );
        fa = treeutils.makeSelect(p, convertCopy(resultId), isAllocSym);
        st = treeutils.makeAssignStat(p, fa, treeutils.makeBooleanLiteral(p,true));
        addStat( st );

    }

    protected void newAllocation(DiagnosticPosition pos, JCIdent resultId) {
        newAllocation1(pos,convertCopy(resultId));
        newAllocation2(pos,convertCopy(resultId));
    }

    // FIXME - review newClass

    @Override
    public void visitNewClass(JCNewClass that) {

        // FIXME - need to check definedness by testing preconditions when translatingJML

        JCExpression savedCondition = condition;
        condition = treeutils.trueLit;
        
        // FIXME - need to call the constructor; need an assertion about the type of the result; about allocation time
        boolean isUtils = that.type.toString().contains("org.jmlspecs.utils.Utils"); // FIXME - must be a better way
        if (pureCopy || isUtils) {
            ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
            for (JCExpression arg: that.args) {
                args.add(convertExpr(arg));
            }
            JCNewClass expr = M.at(that).NewClass(
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
            condition = savedCondition;
            return;
        }
        applyHelper(that);
        condition = savedCondition;
    }
    
    Map<Symbol,MethodSymbol> wellDefinedCheck = new HashMap<Symbol,MethodSymbol>();
    Map<Symbol,MethodSymbol> pureMethod = new HashMap<Symbol,MethodSymbol>();
    
    Set<Symbol> axiomsAdded = new HashSet<Symbol>();
    
    int heapCountForAxioms = -2;
    
    /** Returns true if the symbol was not already in the set for hc */
    protected boolean addAxioms(int hc, Symbol sym) {
        if (hc != heapCountForAxioms) {
            axiomsAdded.clear();
            pureMethod.clear();
            wellDefinedCheck.clear();
            heapCountForAxioms = hc;
        }
        return axiomsAdded.add(sym);
    }
    
    protected JCBlock addMethodAxioms(DiagnosticPosition callLocation, MethodSymbol msym, java.util.List<MethodSymbol> overridden) {
        boolean isFunction = false;
        if (!addAxioms(heapCount,msym)) { return M.at(Position.NOPOS).Block(0L, List.<JCStatement>nil()); }
        boolean isStatic = utils.isJMLStatic(msym);
        
        Map<Symbol,JCExpression> saved = paramActuals;
        JCExpression savedResultExpr = resultExpr;
        JCIdent savedCurrentThisId = currentThisId;
        JCExpression savedCurrentThisExpr = currentThisExpr;
        Map<Symbol,JCExpression> savedParamActuals = paramActuals;
        
        JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(msym);
        int pos = calleeSpecs.decl != null ? calleeSpecs.decl.pos : methodDecl.pos;

        Name newMethodName = names.fromString(utils.qualifiedMethodName(msym).replace('.', '_') + "_" + pos);
        pushBlock();
        addStat(comment(callLocation,"Axioms for method " + utils.qualifiedMethodSig(msym)));
        
        JCExpression combinedPre = treeutils.falseLit;
        JmlMethodClauseExpr clauseToReference = null;
        try {

            // Construct the lists of parameters and parameter types for the logical function representing the pure function
            ListBuffer<JCVariableDecl> newDecls = new ListBuffer<JCVariableDecl>();
            ListBuffer<JCExpression> newparams = new ListBuffer<JCExpression>();
            if (!isFunction) {
                //newDecls.add(treeutils.makeVarDef(syms.intType, names.fromString("heapCount"), methodDecl.sym, pos));
                newparams.add(treeutils.makeIntLiteral(Position.NOPOS,heapCount));
            }
            if (!isStatic) {
                // FIXME _ why are we doing the translation to THIS here, rather than in BasicBlocker2
                JCVariableDecl newDecl = treeutils.makeVarDef(syms.objectType, names.fromString(Strings.thisName), methodDecl.sym, pos);
                newDecls.add(newDecl);
                JCIdent id = M.at(callLocation).Ident(newDecl.sym);
                newparams.add(convertCopy(id));
            }
            if (calleeSpecs.decl != null) {
                for (JCVariableDecl d : specs.getDenestedSpecs(msym).decl.params) {
                    JCVariableDecl newDecl = treeutils.makeVarDef(d.type, d.name, methodDecl.sym, d.pos);
                    newDecls.add(newDecl);
                    JCIdent id = M.at(d).Ident(newDecl.sym);
                    newparams.add(convertCopy(id));
                }
            } else {
                for (VarSymbol d : msym.params) {
                    JCVariableDecl newDecl = treeutils.makeVarDef(d.type, d.name, methodDecl.sym, methodDecl.pos);
                    newDecls.add(newDecl);
                    JCIdent id = M.at(callLocation).Ident(newDecl.sym);
                    newparams.add(convertCopy(id));
                }
            }
            List<JCVariableDecl> newDeclsListq = newDecls.toList();
            List<JCVariableDecl> newDeclsList = newDeclsListq;
            if (!isFunction) {
                JCVariableDecl d = treeutils.makeVarDef(syms.intType, names.fromString("heapCount"), methodDecl.sym, pos);
                newDeclsList = newDeclsListq.prepend(d);
            }
            
            List<JCExpression> newParams = newparams.toList();
            ListBuffer<Type> newparamtypes = new ListBuffer<Type>();
            for (JCExpression e: newParams) {
                newparamtypes.add(e.type);
            }
            List<Type> newParamTypes = newparamtypes.toList();

            // Now go through each spec case for each overridden method and construct axioms for each ensures clause
            for (MethodSymbol mpsym: overridden) {
                // This initial logic must match that above for preconditions
                calleeSpecs = specs.getDenestedSpecs(mpsym);
                if (calleeSpecs == null) continue; // FIXME - not sure about this
                if (calleeSpecs.decl == null) continue;
                
                // Now map the formals as used in the overridden method to 
                // identifiers used in the axioms being constructed
                paramActuals = new HashMap<Symbol,JCExpression>();
                Iterator<JCVariableDecl> iter = newDeclsList.iterator();
                if (!isFunction) iter.next();
                currentThisExpr = currentThisId = isStatic ? null : M.at(calleeSpecs.decl).Ident(iter.next().sym);
                for (JCVariableDecl d : calleeSpecs.decl.params) {
                    JCIdent id = M.at(d).Ident(iter.next().sym);
                    paramActuals.put(d.sym, id);
                }
                
                MethodSymbol newsym = treeutils.makeMethodSym(methodDecl.mods, newMethodName, msym.getReturnType(), classDecl.sym, newParamTypes);
                pureMethod.put(msym,newsym);
                JCExpression fcn = M.at(Position.NOPOS).Ident(newsym);
                JCMethodInvocation call = M.at(Position.NOPOS).Apply(
                        List.<JCExpression>nil(), fcn, newParams);
                call.type = newsym.getReturnType();
                resultExpr = call;
                
                for (JmlSpecificationCase cs : calleeSpecs.cases) {
                    if (!utils.visible(classDecl.sym, mpsym.owner, cs.modifiers.flags/*, methodDecl.mods.flags*/)) continue;

                    // FIXME - will need to add OLD and FORALL clauses in here
                    
                    JCExpression pre = treeutils.trueLit;
                    try {
                        JmlMethodClauseExpr mcc = null; // Remember the first clause in the specification case
                        for (JmlMethodClause clause : cs.clauses) {
                            if (clause.token == JmlToken.REQUIRES) {
                                JmlMethodClauseExpr mce = (JmlMethodClauseExpr)clause;
                                // convertJML will use paramActuals
                                JCExpression e = convertJML(mce.expression,pre,false); // Might throw an exception
                                pre = e == treeutils.falseLit ? e : pre == treeutils.trueLit ? e : treeutils.makeAnd(pre.pos, pre, e);
                                if (mcc == null) mcc = mce;
                            }
                        }
                        if (mcc != null) clauseToReference = mcc;
                    } catch (NoModelMethod e) {
                        pre = treeutils.falseLit;
                    } catch (JmlNotImplementedException e) {
                        notImplemented("requires clause containing ",e); // FIXME _ clause source
                        pre = treeutils.falseLit;
                    }
                   
                    if (treeutils.isFalseLit(pre)) continue; // Don't bother with postconditions if corresponding precondition is explicitly false 
                    combinedPre = (treeutils.isTrueLit(combinedPre)) ? combinedPre: (treeutils.isTrueLit(pre) || treeutils.isFalseLit(combinedPre)) ? convertCopy(pre) : treeutils.makeOr(pre.pos, combinedPre, convertCopy(pre));
                    
                    for (JmlMethodClause clause : cs.clauses) {
                        DiagnosticPosition dpos = clause;
                        JavaFileObject clauseSource = clause.sourcefile == null ? log.currentSourceFile() : clause.sourcefile;
                        if (clause.token == JmlToken.ENSURES) {
                            try {
                                //addStat(comment(clause));
                                JCExpression e = convertJML(((JmlMethodClauseExpr)clause).expression, condition, false);
                                if (newDeclsList.isEmpty()) {
                                    e = treeutils.makeImplies(e.pos, pre, e);
                                } else {
                                    e = M.at(dpos).JmlQuantifiedExpr(
                                        JmlToken.BSFORALL,
                                        newDeclsListq, // FIXME - is it OK that we use the same copy of this array (and so the same symbols) for each postcondition expression
                                        // FIXME - if not, we have to conjoin all the ensures 
                                        pre,
                                        e);
                                    e.type = syms.booleanType;
                                }
                                addAssume(dpos,Label.IMPLICIT_ASSUME,e,dpos,clauseSource);
                            } catch (JmlNotImplementedException e) {
                                notImplemented(clause.token.internedName() + " clause containing ",e, clause.source());
                            }
                        }
                    }
                }
                paramActuals = null;
            }

            if (!treeutils.isTrueLit(combinedPre)) {
                MethodSymbol methodDefinedSym = treeutils.makeMethodSym(methodDecl.mods, names.fromString("_JML_METHODEF__" + newMethodName.toString()), syms.booleanType, classDecl.sym, newParamTypes);
                JCExpression methodDefinedFcn = M.at(Position.NOPOS).Ident(methodDefinedSym);
                JCMethodInvocation wellDefinedCall = M.at(Position.NOPOS).Apply(
                        List.<JCExpression>nil(), methodDefinedFcn, newParams);
                wellDefinedCall.type = syms.booleanType;
                wellDefinedCheck.put(msym, methodDefinedSym);
            
                if (newDeclsList.isEmpty()) {
                    addAssume(clauseToReference,Label.IMPLICIT_ASSUME,combinedPre);
                } else {
                    JCExpression e = M.at(Position.NOPOS).JmlQuantifiedExpr(
                            JmlToken.BSFORALL,
                            newDeclsListq,
                            null,
                            treeutils.makeEquality(Position.NOPOS, wellDefinedCall, combinedPre));
                    e.type = syms.booleanType;
                    addAssume(clauseToReference,Label.IMPLICIT_ASSUME,e);
                }
            }
        } finally {
            paramActuals = saved;
            resultExpr = savedResultExpr;
            currentThisId = savedCurrentThisId;
            currentThisExpr = savedCurrentThisExpr;
            paramActuals = savedParamActuals;
        }
        
        return popBlock(0L,null); // FIXME - what DiagnosticPosition to use

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
                addAssert(that,
                        translatingJML ? Label.UNDEFINED_NEGATIVESIZE : Label.POSSIBLY_NEGATIVESIZE, 
                        comp);
            }
        }
        
        ListBuffer<JCExpression> elems = new ListBuffer<JCExpression>();
        if (that.elems != null) {
            for (JCExpression elem: that.elems) {
                elems.add(convertExpr(elem)); // FIXME - we need implicit conversions
            }
        } else {
            elems = null;
        }

        if (pureCopy) {
            JCExpression elemtype = convert(that.elemtype);
            result = eresult = M.at(that).NewArray(elemtype, dims.toList(), elems == null ? null: elems.toList()).setType(that.type);
        } else if (rac) {
            // This will create a fully-qualified version of the type name
            JCExpression elemtype = that.elemtype == null ? null : treeutils.makeType(that.elemtype.pos, that.elemtype.type);
            result = eresult = M.at(that).NewArray(elemtype, dims.toList(), elems == null ? null: elems.toList()).setType(that.type);
            result = eresult = newTemp(eresult);
        } else { // esc
            // FIXME - Creating a decl and initializing it outside the expression doe snot work for translatigJML if there is a quantifier expression
            JCVariableDecl decl = treeutils.makeVarDef(that.type,names.fromString(Strings.newArrayVarString + that.pos), null, that.pos);
            addStat(decl);
            JCIdent id = treeutils.makeIdent(that.pos, decl.sym);

            addArrayElementAssumptions(id, dims, elems);

            result = eresult = convertCopy(id);

            // FIXME - need assertions about size of array and about any known array elements; about allocation time
            // also about type of the array
        }
    }
    
    protected void addArrayElementAssumptions(JCIdent array, ListBuffer<JCExpression> dims, ListBuffer<JCExpression> elems) {
        JCExpression size = null;
        if (dims != null && dims.length() > 0) { 
            size = dims.first();
        } else if (elems != null) {
            size = treeutils.makeIntLiteral(array.pos, elems.length());
        } else {
            // ERROR
        }
        if (elems != null) {
            Type ctype = ((Type.ArrayType)array.type).getComponentType();
            addAssume(array,Label.NULL_CHECK,treeutils.makeNeqObject(array.pos, array, treeutils.nullLit));
            newAllocation(array,array);
            if (size != null) {
                addAssume(array,Label.IMPLICIT_ASSUME,treeutils.makeEquality(array.pos,treeutils.makeLength(array,convertCopy(array)),convert(size)));
            }
            int i = 0;
            for (JCExpression e: elems) {
                JCLiteral index = treeutils.makeIntLiteral(e.pos, i);
                e = addImplicitConversion(e,ctype,e);
                JmlBBArrayAccess aa = new JmlBBArrayAccess(null,array,index); // FIXME - switch to factory
                aa.pos = array.pos;
                aa.setType(ctype);
                aa.arraysId = null;

                JCBinary b = treeutils.makeEquality(e.pos,aa,e);
                addAssume(e.pos(),Label.IMPLICIT_ASSUME,b);
                ++i;
            }
        } else {
            if (dims.first() instanceof JCLiteral) {
                JCExpression e = createNullInitializedArray(array.type, dims.toList());
                JCBinary b = treeutils.makeEquality(e.pos,array,e);
                addAssume(array,Label.IMPLICIT_ASSUME,b);
            } else {
                addAssume(array,Label.NULL_CHECK,treeutils.makeNeqObject(array.pos, array, treeutils.nullLit));
                newAllocation(array,array);
                if (size != null) {
                    addAssume(array,Label.IMPLICIT_ASSUME,treeutils.makeEquality(array.pos,treeutils.makeLength(array,convertCopy(array)),convert(size)));
                }
                // FIXME - needs lots more implementation - quantified expressions
            }
        }
    }
    
    protected JCExpression createNullInitializedArray(Type type, List<JCExpression> dims) {
        DiagnosticPosition pos = methodDecl;
        int p = pos.getPreferredPosition();
        if (!(type instanceof Type.ArrayType)) {
            return treeutils.makeZeroEquivalentLit(p,type);
        } else if (dims.head instanceof JCLiteral) {
            Type ctype = ((Type.ArrayType)type).getComponentType();
            int sz = (Integer)((JCLiteral)dims.head).value; // FIXME - long?
            JCVariableDecl decl = newTempDecl(methodDecl, type);
            addStat(decl);
            JCIdent id = treeutils.makeIdent(p, decl.sym);
            addAssume(pos,Label.IMPLICIT_ASSUME, treeutils.makeNeqObject(p, id, treeutils.nullLit));
            newAllocation(pos,id);
            addAssume(id,Label.IMPLICIT_ASSUME,treeutils.makeEquality(p,treeutils.makeLength(pos,convertCopy(id)),convertExpr(dims.head)));
            for (int i=0; i<sz; ++i) {
                JCLiteral index = treeutils.makeIntLiteral(p, i);
                JmlBBArrayAccess aa = new JmlBBArrayAccess(null,id,index); // FIXME - switch to factory
                aa.pos = p;
                aa.setType(ctype);
                aa.arraysId = null;
                JCExpression e = createNullInitializedArray(ctype, dims.tail);
                JCBinary b = treeutils.makeEquality(p,aa,e);
                addAssume(pos,Label.IMPLICIT_ASSUME,b);
            }
            return id;
        } else if (dims.head == null) {
            return treeutils.nullLit;
        } else {
            JCVariableDecl decl = newTempDecl(methodDecl, type);
            JCIdent id = treeutils.makeIdent(p, decl.sym);
            // id != null && id.length == 'dims.head'
            // (\forall int i; 0<=i && i < 'dims.head'; id[i] != null && TBD
            // FIXME - not implemented
            return id;
        }
    }

    // OK
    @Override
    public void visitParens(JCParens that) {
        JCExpression arg = convertExpr(that.getExpression());
        result = eresult = M.at(that).Parens(arg).setType(that.type);
        treeutils.copyEndPosition(eresult,that);
    }
    
    // FIXME - check endpos everywhere
    
    // FIXME - this needs work per the complicated Java conversion rules
    
    /** Adds any checks and conversions that Java implicitly applies to convert
     * the given expression to the given type.
     */
    protected JCExpression addImplicitConversion(DiagnosticPosition pos, Type newtype, JCExpression expr) {
        if (pureCopy) return expr;
        
        boolean isPrim = expr.type.isPrimitive() && expr.type.tag != TypeTags.BOT;
        boolean newIsPrim = newtype.isPrimitive() && expr.type.tag != TypeTags.BOT;
        
        // If we are converting from a non-primitive to primitive type (unboxing),
        // check that the expression is not null
        // But we don't unbox for rac for JML types because those are represented as a non-primitive anyway
        if (javaChecks && newIsPrim && !isPrim && (esc || !jmltypes.isJmlType(newtype))) {
            JCExpression e = treeutils.makeNeqObject(pos.getPreferredPosition(), expr, treeutils.nullLit);
            if (translatingJML) {
                addAssert(pos, Label.UNDEFINED_NULL_UNBOX, 
                        treeutils.makeImplies(pos.getPreferredPosition(),  condition,  e));
                
            } else {
                addAssert(pos, Label.POSSIBLY_NULL_UNBOX, e);
            }
        }
        
        if (rac) {
            if ((jmltypes.isSameType(newtype,jmltypes.BIGINT) || newtype.tsym == jmltypes.repSym(jmltypes.BIGINT)) && 
                    isPrim && !jmltypes.isJmlType(expr.type)) {
                return treeutils.makeUtilsMethodCall(expr.pos,"bigint_valueOf",expr);
            } else if ((jmltypes.isSameType(newtype,jmltypes.REAL) || newtype.tsym == jmltypes.repSym(jmltypes.REAL)) && 
                    isPrim && !jmltypes.isJmlType(expr.type)) {
                return treeutils.makeUtilsMethodCall(expr.pos,"real_valueOf",expr);
            } else {
                return expr; // RAC handles implicit conversions implicitly
            }
        }
        
        if (types.isSameType(newtype,expr.type)) return expr;
        if (expr.type.tag == TypeTags.BOT || (expr instanceof JCLiteral && ((JCLiteral)expr).value == null)) return expr;
        
//        Type unboxed = unboxedType(expr.type);
//        int tag = unboxed.tag;
//        String methodName =
//                tag == TypeTags.INT ? "intValue" :
//                tag == TypeTags.SHORT ? "shortValue" :
//                tag == TypeTags.LONG ? "longValue" :
//                tag == TypeTags.BOOLEAN ? "booleanValue" :
//                tag == TypeTags.DOUBLE ? "doubleValue" :
//                tag == TypeTags.FLOAT ? "floatValue" :
//                tag == TypeTags.BYTE ? "byteValue" :
//                tag == TypeTags.CHAR ? "charValue" : "";
//                ;
//        JCIdent id = M.Ident(names.fromString(methodName));
        if (newIsPrim && !isPrim) {
            JCExpression mth = createUnboxingExpr(expr);
            if (translatingJML) {
                eresult = mth;
            } else {
                eresult = newTemp(mth);
            }
        } else if (!newIsPrim && isPrim) {
            // boxing: Integer = int and the like
            JCExpression id = createBoxingStatsAndExpr(expr,newtype);
            eresult = id;

        } else {
            eresult = M.at(pos).TypeCast(newtype,eresult);
            // FIXME - for integer promotions, add assumptions about range of value
        }
        return eresult;
    }
    
    /** If the argument is a reference type with an unboxed version (e.g. Integer -> int)
     * then returns the unboxed type, otherwise returns the argument.
     */
    protected Type unboxedType(Type t) {
        Type tt = types.unboxedType(t);
        if (tt == Type.noType) tt = t;
        return tt;
    }
    
    protected Type boxedType(Type t) {
        Type tt = types.boxedTypeOrType(t);
        return tt;
    }
    
    protected JCExpression createUnboxingExpr(JCExpression expr) {
        Type unboxed = unboxedType(expr.type);
        int tag = unboxed.tag;
        String methodName =
                tag == TypeTags.INT ? "intValue" :
                tag == TypeTags.SHORT ? "shortValue" :
                tag == TypeTags.LONG ? "longValue" :
                tag == TypeTags.BOOLEAN ? "booleanValue" :
                tag == TypeTags.DOUBLE ? "doubleValue" :
                tag == TypeTags.FLOAT ? "floatValue" :
                tag == TypeTags.BYTE ? "byteValue" :
                tag == TypeTags.CHAR ? "charValue" : "";
                ;
        JCIdent id = M.Ident(names.fromString(methodName));
        JCExpression mth = M.at(expr).JmlMethodInvocation(id, List.<JCExpression>of(expr));
        mth.type = unboxed;
        return mth;
    }
    
    protected JCExpression createBoxingStatsAndExpr(JCExpression expr, Type newtype) {
        int tag = expr.type.tag;
        String methodName =
                tag == TypeTags.INT ? "intValue" :
                tag == TypeTags.SHORT ? "shortValue" :
                tag == TypeTags.LONG ? "longValue" :
                tag == TypeTags.BOOLEAN ? "booleanValue" :
                tag == TypeTags.DOUBLE ? "doubleValue" :
                tag == TypeTags.FLOAT ? "floatValue" :
                tag == TypeTags.BYTE ? "byteValue" :
                tag == TypeTags.CHAR ? "charValue" : "";
                ;
        JCIdent id = M.Ident(names.fromString(methodName));
        // T id
        JCIdent tmp = newTemp(expr.pos(), newtype); // the result - uninitialized id of type 'newtype'
        // assume id != null
        JCExpression e = treeutils.makeNeqObject(expr.getPreferredPosition(), tmp, treeutils.nullLit);
        addAssume(expr,Label.IMPLICIT_ASSUME,e);

        JmlMethodInvocation call = M.at(expr).JmlMethodInvocation(id, List.<JCExpression>of(tmp));
        call.setType(expr.type); // Note: no symbol set, OK since this is esc
        e = treeutils.makeEquality(expr.pos,call,expr);
        addAssume(expr,Label.IMPLICIT_ASSUME,e);

        // assume 
        addAssume(expr,Label.IMPLICIT_ASSUME,
                treeutils.makeDynamicTypeEquality(expr, 
                        treeutils.makeIdent(expr.getPreferredPosition(), tmp.sym), 
                        newtype));
        return tmp;

    }
    
    // FIXME - document
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
            rhs = addImplicitConversion(that,lhs.type, rhs);

            if (specs.isNonNull(id.sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(that.pos, rhs, treeutils.nullLit);
                // FIXME - location of nnonnull declaration?
                addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e);
            }
            checkAccess(JmlToken.ASSIGNABLE, that, lhs, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);
            
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
            if (!utils.isJMLStatic(fa.sym)) {
                JCExpression obj = convertExpr(fa.selected);
                JCExpression e = treeutils.makeNeqObject(obj.pos, obj, treeutils.nullLit);
                if (javaChecks) {
                    addAssert(that.lhs, Label.POSSIBLY_NULL_DEREFERENCE, e);
                }
                newfa = treeutils.makeSelect(that.pos, convertCopy(obj), fa.sym);
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
                addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e);
            }

            // FIXME _ use checkAssignable
            checkAccess(JmlToken.ASSIGNABLE, that,fa, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);
//            for (JmlSpecificationCase c: specs.getDenestedSpecs(methodDecl.sym).cases) {
//                JCExpression check = checkAssignable(fa,c,currentThisId.sym,currentThisId.sym);
//                if (!treeutils.isTrueLit(check)) {
//                    DiagnosticPosition pos = c;
//                    for (JmlMethodClause m : c.clauses) {
//                        if (m.token == JmlToken.ASSIGNABLE) { pos = m; break; }
//                    }
//                    addAssert(that,Label.ASSIGNABLE,check,pos,c.sourcefile);
//                }
//            }

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
            if (javaChecks) addAssert(aa, Label.POSSIBLY_NULL_DEREFERENCE, e);

            JCExpression index = convertExpr(aa.index);
            index = addImplicitConversion(index,syms.intType,index);
            e = treeutils.makeBinary(index.pos, JCTree.GE, index, treeutils.zero);
            if (javaChecks) addAssert(aa, Label.POSSIBLY_NEGATIVEINDEX, e);
            
            JCFieldAccess newfa = treeutils.makeLength(array,array);
            e = treeutils.makeBinary(index.pos, JCTree.GT, newfa, index);
            if (javaChecks) addAssert(aa, Label.POSSIBLY_TOOLARGEINDEX, e);
            
            // FIXME - test this 
            checkAccess(JmlToken.ASSIGNABLE, that,aa, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);
//            for (JmlSpecificationCase c: specs.getDenestedSpecs(methodDecl.sym).cases) {
//                JCExpression check = checkAssignable(aa,c,currentThisId.sym,currentThisId.sym);
//                if (!treeutils.isTrueLit(check)) {
//                    DiagnosticPosition pos = c;
//                    for (JmlMethodClause m : c.clauses) {
//                        if (m.token == JmlToken.ASSIGNABLE) { pos = m; break; }
//                    }
//                    addAssert(that,Label.ASSIGNABLE,check,pos,c.sourcefile);
//                }
//            }

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
            error(that,"An unknown kind of assignment seen in JmlAssertionAdder: " + that.lhs.getClass());
        }
        changeState();
    }
    
    
    // OK
    @Override
    public void visitAssignop(JCAssignOp that) {
        if (pureCopy) {
            JCExpression lhs = convertExpr(that.lhs);
            JCExpression rhs = convertExpr(that.rhs);
            JCAssignOp a = M.at(that).Assignop(that.getTag(), lhs, rhs);
            a.operator = that.operator;
            a.setType(that.type);
            result = eresult = a;
            return;
        }
        visitAssignopHelper(that,false);
        changeState();
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
        Type maxJmlType = that.lhs.type;
        if (jmltypes.isJmlType(that.rhs.type)) maxJmlType = that.rhs.type;
        if (lhs instanceof JCIdent) {
            // We start with: id = expr
            // We generate
            //    ... statements for the subexpressions of lhs (if any)
            //    ... statements for the subexpressions of expr
            //    temp = lhs' op rhs'
            //    lhs' = temp
            
            Type t = unboxedType(that.type);
            
            JCExpression lhsc = addImplicitConversion(lhs,t,lhs);

            rhs = convertExpr(rhs);
            rhs = addImplicitConversion(rhs,t,rhs);
            

            addBinaryChecks(that, op, lhsc, rhs, maxJmlType);

            rhs = makeBin(that,op,that.getOperator(),lhs,rhs,maxJmlType);
            treeutils.copyEndPosition(rhs, that);

            checkAccess(JmlToken.ASSIGNABLE, that, lhs, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);

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
            if (utils.isJMLStatic(fa.sym)) {
                if (!lhsscanned && !treeutils.isATypeTree(fa.selected))  convertExpr(fa.selected);
                JCExpression typetree = treeutils.makeType(fa.selected.pos, fa.sym.owner.type);
                newfa = treeutils.makeSelect(fa.selected.pos, typetree, fa.sym);
                newfa.name = fa.name;
                rhs = convertExpr(rhs);
                
            } else {
                JCExpression sel = lhsscanned ? fa.selected : convertExpr(fa.selected);

                newfa = M.at(lhs).Select(sel, fa.name);
                newfa.sym = fa.sym;
                newfa.type = fa.type;

                if (javaChecks) {
                    JCExpression e = treeutils.makeNeqObject(lhs.pos, sel, treeutils.nullLit);
                    addAssert(that.lhs, Label.POSSIBLY_NULL_DEREFERENCE, e);
                }

                rhs = convertExpr(rhs);
                rhs = addImplicitConversion(rhs,that.type,rhs);
                if (specs.isNonNull(fa.sym,methodDecl.sym.enclClass())) {
                    JCExpression e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nullLit);
                    // FIXME - location of nnonnull declaration?
                    addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e);
                }

            }
            addBinaryChecks(that,op,newfa,rhs,maxJmlType);
            checkAccess(JmlToken.ASSIGNABLE, that, lhs, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);

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
                addAssert(that.lhs, Label.POSSIBLY_NULL_DEREFERENCE, e);
            }

            JCExpression index = convertExpr(aa.index);
            index = addImplicitConversion(index,syms.intType,index);
            if (javaChecks) {
                JCExpression e = treeutils.makeBinary(index.pos, JCTree.GE, index, treeutils.zero);
                addAssert(that.lhs, Label.POSSIBLY_NEGATIVEINDEX, e);
            }
            
            JCFieldAccess newfa = treeutils.makeLength(array, array);
            if (javaChecks) {
                JCExpression e = treeutils.makeBinary(index.pos, JCTree.LT, index, newfa);
                addAssert(that.lhs, Label.POSSIBLY_TOOLARGEINDEX, e);
            }

            checkAccess(JmlToken.ASSIGNABLE, that, lhs, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);

            rhs = convertExpr(rhs);
            rhs = addImplicitConversion(rhs,that.type,rhs);

            lhs = new JmlBBArrayAccess(null,array,index); // FIXME - use factory
            lhs.pos = aa.pos;
            lhs.type = aa.type;
            lhs = newTemp(lhs);

            addBinaryChecks(that,op,lhs,rhs,maxJmlType);
            
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
            error(that,"Unexpected kind of AST in JmlAssertionAdder.visitAssignOp: " + that.getClass());
        }
    }


    // FIXME - check boxing conversions for ++ --?
    

    /** This translates Java unary operations: ++ -- ! ~ - + */
    @Override
    public void visitUnary(JCUnary that) {
        int tag = that.getTag();
        if (pureCopy) {
            JCExpression arg = convertExpr(that.getExpression());
            result = eresult = treeutils.makeUnary(that.pos,tag,that.getOperator(),arg);
        } else if (tag == JCTree.PREDEC || tag == JCTree.PREINC) {
            JCAssignOp b = M.at(that.getStartPosition()).Assignop(tag == JCTree.PREDEC ? JCTree.MINUS_ASG : JCTree.PLUS_ASG ,that.getExpression(),treeutils.one);
            treeutils.copyEndPosition(b, that);
            b.setType(that.type);
            b.operator = treeutils.findOpSymbol(tag == JCTree.PREDEC ? JCTree.MINUS : JCTree.PLUS ,that.type);
            visitAssignopHelper(b,false);
        } else if (tag == JCTree.POSTDEC || tag == JCTree.POSTINC){
            JCExpression arg = convertExpr(that.getExpression());
            JCIdent id = newTemp(arg);
            JCAssignOp b = M.at(that).Assignop(tag == JCTree.POSTDEC ? JCTree.MINUS_ASG : JCTree.PLUS_ASG, that.getExpression() ,treeutils.one);
            treeutils.copyEndPosition(b, that);
            b.setType(that.type);
            Type t = that.type.tag < TypeTags.INT ? syms.intType : that.type;
            b.operator = treeutils.findOpSymbol(tag == JCTree.POSTDEC ? JCTree.MINUS : JCTree.PLUS, t);
            visitAssignopHelper(b,true);
            exprBiMap.put(that.getExpression(),eresult);
            result = eresult = id;
        } else {
            JCExpression arg = convertExpr(that.getExpression());
            if (rac && jmltypes.isJmlType(that.type)) {
                if (tag == JCTree.NEG){ 
                    if (that.type == jmltypes.BIGINT) {
                        result = eresult = treeutils.makeUtilsMethodCall(that.pos,"bigint_neg",arg);
                    }
                    if (that.type == jmltypes.REAL) {
                        result = eresult = treeutils.makeUtilsMethodCall(that.pos,"real_neg",arg);
                    }
                    if (splitExpressions) result = eresult = newTemp(eresult);
                } else if (tag == JCTree.PLUS) {
                    result = eresult = arg;
                } else { 
                    log.error(that,"jml.internal","Unknown unary operation for JML type: " + that);
                    result = eresult = arg;
                }
//                } else {
//                    // FIXME - this does not differentiate the result value of pre and post operations. It presumes that this non-pure operator is only ever used at the top-level of a set statement, which may not be true, but we don't handle other side effects in JML expressions either
//                    String s = (that.type == jmltypes.BIGINT) ? "bigint_" : "real_";
//                    String op = tag == JCTree.PREINC || tag == JCTree.POSTINC ? "add" : "sub";
//                    JCExpression lit = treeutils.makeIntLiteral(that.pos, 1);
//                    JCExpression e = treeutils.makeUtilsMethodCall(that.pos,s+op,arg,
//                            addImplicitConversion(that,arg.type,lit));
//                    result = eresult = treeutils.makeAssign(that.pos, that.getExpression(), e);
//                }
            } else {
                JCExpression e = treeutils.makeUnary(that.pos,tag,that.getOperator(),arg);
                if (!translatingJML) {
                    arg = addImplicitConversion(that,that.type,arg);
                    addUnaryChecks(that,tag,arg);
                }
                if (splitExpressions) e = newTemp(e);
                result = eresult = e;
            }
        }
    }

    /** Add any assertions to check for problems with unary operations. */
    protected void addUnaryChecks(JCExpression that, int op, JCExpression expr) {

        // FIXME - add checks for numeric overflow
        
    }
    
    /** Add any assertions to check for problems with binary operations. */
    protected void addBinaryChecks(JCExpression that, int op, JCExpression lhs, JCExpression rhs, Type maxJmlType) {

        
        if (op == JCTree.DIV || op == JCTree.MOD) {
            JCExpression nonzero = nonZeroCheck(that,rhs,maxJmlType);
            if (javaChecks) addAssert(that,Label.POSSIBLY_DIV0,nonzero);
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
            addAssert(that,Label.POSSIBLY_LARGESHIFT,expr);
        }
        // FIXME - add a command-line switch to enable the above?
        // FIXME - add checks for numeric overflow
        
    }

    // FIXME - check that condition is never used when pureCopy == true

    // OK
    @Override
    public void visitBinary(JCBinary that) {
        // FIXME - check on numeric promotion, particularly shift operators
        int tag = that.getTag();
        boolean comp = tag == JCTree.EQ || tag == JCTree.NE || tag == JCTree.GE || tag == JCTree.LE || tag == JCTree.LT || tag == JCTree.GT;
        boolean shift = tag == JCTree.SL || tag == JCTree.SR || tag == JCTree.USR;
        boolean arith = tag == JCTree.PLUS || tag == JCTree.MINUS || tag == JCTree.MUL || tag == JCTree.DIV || tag == JCTree.MOD;
        boolean bit = tag == JCTree.BITAND || tag == JCTree.BITOR || tag == JCTree.BITXOR;
        if (pureCopy) {
            JCExpression lhs = convertExpr(that.getLeftOperand());
            JCExpression rhs = convertExpr(that.getRightOperand());
            result = eresult = treeutils.makeBinary(that.pos,tag,that.getOperator(),lhs,rhs);
        } else if (esc && tag == JCTree.PLUS && that.type.equals(syms.stringType)) {
            Symbol s = utils.findMember(syms.stringType.tsym,"concat");
            if (s == null) log.error(that,"jml.internal","Could not find the concat method");
            else {
            	JCMethodInvocation call;
            	JCExpression lhs = that.getLeftOperand();
            	JCExpression rhs = that.getRightOperand();
            	if (esc) {
            	    lhs = convertExpr(lhs);
            	    if (lhs.type.isPrimitive() && lhs.type.tag != TypeTags.BOT) {
            	        lhs = addImplicitConversion(that.getLeftOperand(),boxedType(lhs.type),lhs);
            	    }
            	    rhs = convertExpr(rhs);
            	    if (rhs.type.isPrimitive() && rhs.type.tag != TypeTags.BOT) {
            	        rhs = addImplicitConversion(that.getRightOperand(),boxedType(rhs.type),rhs);
            	    }
            	    JCExpression meth = M.at(that).Select(lhs,s);
            	    call = M.at(that).Apply(null, meth, List.<JCExpression>of(rhs)).setType(that.type);
            	} else {
            	    JCExpression meth = M.at(that).Select(lhs,s);
            	    call = M.at(that).Apply(null, meth, List.<JCExpression>of(rhs)).setType(that.type);
            	}
                visitApply(call);
            }
            return;
        } else if (tag == JCTree.AND || tag == JCTree.OR) {
            JCExpression prev = condition;
            try {
                Type maxJmlType = that.getLeftOperand().type;
                if (jmltypes.isJmlType(that.getRightOperand().type)) maxJmlType = that.getRightOperand().type;
                
                // FIXME - check that all the checks in makeBinaryCHecks are here - or somehow reuse that method here
                // same for unary checks
                if (tag == JCTree.AND) {
                    if (splitExpressions) {
                        JCConditional cond = M.at(that).Conditional(that.lhs,that.rhs,treeutils.falseLit);
                        cond.setType(that.type);
                        visitConditional(cond);
                        return;
                    } else {
                        JCExpression lhs = convertExpr(that.getLeftOperand());
                        JCExpression rhs = that.getRightOperand();
                        lhs = addImplicitConversion(lhs,syms.booleanType,lhs);
                        if (translatingJML) condition = treeutils.makeAnd(that.lhs.pos, condition, lhs);
                        rhs = convertExpr(rhs); // condition is used within scanExpr so this statement must follow the previous one
                        rhs = addImplicitConversion(rhs,syms.booleanType,rhs);
                        if (translatingJML) adjustWellDefinedConditions(lhs);
                        result = eresult = makeBin(that,tag,that.getOperator(),lhs,rhs,maxJmlType);
                    }
                } else if (tag == JCTree.OR) { 
                    if (splitExpressions) {
                        JCConditional cond = M.at(that).Conditional(that.lhs,treeutils.trueLit,that.rhs);
                        cond.setType(that.type);
                        visitConditional(cond);
                        return;
                    } else {
                        JCExpression lhs = convertExpr(that.getLeftOperand());
                        JCExpression rhs = that.getRightOperand();
                        lhs = addImplicitConversion(lhs,syms.booleanType,lhs);
                        if (translatingJML) condition = treeutils.makeAnd(that.lhs.pos, condition, treeutils.makeNot(that.lhs.pos,lhs));
                        rhs = convertExpr(rhs); // condition is used within scanExpr so this statement must follow the previous one
                        rhs = addImplicitConversion(rhs,syms.booleanType,rhs);
                        if (translatingJML) adjustWellDefinedConditions(treeutils.makeNot(that.lhs.pos,lhs));
                        result = eresult = makeBin(that,tag,that.getOperator(),lhs,rhs,maxJmlType);
                    }
                    // FIXME - add checks for numeric overflow - PLUS MINUS MUL
                }
            } finally {
                condition = prev;
            }
                
        } else if (translatingJML) {
            Type maxJmlType = that.getLeftOperand().type;
            boolean lhsIsPrim = that.getLeftOperand().type.isPrimitive() && that.getLeftOperand().type.tag != TypeTags.BOT;
            boolean rhsIsPrim = that.getRightOperand().type.isPrimitive() && that.getRightOperand().type.tag != TypeTags.BOT;
            if (jmltypes.isJmlType(that.getRightOperand().type)) maxJmlType = that.getRightOperand().type;
            if (lhsIsPrim && rhsIsPrim
                    && that.getLeftOperand().type.tag < that.getRightOperand().type.tag) maxJmlType = that.getRightOperand().type;

            JCExpression lhs = convertExpr(that.getLeftOperand());
            JCExpression rhs = that.getRightOperand();
            // FIXME - check that all the checks in makeBinaryCHecks are here - or somehow reuse that method here
            // same for unary checks
            if (tag == JCTree.DIV || tag == JCTree.MOD) {
                lhs = addImplicitConversion(lhs,that.type,lhs);
                rhs = convertExpr(rhs);
                rhs = addImplicitConversion(rhs,that.type,rhs);
                JCExpression nonzero = nonZeroCheck(that,rhs,maxJmlType);
                if (javaChecks) addAssert(that,Label.UNDEFINED_DIV0,treeutils.makeImplies(that.pos, condition, nonzero));
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
                lhs = addImplicitConversion(lhs,maxJmlType,lhs);
                rhs = convertExpr(rhs);
                rhs = addImplicitConversion(rhs,maxJmlType,rhs);
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
                lhs = addImplicitConversion(lhs,maxJmlType,lhs);
                rhs = convertExpr(rhs);
                rhs = addImplicitConversion(rhs,maxJmlType,rhs);
                if (rac) lhs = treeutils.makeUtilsMethodCall(that.pos,"real_eq",lhs,rhs);
                else lhs = treeutils.makeBinary(that.pos, JCTree.EQ, lhs, rhs);
                if (tag == JCTree.NE) lhs = treeutils.makeNot(that.pos, lhs);
                result = eresult = lhs;
                eresult.pos = that.getStartPosition();
                treeutils.copyEndPosition(eresult, that);
                return;
            } else {
                Type t = that.type;
                if (t.tag == TypeTags.BOOLEAN) {
                    // Compute a max type - FIXME - need to do this for all types
                    if (jmltypes.isJmlType(maxJmlType)) {
                        t = maxJmlType;
                    } else if (that.lhs.type.tag == TypeTags.BOT) {
                        t = boxedType(that.rhs.type);
                    } else if (that.rhs.type.tag == TypeTags.BOT) {
                        t = boxedType(that.lhs.type);
                    } else {
                        Type tlhs = unboxedType(that.getLeftOperand().type);
                        Type trhs = unboxedType(that.getRightOperand().type);
                        t = tlhs;
                        if (tlhs.tag == TypeTags.BOT || (tlhs.tag < trhs.tag && trhs.tag != TypeTags.BOT)) t = trhs;
                    }
                }
                // FIXME - this is incorrect, but handles Jml primitive types at least
//                if (jmltypes.isJmlType(t)){ 
                if (comp) lhs = addImplicitConversion(lhs,t,lhs); // FIXME - what final type
                else if (shift) lhs = addImplicitConversion(lhs,unboxedType(that.type),lhs); // FIXME - what final type
                else lhs = addImplicitConversion(lhs,that.type,lhs);
                rhs = convertExpr(rhs);
                if (comp) rhs = addImplicitConversion(rhs,t,rhs); // FIXME - what final type
                else if (shift) {
                    Type tt = unboxedType(that.rhs.type);
                    if (!tt.equals(syms.longType)) tt = syms.intType; 
                    rhs = addImplicitConversion(rhs,syms.intType,rhs); // FIXME - what is tt used for?
                }
                else rhs = addImplicitConversion(rhs,that.type,rhs);
            }
            // FIXME - add checks for numeric overflow - PLUS MINUS MUL
            if (!translatingJML) addBinaryChecks(that,tag,lhs,rhs,null);
            result = eresult = makeBin(that,tag,that.getOperator(),lhs,rhs,maxJmlType);
            if (!translatingJML) result = eresult = newTemp(eresult); // FIXME - use splitExpressions?

        } else {
            Symbol s = that.getOperator();
            Type maxJmlType = that.getLeftOperand().type;
            boolean lhsIsPrim = that.getLeftOperand().type.isPrimitive() && that.getLeftOperand().type.tag != TypeTags.BOT;
            boolean rhsIsPrim = that.getRightOperand().type.isPrimitive() && that.getRightOperand().type.tag != TypeTags.BOT;
            if (jmltypes.isJmlType(that.getRightOperand().type)) maxJmlType = that.getRightOperand().type;
            if (lhsIsPrim && rhsIsPrim
                    && that.getLeftOperand().type.tag < that.getRightOperand().type.tag) maxJmlType = that.getRightOperand().type;
                    
            Type t = that.type;
            if (t.tag == TypeTags.BOOLEAN) {
                // Compute a max type - FIXME - need to do this for all types
                if (jmltypes.isJmlType(maxJmlType)) {
                    t = maxJmlType;
                } else if (that.lhs.type.tag == TypeTags.BOT) {
                    t = boxedType(that.rhs.type);
                } else if (that.rhs.type.tag == TypeTags.BOT) {
                    t = boxedType(that.lhs.type);
                } else {
                    Type tlhs = unboxedType(that.getLeftOperand().type);
                    Type trhs = unboxedType(that.getRightOperand().type);
                    t = tlhs;
                    if (tlhs.tag == TypeTags.BOT || (tlhs.tag < trhs.tag && trhs.tag != TypeTags.BOT)) t = trhs;
                }
            }
            JCExpression lhs = convertExpr(that.getLeftOperand());
            {
                if (comp) lhs = addImplicitConversion(lhs,t,lhs);
                else if (shift) lhs = addImplicitConversion(lhs,unboxedType(that.type),lhs); // FIXME - what final type
                else lhs = addImplicitConversion(lhs,that.type,lhs);
            }
            
            JCExpression rhs = convertExpr(that.getRightOperand());
            {
                if (comp) rhs = addImplicitConversion(rhs,t,rhs);
                else if (shift) {
                    Type tt = unboxedType(that.rhs.type);
                    if (!tt.equals(syms.longType)) tt = syms.intType; 
                    rhs = addImplicitConversion(rhs,tt,rhs);  // FIXME - tt or int as above?
                }
                else rhs = addImplicitConversion(rhs,that.type,rhs);
            }
            
            addBinaryChecks(that,tag,lhs,rhs,null);
            JCBinary bin = treeutils.makeBinary(that.pos,tag,that.getOperator(),lhs,rhs);
            result = eresult = newTemp(bin);
        }
        eresult.pos = that.getStartPosition(); // Need to make the start of the temporary Ident the same as the start of the expression it represents
        treeutils.copyEndPosition(eresult, that);
    }
    
    /** Returns the AST for (rhs != 0), for the appropriate type */
    public JCExpression nonZeroCheck(JCTree that, JCExpression rhs, Type maxJmlType) {
        JCExpression nonzero;
        if (rac && maxJmlType == jmltypes.BIGINT) {
            nonzero = treeutils.makeUtilsMethodCall(that.pos, "bigint_nonzero", rhs);
        } else if (rac && maxJmlType == jmltypes.REAL) {
            nonzero = treeutils.makeUtilsMethodCall(that.pos, "real_nonzero", rhs);
        } else {
            nonzero = treeutils.makeBinary(that.pos, JCTree.NE, rhs, treeutils.makeIntLiteral(rhs.pos, 0)); // FIXME - long, float, double?
        }
        return nonzero;
    }
    
    protected JCExpression makeBin(JCTree that, int tag, Symbol opSym, JCExpression lhs, JCExpression rhs, Type maxJmlType) {
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
                    // FIXME - need shift types
                    default: {
                        String msg = "Unexpected operation tag in JmlAssertionAdder.makeBin: " + tag;
                        log.error(that.pos,"jml.internal",msg);
                        throw new JmlInternalError(msg);
                    }
                }
                String pre = maxJmlType == jmltypes.BIGINT ? "bigint_" : "real_";
                return treeutils.makeUtilsMethodCall(that.pos,pre+fcn,lhs,rhs);
            } else {
                String msg = "Unexpected JML type in JmlAssertionAdder.makeBin: " + maxJmlType;
                log.error(that.pos,"jml.internal",msg);
                throw new JmlInternalError(msg);
            }
        } else {
            return treeutils.makeBinary(that.pos,tag,opSym,lhs,rhs);
        }

    }
    
    public long maxValue(int pos, int tag) {
        switch (tag) {
            case TypeTags.INT: return Integer.MAX_VALUE;
            case TypeTags.SHORT: return Short.MAX_VALUE;
            case TypeTags.LONG: return Long.MAX_VALUE;
            case TypeTags.BYTE: return Byte.MAX_VALUE;
            case TypeTags.CHAR: return Character.MAX_VALUE;
            default:
                log.error(pos,"jml.internal","Unknown type tag " + tag);
                return 0;
        }
    }

    public long minValue(int pos, int tag) {
        switch (tag) {
            case TypeTags.INT: return Integer.MIN_VALUE;
            case TypeTags.SHORT: return Short.MIN_VALUE;
            case TypeTags.LONG: return Long.MIN_VALUE;
            case TypeTags.BYTE: return Byte.MIN_VALUE;
            case TypeTags.CHAR: return Character.MIN_VALUE;
            default:
                log.error(pos,"jml.internal","Unknown type tag " + tag);
                return 0;
        }
    }
    

    @Override
    public void visitTypeCast(JCTypeCast that) {
        // Note - casting a null produces a null value
        Type origType = that.getExpression().type;
        JCExpression arg = convertExpr(that.getExpression());
        JCTree newTypeTree = that.getType(); // the tree, not the Type
        JCTree clazz = convert(newTypeTree);
        
        if (rac && that.type.isPrimitive() && jmltypes.isJmlType(origType)) {
            if (jmltypes.isSameType(that.type,origType)) {
                result = eresult = arg; // No-op
                // FIXME - will need a cast from real to bigint
            } else {
                // FIXME - the null here should be an error
                String s = (origType == jmltypes.BIGINT ? "bigint_to" :
                            origType == jmltypes.REAL ? "real_to" : null) + newTypeTree.toString();
                JCExpression e = treeutils.makeUtilsMethodCall(that.pos,s,arg);
                result = eresult = e;
            }
            return;
        }
        JCTypeCast castexpr = M.at(that).TypeCast(clazz,arg);
        castexpr.setType(that.type); // may be superfluous
        treeutils.copyEndPosition(castexpr,that);
        JCExpression newexpr = castexpr;
        
        if (pureCopy) {
            result = eresult = newexpr;
            return;
        }
        
        // Check that expression is null
        JCExpression eqnull = treeutils.makeEqObject(that.pos,arg,treeutils.makeNullLiteral(that.pos));

        JCExpression emax = null, emin = null;
        boolean increasePrecision = false;
        if (types.isSameType(clazz.type,origType)) {
            // redundant - remove the cast in both rac and esc
            newexpr = arg;
        } else if (clazz.type.isPrimitive()) {
            if (origType.isPrimitive()) {
                // Java primitive to Java primitive - must be a numeric cast
                if (origType.tag > that.type.tag) switch (origType.tag) {
                    case TypeTags.LONG:
                        emax = treeutils.makeBinary(that.pos, JCTree.LE, arg, 
                                treeutils.makeLit(that.pos, arg.type, Long.valueOf(maxValue(that.pos,that.type.tag))));
                        emin = treeutils.makeBinary(that.pos, JCTree.LE,  
                                treeutils.makeLit(that.pos, arg.type, Long.valueOf(minValue(that.pos,that.type.tag))),
                                arg);
                        break;
                    case TypeTags.INT:
                    case TypeTags.SHORT:
                    case TypeTags.CHAR:
                    case TypeTags.BYTE:
                        emax = treeutils.makeBinary(that.pos, JCTree.LE, arg, 
                                treeutils.makeLit(that.pos, arg.type, Integer.valueOf((int)maxValue(that.pos,that.type.tag))));
                        emin = treeutils.makeBinary(that.pos, JCTree.LE,  
                                treeutils.makeLit(that.pos, arg.type, Integer.valueOf((int)minValue(that.pos,that.type.tag))),
                                arg);
                        break;
                    default:
                        log.error(that, "jml.internal", "Unimplemented case combination");
                    case TypeTags.FLOAT: // FIXME - ignore for now
                    case TypeTags.DOUBLE:
                        emax = emin = treeutils.trueLit;
                        // Must be numeric to numeric - do numeric range checks
                        // FIXME - implement
                }
                if (origType.tag > that.type.tag) {
                    // reducing precision - make assertions about range of input value
                    addAssert(that, Label.ARITHMETIC_RANGE, emax);
                    addAssert(that, Label.ARITHMETIC_RANGE, emin);
                } else {
                    // increasing precision - make assumptions about range of output value
                    increasePrecision = true;
                    // FIXME
                }

            } else if (jmltypes.isSameType(origType,jmltypes.BIGINT)) {
                // \bigint to primitive
                    // FIXME - reducing precision - check range
                String s = "bigint_to"  + that.type.toString();
                JCExpression e = treeutils.makeUtilsMethodCall(that.pos,s,arg);
                newexpr = e;
            } else if (jmltypes.isSameType(origType,jmltypes.REAL)) {
                // \real to primitive
                    // FIXME - reducing precision - check range
                String s = "real_to" + that.type.toString();
                JCExpression e = treeutils.makeUtilsMethodCall(that.pos,s,arg);
                newexpr = e;

            } else {
                // unboxing = FIXME = check type combinations
                JCExpression e = treeutils.makeNot(that.pos,  eqnull);
                if (translatingJML) {
                    addAssert(that, Label.UNDEFINED_NULL_UNBOX, 
                            treeutils.makeImplies(that.pos,  condition,  e));
                    
                } else {
                    addAssert(that, Label.POSSIBLY_NULL_UNBOX, e);
                }
                newexpr = rac ? castexpr : createUnboxingExpr(arg);
            }
        } else if (jmltypes.isSameType(clazz.type,jmltypes.BIGINT)) {
            if (origType.isPrimitive()) {
                // FIXME - need assumptions about range of output
                // Java primitive to JML \bigint - must be a numeric cast
                switch (origType.tag) {
                    case TypeTags.LONG:
                    case TypeTags.INT:
                    case TypeTags.SHORT:
                    case TypeTags.CHAR:
                    case TypeTags.BYTE:
                        String s = "bigint_valueOf";
                        JCExpression e = treeutils.makeUtilsMethodCall(that.pos,s,arg);
                        newexpr = e;
                        break;
                    case TypeTags.FLOAT:
                    case TypeTags.DOUBLE:
                        // FIXME float/double to bigint
                        // continue using cast expression
                        break;
                    default:
                        log.error(that.pos,"jml.internal","Unexpected cast from " + origType + " to " + that.type);
                        // continue using cast expression
                }
            } else if (jmltypes.isSameType(origType,jmltypes.BIGINT)) {
                // this case should not happen
                newexpr = arg;
            } else if (jmltypes.isSameType(origType,jmltypes.REAL)) {
                // FIXME - reducing precision \real to \bigint
                String s = "real_to"  + that.type.toString();
                JCExpression e = treeutils.makeUtilsMethodCall(that.pos,s,arg);
                newexpr = e;

            } else {
                // FIXME - unboxing numeric reference to \bigint
            }            
        } else if (jmltypes.isSameType(clazz.type,jmltypes.REAL)) {
            if (origType.isPrimitive()) {
                // Java primitive to JML \real - must be a numeric cast
                // FIXME - need assumptions about range of output
                String s = "real_valueOf";
                JCExpression e = treeutils.makeUtilsMethodCall(that.pos,s,arg);
                newexpr = e;

            } else if (jmltypes.isSameType(origType,jmltypes.BIGINT)) {
                // convert \bigint to \real
                String s = "bigint_to"  + that.type.toString();
                JCExpression e = treeutils.makeUtilsMethodCall(that.pos,s,arg);
                newexpr = e;
                
            } else if (jmltypes.isSameType(origType,jmltypes.REAL)) {
                // this case should not happen
                newexpr = arg;

            } else {
                // FIXME - unboxing numeric reference to \real
            }            

        } else {
            if (origType.isPrimitive()) {
                // Must be primitive to object (boxing) 
                // OK for Rac
                newexpr = rac ? castexpr : createBoxingStatsAndExpr(arg,clazz.type);
            } else if (jmltypes.isSameType(origType,jmltypes.BIGINT)) {
                // FIXME - box a \bigint to reference
                
            } else if (jmltypes.isSameType(origType,jmltypes.REAL)) {
                // FIXME - box a \real to reference

            } else {
                // object to object
                // For RAC, we check that the expression will not throw an exception
                // and then we calculate it
                // For ESC, we do the same check, but we don't do the cast
                
                JCTree erasure = clazz;
                if (clazz instanceof JCTypeApply) erasure = ((JCTypeApply)clazz).clazz;
                
                JCExpression typeok = M.at(that).TypeTest(arg, erasure);
                typeok.setType(syms.booleanType);
                // FIXME - end position?
                
                JCExpression cond = treeutils.makeOr(that.pos, eqnull, typeok);
                if (javaChecks && localVariables.isEmpty()) {
                    if (!splitExpressions) cond = treeutils.makeImplies(that.pos,condition,cond);
                    addAssert(that,translatingJML ? Label.UNDEFINED_BADCAST : Label.POSSIBLY_BADCAST, cond, arg.type, clazz.type);
                }
                newexpr = castexpr;
            }
        }
        result = eresult = !splitExpressions ? newexpr : newTemp(newexpr);
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
        JCInstanceOf e = M.at(that).TypeTest(lhs,clazz);
        e.setType(that.type);
        treeutils.copyEndPosition(e,that);
        result = eresult = (translatingJML || pureCopy) ? e : newTemp(e);

    }

    // OK
    @Override
    public void visitIndexed(JCArrayAccess that) {

        JCExpression indexed = convertExpr(that.indexed);

        // FIXME - resolve the use of splitExpressions vs. !pureCopy
        
        // FIXME - for now we don't check undefinedness inside quantified expressions
        if (javaChecks && !pureCopy && localVariables.isEmpty()) {
            JCExpression nonnull = treeutils.makeNeqObject(that.indexed.pos, indexed, 
                    treeutils.makeNullLiteral(that.indexed.getEndPosition(log.currentSource().getEndPosTable())));
            if (translatingJML) {
                nonnull = treeutils.makeImplies(that.pos, condition, nonnull);
                addAssert(that,Label.UNDEFINED_NULL_DEREFERENCE,nonnull);
            } else {
                addAssert(that,Label.POSSIBLY_NULL_DEREFERENCE,nonnull);
            }
        }

        JCExpression index = convertExpr(that.index);
        index = addImplicitConversion(index,syms.intType,index);
        if (javaChecks && !pureCopy && localVariables.isEmpty()) {
            JCExpression compare = treeutils.makeBinary(that.index.pos, JCTree.LE,
                    treeutils.intleSymbol,
                    treeutils.makeIntLiteral(that.index.pos, 0), 
                    index);
            if (translatingJML) {
                compare = treeutils.makeImplies(that.pos, condition, compare);
                addAssert(that,Label.UNDEFINED_NEGATIVEINDEX,compare);
            } else {
                addAssert(that,Label.POSSIBLY_NEGATIVEINDEX,compare);
            }
        }
        
        JCExpression length = treeutils.makeLength(that.indexed,indexed);
        if (javaChecks && !pureCopy && localVariables.isEmpty()) {
            JCExpression compare = treeutils.makeBinary(that.pos, JCTree.GT, treeutils.intgtSymbol, length, 
                    index); // We use GT to preserve the textual order of the subexpressions
            if (translatingJML) {
                compare = treeutils.makeImplies(that.pos, condition, compare);
                addAssert(that,Label.UNDEFINED_TOOLARGEINDEX,compare);
            } else {
                addAssert(that,Label.POSSIBLY_TOOLARGEINDEX,compare);
            }
        }

//        if (!pureCopy && !translatingJML) checkAccess(JmlToken.ACCESSIBLE, that, that, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);

        if (pureCopy && !(that instanceof JmlBBArrayAccess)) {
            JCArrayAccess aa = M.at(that).Indexed(indexed,index);
            aa.setType(that.type);
            result = eresult = aa;
        } else {
            JmlBBArrayAccess aa = new JmlBBArrayAccess(null,indexed,index); // FIXME - switch to factory
            aa.pos = that.pos;
            aa.setType(that.type);
            aa.arraysId = that instanceof JmlBBArrayAccess ? ((JmlBBArrayAccess)that).arraysId : null;
            result = eresult = (translatingJML || pureCopy) ? aa : newTemp(aa);
        }

        treeutils.copyEndPosition(result, that);
    }

    // OK
    @Override
    public void visitSelect(JCFieldAccess that) {
        JCExpression selected;
        if (pureCopy || localVariables.containsKey(that.sym)) {
            result = eresult = treeutils.makeSelect(that.pos, convertExpr(that.getExpression()), that.sym);
        } else if (translatingJML && that.sym == null) {
            // This can happen while scanning a store-ref x.* 
            JCExpression sel = convertJML(that.selected); // FIXME - what if static; what if not a variable
            JCFieldAccess fa = M.Select(sel, (Name)null);
            fa.pos = that.pos;
            fa.sym = null;
            result = eresult = fa;
        } else if (translatingJML && attr.isModel(that.sym) && !convertingAssignable) {
            JCExpression sel = convertJML(that.selected); // FIXME - what if static; what if not a variable
            if (rac) {
                Name mmName = names.fromString(Strings.modelFieldMethodPrefix + that.name.toString());
                JmlSpecs.TypeSpecs tyspecs = specs.getSpecs((ClassSymbol)that.sym.owner);
                for (JmlTypeClauseDecl x: tyspecs.modelFieldMethods) {
                    if (x.decl instanceof JmlMethodDecl && ((JmlMethodDecl)x.decl).name.equals(mmName)) {
                        JmlMethodDecl md = (JmlMethodDecl)x.decl;
                        JCMethodInvocation app = treeutils.makeMethodInvocation(that,sel,md.sym);
                        result = eresult = app;
                        treeutils.copyEndPosition(result, that);
                        return;
                    }
                }
                if (that.sym.name.toString().equals("erasure") && that.sym instanceof MethodSymbol && utils.qualifiedMethodName((MethodSymbol)that.sym).equals("org.jmlspecs.lang.JML.erasure")) {
                    
                    JCMethodInvocation m = treeutils.makeUtilsMethodCall(that.pos,"erasure");
                    result = eresult = m.meth;
                    return;
                }
                // This is an internal error - the wrapper for the model field method
                // should have been created during the MemberEnter phase.
                throw new NoModelMethod();
            }
            if (esc) {
                JCFieldAccess fa = M.Select(sel, that.name);
                fa.pos = that.pos;
                fa.sym = that.sym;
                fa.type = that.type;
                result = eresult = fa;
                if (fa.sym instanceof VarSymbol && specs.isNonNull(fa.sym)) {
                    JCExpression nonnull = treeutils.makeNeqObject(that.pos,fa,treeutils.nullLit);
                    condition = treeutils.makeAnd(fa.pos, condition, nonnull);
                }
                TypeSpecs tspecs = specs.getSpecs((ClassSymbol)that.sym.owner);
                for (JmlTypeClause tc : tspecs.clauses) {
                    if (tc.token == JmlToken.REPRESENTS) {
                        JmlTypeClauseRepresents rep = (JmlTypeClauseRepresents)tc;

                        if (((JCIdent)rep.ident).sym.equals(that.sym)) {
                            // FIXME - why this?
//                            if (oldenv == null) {
//                                JmlStatementHavoc st = M.at(that.pos).JmlHavocStatement(List.<JCExpression>of(rep.ident));
//                                addStat(st);
//                            }
                            if (rep.suchThat){
                                addAssume(that,Label.IMPLICIT_ASSUME,
                                        convertExpr(rep.expression));

                            } else {
                                // FIXME - This does not work if the model variable is used within a pure method spec, because it ends up in the body of a constructed quantifier, but localVariables is not used
//                                if (localVariables.isEmpty()) {
//                                    addAssumeEqual(that,Label.IMPLICIT_ASSUME,
//                                            convertExpr(rep.ident),
//                                            convertExpr(rep.expression));
//                                } else {
                                JCIdent thisId = currentThisId;
                                JCExpression thisExpr = currentThisExpr;
                                try {
                                    currentThisExpr = sel;
                                    currentThisId = sel instanceof JCIdent ? (JCIdent)sel : null;
                                    result = eresult = convertExpr(rep.expression);
                                } finally {
                                    currentThisId = thisId;
                                    currentThisExpr = thisExpr;
                                }
                                    // FIXME - we could get recursion here
                                return;
//                                }
                            }
                        }
                    }
                }
                return;
            }
        } else if (that.sym instanceof Symbol.TypeSymbol) {
            // This is a type name, so the tree should be copied, but without inserting temporary assignments
            // makeType creates a fully-qualified name
            result = eresult = treeutils.makeType(that.pos,that.type);
        } else if (translatingJML && esc && !localVariables.isEmpty()) {
            selected = convertExpr(that.selected);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,selected,that.sym);
            result = eresult = fa;
            if (oldenv != null) {
                result = eresult = treeutils.makeOld(that.pos,eresult,oldenv);
            }
//        } else if (translatingJML) {
//            selected = convertExpr(that.selected);
//            boolean var = false;
//            JCFieldAccess fa = treeutils.makeSelect(that.pos,selected,that.sym);
//            result = eresult = fa;
//            if (oldenv != null) {
//                result = eresult = treeutils.makeOld(that.pos,eresult,oldenv);
//            }
        } else {
            selected = convertExpr(that.selected);
            boolean var = false;
            if (!utils.isJMLStatic(that.sym) && that.selected instanceof JCIdent && !localVariables.containsKey(((JCIdent)that.selected).sym)) {
                if (convertingAssignable && currentFresh != null && selected instanceof JCIdent && ((JCIdent)selected).sym == currentFresh.sym) {
                    // continue
                } else {
                    JCExpression nonnull = treeutils.makeNeqObject(that.pos, selected, 
                            treeutils.nullLit);
                    if (translatingJML) nonnull = treeutils.makeImplies(that.pos, condition, nonnull);
                    if (javaChecks && localVariables.isEmpty()) {
                        addAssert(that,
                                translatingJML? Label.UNDEFINED_NULL_DEREFERENCE : Label.POSSIBLY_NULL_DEREFERENCE,
                                        nonnull); // FIXME - what if the dereference happens in a spec in a different file - ,that,log.currentSourceFile());
                    }
                }
                var = true;
            }
            if (that.sym.owner instanceof ClassSymbol) {
                if (specs.isNonNull(that.sym,classDecl.sym) && that.sym instanceof VarSymbol && !localVariables.containsKey(that.sym)
                        && (!methodDecl.sym.isConstructor() || utils.isJMLStatic(that.sym))) {
                    if (convertingAssignable && currentFresh != null && selected instanceof JCIdent && ((JCIdent)selected).sym == currentFresh.sym) {
                        // continue
                    } else {
                        JCFieldAccess e = M.at(that).Select(selected,that.name);
                        e.sym = that.sym;
                        e.type = that.type;
                        JCExpression nl = treeutils.makeNullLiteral(that.pos);
                        treeutils.copyEndPosition(nl,e);
                        JCExpression nonnull = treeutils.makeNeqObject(that.pos, e, nl);
                        addAssume(nonnull,Label.NULL_FIELD,nonnull);
                    }
                }
            }
    //        if (!translatingJML && !pureCopy && that.sym != syms.lengthVar) checkAccess(JmlToken.ACCESSIBLE, that, that, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,selected,that.sym);
            result = eresult = (translatingJML || !var) ? fa : newTemp(fa);
            if (oldenv != null) {
                result = eresult = treeutils.makeOld(that.pos,eresult,oldenv);
            }
        }
        treeutils.copyEndPosition(result, that);
        if (translatingJML && !pureCopy && that.sym instanceof VarSymbol && specs.isNonNull(that.sym) ) {
            JCExpression nn = treeutils.makeNeqObject(that.pos,eresult,treeutils.nullLit);
            condition = treeutils.makeAnd(that.pos, condition, nn);
        }
    }
    
    public static class NoModelMethod extends RuntimeException {
        private static final long serialVersionUID = 1L;
    }
    
    // FIXME - check use of condition everywhere 
    
    java.util.List<Symbol> reps = new LinkedList<Symbol>();
    
    // OK
    @Override
    public void visitIdent(JCIdent that) {
        if (pureCopy) {
            JCIdent id = treeutils.makeIdent(that.pos, that.name, that.sym);
            result = eresult = id;
            treeutils.copyEndPosition(eresult, that);
            return;
        }
        try {
        // If we are translating the postcondition then parameters
        // must be mapped to the values at the beginning of the method, 
        // not the current values
        if (translatingJML) {
            JCVariableDecl decl;
            if (!isPostcondition) {
                JCExpression actual = paramActuals == null ? null : paramActuals.get(that.sym);
                if (actual != null) {
                    // Replicate the AST so we are not sharing ASTs across multiple
                    // instances of the original ID.
                    result = eresult = convertCopy(actual);
                    eresult.pos = that.pos; // FIXME - this might be better if the actual were converted to a temporary Ident
                    treeutils.copyEndPosition(eresult, that);
                    return;
                }
            }
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

        if (attr.isModel(that.sym) && that.sym instanceof VarSymbol && !convertingAssignable) {
            if (!reps.contains(that.sym)) {
                reps.add(0,that.sym);
                try {
                    if (rac) {
                        Name mmName = names.fromString(Strings.modelFieldMethodPrefix + that.name.toString());
                        JmlSpecs.TypeSpecs tyspecs = specs.getSpecs(classDecl.sym);
                        for (JmlTypeClauseDecl x: tyspecs.modelFieldMethods) {
                            if (x.decl instanceof JmlMethodDecl && ((JmlMethodDecl)x.decl).name.equals(mmName)) {
                                JmlMethodDecl md = (JmlMethodDecl)x.decl;
                                JCMethodInvocation app = treeutils.makeMethodInvocation(that,currentThisExpr,md.sym);
                                result = eresult = app;
                                treeutils.copyEndPosition(eresult, that);
                                return;
                            }
                        }
                        if (rac) throw new NoModelMethod();
                        error(that, "No corresponding model method for " + that.sym);
                        return;
                    }
                    if (esc) {
                        TypeSpecs tspecs = specs.getSpecs((ClassSymbol)that.sym.owner);
                        for (JmlTypeClause tc : tspecs.clauses) {
                            if (tc.token == JmlToken.REPRESENTS) {
                                JmlTypeClauseRepresents rep = (JmlTypeClauseRepresents)tc;

                                if (((JCIdent)rep.ident).sym.equals(that.sym)) {
                                    // FIXME - why this?
//                                    if (oldenv == null) {
//                                        JmlStatementHavoc st = M.at(that.pos).JmlHavocStatement(List.<JCExpression>of(rep.ident));
//                                        addStat(st);
//                                    }
                                    if (rep.suchThat){
                                        addAssume(that,Label.IMPLICIT_ASSUME,
                                                convertExpr(rep.expression));

                                    } else {
                                        // FIXME - This does not work if the model variable is used within a pure method spec, because it ends up in the body of a constructed quantifier, but localVariables is not used
//                                        if (localVariables.isEmpty()) {
//                                            addAssumeEqual(that,Label.IMPLICIT_ASSUME,
//                                                    convertExpr(rep.ident),
//                                                    convertExpr(rep.expression));
//                                        } else {
                                            result = eresult = convertExpr(rep.expression);
                                            // FIXME - we could get recursion here
                                            return;
//                                        }
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
            
        } else if (localVariables.containsKey(that.sym)) {
            // just copy
            Symbol sym = localVariables.get(that.sym);
            if (sym == null) {
                // FIXME - error
                sym = that.sym;
            }
            result = eresult = treeutils.makeIdent(that.pos,sym);
            
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

        } else if (currentThisExpr instanceof JCIdent && that.sym == ((JCIdent)currentThisExpr).sym) {
            // 'this' - leave it as it is
            result = eresult = convertCopy(currentThisExpr);
            
        } else if (that.name.toString().equals("this")) {
            result = eresult = currentThisExpr != null ? convertCopy(currentThisExpr) : convertCopy(that);
            
        } else if (that.name.toString().equals("super")) {
            result = eresult = currentThisExpr != null ? convertCopy(currentThisExpr) : convertCopy(that); // FIXME - want this instead of super

        } else if (!utils.isJMLStatic(that.sym)) {
            // It is a non-static class field, so we prepend 'this'
            // FIXME - do we need to use the current this?
            JCExpression cId = currentThisExpr != null ? currentThisExpr : getThisId(classDecl.sym); // FIXME - why would this be null - it cat be at least if we are checking a single method
//            if (rac && cId.toString().equals("THIS")) Utils.print("");
            JCExpression fa = treeutils.makeSelect(that.pos,cId,that.sym);
            if (that.sym instanceof VarSymbol && that.sym.owner instanceof ClassSymbol && specs.isNonNull(that.sym, classDecl.sym) && !localVariables.isEmpty()) {
                JCExpression e = treeutils.makeNeqObject(that.pos, fa, treeutils.nullLit);
                addAssume(that,Label.NULL_FIELD,e);
            }
            // FIXME - need a better way to test for presence of this - here and below
//            if (!translatingJML && !pureCopy && !"this".equals(that.sym.toString())) checkAccess(JmlToken.ACCESSIBLE, that, fa, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);
            result = eresult = fa;
            
        } else {
            if (that.name.toString().equals("this")) {
                System.out.println("STATIC THIS");
            }
            // static class field - add the qualified name
            JCExpression typetree = treeutils.makeType(that.pos,that.sym.owner.type);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,typetree,that.sym);
            if (!translatingJML && that.sym instanceof VarSymbol && that.sym.owner instanceof ClassSymbol && specs.isNonNull(that.sym, (ClassSymbol)that.sym.owner)) {
                JCExpression e = treeutils.makeNeqObject(that.pos, fa, treeutils.nullLit);
                addAssume(that,Label.NULL_FIELD,e);
            }
            // FIXME - need a better way to test for presence of this - here and below
            //if (!translatingJML && !pureCopy && !"this".equals(that.sym.toString())) checkAccess(JmlToken.ACCESSIBLE, that, fa, (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);
            result = eresult = fa;
        }
        treeutils.copyEndPosition(eresult, that);
        if (oldenv != null) {
            result = eresult = treeutils.makeOld(that.pos, eresult, oldenv);
            treeutils.copyEndPosition(eresult, that);
        }
        
        } finally {
            if (translatingJML && that.sym instanceof VarSymbol && specs.isNonNull(that.sym)) {
                JCExpression nn = treeutils.makeNeqObject(that.pos,eresult,treeutils.nullLit);
                condition = treeutils.makeAnd(that.pos, condition, nn);
            }

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
        if (pureCopy || rac) return;
        if (types.isSameType(that.type,syms.stringType)) {
            JCIdent id = newTemp(that);
            JCExpression e = treeutils.makeNeqObject(that.pos,id,treeutils.nullLit);
            addAssume(that,Label.IMPLICIT_ASSUME,e);

            // These assumptions are necessary so that String literals are
            // known to satisfy the invariants about Strings
            addInvariants(id,id.type.tsym,id,currentStatements,false,false,false,false,false,true,Label.INVARIANT_ENTRANCE,utils.qualifiedMethodSig(methodDecl.sym));

            result = eresult = id;
        }
        
    }

    // OK
    @Override
    public void visitTypeIdent(JCPrimitiveTypeTree that) {
        // This is a simple primitive type
        eresult = that;
        if (fullTranslation) {
            eresult = M.at(that).TypeIdent(that.typetag).setType(that.type);
        }
        result = eresult;
    }

    @Override
    public void visitTypeArray(JCArrayTypeTree that) {
        // This is a type literal that is an array - we just copy it
        if (fullTranslation) {
            result = eresult = M.at(that).TypeArray(convertExpr(that.elemtype)).setType(that.type);
        } else {
            result = eresult = that;
        }
    }

    // OK
    @Override
    public void visitTypeApply(JCTypeApply that) {
        // This is a type literal which is the application of a generic type to its parameters
        result = eresult = !fullTranslation ? that :
            M.at(that).TypeApply(convertExpr(that.clazz),convertExprList(that.arguments)).setType(that.type);
    }

    // OK
    @Override
    public void visitTypeParameter(JCTypeParameter that) {
        // This is a formal class type parameter, possibly including bounds
        result = !fullTranslation ? that :
            M.at(that).TypeParameter(that.name, convertExprList(that.bounds)).setType(that.type);
    }

    // OK
    @Override
    public void visitWildcard(JCWildcard that) {
        // This is a wildcard (?) type
        result = eresult = !fullTranslation ? that :
            M.at(that).Wildcard(convert(that.kind),convert(that.inner)).setType(that.type);
    }

    // OK
    @Override
    public void visitTypeBoundKind(TypeBoundKind that) {
        result = !fullTranslation ? that :
            M.at(that).TypeBoundKind(that.kind).setType(that.type);
    }

    // OK
    @Override
    public void visitAnnotation(JCAnnotation that) {
        // Only needed for a full tree copy
        // A JCAnnotation is a kind of JCExpression
        if (fullTranslation) {
            JCTree aType = convertCopy(that.annotationType);
            List<JCExpression> args = convertCopy(that.args);
            JCAnnotation a = M.at(that).Annotation(aType,args);
            a.setType(that.type);
            treeutils.copyEndPosition(a,that);
            result = eresult = a;
        } else {
            result = eresult = that;
        }
    }

    // TODO: No checks are performed on annotations or modifiers

    // OK
    @Override
    public void visitModifiers(JCModifiers that) {
        if (fullTranslation) {
            ListBuffer<JCAnnotation> annotations = new ListBuffer<JCAnnotation>();
            for (JCAnnotation a: that.annotations) {
                annotations.add(convertCopy(a));
            }
            JCModifiers mods = M.at(that).Modifiers(that.flags, annotations.toList());
            result = mods;
        } else {
            result = that;
        }
    }

    // OK
    @Override
    public void visitErroneous(JCErroneous that) {
        List<? extends JCTree> errs = fullTranslation ? convertCopy(that.errs) : that.errs;
        result = eresult = M.at(that).Erroneous(errs).setType(that.type);
    }

    // OK
    @Override
    public void visitLetExpr(LetExpr that) {
        if (splitExpressions) {
            JCIdent id = newTempNull(that,that.type); // Adds a declaration
            pushBlock();
            try {
                for (JCVariableDecl d : that.defs) {
                    convert(d);
                }
                JCExpression e = convertExpr((JCExpression)that.expr);
                addStat(treeutils.makeAssignStat(that.pos,treeutils.makeIdent(id.pos, id.sym),e));
            } finally {
                addStat(popBlock(0L,that));
                result = eresult = treeutils.makeIdent(id.pos,id.sym);
            }
        } else {
            result = eresult = M.at(that).LetExpr(convert(that.defs), convert(that.expr)).setType(that.type);
        }
    }

    // OK
    @Override
    public void visitJmlBinary(JmlBinary that) {
        JCExpression saved = condition;
        try {
            JCExpression lhs = convertExpr(that.lhs);
            if (pureCopy) {
                JCExpression rhs = convertExpr(that.rhs);
                JCExpression t = M.at(that.pos).JmlBinary(that.op,lhs,rhs);
                t.type = that.type;
                result = eresult = t;
                return;
            }
            if (that.op != JmlToken.SUBTYPE_OF && that.op != JmlToken.JSUBTYPE_OF) {
                lhs = addImplicitConversion(that.lhs,that.type,lhs);
            }
            JCExpression rhs,t;
            switch (that.op) {
                case IMPLIES: // P ==> Q is !P || Q
                    if (translatingJML) condition = treeutils.makeAnd(that.pos, condition, lhs);
                    if (splitExpressions) {  // temp = true; if (P) { temp = Q; }
                        JCIdent id = newTemp(treeutils.trueLit);
                        pushBlock();
                        try {
                            rhs = convertExpr(that.rhs);
                            rhs = addImplicitConversion(that.rhs,that.type,rhs);
                            addStat(treeutils.makeAssignStat(that.rhs.pos,treeutils.makeIdent(rhs.pos, id.sym), rhs));
                        } finally { // Particularly NoModelMethod
                            JCBlock bl = popBlock(0L,that.rhs);
                            addStat(M.If(lhs, bl, null));
                        }
                        eresult = treeutils.makeIdent(that.pos, id.sym);
                    } else { 
                        rhs = convertExpr(that.rhs);
                        rhs = addImplicitConversion(that.rhs,that.type,rhs);
                        t = treeutils.makeNot(lhs.pos, lhs);
                        t = treeutils.makeOr(that.pos, t, rhs);
                        eresult = t;
                    }
                    if (translatingJML) adjustWellDefinedConditions(lhs);
                    break;

                case REVERSE_IMPLIES: // P <== Q is P || !Q 
                    t = treeutils.makeNot(lhs.pos, lhs);
                    if (translatingJML) condition = treeutils.makeAnd(that.pos, condition, t);
                    if (splitExpressions) { // temp = true; if (not P) { temp = (not Q); }
                        JCIdent id = newTemp(treeutils.trueLit);
                        pushBlock();
                        try {
                            rhs = convertExpr(that.rhs);
                            rhs = addImplicitConversion(that.rhs,that.type,rhs);
                            addStat(treeutils.makeAssignStat(that.rhs.pos,treeutils.makeIdent(rhs.pos, id.sym), treeutils.makeNot(rhs.pos, rhs)));
                        } finally {
                            JCBlock bl = popBlock(0L,that.rhs);
                            addStat(M.If(treeutils.makeNot(lhs.pos, lhs), bl, null));
                        }
                        eresult = treeutils.makeIdent(that.pos, id.sym);
                    } else {
                        rhs = convertExpr(that.rhs);
                        rhs = addImplicitConversion(that.rhs,that.type,rhs);
                        rhs = treeutils.makeNot(that.rhs.pos, rhs);
                        t = treeutils.makeOr(that.pos, lhs, rhs);
                        eresult = t;
                    }
                    if (translatingJML) adjustWellDefinedConditions(t);
                    break;

                case EQUIVALENCE:
                    rhs = convertExpr(that.rhs);
                    rhs = addImplicitConversion(that.rhs,that.type,rhs);
                    t = treeutils.makeBinary(that.pos, JCTree.EQ, treeutils.booleqSymbol, lhs, rhs);
                    eresult = splitExpressions ? newTemp(t) : t;
                    break;

                case INEQUIVALENCE:
                    rhs = convertExpr(that.rhs);
                    rhs = addImplicitConversion(that.rhs,that.type,rhs);
                    t = treeutils.makeBinary(that.pos, JCTree.NE, treeutils.boolneSymbol, lhs, rhs);
                    eresult = splitExpressions ? newTemp(t) : t;
                    break;

                case SUBTYPE_OF: // JML subtype
                    rhs = convertExpr(that.rhs);
                    // \TYPE <: \TYPE
                    if (rac) {
                        JCExpression c = methodCallUtilsExpression(that,"isSubTypeOf",lhs,rhs);
                        eresult = splitExpressions ? newTemp(c) : c;
                    } else {
                        JmlMethodInvocation c = treeutils.makeJmlMethodInvocation(that,JmlToken.SUBTYPE_OF,that.type,lhs,rhs);
                        eresult = splitExpressions ? newTemp(c) : c;
                    }
                    break;
                        
                case JSUBTYPE_OF: // Java subtype
                    rhs = convertExpr(that.rhs);
                    // Class <: Class - in case type checking allows it

                    // TODO - move to a utility method
                    // FIXME - do we intend that <: is always false among pairs of primitive types (even the same)
                    if (rac) {
                        Name n = names.fromString("isAssignableFrom");
                        Scope.Entry e = rhs.type.tsym.members().lookup(n);
                        Symbol ms = e.sym;
                        JCFieldAccess m = M.at(that).Select(rhs,n);
                        m.sym = ms;
                        m.type = m.sym.type;

                        JCExpression c = M.at(that).Apply(null,m,List.<JCExpression>of(lhs));
                        c.setType(syms.booleanType);
                        eresult = splitExpressions ? newTemp(c) : c;
                    } else {
                        JmlMethodInvocation c = treeutils.makeJmlMethodInvocation(that,JmlToken.JSUBTYPE_OF,that.type,lhs,rhs);
                        eresult = splitExpressions ? newTemp(c) : c;
                    }
                    break;

                case LOCK_LT:
                case LOCK_LE:
                    notImplemented(that,"Lock ordering operations");
                    throw new JmlNotImplementedException(that,"Lock ordering operations");
                    // FIXME - need <# <#= operators
                    
                default:
                    error(that,"Unexpected token in JmlAssertionAdder.visitJmlBinary: " + that.op);

            }
        } finally {
            condition = saved;
        }
        result = eresult;
        eresult.pos = that.getStartPosition();
        treeutils.copyEndPosition(eresult, that);
    }

    // OK // FIXME - needs work
    @Override
    public void visitJmlChoose(JmlChoose that) {
        result = M.at(that).JmlChoose(that.token,convert(that.orBlocks),convert(that.elseBlock)).setType(that.type);
    }
    
    // FIXME - review this
    public JCIdent getThisId(Symbol sym) {
        JCIdent id = thisIds.get(sym);
        if (id == null) {
            id = makeThisId(Position.NOPOS,sym); // FIXME - do we really want NOPOS?
        }
        return id;
    }
    
    // FIXME - review this
    public JCIdent makeThisId(int pos, Symbol sym)  {
        VarSymbol THISSym = treeutils.makeVarSymbol(Flags.STATIC,names.fromString(Strings.thisName),sym.type, Position.NOPOS);
        THISSym.owner = esc ? null : sym; 
            // In esc, the owner is null (instead of sym) to indicate
            // that this new symbol is a synthetic variable that will not ever
            // be assigned to.
        JCIdent id = treeutils.makeIdent(pos,THISSym);
        this.thisIds.put(sym, id);
        exprBiMap.put(id,id);
        return id;
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
        JCExpression savedThisExpr = this.currentThisExpr;

        
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
                this.currentThisId = makeThisId(classDecl.pos,classDecl.sym);
                this.currentThisExpr = currentThisId;
            } else { // rac
                this.currentThisId = treeutils.makeIdent(classDecl.pos,that.thisSymbol);
                this.currentThisExpr = currentThisId;
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

            enclosingClass = that.sym;
            for (JCTree t: that.defs) {
                scan(t);
            }
 
            // FIXME - need to fixup RAC and ESC check o fstatic initialization
            if (!pureCopy) {
                JCBlock bl = checkStaticInitialization();
                if (bl != null) this.classDefs.add(bl);
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
            JmlClassDecl n = M.at(that).ClassDef(convert(that.mods),that.name,typarams,convertExpr(that.extending),convertExprList(that.implementing),defs);
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
            this.currentThisExpr = savedThisExpr;
            this.currentStatements = savedCurrentStatements;
            this.allocSym = savedAllocSym;
            this.isAllocSym = savedIsAllocSym;
        }
    }
    
    // FIXME - review
    protected JCBlock checkStaticInitialization() {
        JmlMethodDecl md = methodSymForInitBlock(classDecl, Flags.STATIC, classDecl);

        pushBlock();
        for (Symbol s: classDecl.sym.getEnclosedElements()) {
            if (utils.isJMLStatic(s) && !s.type.isPrimitive() && s instanceof VarSymbol) {
                VarSymbol v = (VarSymbol)s;
                if (specs.isNonNull(v)) {
                    JCIdent id = treeutils.makeIdent(v.pos, v);
                    JCExpression e = treeutils.makeNeqObject(v.pos, id, treeutils.nullLit);
                    //e = convertJML(e);
                    JCStatement st = addAssert(new JCDiagnostic.SimpleDiagnosticPosition(v.pos),Label.STATIC_INIT,e,"null static field has null value: " + v.name);
                    if (st instanceof JCAssert) {
                        e = ((JCAssert)st).cond;
                    } else if (st instanceof JCIf) {
                        e = ((JCIf)st).cond;
                        if (e instanceof JCUnary) e = ((JCUnary)e).arg;
                    } else {
                        e = null;
                    }
                    if (e instanceof JCIdent) {
                        ((JCIdent)e).sym.owner = md.sym;
                    }
                    
                }
            }
        }
        addInvariants(classDecl,classDecl.sym,null,currentStatements,true,false,false,false,true,false,Label.STATIC_INIT,
                "invariant is false");
        JCBlock bl = popBlock(Flags.STATIC,classDecl);
        if (onlyComments(bl.stats)) bl = null;
        return bl;
    }

    // OK
    @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        if (translatingJML) {
            error(that,"Unexpected call of JmlAssertionAdder.visitJmlCompilationUnit while translating JML: " + that.getClass());
            return;
        }

        List<JCTree> defs = convert(that.defs);
        JmlCompilationUnit n = M.at(that).TopLevel(that.packageAnnotations,that.pid,defs);
        n.docComments = that.docComments; // FIXME: need to translate map
        n.endPositions = that.endPositions; // FIXME: need to convert map?
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
    public void visitJmlMethodSig(JmlMethodSig that) {
        result = M.at(that).JmlConstraintMethodSig(convertExpr(that.expression),convertExprList(that.argtypes));
        result.setType(that.type);
    }

    // OK
    @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        if (pureCopy) {
            JCExpression e = convertExpr(that.cond);
            JmlDoWhileLoop loop = M.at(that).DoLoop(null,e);
            try {
                treeMap.put(that, loop);
                JCStatement bl = convert(that.body);
                loop.body = bl;
                loop.setType(that.type);
                loop.loopSpecs = convert(that.loopSpecs); 
                result = loop;
            } finally {
                treeMap.remove(that);
            }
            addStat(loop);
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

        JCVariableDecl indexDecl = loopHelperDeclareIndex(that);

        java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

        // Create this early so it is available as a target
        JmlWhileLoop loop = M.at(that).WhileLoop(treeutils.trueLit,null);
        treeMap.put(that, loop);

        // Test that invariants hold before entering loop
        loopHelperInitialInvariant(that.loopSpecs);

        // New loop body
        pushBlock();
        
        // Havoc all items that might be changed in the loop
        if (esc) {
            loopHelperHavoc(that.body,indexDecl,that.body,that.cond);
        }
        
        loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that);
        
        // Now in the loop, so check that the variants are non-negative
        loopHelperCheckNegative(decreasesIDs, that);
        
        // Then translate the original loop body
        
        loopHelperMakeBody(that.body);
        
        // Now compute any side-effects of the loop condition
        addTraceableComment(that.cond,that.cond,"Loop test");
        JCExpression cond = convertExpr(that.cond);
        
        // increment the index
        loopHelperIncrementIndex(indexDecl);
        
        // In a do-while loop we test the condition before the invariants
        
        // Construct the loop test and the exit block. 
        loopHelperMakeBreak(that.loopSpecs,cond,loop,that);

        // After the loop, check the invariants and check that the variants have decreased
        loopHelperAssertInvariants(that.loopSpecs,decreasesIDs);
        
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
            JCEnhancedForLoop jloop = M.at(that).ForeachLoop(var,expr,null);
            List<JmlStatementLoop> loopSpecs = that.loopSpecs == null ? null : convertCopy(that.loopSpecs);
            JmlEnhancedForLoop loop = M.at(that).JmlEnhancedForLoop(jloop, loopSpecs);
            jloop.type = loop.type = that.type;
            try {
                treeMap.put(that, jloop);
                JCStatement bl = convertIntoBlock(that.body,that.body);
                loop.body = bl;
                loop.loopSpecs = that.loopSpecs == null ? null : convertCopy(that.loopSpecs); 
                result = loop;
            } finally {
                treeMap.remove(that);
            }
            // FIXME - map the sym of the loop variable here, and in other loop types, just as below?
            addStat(loop);
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

        JCVariableDecl indexDecl = loopHelperDeclareIndex(that);;

        java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

        // Create this early so it is available as a target
        JmlWhileLoop loop = M.at(that).WhileLoop(treeutils.trueLit,null);
        treeMap.put(that, loop);

        if (that.expr.type.tag == TypeTags.ARRAY) {
        
            JCExpression lengthExpr = treeutils.makeLength(array, array);
            lengthExpr = newTemp(lengthExpr); // FIXME - could give it a recognizable name

            // Test that invariants hold before entering loop
            loopHelperInitialInvariant(that.loopSpecs);

            // New loop body
            pushBlock();

            // Havoc all items that might be changed in the loop
            if (esc) {
                loopHelperHavoc(that.body,indexDecl,that.body,that.expr);
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
                loopHelperMakeBreak(that.loopSpecs,cond,loop,that);
            }

            // Now in the loop, so check that the variants are non-negative
            loopHelperCheckNegative(decreasesIDs, that);

            JCArrayAccess aa = new JmlBBArrayAccess(null,array,treeutils.makeIdent(that.pos, indexDecl.sym));
            aa.setType(that.var.type);
            JCVariableDecl loopVarDecl = treeutils.makeVarDef(that.var.type, 
                    that.var.name, methodDecl.sym, aa);
            loopVarDecl.sym = that.var.sym; // We share syms; if we don't we have to add
                                        // a mapping to paramActuals
            addStat(loopVarDecl);

        } else {
            // Have an iterable instead of an array
            
            Name iteratorName = names.fromString("_JML_iterator_" + (++count));
            JCExpression iter = methodCallUtilsExpression(array,"iterator",array);
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
                loopHelperHavoc(that.body,indexDecl,that.expr,that.body);
            }

            // Assume the invariants
            // Compute and remember the variants
            loopHelperAssumeInvariants(that.loopSpecs,decreasesIDs,that);

            // Compute the condition, recording any side-effects
            {

                // iterator.hasNext()
                JCExpression ocond = methodCallUtilsExpression(iter,"hasNext",
                        treeutils.makeIdent(array.pos, decl.sym));
                JCExpression cond = convertCopy(ocond);
                
                addTraceableComment(ocond,ocond,"Loop test");

                // The exit block tests the condition; if exiting, it tests the
                // invariant and breaks.
                loopHelperMakeBreak(that.loopSpecs,cond,loop,that);
            }
            
            // Now in the loop, so check that the variants are non-negative
            loopHelperCheckNegative(decreasesIDs, that);

            // T v = ITERATOR.next()
            JCExpression value = methodCallUtilsExpression(iter,"next",
                    treeutils.makeIdent(array.pos, decl.sym));
            value.type = that.iterDecl.type.getTypeArguments().get(0);
            value = newTemp(value);
            value = addImplicitConversion(array, that.var.type, value);

            JCVariableDecl vd = ( treeutils.makeVarDef(
                    that.var.type,
                    that.var.name,
                    methodDecl.sym,
                    value) );
            vd.sym = that.var.sym; // We share syms; if we don't we have to add
                            // a mapping to paramActuals
            addStat(vd);

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
//        addStat(M.at(that).ForeachLoop(v, e, b));
        // result?
    }
    
    /** Declares the synthetic index variable for the loop, adding the declaration
     * to the current statement list.
     */
    // OK
    protected JCVariableDecl loopHelperDeclareIndex(DiagnosticPosition pos) {
        int p = pos.getPreferredPosition();
        if (p<0) p = 0;
        Name indexName = names.fromString("index_" + p + "_" + (++count));
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
    protected void loopHelperHavoc(DiagnosticPosition pos, JCVariableDecl indexDecl, List<? extends JCTree> list, JCTree... trees) {
        ListBuffer<JCExpression> targets = new ListBuffer<JCExpression>();
        if (list != null) for (JCTree t: list) {
            TargetFinder.findVars(t,targets);
        }
        for (JCTree t: trees) {
            TargetFinder.findVars(t,targets);
        }
        targets.add(treeutils.makeIdent(pos.getPreferredPosition(),indexStack.get(0).sym));
        // synthesize a modifies list
        ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
        for (JCExpression target: targets.toList()) {
            if (target instanceof JCArrayAccess) {
                // FIXME - we convert array accesses to the entire array.
                // This is partly because the array index may depend on the loop variable, which is also havoced.
                // But the test for whether the index is in range occurs before the invariants are assumed,
                // which would put the index back in range.
                target = M.at(target.pos).JmlStoreRefArrayRange(((JCArrayAccess)target).indexed,null,null).setType(target.type);
            } 
            newlist.add(convertJML(target));
        }
        int p = pos.getPreferredPosition();
        JmlStatementHavoc st = M.at(p).JmlHavocStatement(newlist.toList());
        // FIXME - this ought to work to preserve initialized values at the beginning of th e0th iteration, but makes loops infeasbile
//        JCExpression id = treeutils.makeIdent(indexDecl.pos, indexDecl.sym);
//        JCExpression e = treeutils.makeBinary(p, JCTree.GT, id, treeutils.zero);
//        addStat(M.at(p).If(e, st, null));
        addStat(st);
    }
    
    // FIXME: implement loop_modifies?
    
    /** Finds variables assigned in the loop body and adds a havoc statement */
    // OK
    // FIXME - needs checking that we are getting all of needed variables
    protected void loopHelperHavoc(DiagnosticPosition pos, JCVariableDecl indexDecl, JCTree... trees) {
        loopHelperHavoc(pos, indexDecl, null, trees);
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
                    addAssert(inv,Label.LOOP_INVARIANT_PRELOOP, e);
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
        JCBlock bodyBlock = M.at(body).Block(0, null);
        Name label = names.fromString("loopBody_" + body.pos + "_" + (++count));
        JCLabeledStatement lab = M.at(body).Labelled(label,bodyBlock);
        continueStack.push(lab);
        addStat(lab);

        try {
            JCBlock bl = convertIntoBlock(body,body);
            bodyBlock.stats = bl.stats;
        } finally {
            continueStack.pop();
        }
    }
    
    /** Inserts the invariants as assumptions; also computes initial values of
     * the variants. (at the beginning of a loop body) */
    protected void loopHelperAssumeInvariants(List<JmlStatementLoop> loopSpecs, java.util.List<JCIdent> decreasesIDs, JCTree that) {
        addTraceableComment(that, null, "Begin loop check");
        DiagnosticPosition pos = that;
        
        // Assume the invariants
        if (loopSpecs != null) {
            for (JmlStatementLoop inv: loopSpecs) {
                if (inv.token == JmlToken.LOOP_INVARIANT) {
                    JCExpression copy = convertCopy(inv.expression);
                    addTraceableComment(inv,copy,inv.toString());
                    JCExpression e = convertJML(copy);
                    addAssume(inv,Label.LOOP_INVARIANT_ASSUMPTION, e);
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
                    id.pos = inv.pos;
                    decreasesIDs.add(id);
                }
            }
        }
    }
    
    /** Check that the variants are non-negative */
    protected void loopHelperCheckNegative(java.util.List<JCIdent> decreasesIDs, DiagnosticPosition pos) {
        for (JCIdent id: decreasesIDs) {
            JCBinary compare = treeutils.makeBinary(pos.getPreferredPosition(), JCTree.LE, treeutils.intleSymbol, treeutils.zero, id);
            addAssert(id,Label.LOOP_DECREASES_NEGATIVE,compare);
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
                    addAssert(inv,Label.LOOP_INVARIANT, e);
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
                    addAssert(inv,Label.LOOP_DECREASES, bin);
                }
            }
        }
        
    }
    
    /** Completes the loop */
    protected void loopHelperFinish(JmlWhileLoop loop, JCTree that) {
        JCBlock bl = popBlock(0,that);
        loop.body = bl;
        loop.setType(that.type);
        addStat(loop);
        treeMap.remove(that);
        indexStack.remove(0);

        
        addStat(popBlock(0,that));
    }
    
    // OK
    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        if (pureCopy) {
            List<JCStatement> init = convert(that.init);
            JCExpression cond = convertExpr(that.cond);
            List<JCExpressionStatement> step = convert(that.step);
            JmlForLoop loop = M.at(that).ForLoop(init,cond,step,null);
            try {
                treeMap.put(that, loop);
                JCStatement bl = convertIntoBlock(that.body,that.body);
                loop.body = bl;
                loop.setType(that.type);
                loop.loopSpecs = convertCopy(that.loopSpecs); 
                result = loop;
            } finally {
                treeMap.remove(that);
            }
            addStat(loop);
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
        
        JCVariableDecl indexDecl = loopHelperDeclareIndex(that);

        java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

        // Create this early so it is available as a target
        JmlWhileLoop loop = M.at(that).WhileLoop(treeutils.trueLit,null);
        treeMap.put(that, loop);

        // Test that invariants hold before entering loop
        loopHelperInitialInvariant(that.loopSpecs);

        // New loop body
        pushBlock();
        
        // Havoc all items that might be changed in the loop
        if (esc) {
            loopHelperHavoc(that.body,indexDecl,that.step,that.body,that.cond);
        }
        
        loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that);
        
        // Compute the condition, recording any side-effects
        if (that.cond != null) {
            
            addTraceableComment(that.cond,that.cond,"Loop test");
            JCExpression cond = convertExpr(that.cond);

            // The exit block tests the condition; if exiting, it breaks out of the loop
            loopHelperMakeBreak(that.loopSpecs, cond, loop, that);
        }
        
        // Now in the loop, so check that the variants are non-negative
        loopHelperCheckNegative(decreasesIDs, that);
        
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
        JmlGroupName g = M.at(that).JmlGroupName(convertCopy(that.selection)); // FIXME - not sure about the kind of copying
        g.setType(that.type);
        g.sym = that.sym;
        result = g;
    }

    // OK
    @Override
    public void visitJmlImport(JmlImport that) {
        // FIXME - need to rewrite qualid - might have a *; might have a method name
        result = M.at(that).Import(that.qualid, that.staticImport).setType(that.type);
    }
    
    int lblUnique = 0;

    // OK
    @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        JCExpression expr = convertExpr(that.expression);

        if (pureCopy) {
            result = eresult = M.at(that).JmlLblExpression(that.labelPosition, that.token, that.label, expr).setType(that.type);
            return;
        }
        // The format of this string is important in interpreting it in JmlEsc
        String nm = Strings.labelVarString + that.token.internedName().substring(1) + "_" + that.label + "_" + (++lblUnique);
        JCIdent id = newTemp(that.getLabelPosition(),nm,expr);
        id.pos = that.pos;
        result = eresult = id;
        
        if (esc) ((VarSymbol)id.sym).pos = Position.NOPOS; // TODO: Why?
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
                error(that,"Unknown type in a \\lbl expression: " + t);
            }
            if (name != null) {
                JCFieldAccess m = findUtilsMethod(that,name);
                JCMethodInvocation c = M.at(that).Apply(null,m,List.<JCExpression>of(lit,treeutils.makeIdent(id.pos,id.sym))); 
                c.type = id.type;
                JCStatement st = M.at(that).Exec(c);
                if (that.token == JmlToken.BSLBLPOS) {
                    // Only report if the expression is true
                    // It is a type error if it is not boolean
                    st = M.at(that).If(treeutils.makeIdent(id.pos,id.sym), st, null);
                } else if (that.token == JmlToken.BSLBLNEG) {
                    // Only report if the expression is false
                    // It is a type error if it is not boolean
                    st = M.at(that).If(treeutils.makeNot(that.pos, treeutils.makeIdent(id.pos,id.sym)), st, null);
                }
                addStat(st);
            }
        }
    }

    // OK
    @Override
    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) {
        JmlMethodClauseCallable mc = M.at(that).JmlMethodClauseCallable(that.keyword);
        mc.setType(that.type);
        mc.methodSignatures = convert(that.methodSignatures);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        JmlMethodClauseConditional mc = M.at(that).JmlMethodClauseConditional(
                that.token,
                convertExpr(that.expression),
                convertExpr(that.predicate));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        JmlMethodClauseDecl mc = M.at(that).JmlMethodClauseDecl(
                that.token,
                convert(that.decls));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        JmlMethodClauseExpr mc = M.at(that).JmlMethodClauseExpr(
                that.token,
                convertExpr(that.expression));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        JmlMethodClauseGroup mc = M.at(that).JmlMethodClauseGroup(
                convert(that.cases));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        JmlMethodClauseSignals mc = M.at(that).JmlMethodClauseSignals(
                that.token,
                convert(that.vardef),
                convertExpr(that.expression));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        JmlMethodClauseSignalsOnly mc = M.at(that).JmlMethodClauseSignalsOnly(
                that.token,
                convertExprList(that.list));
        mc.setType(that.type);
        mc.sourcefile = that.sourcefile;
        result = mc;
    }

    // OK
    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        JmlMethodClauseStoreRef mc = M.at(that).JmlMethodClauseStoreRef(
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
        if (!pureCopy && attr.isModel(that.sym) && nm.startsWith(Strings.modelFieldMethodPrefix)) {
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
            JCBlock body = null;
            if (pureCopy) {
                JmlMethodDecl savedMD = methodDecl;
                methodDecl = that;
                body = convertIntoBlock(that.body,that.body);
                methodDecl = savedMD;
            } else {
                body = convertMethodBodyNoInit(that,classDecl);
            }

            List<JCTypeParameter> typarams = that.typarams;
            if (fullTranslation) typarams = convertCopy(typarams); // FIXME - is there anything to be translated
            List<JCVariableDecl> params = that.params;
            if (fullTranslation) params = convertCopy(params); // Just a copy - the parameters are just modifiers, types, and names
            JCExpression restype = that.restype;
            if (fullTranslation) restype = convertExpr(restype);
            JmlMethodDecl m = M.at(that).MethodDef(convert(that.mods), that.name, restype, typarams, params, convertExprList(that.thrown), body, convertExpr(that.defaultValue));
            m.sym = that.sym;
            m.setType(that.type);
            m._this = that._this;
            m.sourcefile = that.sourcefile;
            //m.owner = that.owner; // FIXME - new class decl?
            m.docComment = that.docComment;
            m.cases = convertCopy(that.cases);
            m.methodSpecsCombined = that.methodSpecsCombined; // FIXME - copy?
            m.specsDecl = that.specsDecl; // FIXME - needs new reference
            if (classDefs != null) classDefs.add(m); // classDefs can be null if  JmlEsc.check is called directly on a JCMethodDecl
            result = m;
            methodBiMap.put(that,m);
        } catch (JmlNotImplementedException e) {
            notImplemented("method (or represents clause) containing ",e); // FIXME - location?
            log.error(e.pos,"jml.unrecoverable", "Unimplemented construct in a method or model method or represents clause");
        } finally {
            translatingJML = saved;
        }
    }


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
            return methodCallUtilsExpression(targ,"makeTYPE",f,argsarray);
        } else if (targ instanceof JCTree.JCWildcard) {
            return methodCallUtilsExpression(targ,"makeTYPEQ");
            // FIXME - need to handle more subtypes differently, I'm sure
        } else { // JCPrimitiveTypeTree, JCFieldAccess, JCIdent, JCArrayTypeTree
            JCTree.JCFieldAccess f = M.Select(targ,names._class);
            f.type = syms.classType;
            f.sym = f.type.tsym;
            return methodCallUtilsExpression(targ,"makeTYPE0",f);
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
    /** Translates \typeof(arg) */
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
        result = eresult = methodCallUtilsExpression(tree,"makeTYPE0",eresult);
    }
    
    // TODO: Review
    /** Translates \type(arg) */
    protected JCExpression translateType(JCExpression arg) {
        if (arg.type instanceof Type.TypeVar) {
            JCExpression t = paramActuals.get(((Type.TypeVar)arg.type).tsym);
            if (t != null) arg = t;
        } 
        return convertExpr(arg);
    }

    /** Helper method to translate \elemtype expressions for RAC */
    protected void translateElemtype(JCMethodInvocation tree) {
        // OK for Java types, but not complete for JML types - FIXME
        JCExpression arg = tree.args.head;
        arg = convertExpr(arg);
        if (tree.type == JmlTypes.instance(context).TYPE) {
            arg = methodCallUtilsExpression(tree,"erasure",arg);
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
            result = eresult = methodCallUtilsExpression(tree,"makeTYPE0",c);
        }
    }

    protected Utils.DoubleMap<Name,Symbol,JCVariableDecl> oldarrays = new Utils.DoubleMap<Name,Symbol,JCVariableDecl>();

    protected boolean inOldEnv = false;
    // OK
    // These are special JML fcn-like calls (e.g. \old, \nonnullelements, ...)
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        if (pureCopy && !rac) {
            if (that.token == JmlToken.BSOLD || that.token == JmlToken.BSPAST|| that.token == JmlToken.BSPRE) {
                boolean savedInOldEnv = inOldEnv;
                inOldEnv = true;
                JCExpression arg0 = convertExpr(that.args.get(0));
                JmlMethodInvocation m;
                if (that.args.size() > 1) {
                    JCExpression arg1 = that.args.get(1);
                    arg1 = M.at(arg1).Ident(((JCIdent)arg1).name);
                    m = M.at(that).JmlMethodInvocation(that.token, List.<JCExpression>of(arg0,arg1));
                } else {
                    m = M.at(that).JmlMethodInvocation(that.token, List.<JCExpression>of(arg0));
                }
                m.setType(that.type);
                m.label = that.label;
                m.startpos = that.startpos;
                m.varargsElement = that.varargsElement;
                // typeargs and meth are always null for a JML operation
                result = eresult = m;
                inOldEnv = savedInOldEnv;
                return;
            } else {
                JmlMethodInvocation m = M.at(that).JmlMethodInvocation(that.token, convertExprList(that.args));
                m.setType(that.type);
                m.label = that.label;
                m.startpos = that.startpos;
                m.varargsElement = that.varargsElement;
                // typeargs and meth are always null for a 
                result = eresult = m;
                return;
            }
        }
        switch (that.token) {
            case BSPAST:
            case BSOLD:
            case BSPRE:
            {
                JCIdent savedEnv = oldenv;
                // FIXME _ this implementation is not adequate for checking postconditions with \old from callers
                // FIXME - also it does not work for rac at labelled locations
                boolean savedInOldEnv = inOldEnv;
                inOldEnv = true;
                try {
                    if (rac) {
                        ListBuffer<JCStatement> saved = currentStatements;
                        try {
                            Name label = null;
                            if (that.args.size() == 2) {
                                currentStatements = new ListBuffer<JCStatement>();
                                label = ((JCIdent)that.args.get(1)).name;
                            } else {
                                currentStatements = oldStatements;
                                label = defaultOldLabel;
                            }
                            JCExpression arg = (that.args.get(0));
                            if (!convertingAssignable && arg instanceof JCArrayAccess && (
                                    ((JCArrayAccess)arg).indexed instanceof JCIdent ||
                                    ((JCArrayAccess)arg).indexed instanceof JCFieldAccess)) {
                                JCArrayAccess aa = (JCArrayAccess)arg;
                                Symbol sym = treeutils.getSym(aa.indexed);
                                JCExpression ad = convertExpr(aa.indexed);
                                JCExpression a = treeutils.copyArray(that.pos,ad);
                                JCVariableDecl d = newTempDecl(arg, a.type);
                                d.init = a;
                                oldarrays.put(label, sym, d);
                                JCStatement v = d;
                                // FIXME - combine with duplicate code below
                                addStat(v);
                                if (that.args.size() == 2) {
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
                                
                                JCIdent id = treeutils.makeIdent(arg.pos,d.sym);
                                JCArrayAccess newaa = M.at(aa.pos).Indexed(id, aa.index);
                                newaa.type = aa.type;
                                visitIndexed(newaa);
                                // The above call sets result and eresult
                                
                            } else {
                                arg = convertExpr(arg);
                                String s = "_JML___old_" + (++count); // FIXME - Put string in Strings
                                Name nm = names.fromString(s);
                                JCVariableDecl v = treeutils.makeVarDef(arg.type,nm,methodDecl.sym,treeutils.makeZeroEquivalentLit(arg.pos,arg.type));
                                //v.mods.flags |= Flags.FINAL; // If we use this, the sym has to be set FINAL as well.
                                addStat(v);
                                pushBlock();
                                addStat(treeutils.makeAssignStat(arg.pos, treeutils.makeIdent(arg.pos, v.sym), arg));
                                JCBlock bl = popBlock(0,arg);
                                pushBlock();
                                JCBlock cbl = popBlock(0,arg);
                                JCVariableDecl ex = treeutils.makeVarDef(syms.exceptionType, names.fromString("_JML__old_ex"), methodDecl.sym, arg.pos);
                                JCTry st = M.at(arg.pos).Try(bl,List.<JCCatch>of(M.at(arg.pos).Catch(ex,cbl)),null);
                                addStat(st);
                                if (label != null) {
                                    //JCExpression e = that.args.get(1);
                                    ListBuffer<JCStatement> list = labelActiveOldLists.get(label);
                                    if (list != null) {
                                        list.add(v);
                                    } else {
                                        ListBuffer<JCStatement> stlist = labelOldLists.get(label);
                                        if (stlist != currentStatements) {
                                            ListBuffer<JCStatement> newlist = new ListBuffer<JCStatement>();
                                            for (JCStatement stt: stlist) {
                                                if (stt instanceof JCLabeledStatement && ((JCLabeledStatement)stt).label.equals(label)) {
                                                    newlist.addAll(currentStatements);
                                                }
                                                newlist.add(stt);
                                            }
                                            stlist.clear();
                                            stlist.addAll(newlist);
                                        }
                                    }
                                }
                                JCIdent id = treeutils.makeIdent(arg.pos,v.sym);
                                eresult = id;
                            }
                        } finally {
                            currentStatements = saved;
                            inOldEnv = savedInOldEnv;
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
                        // We have to wrap this in an old (even though it sometimes wraps twice) 
                        // in order to get arrays properly resolved
                        arg = treeutils.makeOld(that.pos, arg, oldenv);
                        //                        JmlMethodInvocation meth;
//                        if (that.args.size() == 1) {
//                            meth = M.at(that).JmlMethodInvocation(that.token,arg);
//                        } else {
//                            // The second argument is a label, held as a JCIdent
//                            meth = M.JmlMethodInvocation(that.token,arg,that.args.get(1));
//                        }
//                        meth.setType(that.type);
//                        meth.pos = that.pos;
//                        meth.startpos = that.startpos;
//                        meth.varargsElement = that.varargsElement;
//                        meth.meth = m;
//                        meth.label = that.label;
//                        meth.typeargs = that.typeargs; // FIXME - do these need translating?
//                        eresult = meth;
                        eresult = arg;
                    }
                } finally {
                    oldenv = savedEnv;
                    inOldEnv = savedInOldEnv;
                }
            }
            break;
            
            case BSNONNULLELEMENTS :
            {
                int n = that.args.size();
                if (n == 0) {
                    result = eresult = treeutils.trueLit;
                } else {
                    JCExpression conj = null;
                    for (JCExpression arg : that.args) {
                        JCExpression e = convertExpr(arg);
                        e = rac ? methodCallUtilsExpression(arg,"nonnullElementCheck",e)
                                : treeutils.makeAnd(that.pos, 
                                        treeutils.makeNeqObject(that.pos, e, treeutils.nullLit),
                                        treeutils.makeJmlMethodInvocation(arg,
                                                that.token,that.type,e));
                        conj = conj == null? e :
                            treeutils.makeAnd(arg.pos, conj, e);
                    }
                    result = eresult = conj; 
                }
            }
            break;
            
            case BSTYPEOF:
                {
                    if (rac) {
                        translateTypeOf(that);
                    }
                    if (esc) {
                        JCExpression arg = convertExpr(that.args.get(0));
                        JmlMethodInvocation meth = M.at(that).JmlMethodInvocation(that.token,arg);
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
                    JCExpression arg = that.args.get(0);
                    result = eresult = translateTypeArg(arg);
                    // FIXME - used to be something like result = eresult = treeutils.trType(that.pos, type); ???
                }
                if (esc) {
                    JCExpression t = translateType(that.args.get(0));
                    result = eresult = treeutils.makeJmlMethodInvocation(that, JmlToken.BSTYPELC, that.type, t);
                }
                break;
            
            case BSELEMTYPE:
                if (rac) translateElemtype(that);
                if (esc) throw new JmlNotImplementedException(that,that.token.internedName());
                // FIXME - need esc
                break;

            case BSFRESH :
            {
                if (rac) throw new JmlNotImplementedException(that,that.token.internedName());// FIXME
                else {
                    JCExpression e = convertJML(that.args.get(0));
                    e = newTemp(e); // We make a temp variable so that the (converted) argument is not captured by the \old
                    JCFieldAccess fa = isAllocated(that,e);
                    JCExpression n = treeutils.makeOld(that.pos,fa,preLabel);
                    JCExpression prev = treeutils.makeNot(that.pos, n);
                    fa = isAllocated(that,convertCopy(e));
                    result = eresult = treeutils.makeAnd(that.pos, prev, fa);
                    e = treeutils.makeNeqObject(that.pos, e, treeutils.nullLit);
                    result = eresult = treeutils.makeAnd(that.pos, e, eresult);
                    }
                break;
            }
            
            case BSDISTINCT:
            {
                // Any type error should have been reported in JmlAttr
                boolean anyPrimitive = false;
                Type maxPrimitiveType = null;
                for (JCExpression arg : that.args) {
                    Type tt = arg.type;
                    if (tt.isErroneous()) continue;
                    if (tt.isPrimitive()) {
                        anyPrimitive = true;
                    }
                }
                if (anyPrimitive) for (JCExpression arg : that.args) {
                    Type tt = arg.type;
                    if (arg.type.isErroneous()) continue;
                    if (!tt.isPrimitive()) tt = types.unboxedType(tt);
                    if (arg.type.tag == TypeTags.VOID) {
                        // FIXME -error
                    } else if (maxPrimitiveType == null) {
                        maxPrimitiveType = arg.type;
                    } else if (types.isConvertible(tt,maxPrimitiveType)) {
                        // OK
                    } else if (types.isConvertible(maxPrimitiveType, tt)) {
                        maxPrimitiveType = tt;
                    } else {
                        // FIXME - error
                    }
                }
                ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
                for (JCExpression arg : that.args) {
                    JCExpression ex = convertExpr(arg);
                    if (anyPrimitive) ex = addImplicitConversion(arg,maxPrimitiveType,ex);
                    newargs.add(ex);
                }
                result = eresult = M.at(that.pos).JmlMethodInvocation(JmlToken.BSDISTINCT, newargs.toList());
                eresult.type = syms.booleanType;
                break;
            }
            
            case BSMAX :
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
                throw new JmlNotImplementedException(that,that.token.internedName());

            default:
                Log.instance(context).error("esc.internal.error","Unknown token in JmlAssertionAdder: " + that.token.internedName());
                throw new JmlNotImplementedException(that,that.token.internedName());
        }
        result = eresult;
    }

    @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        if (!pureCopy) {
            error(that,"Unexpected call of JmlAssertionAdder.visitJmlMethodSpecs: " + that.getClass());
            return;
        }
        
        List<JmlSpecificationCase> cases = convertCopy(that.cases);
        JmlMethodSpecs ms = M.at(that).JmlMethodSpecs(cases);
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
        result = M.at(that).JmlModelProgramStatement(convert(that.item)).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        result = eresult = M.at(that).JmlPrimitiveTypeTree(that.token).setType(that.type);
    }

    /** Maps symbols declared in quantified and let statements to new symbols - needed because
     * quantified symbols can be used in multiple places
     */
    protected java.util.Map<Symbol,Symbol> localVariables = new java.util.HashMap<Symbol,Symbol>();
    
    // OK
    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        for (JCVariableDecl d: that.decls) {
            localVariables.put(d.sym,d.sym);
        }
        result = eresult = treeutils.makeZeroEquivalentLit(that.pos,that.type);
        try {

            if (!splitExpressions) {
                JmlQuantifiedExpr q = M.at(that).
                        JmlQuantifiedExpr(that.op,
                                convertCopy(that.decls),
                                convertExpr(that.range),
                                convertExpr(that.value));
                q.setType(that.type);
                result = eresult = q;
            } else {
                java.util.List<Bound> bounds = new java.util.LinkedList<Bound>();
                JCExpression innerexpr = determineRacBounds(that.decls,that.range,bounds);
                if (innerexpr == null) {
                    log.note(that,"rac.not.implemented.quantified");
                    return;
                }

                // The accumulator variable
                Type t = that.type;
                Name n = names.fromString("_JML$val$$" + (++count));
                JCVariableDecl decl = treeutils.makeVarDef(t, n, methodDecl.sym, that.pos);
                addStat(decl);
                decl.init = treeutils.makeZeroEquivalentLit(that.pos, t);
                
                // Label for the loop, so we can break out of it
                Name label = names.fromString("__JMLwhile_" + (++count));
                pushBlock(); // enclosing block, except for declaration of accumulator
                try {
                    for (Bound bound: bounds) {

                        JCVariableDecl indexdef = treeutils.makeVarDef(bound.decl.type,bound.decl.name,methodDecl.sym,bound.decl.pos);
                        localVariables.put(bound.decl.sym, indexdef.sym);
                        JCIdent id = treeutils.makeIdent(that.pos, decl.sym); // accumulator
                        JCIdent idd = treeutils.makeIdent(that.pos, decl.sym); // another id for the accumulator
                        JCStatement st;
                        JCBreak brStat = null;
                        JCBlock bl;
                        pushBlock(); // Start of loop block
                        try {
                            JCExpression guard = convertExpr(innerexpr);
                            pushBlock(); // Start of guarded block
                            try {
                                JCExpression val = convertExpr(that.value);
                                switch (that.op) {
                                    case BSFORALL:
                                        // if (guard) { val = convert(value); if (!val) { accumulator = false; break <label>; }}
                                        decl.init = treeutils.trueLit;

                                        pushBlock();
                                        addStat(treeutils.makeAssignStat(that.pos, id, treeutils.falseLit));
                                        addStat(brStat = M.Break(label));
                                        bl = popBlock(0L,that);
                                        st = M.If(treeutils.makeNot(that.pos,val), bl, null);
                                        break;

                                    case BSEXISTS:
                                        // if (guard) { val = convert(value); if (!val) { accumulator = true; break <label>; }}

                                        pushBlock();
                                        addStat(treeutils.makeAssignStat(that.pos, id, treeutils.trueLit));
                                        addStat(brStat = M.Break(label));
                                        bl = popBlock(0L,that);
                                        st = M.If(val, bl, null);
                                        break;

                                    case BSSUM:
                                        // if (guard) { val = convert(value); accumulator = accumulator + val; }
                                        st = treeutils.makeAssignStat(that.pos,id,treeutils.makeBinary(that.pos, JCTree.PLUS, idd, val));
                                        break;

                                    case BSPRODUCT:
                                        // if (guard) { val = convert(value); accumulator = accumulator * val; }
                                        switch (that.type.tag) {
                                            case TypeTags.INT:
                                                decl.init = treeutils.makeIntLiteral(that.pos, Integer.valueOf(1));
                                                break;
                                            case TypeTags.LONG:
                                                decl.init = treeutils.makeLit(that.pos, that.type, Long.valueOf(1));
                                                break;
                                            case TypeTags.SHORT:
                                                decl.init = treeutils.makeLit(that.pos, that.type, Short.valueOf((short)1));
                                                break;
                                            case TypeTags.BYTE:
                                                decl.init = treeutils.makeLit(that.pos, that.type, Byte.valueOf((byte)1));
                                                break;
                                            case TypeTags.DOUBLE:
                                                decl.init = treeutils.makeLit(that.pos, that.type, Double.valueOf(1));
                                                break;
                                            case TypeTags.FLOAT:
                                                decl.init = treeutils.makeLit(that.pos, that.type, Float.valueOf(1));
                                                break;
                                                // Skipping CHAR - multiplying chars does not make sense.
                                            default:
                                                log.note(that,"rac.not.implemented.quantified");
                                                throw new JmlNotImplementedException(that,"RAC not implemented for this type: " + that.type);

                                        }
                                        st = treeutils.makeAssignStat(that.pos,id,treeutils.makeBinary(that.pos, JCTree.MUL, idd, val));
                                        break;

                                    case BSNUMOF:
                                        // if (guard) { val = convert(value); if (val) accumulator = accumulator + 1;
                                        st = treeutils.makeAssignStat(that.pos,id,treeutils.makeBinary(that.pos, JCTree.PLUS, idd, 
                                                idd.type.tag == TypeTags.LONG ? treeutils.longone : treeutils.one)); // FIXME - what about bigint?
                                        st = M.at(that).If(val, st, null);
                                        break;

                                    case BSMAX:
                                    case BSMIN:
                                        // if (guard) { val = convert(value); if ( accumulator </> val) accumulator = val;
                                        switch (that.type.tag) {
                                            case TypeTags.INT:
                                                decl.init = treeutils.makeIntLiteral(that.pos, that.op == JmlToken.BSMAX ? Integer.MIN_VALUE : Integer.MAX_VALUE);
                                                break;
                                            case TypeTags.LONG:
                                                decl.init = treeutils.makeLit(that.pos, that.type, (that.op == JmlToken.BSMAX ? Long.MIN_VALUE : Long.MAX_VALUE));
                                                break;
                                            case TypeTags.SHORT:
                                                decl.init = treeutils.makeLit(that.pos, that.type, (that.op == JmlToken.BSMAX ? Short.MIN_VALUE : Short.MAX_VALUE));
                                                break;
                                            case TypeTags.BYTE:
                                                decl.init = treeutils.makeLit(that.pos, that.type, (that.op == JmlToken.BSMAX ? Byte.MIN_VALUE : Byte.MAX_VALUE));
                                                break;
                                            case TypeTags.CHAR:
                                                decl.init = treeutils.makeLit(that.pos, syms.intType, (int)(that.op == JmlToken.BSMAX ? Character.MIN_VALUE : Character.MAX_VALUE));
                                                break;
                                            case TypeTags.DOUBLE:
                                                decl.init = treeutils.makeLit(that.pos, that.type, (that.op == JmlToken.BSMAX ? Double.MIN_VALUE : Double.MAX_VALUE));
                                                break;
                                            case TypeTags.FLOAT:
                                                decl.init = treeutils.makeLit(that.pos, that.type, (that.op == JmlToken.BSMAX ? Float.MIN_VALUE : Float.MAX_VALUE));
                                                break;
                                            default:
                                                log.note(that,"rac.not.implemented.quantified");
                                                throw new JmlNotImplementedException(that,"RAC not implemented for this type: " + that.type);

                                        }
                                        // FIXME - what about \bigint? should \min and \max be undefined if the range is empty?
                                        JCExpression tmp = !splitExpressions? newTemp(val) : val; // Make an ID if not already
                                        st = treeutils.makeAssignStat(that.pos,id,tmp);
                                        st = M.at(that.pos).If(treeutils.makeBinary(that.pos,
                                                that.op == JmlToken.BSMAX ? JCTree.LT : JCTree.GT,
                                                        idd, tmp), st, null);
                                        break;

                                    default:
                                        popBlock(0,that); // ignore
                                        popBlock(0,that); // ignore
                                        String msg = "Unknown quantified expression operation: " + that.op.internedName();
                                        log.error(that,"jml.internal",msg);
                                        throw new JmlNotImplementedException(that,msg);
                                }
                                addStat(st);
                            } finally {
                                bl = popBlock(0L,that); // end of guarded block
                            }
                            st = M.If(guard, bl, null);
                            addStat(st);

                        } finally {
                            if (bound.decl.type.tag == TypeTags.BOOLEAN) {
                                // index = false; do { <innercomputation>; index = !index } while (index);
                                st = treeutils.makeAssignStat(that.pos,
                                        treeutils.makeIdent(that.pos, indexdef.sym),
                                        treeutils.makeNot(that.pos, treeutils.makeIdent(that.pos, indexdef.sym)));
                                addStat(st);

                                bl = popBlock(0L,that); // loop block

                                indexdef.init = treeutils.falseLit;
                                JCExpression comp = treeutils.makeIdent(that.pos, indexdef.sym);
                                addStat(indexdef);
                                st = M.at(that.pos).DoLoop(bl,comp);
                                if (brStat != null) brStat.target = st;
                                st = M.at(that.pos).Labelled(label,st);
                                addStat(st);

                            } else if (bound.decl.type.tag == TypeTags.CLASS) {
                                // for (T o: container) { <innercomputation>;  } 

                                bl = popBlock(0L,that); // loop block

                                st = M.at(that.pos).ForeachLoop(indexdef,bound.lo,bl);
                                if (brStat != null) brStat.target = st;
                                st = M.at(that.pos).Labelled(label,st);
                                addStat(st);

                            } else {
                                // T index = lo; while (index </<= hi) { <inner computation>; index = index + 1 }
                                st = treeutils.makeAssignStat(that.pos,
                                        treeutils.makeIdent(that.pos, indexdef.sym),
                                        treeutils.makeBinary(that.pos, JCTree.PLUS, treeutils.makeIdent(that.pos, indexdef.sym), treeutils.one));
                                // FIXME - one above might have to be long or bigint
                                addStat(st);

                                bl = popBlock(0L,that); // loop block

                                indexdef.init = convertExpr(bound.lo);
                                addStat(indexdef);
                                JCExpression hi = convertExpr(bound.hi);
                                JCExpression comp = treeutils.makeBinary(that.pos,
                                        bound.hi_equal ? JCTree.LE : JCTree.LT,
                                                bound.hi_equal ? treeutils.intleSymbol : treeutils.intltSymbol,
                                                        treeutils.makeIdent(that.pos, indexdef.sym), hi);
                                st = M.at(that.pos).WhileLoop(comp,bl);
                                if (brStat != null) brStat.target = st;
                                st = M.at(that.pos).Labelled(label,st);
                                addStat(st);
                            }
                        }

                    }
                } finally {
                    addStat(popBlock(0L,that)); // pops enclosing block
                }
                result = eresult = treeutils.makeIdent(that.pos, decl.sym);
            }
        } finally {
            for (JCVariableDecl d: that.decls) {
                localVariables.remove(d.sym);
            }
        }
        return;
    }

    // FIXME - duplicate with what is in JmlAttr?
    
    protected static class Bound {
        public JCVariableDecl decl;
        public JCExpression lo;
        public JCExpression hi;
        boolean lo_equal;
        boolean hi_equal;
        JCVariableDecl indexdef;
        /*@Nullable*/JCVariableDecl lodef;
        /*@Nullable*/JCVariableDecl hidef;
    }
    

    /** If appropriate bounds can be determined for all defined variables, the method returns the
     * remaining expression and fills in the Bound list (first element is innermost loop); if appropriate
     * bounds cannot be determined, the method returns null.
     */
    public JCExpression determineRacBounds(List<JCVariableDecl> decls, JCExpression range, java.util.List<Bound> bounds) {
        // Some current assumptions
        if (decls.length() != 1) return null; // FIXME - does only one declaration!!!!!!
        if (decls.head.type.tag == TypeTags.DOUBLE) return null;
        if (decls.head.type.tag == TypeTags.FLOAT) return null;
        
        if (decls.head.type.tag == TypeTags.BOOLEAN) {
            Bound b = new Bound();
            b.decl = decls.head;
            b.lo = null;
            b.hi = null;
            bounds.add(0,b);
            return range;
        } else if (decls.head.type.tag == TypeTags.CLASS) {
            if (range instanceof JCBinary && ((JCBinary)range).getTag() != JCTree.AND) return null;
            JCExpression check = 
                range instanceof JCBinary? ((JCBinary)range).lhs : range;
            if (!(check instanceof JCMethodInvocation)) return null;
            JCMethodInvocation mi = (JCMethodInvocation)check;
            if (!(mi.meth instanceof JCFieldAccess)) return null;
            JCFieldAccess fa = (JCFieldAccess)mi.meth;
            if (!fa.name.toString().equals("contains") && !fa.name.toString().equals("has")) return null;
            Bound b = new Bound();
            b.decl = decls.head;
            b.lo = fa.selected;
            // FIXME - should check whether fa.selected is Iterable
            b.hi = null;
            bounds.add(0,b);
            return check == range ? check : // FIXME - could be set to true 
                ((JCBinary)range).rhs;
        }


        try {
            // presume int
            JCBinary locomp = (JCBinary)((JCBinary)range).lhs;
            JCBinary hicomp = (JCBinary)((JCBinary)range).rhs;
            if (locomp.getTag() == JCTree.AND) {
                hicomp = (JCBinary)locomp.rhs;
                locomp = (JCBinary)locomp.lhs;
            } else if (hicomp.getTag() == JCTree.AND) {
                hicomp = (JCBinary)hicomp.lhs;
            }
            Bound b = new Bound();
            b.decl = decls.head;
            int tag = locomp.getTag();
            if (tag == JCTree.GE || tag == JCTree.GT) b.lo = locomp.rhs;
            else b.lo = locomp.lhs;
            b.lo_equal = tag == JCTree.LE || tag == JCTree.GE;
            tag = hicomp.getTag();
            if (tag == JCTree.GE || tag == JCTree.GT) b.hi = hicomp.lhs;
            else b.hi = hicomp.rhs;
            b.hi_equal = tag == JCTree.LE || tag == JCTree.GE;
            bounds.add(0,b);
        } catch (Exception e) {
            return null;
        }
        return range;
    }


    // OK
    @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        if (pureCopy || esc) {
            result = eresult = M.at(that).
                    JmlSetComprehension(convert(that.newtype),convert(that.variable),convertExpr(that.predicate)).setType(that.type);
            return;
        }
        // FIXME - implement
        throw new JmlNotImplementedException(that,"set comprehension expression");
        //return;
    }

    // OK
    @Override
    public void visitJmlSingleton(JmlSingleton that) {
        if (pureCopy) {
            JmlSingleton e = M.at(that).JmlSingleton(that.token);
            e.type = that.type;
            //e.symbol = that.symbol;
            e.info = that.info;
            treeutils.copyEndPosition(e,that);
            result = eresult = e;
            return;
        }
        if (!translatingJML) {
            error(that,"Unexpected call of JmlAssertionAdder.visitJmlSingleton: " + that.getClass());
            return;
        }
        switch (that.token) {
            case BSRESULT:
                // FIXME - sort out resultExpr and resultSym
                if (resultExpr != null) {
                    eresult = convertCopy(resultExpr);
                } else if (resultSym == null) {
                    error(that, "It appears that \\result is used where no return value is defined"); // FIXME - not an internal error
                } else {
                    eresult = treeutils.makeIdent(that.pos, resultSym);
                }
                break;

            case INFORMAL_COMMENT:
                eresult = treeutils.makeBooleanLiteral(that.pos,true);
                break;
                
            case BSEXCEPTION:
                if (exceptionSym == null) {
                    error(that,"It appears that \\exception is used where no exception value is defined" ); // FIXME - not an internal error
                } else {
                    eresult = treeutils.makeIdent(that.pos,exceptionSym);
                }
                break;

            case BSINDEX:
                if (indexStack.isEmpty()) {
                    error(that,"\\index expression used outside a loop");
                } else {
                    // Get the index of the inner most loop
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
                    JmlSingleton e = M.at(that).JmlSingleton(that.token);
                    e.info = that.info;
                    //e.symbol = that.symbol;
                    e.setType(that.type);
                    eresult = e;
                }
                break;

            default:
                Log.instance(context).error(that.pos, "jml.unknown.construct",that.token.internedName(),"JmlAssertionAdder.visitJmlSingleton");
                eresult = treeutils.makeZeroEquivalentLit(that.pos,that.type); // Not sure continuation will be successful in any way
                break;
        }
        result = eresult;
    }
    

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        if (translatingJML) {
            error(that,"Unexpected call of JmlAssertionAdder.visitJmlSpecificationCase while translating JML: " + that.getClass());
            return;
        }
        if (!pureCopy) {
            error(that,"Unexpected call of JmlAssertionAdder.visitJmlSpecificationCase: " + that.getClass());
            return;
        }
        
        JmlSpecificationCase sc = M.at(that).JmlSpecificationCase(
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
                        result = addStat( M.at(that).Exec(arg).setType(that.type) );
                    }
                } catch (JmlNotImplementedException e) {
                    notImplemented(that.token.internedName() + " statement containing ",e);
                    result = null;
                }
                break;

            default:
                String msg = "Unknown token in JmlAssertionAdder.visitJmlStatement: " + that.token.internedName();
                error(that, msg);
        }
    }

    // jmlrewriter? FIXME; also explain what this is
    @Override
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        if (translatingJML) {
            error(that,"Unexpected call of JmlAssertionAdder.visitJmlStatementDecls while translating JML: " + that.getClass());
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
        if (pureCopy) {
            JmlStatementExpr st = M.at(that).JmlExpressionStatement(that.token,that.label,convertExpr(that.expression));
            st.setType(that.type);
            st.associatedSource = that.associatedSource;
            st.associatedPos = that.associatedPos;
            st.optionalExpression = convertExpr(that.optionalExpression);
            st.source = that.source;
            st.description = that.description;
            st.id = that.id;
            result = addStat(st);
            return;
        }
        try {
          switch (that.token) {
            case ASSERT:
                addTraceableComment(that);
                JCExpression e = convertJML(that.expression);
                addAssumeCheck(that,currentStatements,"before explicit assert statement");
                JCExpression opt = that.optionalExpression;
                if (!(opt instanceof JCLiteral)) {
                    opt = convertJML(opt);
                } 
                result = addAssert(false,that,Label.EXPLICIT_ASSERT,e,null,null,opt);
                break;
            case ASSUME:
                addTraceableComment(that);
                JCExpression ee = convertJML(that.expression);
                opt = that.optionalExpression;
                if (!(opt instanceof JCLiteral)) {
                    opt = convertJML(opt);
                } 
                result = addAssume(that,Label.EXPLICIT_ASSUME,ee,null,null,opt);
                addAssumeCheck(that,currentStatements,"after explicit assume statement");
                break;
            case COMMENT:
                JCExpression expr = fullTranslation ? convertJML(that.expression) : that.expression;
                {
                    JmlStatementExpr st = M.at(that).JmlExpressionStatement(that.token,that.label,expr);
                    st.setType(that.type);
                    st.associatedSource = that.associatedSource;
                    st.associatedPos = that.associatedPos;
                    st.optionalExpression = fullTranslation ? convertExpr(that.optionalExpression) : that.optionalExpression;
                    st.source = that.source;
                    result = addStat(st);
                }
                break;
            case UNREACHABLE:
                addTraceableComment(that);
                result = addAssert(that,Label.UNREACHABLE,treeutils.falseLit);
                break;
            case REACHABLE:
                addTraceableComment(that);
                addAssumeCheck(that,currentStatements,"at reachable statement",
                        that.expression == null ? treeutils.trueLit : convertExpr(that.expression));
                break;
            case HENCE_BY:
                // FIXME - implement HENCE_BY
                notImplemented(that,"hence_by statement");
                result = null;
                break;
            default:
                error(that,"Unknown token type in JmlAssertionAdder.visitJmlStatementExpr: " + that.token.internedName());
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
            error(that,"Unexpected call of JmlAssertionAdder.visitJmlStatementHavoc while translating JML: " + that.getClass());
            return;
        }
        try {
            result = addStat( M.at(that).JmlHavocStatement(convertJML(that.storerefs)).setType(that.type));
        } catch (JmlNotImplementedException e) {
            notImplemented("havoc statement containing ",e);
        }
    }

    // OK
    @Override
    public void visitJmlStatementLoop(JmlStatementLoop that) {
        JmlStatementLoop st = M.at(that).JmlStatementLoop(that.token, convertExpr(that.expression));
        st.setType(that.type);
        //st.sym = that.sym;
        result = st;
    }

    // OK
    @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        log.warning(that,"jml.refining.specs.not.implemented");
        //result = M.at(that).JmlStatementSpec(convert(that.statementSpecs)).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        JCExpression ta = convertExpr(that.expression);
        JCExpression tl = convertExpr(that.lo);
        result = eresult = M.at(that).JmlStoreRefArrayRange(
                ta,
                tl,
                (that.lo == that.hi) ? tl : convertExpr(that.hi)
                        ).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        eresult = that;
        if (fullTranslation) eresult = M.at(that).JmlStoreRefKeyword(that.token);
        result = eresult;
    }

    // OK
    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        if (pureCopy) {
            result = eresult = M.at(that).JmlStoreRefListExpression(that.token,convert(that.list)).setType(that.type);
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
                        if (rac) old = convertJML(old);
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
                            if (rac) old = convertJML(old);
                            bin = treeutils.makeEquality(arg.pos, expr, old);
                        } else {
                            throw new JmlNotImplementedException(that,that.token.internedName());
                        }
                    } else {
                        // could be a.*, a[*], a[i..j]
                        throw new JmlNotImplementedException(that,that.token.internedName());
                    }
                    and = and == null ? bin : treeutils.makeAnd(that.pos, and, bin);
                }
                result = eresult = convertExpr(and);
                break;
            }

            default:
                result = eresult = M.at(that).JmlStoreRefListExpression(that.token,convert(that.list)).setType(that.type);
                
        }
    }

    // OK - readable and writable clauses
    @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCIdent id = treeutils.makeIdent(that.identifier.pos,that.identifier.sym);
        JCExpression expr = convertExpr(that.expression);
        JmlTypeClauseConditional cl = M.at(that).JmlTypeClauseConditional(mods, that.token, id, expr);
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
        JmlTypeClauseConstraint cl = M.at(that).JmlTypeClauseConstraint(mods, expr, convert(that.sigs));
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    // OK - e.g. ghost or model declaration
    @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        if (pureCopy) {
            JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
            JmlTypeClauseDecl cl = M.at(that).JmlTypeClauseDecl(convert(that.decl));
            cl.setType(that.type);
            cl.source = that.source;
            cl.modifiers = mods;
            cl.token = that.token;
            classDefs.add(cl);
            result = cl;
            return;
        }
        scan(that.decl);
    }

    // OK - e.g. invariant
    @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCExpression expr = convertExpr(that.expression);
        JmlTypeClauseExpr cl = M.at(that).JmlTypeClauseExpr(mods, that.token, expr);
        cl.setType(that.type);
        cl.source = that.source;
//        if (!rac) classDefs.add(cl);// FIXME - should we have this at all?
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JmlTypeClauseIn cl = M.at(that).JmlTypeClauseIn(convert(that.list));
        cl.modifiers = mods;
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        cl.parentVar = that.parentVar; // FIXME - need to map declaration
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JmlTypeClauseInitializer cl = M.at(that).JmlTypeClauseInitializer(that.token);
        cl.modifiers = mods;
        cl.specs = convert(that.specs);
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
        JmlTypeClauseMaps cl = M.at(that).JmlTypeClauseMaps(expr,convert(that.list));
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
        JmlTypeClauseMonitorsFor cl = M.at(that).JmlTypeClauseMonitorsFor(mods, id, convert(that.list));
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    // FIXME - needs review
    @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        // FIXME - implement for esc
        if (pureCopy) {
            JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
            JCExpression id = convertExpr(that.ident);
            JCExpression expr = convertExpr(that.expression);
            JmlTypeClauseRepresents cl = M.at(that).JmlTypeClauseRepresents(mods, id, that.suchThat, expr);
            cl.setType(that.type);
            cl.source = that.source;
            cl.token = that.token;
            classDefs.add(cl);
            result = cl;
            return;
        }
        
        if (rac && that.suchThat) {
            notImplemented(that,"relational represents clauses (\\such_that)", that.source());
            return;
        }
        
        JCExpression e = that.ident;
        Symbol sym = null;
        if (e instanceof JCIdent) sym = ((JCIdent)e).sym;
        else if (e instanceof JCFieldAccess) sym = ((JCFieldAccess)e).sym;
        else {
            log.warning(that,"jml.internal.notsobad",
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
                    JCReturn st = M.at(that).Return(that.expression);
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
                    notImplemented(that,"represents clause containing " + ee.toString() + " expression", that.source());
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
                    notImplemented(that,"represents clause containing " + ee.getMessage() + " expression", that.source());
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
        JavaFileObject prevSource = log.useSource(that.source());

        try {
            
        if (pureCopy) { 
            JCStatement stat = M.at(that).VarDef(that.sym,convertExpr(that.init));
            if (inClassDecl()) classDefs.add(stat);
            else addStat(stat);
            result = stat;
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
            if (that.sym.attribute(attr.tokenToAnnotationSymbol.get(JmlToken.SPEC_PUBLIC)) != null) {
                that.mods.flags &= ~Flags.AccessFlags;
                that.mods.flags |= Flags.PUBLIC;
                that.sym.flags_field  &= ~Flags.AccessFlags;
                that.sym.flags_field |= Flags.PUBLIC;
            }
            if (that.sym.attribute(attr.tokenToAnnotationSymbol.get(JmlToken.SPEC_PROTECTED)) != null) {
                that.mods.flags &= ~Flags.AccessFlags;
                that.mods.flags |= Flags.PROTECTED;
                that.sym.flags_field  &= ~Flags.AccessFlags;
                that.sym.flags_field |= Flags.PROTECTED;
            }
        }
        
        
        if (!inClassDecl()) {
            addTraceableComment(that,that,that.toString(),null);
        }
       
        if (( that.type.tsym.flags_field & Flags.ENUM)!= 0) { // FIXME - should check the initializer expressions of enums
            JmlVariableDecl stat = M.at(that).VarDef(that.sym,that.init);
            stat.ident = newident;

            if (inClassDecl()) classDefs.add(stat);
            else addStat(stat);

            result = stat;
            return;
        }
        
        boolean inClassDecl = inClassDecl(); 
        if (localVariables.containsKey(that.sym)) {
            JmlVariableDecl stat = M.at(that).VarDef(that.sym,null);
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
                JmlVariableDecl stat = null;
                try { 
                    init = convertJML(that.init);
                    if (init != null) init = addImplicitConversion(init,that.type,init);

                    stat = M.at(that).VarDef(that.sym,init);
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
                    if (nn != null) addAssert(that,Label.POSSIBLY_NULL_INITIALIZATION,nn,that.name);
                    if (esc && !that.type.isPrimitive()) {
                        addAssume(that,Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeInEquality(that, 
                                treeutils.makeIdent(that.pos, that.sym), 
                                that.type));
                    }
                } finally {
                    if (inClassDecl) {
                        JCBlock bl = popBlock(that.mods.flags & Flags.STATIC,that);
                        if (stat != null) classDefs.add(stat);
                        classDefs.add(bl);
                    } else {
                        if (stat != null) addStat(stat);
                    }
                }
                result = stat;
            } catch (JmlNotImplementedException e) {
                notImplemented("ghost declaration containing ",e);
            }
        } else if (that.init == null) {
            JmlVariableDecl stat = M.at(that).VarDef(that.sym,that.init);
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
                addAssume(that,Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeInEquality(that, 
                    treeutils.makeIdent(that.pos, that.sym), 
                    that.type));
            }

            result = stat;
        } else {
            // FIXME - are these regular Java declarations?  what about model decls?

            // FIXME - need to make a unique symbol; what if the decl is final?
            JmlVariableDecl stat = M.at(that).VarDef(that.sym,null);
            stat.ident = newident;
            // type, vartype, sym, name, mods, init are filled in
            stat.mods = that.mods;
            stat.sourcefile = that.sourcefile;
            stat.docComment = that.docComment;
            stat.fieldSpecs = that.fieldSpecs;
            stat.fieldSpecsCombined = that.fieldSpecsCombined;
            stat.specsDecl = that.specsDecl;

            pushBlock();
            JCExpression init = null;
            JCExpression nn = null;
            try {
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

                init = convertExpr(that.init);
                if (init != null) init = addImplicitConversion(init,that.type,init);

                if (init != null && !init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
                    nn = treeutils.makeNeqObject(init.pos, init, treeutils.nullLit);
                    if (init instanceof JCLiteral) {
                        // FIXME - potential optimizations, but they need testing, particularly the second one
                        if (init.type.tag == TypeTags.BOT) nn = treeutils.falseLit;
                        else if (init.type.tag == TypeTags.CLASS) nn = treeutils.trueLit;
                    } 
                    // FIXME - should have an associated position
                }

            } finally {
                if (statementStack.get(0) == null) {
                    // Class definition
                    if (currentStatements.isEmpty() && nn == null) {
                        // Just a simple initialization since there is no nonnull check
                        // and the init expression did not create any new statements
                        popBlock(0,null); // Nothing present - just ignore the empty block
                        stat.init = init;
                        this.classDefs.add(stat);
                        if (esc && !that.type.isPrimitive()) {
                            addAssume(that,Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeInEquality(that, 
                                    treeutils.makeIdent(that.pos, that.sym), 
                                    that.type));
                        }
                    } else {
                        long flags = that.mods.flags & Flags.STATIC;

                        // Create a initializer block
                        if (nn != null) addAssert(that,Label.POSSIBLY_NULL_INITIALIZATION,nn,that.name);
                        addStat(treeutils.makeAssignStat(that.pos, treeutils.makeIdent(that.pos, stat.sym), init));
                        if (esc && !that.type.isPrimitive()) {
                            addAssume(that,Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeInEquality(that, 
                                    treeutils.makeIdent(that.pos, that.sym), 
                                    that.type));
                        }
                        JCBlock bl = popBlock(flags,that);
                        this.classDefs.add(stat);
                        this.classDefs.add(bl);
                    }
                    methodDecl = null;
                } else {
                    // Regular method body
                    JCBlock bl = popBlock(0,that);
                    currentStatements.addAll(bl.stats);
                    if (nn != null) addAssert(that,Label.POSSIBLY_NULL_INITIALIZATION,nn,that.name);
                    stat.init = init;
                    addStat(stat);
                    if (esc && !that.type.isPrimitive()) {
                        addAssume(that,Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeInEquality(that, 
                                treeutils.makeIdent(that.pos, that.sym), 
                                that.type));
                    }
                }
                result = stat;
            }
        }
        
        } finally {
            log.useSource(prevSource);
        }
        
    }
    
    // FIXME - review for best implementeation and uniform use
    protected boolean inClassDecl() {
        return currentStatements == null;
    }
    
    // OK
    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        if (pureCopy) {
            JCExpression e = convertExpr(that.cond);
            JmlWhileLoop loop = M.at(that).WhileLoop(e,null);
            try {
                treeMap.put(that, loop);
                JCStatement bl = convertIntoBlock(that.body,that.body);
                loop.body = bl;
                loop.setType(that.type);
                loop.loopSpecs = convertCopy(that.loopSpecs); 
                result = loop;
            } finally {
                treeMap.remove(that);
            }
            addStat(loop);
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

        JCVariableDecl indexDecl = loopHelperDeclareIndex(that);;

        java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

        // Create this early so it is available as a target
        JmlWhileLoop loop = M.at(that).WhileLoop(treeutils.trueLit,null);
        treeMap.put(that, loop);

        // Test that invariants hold before entering loop
        loopHelperInitialInvariant(that.loopSpecs);

        // New loop body
        pushBlock();
        
        // Havoc all items that might be changed in the loop
        if (esc) {
            loopHelperHavoc(that.body,indexDecl,that.body,that.cond);
        }
        
        loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that);
        
        // Compute the condition, recording any side-effects
        {
            
            addTraceableComment(that.cond,that.cond,"Loop test");
            JCExpression cond = convertExpr(that.cond);

            // The exit block tests the condition; if exiting, it tests the
            // invariant and breaks.
            loopHelperMakeBreak(that.loopSpecs, cond, loop, that);
        }
        
        // Now in the loop, so check that the variants are non-negative
        loopHelperCheckNegative(decreasesIDs, that);
        
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
                sp = pp;
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

//    public void record(JCTree that) {
//        idmapper.scan(that);
//    }
//
//    final public IdentityMap idmapper = new IdentityMap();
//    
//
//    // Not static 
//    public class IdentityMap extends JmlTreeScanner {
//        
//        public void scan(JCTree that) {
//            super.scan(that);
//            exprBiMap.put(that, that);
//        }
//        
//    }
//    
//    public static interface I {
//        public int v(final Object[] args);
//    }
//    
//    public static class A {
//        
//        
//        public int m() {
//            
//            Object o;
//            o = new Object();
//            
//            int r = (new I(){ public int v(final Object[] args) { return 1; }}).v(new Object[]{o});
//            return r;
//        }
//    }
// 
    
    protected void markLocation(Name label, ListBuffer<JCStatement> list, JCStatement marker) {
        Location loc = new Location(list,marker);
        locations.put(label,loc);
    }
    
    protected void insertAtLocation(Name label, JCStatement ... statements) {
        Location loc = locations.get(label);
        if (loc == null) {
            // INTENRAL ERROR - FIXME
        } else {
            ListBuffer<JCStatement> orig = loc.list;
            ListBuffer<JCStatement> temp = new ListBuffer<JCStatement>();
            ListBuffer<JCStatement> tail = new ListBuffer<JCStatement>();
            head: {
                while (!orig.isEmpty()) {
                    JCStatement t = orig.remove();
                    if (t == loc.marker) { tail.add(t); break head; }
                    temp.add(t);
                }
                // FIXME - INTERNAL ERROR - marker not in list
            }
            while (!orig.isEmpty()) {
                JCStatement t = orig.remove();
                tail.add(t);
            }
            orig.appendList(temp);
            orig.appendArray(statements);
            orig.appendList(tail);
        }
    }
    
    protected Map<Name, Location> locations = new HashMap<Name,Location>();
    public class Location {
        public ListBuffer<JCStatement> list;
        public JCStatement marker;
        public Location(ListBuffer<JCStatement> list, JCStatement marker) {
            this.list = list;
            this.marker = marker;
        }
    }

}

