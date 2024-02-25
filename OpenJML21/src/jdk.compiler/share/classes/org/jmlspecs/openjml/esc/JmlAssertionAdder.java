/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URI;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;

import javax.lang.model.type.ExecutableType;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.SpecsStatus;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.Nowarns.Item;
import org.jmlspecs.openjml.Utils.JmlNotImplementedException;
import org.jmlspecs.openjml.ext.*;
import org.jmlspecs.openjml.ext.StatementLocationsExtension.LocationSetStatementType;

import static org.jmlspecs.openjml.ext.RecommendsClause.*;
import static org.jmlspecs.openjml.ext.MiscExtensions.*;
import static org.jmlspecs.openjml.ext.AssignableClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeRWClauseExtension.*;
import static org.jmlspecs.openjml.ext.ShowStatement.*;
import static org.jmlspecs.openjml.ext.MiscExpressions.*;
import static org.jmlspecs.openjml.ext.FrameExpressions.*;
import static org.jmlspecs.openjml.ext.QuantifiedExpressions.*;
import static org.jmlspecs.openjml.ext.Operators.*;
import static org.jmlspecs.openjml.ext.LineAnnotationClauses.*;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.MethodExprListClauseExtensions.*;
import static org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions.*;
import static org.jmlspecs.openjml.ext.SingletonExpressions.*;
import static org.jmlspecs.openjml.ext.FunctionLikeExpressions.*;
import static org.jmlspecs.openjml.ext.StateExpressions.*;
import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;
import static org.jmlspecs.openjml.ext.TypeExprClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeInClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeRepresentsClauseExtension.*;
import static org.jmlspecs.openjml.ext.JMLPrimitiveTypes.*;

import org.jmlspecs.openjml.visitors.JmlTreeCopier;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.visitors.JmlTreeSubstitute;

import com.sun.source.tree.*;
import com.sun.tools.javac.code.*;

import com.sun.tools.javac.code.Attribute.Compound;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol.*;
import com.sun.tools.javac.comp.*;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.*;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.Log.WriterKind;

/**
 * This class translates an attributed Java+JML AST, creating a new
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
 * classes, considered to be non-mutable, are still shared with the original
 * AST, such as JCLiteral, JCAnnotation, JCModifiers.
 * <P>
 * There are two modes of translation:
 * <UL>
 * 
 * <LI>esc=true,rac=false: This inserts all JML semantics as new
 * Java constructs and JML assert and assume statements, retaining the Java
 * control flow statements. The result is a Java AST with some JML features but
 * is not executable.
 * 
 * <LI>rac=true,esc=false: This inserts all executable JML checks
 * as calls to an assertionFailure method - which can dynamically choose to
 * print out warning messages, throw exceptions, or execute a Java assert. The
 * translated AST is a transformation of the original program, but is
 * functionally equivalent to it, aside from the additional checks.
 * 
 * <LI>esc=true,rac=true: unsupported.
 * <LI>esc=false,rac=false: unsupported.
 * </UL>
 * <P>
 * With either rac or esc on, the translated AST uses only a subset of Java
 * functionality. All JML features are translated into assertions and Java
 * statements.
 * <P>
 * Within both the rac and esc modes, subtrees may be translated with
 * 'translatingJML' true - this should not be set by the caller, but is used to
 * translate Java constructs in JML expressions differently than Java constructs
 * in Java code. // *
 * <UL>
 * -- FIXME - fix all of the following // *
 * <LI>Java expressions: // *
 * </UL>
 * // *
 * <LI>binary operations - arithmetic, bit, logical all allowed in Java
 * statements and JML assertions; // * instanceof is allowed in Java, translated
 * into a type relationship in JML // *
 * <LI>unary operations - minus and negation allowed; pre- and post-increment //
 * * and decrement converted to separate operations and assignment // *
 * <LI>assignment - retained // *
 * <LI>assign-op - separated into operation and assignment // *
 * <LI>type cast - TBD // *
 * <LI>field selection - TBD // *
 * <LI>array index - retained, but uses JmlBBArrayAccess nodes instead of
 * JCArrayAccess // *
 * <LI>// *
 * <LI>object allocation - TBD // *
 * <LI>array allocation - TBD // *
 * <LI>anonymous class expression - TBD // *
 * <LI>...TBD // *
 * </UL>
 * // *
 * <LI>Java statements: // *
 * <UL>
 * // *
 * <LI>if, switch, try statements are retained // *
 * <LI>for, while, do, foreach statements are retained but may be transformed //
 * * into other loop types to accommodate inserting loop specifications // *
 * <LI>variable declarations - TBD // *
 * <LI>local class declarations - TBD // *
 * <LI>method declarations, class declarations, import declarations - all
 * retained // *
 * </UL>
 * // *
 * <LI>JML expressions: // *
 * <UL>
 * // *
 * <LI>binary logical operations - converted to Java equivalents // *
 * <LI>subtype operation - TBD // *
 * <LI>... TBD // *
 * </UL>
 * // *
 * <LI>JML statements and features: // *
 * <UL>
 * // *
 * <LI>assert, assume statements - is esc mode, these are retained as JML
 * statements // * in rac mode, they are converted to RAC checks // *
 * <LI>method clauses: requires, ensures, signals - converted to assertions // *
 * </UL>
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

    /** This value is set by the environment variable OJ, as in OJ="assert=n" and has the effect that a stack dump is printed
     * when the assertion with the given number is created. Purely for debugging.
     */
    public static int assertCountCheck = Integer.parseInt(Utils.debugValue("assert:","-1"));
    public static int uniqueCountCheck = Integer.parseInt(Utils.debugValue("unique:","-1"));

	// Parameters of this instance of JmlAssertionAdder


    // Constant items not changed after initialization. They depend on options.
    
	/**
	 * If true then every part of every AST is copied; if false then items expected
	 * to be immutable such as JCLiteral, qualified ids (in import statements,
	 * static type designators), JCAnnotation are not duplicated. Non-AST objects
	 * such as Type, Token or JmlToken values are not duplicated in any case.
	 */
	public boolean fullTranslation = true; // FIXME - should be able to be false, but causes RAC errors

	// NOTE: We support !esc || !rac but not esc && rac.
	// @ invariant !esc || !rac;

	/** True if we are translating for static checks */
	public boolean esc;

	/** True if we are translating for RAC */
	public boolean rac;

	/** True if we are translating for inference */
	public boolean infer;

	/** True if we are translating for boogie */ // Not even started to be implemented.
	public boolean boogie;

	// Constant items set in the constructor -- fixed for a value of 'context'

	/** Cached value of the Log tool */
	final public Log log;

	/** Cached value of the specs database */
	final protected JmlSpecs specs;

	/** Cached value of JmlTypes */
	final public JmlTypes jmltypes;

	/** Cached value of the AST node factory */
	final public JmlTree.Maker M;

	/** Cached value of the names table */
	final public Names names;

	/** Cached value of the symbol table */
	final public Symtab syms;

	/** Cached value of the Types tool */
	final public JmlTypes types;

	/** Cached value of the Utils tool */
	final public Utils utils;

	/** Cached value of the Nowarns object */
	final protected Nowarns nowarns;

	/** Cached value of the Attribute tool */
	final protected JmlAttr attr;

	/** The JmlTreeUtils object, holding a bunch of tree-making utilities */
	final public JmlTreeUtils treeutils;

	/** The tool to find class symbols */
	final protected ClassReader reader;

	/** The symbol for the runtime Utils class */
	final protected ClassSymbol utilsClass;

	/** The Name used for the result of a method */
	final protected Name resultName;
	
    /** The Name used for exceptions thrown in the body of a method */
    final protected Name exceptionName;

    /**
     * The Name used for holding the location at which the final return or throw
     * statement occurs
     */
    final protected Name terminationName;

    final protected Name hereLabelName;
    final protected Name loopinitLabelName;
    final protected Name loopbodyLabelName;

    /** A tree-visitor that copies an AST, including types; symbols do not change */ // FIXME - break targets?
	final protected Copier copier;

    //////////////////////////////////////////////////////////////////////////////////
	// Items that are fixed for a method (while it is being translated)
	// Note that translating methods can be recursive (when there are local classes)
	// so that these items need to be saved and restored, but only at initialization for a method
	// Some of these depend on options that can change from method to method
	
    /**
     * The parent class of the method being converted, for use while the
     * declarations of the class are being walked, and while a method is being
     * translated stand-alone (without having been reached by walking the tree from
     * above).
     */
    protected JmlClassDecl classDecl = null;

    protected Symbol enclosingMethod;
    protected Symbol enclosingClass;

    /**
     * The Ident to use when translating this - starts as the this for the receiver
     * object, but can change as methods or constructors are called.
     */
    protected JCIdent explicitThisId;

    /** The symbol for the variable that holds the result of a method */
    protected VarSymbol resultSym = null;

    /**
     * The symbol for the variable that tracks exceptions in the body of a method
     */
    protected VarSymbol exceptionSym = null;

    /**
     * The symbol for the variable that holds allocation ids to distinguish
     * dynamically allocated objects
     */
    protected Symbol allocSym = null;

    /** The symbol for the variable that says whether an object is allocated */
    protected Symbol isAllocSym = null;

    /** The symbol to go with terminationName. */
    protected VarSymbol terminationSym = null;

    //////////////////////////////////////////////////////////////////////////////////
    // Items that change in the course of translating a method
	
    /** A counter used to make unique precondition detail symbols */
    public int preconditionDetail = 0;

	/**
	 * An expression to be used for \result when translating postconditions; the
	 * expression should always be copied afresh for each instantiation
	 */
	protected JCExpression resultExpr = null;

	/**
	 * Name of the break label when return statements are translated to break
	 * statements for inlining
	 */
	// @ nullable
	protected Name breakName = null;


	/** A counter used to make distinct ids for newly allocated Objects */
	protected int allocCounter = 0;

	/** Exception Symbols used for various methods */
	protected Map<JCMethodDecl, VarSymbol> exceptionSymbols = new HashMap<>();

	/** The Name used for catching exceptions thrown by called methods */
	final protected Name exceptionNameCall;

	/** Termination Symbols used for various methods */
	protected Map<JCMethodDecl, VarSymbol> terminationSymbols = new HashMap<>();

	// Fields used and modified during translation
	// These should only be modified by visit methods

	/** The AST being processed when in a sub-tree of a method declaration */
	protected JmlMethodDecl methodDecl = null;

	/** Location of calls within the method or its specifications */
	protected /* @ nullable */ JCTree nestedCallLocation = null;

	/**
	 * The receiver expression, such as when performing a method call within the
	 * body of the method being translated.
	 */
//	protected JCExpression currentThisExpr;


	protected boolean isRefiningBranch = false;

	/** Depth of nesting of applyHelper calls */
	protected int applyNesting;

	public Translations translations = null;

	/**
	 * The counter used to make uniquely named variables for preconditions, unique
	 * within a method body.
	 */
	int precount = 0;

	/**
	 * The counter used to make uniquely named variables for assertions, unique
	 * within a method body.
	 */
	protected int assertCount = 0;

	/** A counter that ensures unique variable names (within a method body). */
	protected int uniqueCount = 0;
	public int nextUnique() { if (uniqueCount == uniqueCountCheck) Utils.dumpStack("TMP UNIQUE " + uniqueCount); return uniqueCount++; }

	public boolean useBV;

	/**
	 * A map from formal parameter to actual argument, used when translating methods
	 * called within a method body; also used to map formals in inherited method
	 * specs to actual arguments or to the formals in the base method.
	 */
	protected Map<Object, JCExpression> paramActuals_;

	protected Map<Symbol, Type> typeActuals = new HashMap<>();

	/**
	 * A map from specification case to a JCIdent that is a variable holding the
	 * value of the precondition for that specification case.
	 */
	protected Map<JmlSpecificationCase, JCIdent> preconditions = new HashMap<JmlSpecificationCase, JCIdent>();

	/**
	 * A map from old nodes to new ones, for use when there are node references
	 * (rather than copies of trees) within an AST. In particular used to set the
	 * target fields for break and continue statements.
	 */
	protected java.util.Map<JCTree, JCTree> treeMap = new HashMap<JCTree, JCTree>();

	/**
	 * A List used to accumulate translated definitions of a class, for cases where
	 * new declarations are needed.
	 */
	protected ListBuffer<JCTree> classDefs = null;

	/** A list to collect statements as they are being generated. */
	protected ListBuffer<JCStatement> currentStatements;

	/** A list aliased with the place to put computations of \pre expressions. */
	protected ListBuffer<JCStatement> oldStatements;

	/** The prelude statements of the current method */
	protected ListBuffer<JCStatement> initialStatements;

	/**
	 * A stack of 'currentStatements' . The current value of 'currentStatements' is
	 * NOT on this stack.
	 */
	protected LinkedList<ListBuffer<JCStatement>> statementStack = new LinkedList<ListBuffer<JCStatement>>();

	/**
	 * A stack of labeled statements that might be targets of continue statements
	 */
	java.util.Stack<JCLabeledStatement> continueStack = new java.util.Stack<JCLabeledStatement>();

	/**
	 * Stack of the synthetic index (trip count) variables for loops enclosing the
	 * code under current consideration. 0th element is the currently innermost
	 * scope
	 */
	protected java.util.List<JCVariableDecl> indexStack = new LinkedList<JCVariableDecl>();

	/**
	 * true when translating JML constructs, false when translating Java constructs.
	 * This is set and manipulated by the visitor methods
	 */
	public boolean translatingJML = false;

	/**
	 * True when expressions are split to make temporaries; if this is false,
	 * tracing is not available; it needs to be false when translating quantified
	 * expressions
	 */
	public boolean splitExpressions = true;

	// FIXME - DOCUMENT
	public boolean convertingAssignable = false;
	// FIXME - DOCUMENT
	public boolean assumingPureMethod = false;

	// FIXME - DOCUMENT
	public ListBuffer<JCStatement> collectedAxioms = null;

	/**
	 * Contains an expression that is used as a guard in determining whether
	 * expressions are well-defined. For example, suppose we are translating the
	 * expression a != null && a[i] == 0. Then condition is 'true' when a!=null is
	 * translated. But when a[i] is translated, 'condition' will be a != null. The
	 * well-definedness check for a[i] will then be (a != null) ==> (a != null && i
	 * >= 0 && i < a.length). So the full expression is well-defined only if that
	 * implication can be proved given other pre-conditions.
	 */
	public JCExpression condition;

	// FIXME - DOCUMENT
	public JmlMethodClause conditionAssociatedClause = null;

	// FIXME - document
	protected java.util.List<JmlStatementExpr> wellDefinedConditions = new java.util.LinkedList<JmlStatementExpr>();

	/**
	 * Set to true when we are translating a normal or exceptional postcondition. It
	 * is used to be sure the correct scope is used when method parameters are used
	 * in the postcondition. If a method parameter is used in a postcondition it is
	 * evaluated in the pre-state since any changes to the parameter within the body
	 * of the method are discarded upon exit and are invisible outside the method
	 * (i.e. in the postcondition).
	 */
	protected boolean isPostcondition;

	/**
	 * Used to note the environment (e.g., \old label) under which we are currently
	 * evaluating expressions; null indicates the current state; the value preLabel indicates
	 * the pre-state, etc.
	 */
	/*@ nullable */ 
//	public Name evalStateLabel;
	
	/** The current interpretation of \Old. Starts out as \Pre, but can point to
	 * a statement contract or the prestate of a callee.
	 */
	/*@ nullable */ 
	public Name currentOldLabel = null;


	/** Used to hold the result of non-expression AST nodes */
	protected JCTree result;

	/**
	 * Used to hold the result of expression AST nodes, so equal to 'result' when
	 * 'result' is a JCExpression.
	 */
	protected JCExpression eresult;

	protected JCExpression elseExpression = null;

	// FIXME - DOCUMENT
	protected JCBlock axiomBlock = null;

	// FIXME - review which of these bimaps is actually needed

	/**
	 * A bi-map used to record the mapping between original and rewritten nodes, for
	 * reporting expression values
	 */
	public BiMap<JCTree, JCTree> exprBiMap = new BiMap<JCTree, JCTree>();

	/**
	 * A bi-map used to record statement mappings for reporting counterexample paths
	 */
	public BiMap<JCTree, JCTree> pathMap = new BiMap<JCTree, JCTree>();

	/**
	 * A bi-map used to record the mapping between original and rewritten method
	 * ASTs
	 */
	public BiMap<JmlMethodDecl, Translations> methodBiMap = new BiMap<JmlMethodDecl, Translations>();

	/**
	 * A bi-map used to record the mapping between original and rewritten class ASTs
	 */
	public BiMap<JmlClassDecl, JmlClassDecl> classBiMap = new BiMap<JmlClassDecl, JmlClassDecl>();

	public int feasibilityCheckCount = 0;

	public VarSymbol feasCheckSym;

	public Map<String, java.util.List<JmlStatementExpr>> feasibilityChecks = new HashMap<>();

	public int heapCount = 0;
	public int topHeapCount = 0;

	public int nextHeapCount() {
		heapCount = ++topHeapCount;
		return heapCount;
	}

	public VarSymbol heapSym = null;

	public Name heapVarName;

	public class LambdaInfo {
		public List<JCExpression> untrArgs;
		public MethodSymbol msym;
		public Type.MethodType actualType;
	}

	public Stack<LambdaInfo> lambdaUnTrArgs = new Stack<LambdaInfo>();
	{
		lambdaUnTrArgs.push(null);
	}
	boolean applyingLambda = false;

	public Stack<Name> inlinedBreaks = new Stack<Name>();
	{
		inlinedBreaks.push(null);
	}

	public boolean useNamesForHeap = true; // if false, use arguments for heap

	public String originalSplit = Strings.empty;
	public String currentSplit = Strings.empty;

	public void setSplits(Translations t, String split) {
	    translations = t;
	    originalSplit = split;
	    currentSplit = split;
	}


	/**
	 * (Public API) Creates an object to do the rewriting and assertion insertion.
	 * This object can be reused to translate different method bodies, so long as
	 * the arguments to this constructor remain appropriate. May not have both esc
	 * and rac true.
	 * 
	 * @param context the compilation context to be used
	 * @param esc     true if the resulting AST is to be used for ESC, otherwise
	 *                false
	 * @param fac     true if the resulting AST is to be used for RAC, otherwise
	 *                false
	 */
	public JmlAssertionAdder(Context context, boolean esc, boolean rac, boolean infer) {
		super(context);
		this.esc = esc;
		this.rac = rac;
		this.infer = infer;
		this.log = Log.instance(context);
		this.M = JmlTree.Maker.instance(context);
		this.names = Names.instance(context);
		this.nowarns = Nowarns.instance(context);
		this.syms = Symtab.instance(context);
		this.types = JmlTypes.instance(context);
		this.utils = Utils.instance(context);
		this.specs = JmlSpecs.instance(context);
		this.jmltypes = JmlTypes.instance(context);
		this.treeutils = JmlTreeUtils.instance(context);
		this.attr = JmlAttr.instance(context);
		this.resultName = names.fromString(Strings.resultVarString);
		this.exceptionName = names.fromString(Strings.exceptionVarString);
		this.exceptionNameCall = names.fromString(Strings.exceptionCallVarString);
		this.terminationName = names.fromString(Strings.terminationVarString);
        this.hereLabelName = names.fromString(Strings.hereLabelBuiltin);
        this.loopinitLabelName = names.fromString(Strings.loopinitLabelBuiltin);
        this.loopbodyLabelName = names.fromString(Strings.loopbodyLabelBuiltin);
		this.reader = ClassReader.instance(context);
		this.copier = new Copier(context,M);
		// this.reader.init(syms); // FIXME?
		this.utilsClass = !rac ? null : reader.enterClass(names.fromString(Strings.runtimeUtilsFQName));

		initialize();

	}

	public JmlAssertionAdder(Context context, boolean esc, boolean rac) {
		this(context, esc, rac, false);
	}

	public void initialize() {
	    methodEnv = methodEnv.pushEnvInit(context,esc,rac);
		this.boogie = false; // esc && JmlOption.isOption(context,JmlOption.BOOGIE);
		this.uniqueCount = 0;
		this.assertCount = 0;
		this.precount = 0;
		this.preconditions.clear();
		this.treeMap.clear();
//		this.evalStateLabel = null;
		this.currentOldLabel = attr.preLabel;
		this.heapCount = this.topHeapCount = 0;
		this.heapVarName = names.fromString(Strings.heap); // FIXME - cf. BasicBlocker2
		this.applyNesting = 0;
		racMessages.clear();
		escMessages.clear();
		this.useMethodAxioms = false; // !JmlOption.isOption(context,JmlOption.MINIMIZE_QUANTIFICATIONS);
		this.checkAccessEnabled = JmlOption.isOption(context, JmlOption.CHECK_ACCESSIBLE);
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
			msym = new MethodSymbol(flags, classDecl.name, null, classDecl.sym);
			methodDecl = // M.MethodDef(msym, null,null);
					new JmlMethodDecl(
							M.Modifiers(flags, M.Annotations(List.<com.sun.tools.javac.code.Attribute.Compound>nil())),
							classDecl.name, null, null, null, null, null, null, // body,
							null, msym);
		}
		exceptionSym = exceptionSymbols.get(methodDecl);
		if (exceptionSym == null) {
			JCVariableDecl d = treeutils.makeVarDef(syms.exceptionType, exceptionName, msym,
					treeutils.makeNullLiteral(methodDecl.pos));
			exceptionSym = d.sym;
			exceptionSymbols.put(methodDecl, exceptionSym);
			currentStatements.add(d);
		} else {
			JCVariableDecl d = treeutils.makeVarDefWithSym(exceptionSym, treeutils.makeNullLiteral(methodDecl.pos));
			currentStatements.add(d);
		}

		terminationSym = terminationSymbols.get(methodDecl);
		if (terminationSym == null) {
			JCVariableDecl d = treeutils.makeVarDef(syms.intType, terminationName, methodDecl.sym,
					treeutils.makeIntLiteral(methodDecl.pos, 0));
			terminationSym = d.sym;
			terminationSymbols.put(methodDecl, terminationSym);
			currentStatements.add(d);
		} else {
			JCVariableDecl d = treeutils.makeVarDefWithSym(terminationSym,
					treeutils.makeIntLiteral(methodDecl.pos, 0));
			currentStatements.add(d);
		}

		if (esc) {
			JCVariableDecl d = treeutils.makeVarDef(syms.intType, names.fromString(Strings.feasCheckVar), methodDecl.sym, Position.NOPOS); 
					// NOPOS so the name is not mangled
			feasCheckSym = d.sym;
			d.sym.owner = null;
			currentStatements.add(d);
		}

		saveMapping(treeutils.nullLit, treeutils.nullLit);

	}

	// FIXME - this comment needs review and correction
	/**
	 * Creates the overall framework for the block:
	 * 
	 * <PRE>
	 *  
	     preconditions
	     try {
	        method body
	     } finally {
	        postconditions
	     }
	 * </PRE>
	 * <P>
	 * The converted method body is a new block with the following characteristics:
	 * <UL>
	 * <LI>control flow statements are still present: if-then-else, switch,
	 * try-catch-finally blocks
	 * <LI>expressions in Java code are decomposed into individual operations, with
	 * temporaries. This is so that (a) it is easy to add any assertions prior to a
	 * specific operation (b) it is straightforward to handle any operation with
	 * side-effects, even in the context of short-circuit operations
	 * <LI>assertions are added in for any checks that are desired (see the list
	 * below)
	 * <LI>specification expressions are not decomposed into individual operations,
	 * since all the sub-expressions are supposed to be pure; however, additional
	 * assertions are added before any specification expression to check that the
	 * specification expression is well-defined - TODO
	 * <LI>conditional and short-circuit expressions (in Java code) are converted
	 * into if-then-else statements; again, this is to simplify handling of
	 * side-effects in sub-expressions - TODO for short-circuit
	 * <LI>all identifiers are made unique by combining the name with location
	 * information; but no conversions for single-assignment are performed - TODO
	 * </UL>
	 * <P>
	 * These operations are converted:
	 * <UL>
	 * <LI>JML equivalence to boolean =
	 * <LI>JML inequivalence to boolean !=
	 * <LI>JML reverse implies (p <== q) to (p || !q)
	 * <LI>Java assignments with operations are decomposed into the operation and
	 * the assignment
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
	 * <LI>TODO: mod, integer division, shift operations, bit operations, JML
	 * implies, JML subtype, instanceof, short-circuit boolean operations
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

	/**
	 * (Public API) Returns a new JCBlock representing the rewritten body of the
	 * given method declaration.
	 */
	public JCBlock convertMethodBody(JmlMethodDecl pmethodDecl, JmlClassDecl pclassDecl) {
		initialize();
		return convertMethodBodyNoInit(pmethodDecl, pclassDecl);
	}

	Map<TypeSymbol, Type> typevarMapping;

	protected boolean assumingPostConditions;

	protected JCBlock discoveredFields;
	protected Set<Symbol> alreadyDiscoveredFields = new HashSet<>();
	Set<Type> activeExceptions = new HashSet<>();

	int freshnessReferenceCount;

	public void findActiveExceptions(JmlMethodDecl methodDecl) {
		for (MethodSymbol msym : utils.parents(methodDecl.sym,true)) {
			if (msym.params == null)
				continue; // FIXME - we should do something better? or does this mean binary with no
							// specs?
			JmlMethodSpecs denestedSpecs = JmlSpecs.instance(context).getDenestedSpecs(msym);
			if (denestedSpecs != null)
				for (JmlSpecificationCase cs : denestedSpecs.cases) {
					for (JmlMethodClause clause : cs.clauses) {
						if (clause instanceof JmlMethodClauseSignalsOnly) {
							JmlMethodClauseSignalsOnly so = (JmlMethodClauseSignalsOnly) clause;
							if (!so.defaultClause)
								for (JCExpression x : so.list) {
									activeExceptions.add(x.type);
								}
						}
					}
				}
		}
	}

	ListBuffer<Pair<JCExpression, JmlSource>> divergesExpressions = null;

	/** Internal method to do the method body conversion */
	protected JCBlock convertMethodBodyNoInit(JmlMethodDecl pmethodDecl, JmlClassDecl pclassDecl) {
		//System.out.println("CONVERTING " + pclassDecl.sym + " " + pmethodDecl.sym);
		JmlOptions.instance(context).pushOptions(pmethodDecl.mods);
		int prevAssumeCheckCount = feasibilityCheckCount;
		JmlMethodDecl prevMethodDecl = this.methodDecl;
		JmlClassDecl prevClass = this.classDecl;
		JCIdent savedExplicitThisId = this.explicitThisId;
		JCExpression savedThisExpr = this.currentEnv.currentReceiver;
		VarSymbol savedExceptionSym = this.exceptionSym;
		Symbol savedEnclosingMethod = this.enclosingMethod;
		Symbol savedEnclosingClass = this.enclosingClass;
		VarSymbol savedResultSym = this.resultSym;
		JCExpression savedResultExpr = this.resultExpr;
		VarSymbol savedTerminationSym = this.terminationSym;
		int savedFreshnessReferenceCount = this.freshnessReferenceCount;
		this.freshnessReferenceCount = 0;
		ListBuffer<JCStatement> prevStats = initialStatements;
		ListBuffer<JCStatement> savedOldStatements = oldStatements;
		JavaFileObject prevSource = log.useSource(pmethodDecl.source());
		Map<Object, JCExpression> savedParamActuals = paramActuals_;
		java.util.List<Symbol> savedCompletedInvariants = this.completedInvariants;
		Set<Symbol> savedInProcessInvariants = this.inProcessInvariants;
		boolean isModel = isModel(pmethodDecl.sym);
		JCBlock savedDiscoveredFields = discoveredFields;
		Set<Symbol> savedAlreadyDiscoveredFields = alreadyDiscoveredFields;
		int savedAllocCounter = allocCounter;
		JCTree savedNestedCallLocation = nestedCallLocation;
		nestedCallLocation = null;
		Set<Type> savedActiveExceptions = activeExceptions;
		activeExceptions = new HashSet<>();
		findActiveExceptions(pmethodDecl);

		this.currentEnv = this.currentEnv.pushEnvCopy(); // FIXME - or pushCopyInit?
        currentEnv.arithmeticMode = Arithmetic.Math.instance(context).defaultArithmeticMode(pmethodDecl.sym, false);

		var savedDivergesExpressions = divergesExpressions;
		divergesExpressions = new ListBuffer<>();

		allocCounter = 0;

		if (pmethodDecl.sym.isDefault()) {
			allocSym.flags_field |= Utils.JMLINSTANCE;
			isAllocSym.flags_field |= Utils.JMLINSTANCE;
		}

		// Collect all classes that are mentioned in the method, plus some other information
		ClassCollector collector = ClassCollector.collect(pclassDecl, pmethodDecl, context);

		{
			String bv = JmlOption.value(context, JmlOption.ESC_BV);
			useBV = !rac && ((collector.useBV && "auto".equals(bv)) || "true".equals(bv));
			pmethodDecl.usedBitVectors = useBV;
		}
		if (!isModel) addAxioms(-1, null);
		assumingPostConditions = true;

		typevarMapping = typemapping(pclassDecl.type, null, null, null);

		boolean undoLabels = false; // TODO - explain why this is used
		try {
			enclosingMethod = pmethodDecl.sym;
			enclosingClass = pmethodDecl.sym.owner;
			if (utils.hasModifier(pmethodDecl.mods, Modifiers.MODEL) && (pmethodDecl.mods.flags & Flags.SYNTHETIC) != 0) {
				return convertMethodBodyNoInitModel(pmethodDecl, pclassDecl);
			}
			feasibilityCheckCount = 0;
			this.methodDecl = pmethodDecl;
			this.classDecl = pclassDecl != null ? pclassDecl : utils.getOwner(methodDecl);
			this.initialStatements = new ListBuffer<JCStatement>();
			ListBuffer<JCStatement> outerFinalizeStats = new ListBuffer<JCStatement>();
			boolean isConstructor = methodDecl.sym.isConstructor();
			oldStatements = initialStatements;
			currentStatements = initialStatements;

			initialize2(0L);
			{ // Type relationships for generic type parameters and their bounds
				for (JCTypeParameter tp : classDecl.getTypeParameters()) {
					for (JCExpression bound : tp.getBounds()) {
						JCIdent id = M.Ident(tp.name);
						id.sym = tp.type.tsym;
						id.type = tp.type;
						JmlMethodInvocation t1 = M.at(tp.pos).JmlMethodInvocation(typelcKind, id);
						t1.type = jmltypes.TYPE;
						t1.kind = typelcKind;
						JmlMethodInvocation t2 = M.at(bound.pos).JmlMethodInvocation(typelcKind, copy(bound));
						t2.type = jmltypes.TYPE;
						t1.kind = typelcKind;
						JCExpression e = M.at(tp).JmlBinary(subtypeofKind, t1, t2);
						e.type = syms.booleanType;
						e = convertJML(e);
						addAssume(bound, Label.IMPLICIT_ASSUME, e);
					}
				}
			}

			if ((infer || esc)) {
				// THIS is an id that is a proxy for the this object on which a method is
				// called;
				// we need to distinguish it from uses of 'this' in the text
				// FIXME - should make this NonNull
				this.explicitThisId = makeThisId(classDecl.pos, classDecl.sym);
				this.currentEnv.currentReceiver = this.explicitThisId;
			} else { // rac
				// For RAC we use the actual 'this' FIXME - not sure about this design - perhaps
				// just need to be cautious about what is translated and what is not
				this.explicitThisId = treeutils.makeIdent(classDecl.pos, classDecl.thisSymbol);
				this.currentEnv.currentReceiver = this.explicitThisId;
			}

			// Declare the alloc and isAlloc fields
			if (allocSym == null) {
				allocSym = treeutils.makeVarSymbol(0, names.fromString(Strings.allocName), syms.intType, classDecl.pos);
				allocSym.owner = syms.objectType.tsym; // classDecl.sym;
				isAllocSym = treeutils.makeVarSymbol(0, names.fromString(Strings.isAllocName), syms.booleanType,
						classDecl.pos);
				;
				isAllocSym.owner = syms.objectType.tsym; // classDecl.sym;
			}

			if ((infer || esc) && (isConstructor || !utils.isJMLStatic(methodDecl.sym))) {
				addStat(comment(methodDecl, "Declaration of THIS", null));
				currentStatements = initialStatements; // FIXME - an unnecessary assignment I think

				addStat(treeutils.makeVariableDecl(names.fromString(Strings.THIS), currentEnv.currentReceiver.type, null,
						pmethodDecl.pos));
				if (!utils.isJavaOrJmlPrimitiveType(currentEnv.currentReceiver.type)) {
					// assume 'this' is non-null and assume its type
					JCExpression e = treeutils.makeNeqObject(methodDecl.pos, currentEnv.currentReceiver, treeutils.nullLit);
					addAssume(methodDecl, Label.IMPLICIT_ASSUME, e);
					if (isConstructor)
						addAssume(classDecl, Label.IMPLICIT_ASSUME,
								treeutils.makeDynamicTypeEquality(classDecl, currentEnv.currentReceiver, classDecl.type));
					else
						addAssume(classDecl, Label.IMPLICIT_ASSUME,
								treeutils.makeDynamicTypeInEquality(classDecl, currentEnv.currentReceiver, classDecl.type));

					if (!boogie) {
						// Assume when the 'this' object was allocated.
						// Anything already allocated has a alloc value <= 0
						// If this is a constructor, then the alloc value of 'this' is set > 0;
						// otherwise the alloc value of 'this' is 0
						JCExpression fa = M.at(methodDecl.pos).Select(currentEnv.currentReceiver, allocSym);
						fa = treeutils.makeBinary(methodDecl, JCTree.Tag.EQ, fa, treeutils.makeIntLiteral(methodDecl,
								enclosingClass.isEnum() ? 0 : isConstructor ? 1 : 0));
						addStat(treeutils.makeAssume(methodDecl, Label.IMPLICIT_ASSUME, fa));
						// FIXME - the above setting for enums very likely has to be fixed.
					}
				}
			}

            // For esc we are tranlating the method into a block, but
            // for boogie (and rac) there is a method signature that has the
            // formal declarations
            if (esc && !boogie)
                addFormals(initialStatements);

			// Declare the result of the method or constructor

			if (isConstructor) {
				addStat(comment(methodDecl, "Declare result of constructor", null));
				JCVariableDecl d = treeutils.makeVarDef(classDecl.type, resultName, methodDecl.sym, methodDecl.pos);
				d.init = currentEnv.currentReceiver;
				resultSym = d.sym;
				initialStatements.add(d);
			} else if (methodDecl.restype.type.getTag() != TypeTag.VOID) {
				addStat(comment(methodDecl, "Declare result of method", null));
				// The compiler complains that the result variable might not be
				// initialized on every path, even in programs in which it appears
				// obvious that it is. So we initialize it here to a null-like value.
				JCVariableDecl d;
				if (rac) {
					d = treeutils.makeVarDef(methodDecl.restype.type, resultName, methodDecl.sym,
							treeutils.makeZeroEquivalentLit(methodDecl.pos, methodDecl.restype.type));
				} else {
					d = treeutils.makeVarDef(methodDecl.restype.type, resultName, methodDecl.sym, methodDecl.pos);
				}
				resultSym = d.sym;
				initialStatements.add(d);
			} else {
				addStat(comment(methodDecl, "No result declaration - method is void", null));
				resultSym = null;
			}
			resultExpr = resultSym == null ? null : treeutils.makeIdent(methodDecl.pos, resultSym);
			// resultSym and resultExpr (a JCIdent) are now defined

			// Declare the heap counter
			addStat(comment(methodDecl, "Heap value and allocation fields", null));
			if ((infer || esc) && heapSym == null) {
				JCVariableDecl d = treeutils.makeStaticVarDef(syms.intType, heapVarName, enclosingMethod, // classDecl.sym,
						treeutils.makeIntLiteral(0, 0));
				heapSym = d.sym;
				initialStatements.add(d);
			}

			boolean callingSuper = false;
			boolean callingThis = false;
			Iterator<JCStatement> iter = null;
			if (methodDecl.body != null) {
				iter = methodDecl.body.stats.iterator();
				if (iter.hasNext()) {
					JCStatement st = methodDecl.body.stats.get(0);
					if (st instanceof JCExpressionStatement
							&& ((JCExpressionStatement) st).expr instanceof JCMethodInvocation) {
						JCMethodInvocation mi = (JCMethodInvocation) ((JCExpressionStatement) st).expr;
						if (mi.meth instanceof JCIdent) {
							JCIdent id = (JCIdent) mi.meth;
							if (id.name.equals(names._this))
								callingThis = true;
							else if (id.name.equals(names._super))
								callingSuper = true;
						}
					}
				}
			}

			if ((infer || esc) && (isConstructor || !utils.isJMLStatic(methodDecl.sym))) {
//                addStat(comment(methodDecl,"Declaration of THIS",null));
				currentStatements = initialStatements; // FIXME - an unnecessary assignment I think

//                addStat(treeutils.makeVariableDecl(names.fromString(Strings.THIS), currentEnv.currentReceiver.type, null, pmethodDecl.pos));
//                if (!utils.isPrimitiveType(currentEnv.currentReceiver.type)) {
//                    // assume 'this' is non-null and assume its type
//                    JCExpression e = treeutils.makeNeqObject(methodDecl.pos,currentEnv.currentReceiver,treeutils.nullLit);
//                    addAssume(methodDecl,Label.IMPLICIT_ASSUME,e);
//                    addAssume(classDecl,Label.IMPLICIT_ASSUME,treeutils.makeDynamicTypeInEquality(classDecl,currentEnv.currentReceiver,classDecl.type));
//
//                    // Assume when the 'this' object was allocated. 
//                    // Anything already allocated has a alloc value <= 0
//                    // If this is a constructor, then the alloc value of 'this' is set > 0; otherwise the alloc value of 'this' is 0
//                    JCExpression fa = M.at(methodDecl.pos).Select(currentEnv.currentReceiver, allocSym);
//                    fa = treeutils.makeBinary(methodDecl,JCTree.Tag.EQ, fa, 
//                            treeutils.makeIntLiteral(methodDecl, enclosingClass.isEnum() ? 0 : isConstructor ? ++allocCounter : 0));
//                    addStat(treeutils.makeAssume(methodDecl, Label.IMPLICIT_ASSUME, fa ));
//                    // FIXME - the above setting for enums very likely has to be fixed.
//                }
				if (callingSuper && iter != null && iter.hasNext()) {
					if (utils.isExtensionValueType(methodDecl.sym.owner.type)) {
						iter.next(); // Don't do superclass
						callingThis = callingSuper = false;
					}
				}
			}
			LabelProperties lp = new LabelProperties();
			// FIXME - use recordLabel?
			lp.allocCounter = 0;
			lp.heapCount = heapCount;
			lp.name = attr.preLabel;
			lp.labelEnv = currentEnv.newEnvCopy();
			lp.labelEnv.stateLabel = lp.name;
			labelPropertiesStore.put(attr.preLabel, lp);
			JmlLabeledStatement mark = M.JmlLabeledStatement(attr.preLabel, null, null);
			oldStatements = mark.extraStatements;
			undoLabels = true;

			if (isConstructor && rac) {
				ListBuffer<JCStatement> check = pushBlock();
				if (callingThis || callingSuper) {
					addStat(copy(iter.next()));
				}
				JCBlock bl = popBlock(methodDecl, check);

				//System.out.println("ADD PRE CONDITIONS");
				addPreConditions(initialStatements, collector, divergesExpressions);
				allocCounter = 2;
                //System.out.println("HANDLE FRAME CONDITIONS");
				handleFrameConditions(methodDecl, initialStatements);
				addStat(mark);
				markLocation(attr.preLabel, initialStatements, mark);
				addFeasibility(methodDecl, initialStatements);
				
				// FIXME - need to fix RAC So it can check preconditions etc. of a constructor
				ListBuffer<JCStatement> checkZ = pushBlock();
				JCBlock newMainBody = null;
				try {
					while (iter.hasNext()) {
						convert(iter.next());
					}
				} finally {
				    // FIXME - don't know whether execution is still alive here
	                // addFeasibilityCheck(methodDecl.body, currentStatements, Strings.feas_return, "at fall-through return");
					newMainBody = popBlock(methodDecl.body == null ? methodDecl : methodDecl.body, checkZ);
				}

				// The outerTryStatement just has a finally clause in which the
				// postconditions and exceptional postconditions are checked.
				JCCatch c;
				{
					// global catch block
					JCVariableDecl ex = treeutils.makeVarDef(syms.exceptionType, names.fromString("_JML__ex"),
							methodDecl.sym, methodDecl.pos);
					ListBuffer<JCStatement> check2 = pushBlock();
					addStat(treeutils.makeAssignStat(methodDecl.pos, treeutils.makeIdent(methodDecl.pos, exceptionSym),
							treeutils.makeIdent(methodDecl.pos, ex.sym)));
					addStat(M.at(methodDecl.pos).Throw(treeutils.makeIdent(methodDecl.pos, ex.sym)));
					JCBlock bbl = popBlock(methodDecl, check2);
					c = M.at(methodDecl.pos).Catch(ex, bbl);
				}
                //System.out.println("ADD POST CONDITIONS-S");
				if (!isRefiningBranch)
					addPostConditions(outerFinalizeStats);
				else
					isRefiningBranch = false;
                //System.out.println("DONE POST CONDITIONS-S");
				JCTry outerTryStatement = M.at(methodDecl).Try(newMainBody,
						esc ? List.<JCCatch>nil() : List.<JCCatch>of(c), M.Block(0, outerFinalizeStats.toList()));

				initialStatements.add(outerTryStatement);
				bl.stats = bl.stats.appendList(initialStatements);
				return M.at(methodDecl.body).Block(methodDecl.body.flags, bl.stats);
			}

			// The form of the translated method is this:
			// assume invariants and preconditions, assigning precondition
			// values to designated identifiers [initialStatements]
			// try {
			// translation of all the method body statements [currentStatements, after the
			// pushBlock]
			// } finally {
			// assert all the postconditions, suitably guarded by the
			// values of the preconditions in each specification case
			// (which is why they have to be declared before the try
			// statement) [outerFinalizeStatements]
			// }
			// Values of the result, any exception active, and the termination
			// position (location of last return or throw statement) are tracked

			// We create this first, so that it is the first one in the list.
			// We'll add the block into the right spot later.
			// Other checks will be created during addPrePostConditions
            //System.out.println("ADD PRE CONDITIONS");
			ListBuffer<JCStatement> check = pushBlock(); // FIXME - should we have a try block?
			addPreConditions(initialStatements, collector, divergesExpressions);
            allocCounter = 2;
            //System.out.println("HANDLE FRAME CONDITIONS");
			handleFrameConditions(methodDecl, initialStatements);
			initialStatements.add(mark);
			markLocation(attr.preLabel, initialStatements, mark);
			addFeasibility(methodDecl, initialStatements);

			if (esc && isConstructor && !callingThis) {
				boolean pv = checkAccessEnabled;
				checkAccessEnabled = false; // Not sure about this - all references are to instance fieldsd, no?
				try {
					addInstanceInitialization(methodDecl.sym);
				} finally {
					checkAccessEnabled = pv;
				}
			}
			// mapSymbols contains at least the old symbols declared in
			// specification preconditions. If a spec is used in the method body,
			// (called recursively), old symbols will get a new mapping.
			// So we save the current state and restore it before we translate the
			// postconditions.
			Map<Symbol, Symbol> savedMapSymbols = pushMapSymbols();

            ListBuffer<JCStatement> check3 = pushBlock();
            addFeasibilityCheck(methodDecl, currentStatements, Strings.feas_pre, Strings.preconditionFeasCheckDescription);
            addFeasibilityCheck(methodDecl, currentStatements, Strings.feas_preOnly, Strings.preconditionFeasCheckDescription);
            JCStatement preconditionAssumeCheck = popBlock(methodDecl, check3);
            addStat(initialStatements, preconditionAssumeCheck);

            addStat(comment(methodDecl, "Method Body", null));

			if (methodDecl.body != null) {
				continuation = Continuation.CONTINUE;
		        if (feasibilityContains(Strings.feas_preOnly) && !feasibilityContains("debug")) {
					JCStatement s = M.at(methodDecl).JmlExpressionStatement(ReachableStatement.haltID,
							ReachableStatement.haltClause, Label.IMPLICIT_ASSUME, null);
					convert(s);
					continuation = Continuation.HALT;
				}
				if (callingThis || callingSuper) {
					convert(iter.next());
				} else if (isConstructor && (esc || infer)) {
					// FIXME - need assumptions from default super constructor
				}
				if (isConstructor && (infer || esc) && !callingThis) {
					boolean pv = checkAccessEnabled;
					checkAccessEnabled = false;
					try {
						addInstanceInitializationPass2();
					} finally {
						checkAccessEnabled = pv;
					}
				}
				while (continuation == Continuation.CONTINUE && iter.hasNext()) {
					JCStatement s = iter.next();
					convert(s);
				} // TODO: Warn if continuation is EXIT and there are remaining statements?
                // FIXME - don't know whether execution is still alive here
				// addAssumeCheck(methodDecl.body, currentStatements, Strings.feas_return, "at fall-through return");
				continuation = Continuation.CONTINUE;
			}
			JCBlock newMainBody = popBlock(methodDecl.body == null ? methodDecl : methodDecl.body, check);

			if (esc && feasibilityContains(Strings.feas_exit)) {
				String vv = JmlOption.value(context, JmlOption.SPLIT);
				if (vv == null || vv.isEmpty() || vv.endsWith("->")) {
					addFeasibilityCheck(methodDecl, outerFinalizeStats, Strings.atExitFeasCheckDescription);
				}
			}

			// The outerTryStatement just has a finally clause in which the
			// postconditions and exceptional postconditions are checked.
			popMapSymbols(savedMapSymbols);
			outerFinalizeStats.add(comment(methodDecl, "Check Postconditions", null));
            //System.out.println("ADD POST CONDITIONS");
			if (!isRefiningBranch)
				addPostConditions(outerFinalizeStats);
			else
				isRefiningBranch = false;
            //System.out.println("DONE POST CONDITIONS");
			axiomBlock = null;

			JCCatch c;
			{
				// global catch block
				JCVariableDecl ex = treeutils.makeVarDef(syms.exceptionType, names.fromString("_JML__ex"),
						methodDecl.sym, methodDecl.pos);
				ListBuffer<JCStatement> check4 = pushBlock();
				addStat(treeutils.makeAssignStat(methodDecl.pos, treeutils.makeIdent(methodDecl.pos, exceptionSym),
						treeutils.makeIdent(methodDecl.pos, ex.sym)));
				addStat(M.at(methodDecl.pos).Throw(treeutils.makeIdent(methodDecl.pos, ex.sym)));
				JCBlock bl = popBlock(methodDecl, check4);
				c = M.at(methodDecl.pos).Catch(ex, bl);
			}
			JCTry outerTryStatement = M.at(methodDecl).Try(newMainBody,
					(infer || esc) ? List.<JCCatch>nil() : List.<JCCatch>of(c),
					M.Block(0, outerFinalizeStats.toList()));

			// This block is to create the try-catch block for converting PreconditionEntry
			// to Precondition
			if (rac && JmlOption.isOption(context, JmlOption.RAC_PRECONDITION_ENTRY)) {
				// precondition catch block
				JCBlock tryBlock = M.at(methodDecl).Block(0, List.<JCStatement>of(outerTryStatement));
				ClassSymbol preex = ClassReader.instance(context)
						.enterClass(names.fromString("org.jmlspecs.runtime.JmlAssertionError$PreconditionEntry"));
				JCVariableDecl ex = treeutils.makeVarDef(preex.type, names.fromString("_JML__ex"), methodDecl.sym,
						methodDecl.pos);
				ListBuffer<JCStatement> check5 = pushBlock();
				JCMethodInvocation m = treeutils.makeUtilsMethodCall(methodDecl.pos, "convertPrecondition",
						treeutils.makeIdent(methodDecl.pos, ex.sym));
				addStat(M.at(methodDecl.pos).Exec(m));
				JCBlock catchBlock = popBlock(methodDecl, check5);
				JCCatch cc = M.at(methodDecl.pos).Catch(ex, catchBlock);
				JCTry preconditionTryStatement = M.at(methodDecl).Try(tryBlock, List.<JCCatch>of(cc), null);
				outerTryStatement = preconditionTryStatement;
			}

			initialStatements.add(outerTryStatement);
			return M.at(methodDecl).Block(0, initialStatements.toList());
		} catch (JmlNotImplementedException e) {
			throw e;
		} catch (JmlInternalAbort e) {
			return null;
		} catch (Exception e) {
			String message = e.getMessage();
			if (message == null)
				message = "Internal exception: " + e.getClass();
			StringWriter sw = new StringWriter();
			e.printStackTrace(new PrintWriter(sw));
			message = message + JmlTree.eol + sw.toString();
			Log.instance(context).error("jml.internal.notsobad", message);
			return null;
		} finally {
			if (continuation != Continuation.CONTINUE) {
			    //System.out.println("ADDING FINAL HALT");
				addStat(M.at(methodDecl).JmlExpressionStatement(ReachableStatement.haltID,
						ReachableStatement.haltClause, null, null));
			}
			if (undoLabels) {
				labelPropertiesStore.pop(attr.preLabel);
			}

			this.feasibilityCheckCount = prevAssumeCheckCount;
			this.methodDecl = prevMethodDecl;
			this.classDecl = prevClass;
			this.initialStatements = prevStats;
			this.explicitThisId = savedExplicitThisId;
			//this.currentEnv.currentReceiver = savedThisExpr;
			this.resultSym = savedResultSym;
			this.resultExpr = savedResultExpr;
			this.exceptionSym = savedExceptionSym;
			this.terminationSym = savedTerminationSym;
			this.oldStatements = savedOldStatements;
			this.currentStatements = null;
			this.paramActuals_ = savedParamActuals;
			log.useSource(prevSource);
			this.freshnessReferenceCount = savedFreshnessReferenceCount;
			this.completedInvariants = savedCompletedInvariants;
			this.inProcessInvariants = savedInProcessInvariants;
			this.enclosingMethod = savedEnclosingMethod;
			this.enclosingClass = savedEnclosingClass;
			this.alreadyDiscoveredFields = savedAlreadyDiscoveredFields;
			this.discoveredFields = savedDiscoveredFields;
			this.allocCounter = savedAllocCounter;
			this.nestedCallLocation = savedNestedCallLocation;
			this.activeExceptions = savedActiveExceptions;
			this.divergesExpressions = savedDivergesExpressions;
			this.currentEnv = this.currentEnv.popEnv();
			JmlOptions.instance(context).popOptions();
		}
	}

	Map<Symbol, Symbol> pushMapSymbols() {
		return new HashMap<>(mapSymbols);
	}

	void popMapSymbols(Map<Symbol, Symbol> savedMapSymbols) {
		mapSymbols.clear();
		mapSymbols.putAll(savedMapSymbols);
		savedMapSymbols.clear();
	}

	/** Internal method to do the method body conversion */
	protected JCBlock convertMethodBodyNoInitModel(JmlMethodDecl pmethodDecl, JmlClassDecl pclassDecl) {
		feasibilityCheckCount = 0;
		this.methodDecl = pmethodDecl;
		this.classDecl = pclassDecl != null ? pclassDecl : utils.getOwner(methodDecl);
		this.initialStatements = new ListBuffer<JCStatement>();
		ListBuffer<JCStatement> outerFinalizeStats = new ListBuffer<JCStatement>();
		boolean isConstructor = methodDecl.sym.isConstructor();
		oldStatements = initialStatements;
		currentStatements = initialStatements;

		if (methodDecl.restype.type.getTag() != TypeTag.VOID) {
			// The compiler complains that the result variable might not be
			// initialized on every path, even in programs in which it appears
			// obvious that it is. So we initialize it here to a null-like value.
			JCVariableDecl d = treeutils.makeVarDef(methodDecl.restype.type, resultName, methodDecl.sym,
					treeutils.makeZeroEquivalentLit(methodDecl.pos, methodDecl.restype.type));
			resultSym = d.sym;
			initialStatements.add(d);
		}
		resultExpr = resultSym == null ? null : treeutils.makeIdent(methodDecl.pos, resultSym);

		initialize2(0L);

		ListBuffer<JCStatement> check = pushBlock(); // FIXME - should we have a try block

		addStat(comment(methodDecl, "Method Body", null));
		if (methodDecl.body != null) {
			Iterator<JCStatement> iter = methodDecl.body.stats.iterator();
			while (iter.hasNext()) {
				scan(iter.next());
			}
            // FIXME - don't know whether execution is still alive here
			// addAssumeCheck(methodDecl.body, currentStatements, Strings.feas_return, "at fall-through return");
		}
		JCBlock newMainBody = popBlock(methodDecl.body == null ? methodDecl : methodDecl.body, check);

		JCCatch c;
		{
			// global catch block
			JCVariableDecl ex = treeutils.makeVarDef(syms.exceptionType, names.fromString("_JML__ex"), methodDecl.sym,
					methodDecl.pos);
			ListBuffer<JCStatement> check6 = pushBlock();
			addStat(treeutils.makeAssignStat(methodDecl.pos, treeutils.makeIdent(methodDecl.pos, exceptionSym),
					treeutils.makeIdent(methodDecl.pos, ex.sym)));
			addStat(M.at(methodDecl.pos).Throw(treeutils.makeIdent(methodDecl.pos, ex.sym)));
			JCBlock bl = popBlock(methodDecl, check6);
			c = M.at(methodDecl.pos).Catch(ex, bl);
		}
		JCTry outerTryStatement = M.at(methodDecl).Try(newMainBody, esc ? List.<JCCatch>nil() : List.<JCCatch>of(c),
				M.Block(0, outerFinalizeStats.toList()));

		initialStatements.add(outerTryStatement);
		return M.at(methodDecl).Block(0, initialStatements.toList());
	}

	// Generic node translation methods. Most of these may add statements to
	// 'currentStatements'.

	// DESIGN NOTE: These routines expect all visit nodes to return a value in
	// 'result' and (for JCExpression derivatives) in 'eresult'. However, in
	// all modes, there may be side-effects of other statements
	// or declarations being produced; in addition, the class of the returned
	// node may be different than that of the argument, because of the
	// rac or esc translation.

	/**
	 * (Public API) Converts a non-expression AST, returning the converted tree;
	 * this may be called externally on ClassDecl and CompilationUnit trees, but
	 * should not be called outside of JmlAssertionAdder on trees lower in the AST.
	 * In purecopy mode, T can be any JCTree derived type; but otherwise, it may
	 * only be either JCTree or JCExpression (possibly JCStatement)
	 */
	@SuppressWarnings("unchecked")
	public /* @nullable */ <T extends JCTree> T convert(/* @nullable */ T tree) {
		if (tree == null) {
			result = null;
			return null;
		}
		scan(tree);

		saveMapping(tree, result);
		return (T) result;
	}
	
	/**
	 * Returns a translation of a list of tree, possibly pushing additional
	 * statements onto 'currentStatements'; the same restrictions on T apply as
	 * above.
	 */
	public /* @nullable */ <T extends JCTree> List<T> convert(/* @nullable */ List<T> trees) {
		if (trees == null)
			return null;
		ListBuffer<T> newlist = new ListBuffer<T>();
		for (T t : trees) {
			T tt = convert(t);
			if (tt != null)
				newlist.add(tt);
		}
		return newlist.toList();
	}

	/**
	 * Returns a translation of a list of tree, possibly pushing additional
	 * statements onto 'currentStatements'; the same restrictions on T apply as
	 * above.
	 */
	public <T extends JCTree> java.util.List<T> convert(java.util.List<T> trees) { // FIXME - should have /*@nullable*/
																					// on argument and result as in the
																					// previous method declaration
		if (trees == null)
			return null;
		java.util.List<T> newlist = new LinkedList<T>();
		for (T t : trees) {
			newlist.add(convert(t));
		}
		return newlist;
	}

	protected /* @nullable */ JCExpression convertAssignable(/* @nullable */ JCExpression tree, JCExpression receiver,
			boolean isInJML, JavaFileObject itemSource) {
		JavaFileObject prev = log.useSource(itemSource);
		try {
			return convertAssignable(tree, receiver, isInJML);
		} finally {
			log.useSource(prev);
		}
	}

	// FIXME all calls to convertAssignable should use a spcific JavaFileObject

	/**
	 * Returns a translation of an expression, possibly pushing additional
	 * statements onto 'currentStatements'
	 */
	protected /* @nullable */ JCExpression convertAssignable(/* @nullable */ JCExpression tree, JCExpression receiver,
			boolean isInJML) {
		// Normally this method is called on left-values, in which case tree is never
		// just 'this'; if 'this' appears in the
		// expression it is as a receiver and is replaced by the receiver.
		// But it also called to determine accessiblity, in which case it can be called
		// on normal expressions,
		// and 'this' can occur as a normal expression. So we treat it as a special
		// case.
		if (tree instanceof JCIdent && ((JCIdent) tree).name == names._this)
			return tree;

		eresult = null; // Just so it is initialized in case assignment is forgotten
		boolean savedT = translatingJML;
		boolean savedS = splitExpressions;
		boolean savedA = convertingAssignable;
		JCExpression savedC = condition;
		JCExpression savedThis = currentEnv.currentReceiver;
		boolean pv = checkAccessEnabled;
		try {
			translatingJML = isInJML;
			condition = treeutils.trueLit;
			splitExpressions = false;
			convertingAssignable = true;
			currentEnv.currentReceiver = receiver;
			checkAccessEnabled = false;
			if (tree != null) {
				super.scan(tree);
				if (rac && eresult != null && eresult.type != null && eresult.type != Type.noType
						&& jmltypes.isJmlType(eresult.type)) {
					if (!(eresult.type instanceof JmlType)) {
						System.out.println("BAD CONVERSION " + tree + " " + receiver + " " + eresult.type + " "
								+ eresult.type.getClass());
						Utils.dumpStack();
					}
					eresult.type = jmltypes.repSym((JmlType) eresult.type).type;
				}
				saveMapping(tree, eresult);
			}
		} finally {
			translatingJML = savedT;
			splitExpressions = savedS;
			convertingAssignable = savedA;
			condition = savedC;
			currentEnv.currentReceiver = savedThis;
			checkAccessEnabled = pv;
		}
		return eresult;
	}

	/**
	 * Returns a translation of an expression, possibly pushing additional
	 * statements onto 'currentStatements'
	 */
	public /* @nullable */ JCExpression convertExpr(/* @nullable */ JCExpression tree) {
		eresult = null; // Just so it is initialized in case assignment is forgotten
		if (tree != null) {
			super.scan(tree);
			if (rac && eresult != null && eresult.type != null && jmltypes.isJmlType(eresult.type)) {
				eresult.type = jmltypes.repSym((JmlType) eresult.type).type;
			}
			saveMapping(tree, eresult);
		}
		return eresult;
	}

	/**
	 * Returns a translation of a list of expression, possibly pushing additional
	 * statements onto 'currentStatements'
	 */
	public /* @nullable */ List<JCExpression> convertExprList(/* @nullable */ List<? extends JCExpression> trees) {
		if (trees == null)
			return null;
		ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
		for (JCExpression t : trees) {
			scan(t);
			if (eresult == null)
				eresult = t;
			boolean coerce = true;
			if (coerce && eresult.type != t.type) {
				eresult = addImplicitConversion(t.pos(), t.type, eresult);
			}
			newlist.add(eresult);
			saveMapping(t, eresult);
		}
		return newlist.toList();
	}

	/**
	 * Does a pure copy of the tree.
	 */
	public /* @nullable */ <T extends JCTree> T copy(/* @nullable */ T tree) {
		return copier.copy(tree,null);
	}

	/** Does a pure copy of the list of trees */
	public <T extends JCTree> List<T> copy(List<T> trees) {
		return copier.copy(trees,null);
	}

	/** Does a pure copy of the list of trees */
	public <T extends JCTree> ListBuffer<T> copy(ListBuffer<T> trees) {
		return copier.copy(trees,null);
	}

	/** Does a pure copy of the list of trees */
	public <T extends JCTree> java.util.List<T> copy(java.util.List<T> trees) {
		return copier.copy(trees,null);
	}

	public void pushArithMode() {
        currentEnv = currentEnv.pushEnvCopy();
		Arithmetic.Math.instance(context).rac = rac; // FIXME - HACK FOR NOW
		currentEnv.arithmeticMode = Arithmetic.Math.instance(context)
				.defaultArithmeticMode(methodDecl != null ? methodDecl.sym : classDecl.sym, true);
	}

	public void popArithMode() {
		currentEnv = currentEnv.popEnv();
	}

	/**
	 * Translates an AST as JML - that is, assuming that the AST is pure; this call
	 * is used to switch to the translatingJML mode, setting the condition and
	 * isPostcondition to the given values, restoring isPostcondition and
	 * translatingJML upon return. When isPostcondition is true, then parameter
	 * variables are mapped to the pre-state of the method, rather than to the
	 * current state.
	 */
	public /* @nullable */ JCExpression convertJML(/* @nullable */ JCTree that, JCExpression condition,
			boolean isPostcondition) {
		if (that == null) return null;
		boolean savedp = this.isPostcondition;
		boolean savedt = this.translatingJML;
		boolean savedSplit = this.splitExpressions;
		boolean savedCA = this.checkAccessEnabled;
		currentEnv = currentEnv.pushEnvCopy();
		if (!translatingJML) currentEnv.arithmeticMode = Arithmetic.Math.instance(context)
		                        .defaultArithmeticMode(methodDecl != null ? methodDecl.sym : classDecl.sym, true);
		JCExpression savedc = this.condition;
		try {
			if (!translatingJML) { // FIXME - not sure about this translatingJML guard
				if (condition == null)
					condition = treeutils.trueLit;
			}
			this.isPostcondition = isPostcondition;
			this.condition = condition;
			this.translatingJML = true;
//            this.splitExpressions = rac || esc;
			this.checkAccessEnabled = false;
			if (that instanceof JCExpression) {
				return convertExpr((JCExpression) that);
			} else {
				convert(that);
				return null;
			}
		} finally {
			this.isPostcondition = savedp;
			this.translatingJML = savedt;
			this.splitExpressions = savedSplit;
			this.condition = savedc;
			this.currentEnv = this.currentEnv.popEnv();
			this.checkAccessEnabled = savedCA;
		}
	}

	/** Begins JML scanning for a non-postcondition */
	public /* @nullable */ JCExpression convertJML(/* @nullable */ JCExpression that) {
		return convertJML(that, treeutils.trueLit, false);
	}

	public /* @nullable */ JCExpression convertJML(/* @nullable */ JCExpression that, TranslationEnv trenv) {
		var savedThis = currentEnv.currentReceiver;
		var savedEnv = currentEnv;
		currentEnv = trenv;
		try {
			return convertJML(that, treeutils.trueLit, true);
		} finally {
            currentEnv = savedEnv;
			currentEnv.currentReceiver = savedThis;
		}
	}

	/**
	 * Applies convertJML to a list of nno-postcondition expressions, returning the
	 * new list.
	 */
	public /* @nullable */ List<JCExpression> convertJML(/* @nullable */ List<JCExpression> trees) {
		if (trees == null)
			return null;
		else {
			ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
			for (JCExpression tree : trees) {
				convertJML(tree, treeutils.trueLit, false);
				newlist.add(eresult);
			}
			return newlist.toList();
		}
	}

	public /* @nullable */ JCExpression convertNoSplit(JCExpression expr) {
		boolean saved = splitExpressions;
		try {
			splitExpressions = false;
			return convertJML(expr);
		} finally {
			splitExpressions = saved;
		}
	}

	public /* @nullable */ JCExpression convertNoSplit(JCExpression that, JCExpression condition,
			boolean isPostcondition) {
		if (that == null)
			return null;
		boolean savedp = this.isPostcondition;
		boolean savedt = this.translatingJML;
		boolean savedSplit = this.splitExpressions;
		boolean savedCA = this.checkAccessEnabled;
		this.currentEnv = this.currentEnv.pushEnvCopy();
		JCExpression savedc = this.condition;
		try {
			if (!translatingJML) { // FIXME - not sure about this translatingJML guard
				Arithmetic.Math.instance(context).rac = rac; // FIXME - HACK FOR NOW
				currentEnv.arithmeticMode = Arithmetic.Math.instance(context)
						.defaultArithmeticMode(methodDecl != null ? methodDecl.sym : classDecl.sym, true);
				if (condition == null)
					condition = treeutils.trueLit;
			}
			this.isPostcondition = isPostcondition;
			this.condition = condition;
			this.translatingJML = true;
			this.splitExpressions = false;
			this.checkAccessEnabled = false;
			return convertExpr(that);
		} finally {
			this.isPostcondition = savedp;
			this.translatingJML = savedt;
			this.splitExpressions = savedSplit;
			this.condition = savedc;
			this.currentEnv = this.currentEnv.popEnv();
			this.checkAccessEnabled = savedCA;
		}
	}

	private Map<Symbol, Symbol> mapSymbols = new HashMap<Symbol, Symbol>();

	@SuppressWarnings("unchecked")
	protected /* @non_null */ <T extends Symbol> T convertSymbol(T sym) {
		Symbol s = mapSymbols.get(sym);
		return s == null ? sym : (T) s;
	}

	protected <T extends Symbol> void putSymbol(T sym, T newsym) {
		mapSymbols.put(sym, newsym);
	}

	protected Type convertType(Type origtype) {
		// FIXME - need to walk the type to create a new, substituted type
		if (origtype instanceof Type.TypeVar) {
			Type ntype = typeActuals.get(origtype.tsym);
			if (ntype != null)
				return ntype;
			ntype = typevarMapping.get(origtype.tsym);
			if (ntype != null)
				return ntype;
		}
		return origtype;
	}

	/**
	 * Translates a block, but without adding the block to the statement list; any
	 * side-effect statements are placed within the new block.
	 */
	@SuppressWarnings("finally")
	protected /* @nullable */ JCBlock convertBlock(/* @nullable */ JCBlock block) {
		if (block == null)
			return null;
		ListBuffer<JCStatement> check = pushBlock();
		try {
			scan(block.stats);
		} finally {
			return popBlock(block.flags, block, check);
		}
	}

	/**
	 * Translates a list of statements, returning a block containing the
	 * translations
	 */
	@SuppressWarnings("finally")
	protected JCBlock convertIntoBlock(DiagnosticPosition pos, List<JCStatement> stats) {
		ListBuffer<JCStatement> check = pushBlock();
		try {
			scan(stats);
		} finally {
			return popBlock(pos, check);
		}
	}

	/**
	 * Translates one statement, returning a block containing the translation
	 * (including any statements it spawns); if the statement is a block, then the
	 * block's statements are translated, so there is not an excess nested block.
	 */
	@SuppressWarnings("finally")
	protected JCBlock convertIntoBlock(DiagnosticPosition pos, JCStatement stat) {
		ListBuffer<JCStatement> check = pushBlock();
		try {
			if (stat instanceof JCBlock)
				scan(((JCBlock) stat).stats);
			else
				scan(stat);
		} catch (Exception e) {
			e.printStackTrace(System.out);
			throw e;
		} finally {
			return popBlock(pos, check);
		}
	}

	/**
	 * Start collecting statements for a new block; push currentStatements onto a
	 * stack for later use
	 */
	protected ListBuffer<JCStatement> pushBlock() {
		return pushBlock(new ListBuffer<JCStatement>());
	}

	protected ListBuffer<JCStatement> pushBlock(ListBuffer<JCStatement> newbuf) {
		ListBuffer<JCStatement> temp = currentStatements;
		statementStack.add(0, currentStatements);
		currentStatements = newbuf;
		return temp;
	}

	/**
	 * Wrap the active currentStatements as a block (which is returned) and then
	 * resume collecting statements with currentStatements value on the top of the
	 * stack (which is also removed from the stack)
	 */
	protected JCBlock popBlock(DiagnosticPosition pos, ListBuffer<JCStatement> check) {
		return popBlock(0L, pos, check);
	}

	protected JCBlock popBlock(DiagnosticPosition pos) {
		return popBlock(0L, pos, null);
	}

	protected JCBlock popBlock(long flags, DiagnosticPosition pos, ListBuffer<JCStatement> check) {
		JCBlock b = null;
		if (pos != null)
			b = M.at(pos).Block(flags, currentStatements.toList());
		else
			b = M.at(0).Block(flags, currentStatements.toList());
		currentStatements = statementStack.removeFirst();
		if (check != null && check != currentStatements) {
			log.error("jml.internal", "MISMATCHED BLOCKS");
			throw new RuntimeException("MISMATCHED BLOCKS");
		}
		return b;
	}

	/** Pop and ignore the content of currentStatements. */
	protected void popBlock() {
		popBlock(null, null);
	}

	protected LinkedList<ListBuffer<JCStatement>> markBlock() {
		LinkedList<ListBuffer<JCStatement>> temp = new LinkedList<ListBuffer<JCStatement>>();
		temp.addAll(statementStack);
		temp.add(0, currentStatements);
		return temp;
	}

	protected boolean checkBlock(LinkedList<ListBuffer<JCStatement>> temp) {
		Iterator<ListBuffer<JCStatement>> iter = temp.iterator();
		ListBuffer<JCStatement> t = iter.next();
		if (t != currentStatements)
			return false;
		Iterator<ListBuffer<JCStatement>> iter2 = statementStack.iterator();
		while (iter2.hasNext() && iter.hasNext()) {
			if (iter2.next() != iter.next())
				return false;
		}
		return !iter2.hasNext() && !iter.hasNext();
	}

	public JCExpression makeAssertionOptional(JCExpression e) {
		if (rac)
			return e;
		JCIdent id = newTemp(e, syms.booleanType);
		e = treeutils.makeOr(e.getPreferredPosition(), id, e);
		return e;
	}

	/**
	 * JmlAssertionAdder creates temporaries for each subexpression for which a
	 * counterexample value may be wanted; this routine saves such mappings from
	 * original AST (before any translation or copying) to the temporary id. The
	 * original AST is needed because that is the AST that is used when the source
	 * code is traced or when a location is found in the source code editor.
	 * 
	 * @param original
	 * @param ident
	 */
	public void saveMapping(JCTree original, JCTree ident) {
		if (original instanceof JCExpression && localVariables.isEmpty()
				&& exprBiMap.getf(original) == null) {
			exprBiMap.put(original, ident);
		}
	}

	protected void saveMappingOverride(JCTree original, JCTree ident) {
		if (original instanceof JCExpression && localVariables.isEmpty()) {
			exprBiMap.put(original, ident);
		}
	}

	protected JCTree getMapping(JCTree original) {
		return exprBiMap.getf(original);
	}

	/**
	 * Add a statement at the end of the active currentStatements sequence,
	 * returning the argument
	 */
	protected <T extends JCStatement> T addStat(T stat) {
		if (currentStatements != null)
			currentStatements.add(stat);
		else if (classDefs != null)
			classDefs.add(stat);
		else
			log.error(stat.pos, "jml.internal", "No place to add a statement");
		return stat;
	}

	/**
	 * Add a statement at the end of the given buffer of statements, returning the
	 * statement added
	 */
	protected <T extends JCStatement> T addStat(ListBuffer<JCStatement> stats, T stat) {
		stats.add(stat);
		return stat;
	}

	/**
	 * This generates a JmlExpressionStatement comment statement with the given
	 * string as text; the statement is not added to any statement list.
	 */
	protected JmlStatementExpr comment(DiagnosticPosition pos, String s, /* @ nullable */JavaFileObject source) {
		if (s.contains("\n") || s.contains("\r")) {
			s = s.replace("\r\n", " ").replace('\r', ' ').replace('\n', ' ');
		}
		JmlStatementExpr st = M.at(pos).JmlExpressionStatement(commentID, commentClause, null, M.at(pos).Literal(s));
		st.associatedSource = source;
		return st;
	}

	/**
	 * This generates a comment statement whose content is the given JCTree,
	 * pretty-printed; the statement is not added to any statement list
	 */
	public JmlStatementExpr comment(JCTree t) {
		String s = JmlPretty.write(t, false);
		int k = s.indexOf(JmlTree.eol); // No multi-line comments
		if (k == -1)
			k = s.length();
		final int maxlength = 80;
		if (k > maxlength) {
			s = s.substring(0, k) + " ...";
		}
		JavaFileObject source = null;
		if (t instanceof JmlSource)
			source = ((JmlSource) t).source();
		return comment(t, s, source);
	}

	/** Issue an internal error message and throw an exception. */
	public void error(DiagnosticPosition pos, String msg) {
		utils.error(pos, "esc.internal.error", msg);
		throw new JmlInternalError(msg);
	}

	/** Issue an error message. */
	public void error(DiagnosticPosition pos, String key, Object... msg) {
		utils.error(pos, key, msg);
	}

	/** Issue a warning message . */
	public void warning(DiagnosticPosition pos, String key, Object... msg) {
		utils.warning(pos, key, msg);
	}

	// FIXME - this is a hack - fix and document
	// These are used so that we don't send repeated notImplemented messages
	static Set<String> racMessages = new HashSet<String>();
	static Set<String> escMessages = new HashSet<String>();

	/**
	 * Issues a diagnostic message (note) containing the message in the given
	 * exception.
	 */
	protected void notImplemented(String location, JmlNotImplementedException source) {
		notImplemented(location, source, null);
	}

	public void notImplemented(String location, JmlNotImplementedException source, JavaFileObject file) {
		String message = location + source.getMessage();
		String key = source.pos.getPreferredPosition() + message;
		JavaFileObject prev = file == null ? null : log.useSource(file);
		if (rac ? racMessages.add(key) : escMessages.add(key)) {
			utils.note(source.pos, rac ? "rac.not.implemented" : "esc.not.implemented", message);
		}
		if (file != null) log.useSource(prev);
	}

	/**
	 * Issues a diagnostic message (note) containing the given message.
	 */
	public void notImplemented(DiagnosticPosition pos, String message, JavaFileObject file) {
	    String key = pos.getPreferredPosition() + message;
	    if (rac ? !racMessages.add(key) : !escMessages.add(key)) return;
	    JavaFileObject prev = file == null ? null : log.useSource(file);
	    utils.note(pos, rac ? "rac.not.implemented" : "esc.not.implemented", message);
	    if (file != null) log.useSource(prev);
	}

	public void notImplemented(DiagnosticPosition pos, String message) {
		notImplemented(pos, message, null);
	}

	/**
	 * Adds an assertion with the given label and (already translated) expression to
	 * 'currentStatements'. 'codepos' is the position within the code where the
	 * assertion is triggered; log.currentSource() is used as the sourcefile in
	 * which 'codepos' lies. 'associatedSource' and 'associatedPos' are the location
	 * of the specification clause from which this assertion derives, if any. The
	 * args are arguments for the resource key giving the error message
	 * corresponding to the given Label. Returns null if no assertion was added
	 */
	public /* @nullable */ JmlStatementExpr addAssert(boolean trace, DiagnosticPosition codepos, // FIXME _ document
																									// whether nullable
																									// and behavior
			Label label, JCExpression translatedExpr, /* @nullable */ DiagnosticPosition associatedPos,
			/* @nullable */ JavaFileObject associatedSource, /* @nullable */ JCExpression info, Object... args) {

		if (label != Label.FEASIBILITY_CHECK && feasibilityContains(Strings.feas_debug)) {
		    addFeasibilityCheck(translatedExpr, currentStatements, "Extra-Assert");
		}

		boolean isTrue = treeutils.isTrueLit(translatedExpr);
		boolean isFalse = treeutils.isFalseLit(translatedExpr);
		if (isTrue)
			return null; // Literally true - don't even add the statement
		if (nowarns.suppress(log.currentSource(), codepos == null ? Position.NOPOS : codepos.getPreferredPosition(),
				label.toString()))
			return null;
		if (associatedPos != null) {
			if (nowarns.suppress(associatedSource == null ? log.currentSourceFile() : associatedSource,
					associatedPos.getPreferredPosition(), label.toString()))
				return null;
		}
		String assertID = Strings.assertPrefix + (++assertCount);
		if (assertCount == assertCountCheck) Utils.dumpStack("Assertion " + assertID);
		Name assertname = names.fromString(assertID);
		JavaFileObject dsource = log.currentSourceFile();
		JCVariableDecl assertDecl = treeutils.makeVarDef(syms.booleanType, assertname,
				methodDecl == null ? (classDecl == null ? null : classDecl.sym) : methodDecl.sym, translatedExpr);
		assertDecl.mods.flags |= Flags.FINAL;
		assertDecl.sym.flags_field |= Flags.FINAL;
		if (esc || infer) {

			String extra = null;
			for (Object o : args) {
				extra = o == null ? extra : ((extra == null ? "" : (extra + " ")) + utils.abbrev(o.toString()));
			}

			JmlStatementExpr st = treeutils.makeAssert(codepos, label,
					treeutils.makeIdent(translatedExpr.pos, assertDecl.sym));
			st.source = dsource;
			st.associatedPos = associatedPos == null ? Position.NOPOS : associatedPos.getPreferredPosition();
			st.associatedSource = associatedSource;
			st.optionalExpression = info;
			st.id = assertID;
			st.description = extra;
			st.associatedClause = conditionAssociatedClause;
			treeutils.copyEndPosition(st.expression, translatedExpr);
			treeutils.copyEndPosition(st, translatedExpr); // Note that the position of the expression may be that of
															// the associatedPos, not of the original assert, if there
															// even is one

			if ((label == Label.UNDEFINED_PRECONDITION || label == Label.UNDEFINED_NULL_PRECONDITION)
					&& callStack.size() > 1) {
				String cat = String.join("\n", callStack);
				cat = "Call stack\n" + cat + "\n";
				callStacks.put(assertname, cat);
			}

			if (trace) {
				JCExpression newexpr = copy(translatedExpr);
				assertDecl.init = newexpr;
				if (label != Label.POSTCONDITION)
					addTraceableComment(st, translatedExpr, label + " assertion: " + translatedExpr.toString());
			}

			currentStatements.add(assertDecl);
			currentStatements.add(st);
			if (associatedPos == null && nestedCallLocation != null) {
				st.associatedPos = nestedCallLocation.pos;
				st.associatedSource = st.source; // FIXME _ this is wrong - noty necessarily the same file
			}
			return st;
		}
		if (rac) {
			JCExpression racarg = null;
			if (args != null && args.length > 0 && args[0] instanceof JCExpression) {
				racarg = (JCExpression) args[0];
				args = new Object[0];
			}
			JCDiagnostic diag = JCDiagnostic.Factory.instance(context).create(JCDiagnostic.DiagnosticType.WARNING,
					methodEnv.showRacSource == 2 ? log.currentSource() : DiagnosticSource.NO_SOURCE, codepos, "rac." + label,
					args);
			String msg = diag.toString().replace("warning: ", "verify: ").trim();
			// With showRacSource = true, The diag above both the line information and the
			// position within the source line.
			// With sho9wRacSource = false, it includes neight
			// But for showRacSource=false, we still want the line information.
			if (methodEnv.showRacSource == 1)
				msg = utils.locationString(codepos.getPreferredPosition(), log.currentSourceFile()) + " " + msg;
			JCExpression emsg;
			if (racarg != null) {
				int k = msg.indexOf(JmlTree.eol);
				if (k < 0)
					k = msg.indexOf('\n');
				if (k >= 0) {
					String m1 = msg.substring(0, k);
					String m2 = msg.substring(k);
					emsg = treeutils.makeStringLiteral(translatedExpr.pos, m1 + ": ");
					emsg = treeutils.makeUtilsMethodCall(racarg.pos, "concat", emsg, racarg);
					emsg = treeutils.makeUtilsMethodCall(racarg.pos, "concat", emsg,
							treeutils.makeStringLiteral(translatedExpr.pos, m2));
				} else {
					emsg = treeutils.makeStringLiteral(translatedExpr.pos, msg + ": ");
					emsg = treeutils.makeUtilsMethodCall(racarg.pos, "concat", emsg, racarg);
				}
			} else {
				emsg = treeutils.makeStringLiteral(translatedExpr.pos, msg);
			}
			if (associatedPos != null) {
				var ds = new DiagnosticSource(associatedSource != null ? associatedSource : log.currentSourceFile(),
						null);
				int showSource = methodEnv.showRacSource;
				diag = JCDiagnostic.Factory.instance(context).create(JCDiagnostic.DiagnosticType.WARNING,
				    showSource == 2 ? ds : DiagnosticSource.NO_SOURCE, associatedPos,
						Utils.testingMode && showSource != 2 ? "jml.associated.decl" : "jml.associated.decl.cf",
						utils.locationString(codepos.getPreferredPosition()));
				String loc = (showSource != 1) ? "" : (utils.locationString(associatedPos, ds.getFile()) + " ");
				String msg2 = JmlTree.eol + loc + diag.toString().replace("warning: ", "verify: ").trim();
				emsg = treeutils.makeUtilsMethodCall(emsg.pos, "concat", emsg,
						treeutils.makeStringLiteral(translatedExpr.pos, msg2));
			}
			JCStatement stt;
			if (JmlOption.isOption(context, JmlOption.RAC_COMPILE_TO_JAVA_ASSERT)) {
				stt = M.at(codepos).Assert(translatedExpr, emsg);
			} else {
				if (info != null) {
					emsg = info;
				}
				stt = assertFailure(emsg, codepos, label);
				if (!isFalse)
					stt = M.at(codepos) // FIXME - make condition a temp?
							.If(treeutils.makeNot(codepos == null ? Position.NOPOS : codepos.getPreferredPosition(),
									treeutils.makeIdent(translatedExpr.pos, assertDecl.sym)), stt, null);
			}
			addStat(comment(translatedExpr, label + " assertion: " + translatedExpr.toString(), associatedSource));
			currentStatements.add(assertDecl);
			currentStatements.add(stt);
			return null;
		}
		return null;
	}

	/**
	 * Adds an assertion with the given label and (already translated) expression to
	 * 'currentStatements'. 'codepos' is the position within the code where the
	 * assertion is triggered; log.currentSource() is used as the sourcefile in
	 * which 'codepos' lies. There is no associated position or extra information.
	 * The args are arguments for the resource key giving the error message
	 * corresponding to the given Label.
	 */
	public JmlStatementExpr addAssert(DiagnosticPosition codepos, Label label, JCExpression expr, Object... args) {
		return addAssert(true, codepos, label, expr, null, null, null, args);
	}

    public JmlStatementExpr addCheck(DiagnosticPosition codepos, Label label, JCExpression translatedExpr, Object... args) {
        return addCheck(codepos, label, translatedExpr, null, null, null, args);
    }

    public JmlStatementExpr addCheck(DiagnosticPosition pos, Label label, JCExpression translatedExpr,
            /* @nullable */ DiagnosticPosition associatedPosition, /* @nullable */ JavaFileObject associatedSource,
            /* @nullable */ JCExpression info, Object... args) {
        if (!rac) {
            JCIdent id = newTemp(translatedExpr, syms.booleanType);
            translatedExpr = treeutils.makeOr(translatedExpr, id, translatedExpr);
        }
        JmlStatementExpr s = addAssert(true, pos, label, translatedExpr, associatedPosition, associatedSource, info, args);
        if (s != null) s.clauseType = checkClause;
        return s;
    }

    String[] feasibilities = null; // lazily initialized
    
    public boolean feasibilityContains(String i) {
        if (feasibilities == null) {
            String values = JmlOption.value(context,JmlOption.FEASIBILITY);
            if (values == null) values = "";
            feasibilities = values.split(",");
        }
        if (feasibilities.length == 0 || feasibilities[0].equals("none")) return false;
        if (feasibilities[0].startsWith(Strings.feas_debug)) return true;
        if (feasibilities[0].equals(Strings.feas_all) && !Strings.feas_debug.equals(i)) return true;
        //System.out.println("FC " + i + " " + Utils.join(",", feasibilities));
        for (String k: feasibilities) {
            if (i.equals(k)) return true;
        }
        return false;
    }


    /** Creates a statement at which we can check feasibility, if enabled */
    protected void addFeasibilityCheck(JCTree item, ListBuffer<JCStatement> list, String key, String description) {
        if (feasibilityContains(key)) {
            addFeasibilityCheck(item, list, description);
        }
    }

    protected void addFeasibilityCheck(JCTree item, JCBlock block, String key, String description) {
        if (feasibilityContains(key)) {
            ListBuffer<JCStatement> lst = new ListBuffer<>();
            addFeasibilityCheck(item, lst, description);
            block.stats = lst.appendList(block.stats).toList();
        }
    }

	public static boolean useAssertCount = true;

	/** Creates a statement at which we can check feasibility */
	protected void addFeasibilityCheck(JCTree item, ListBuffer<JCStatement> list, String description) {
		if (!esc) return;
		// We create feasibility check points by adding assertions of the
		// form feasCheckVar != n, for different values of n > 0.
		// Then for normal checking of the method, we assert feasCheckVar == 0
		// so all the introduced asserts are trivially true.
		// But later we can pop the feasCheckVar == 0 and add
		// feasCheckVar == k, to check feasibility at point k.

		++feasibilityCheckCount;
		//System.out.println("ADDING FEAS CHECK " + feasibilityCheckCount + " " + description);
		java.util.List<JmlStatementExpr> descs = getFeasibilityChecks(methodDecl, originalSplit);
		if (useAssertCount) {
			JCIdent id = treeutils.makeIdent(item.pos, feasCheckSym);
			JCExpression bin = treeutils.makeBinary(item.pos, JCTree.Tag.NE, treeutils.intneqSymbol, id,
					treeutils.makeIntLiteral(item.pos, feasibilityCheckCount));
			ListBuffer<JCStatement> prev = currentStatements;
			currentStatements = list;
			JmlStatementExpr a = addAssert(item, Label.FEASIBILITY_CHECK, bin);
			a.description = description;
			a.source = (item instanceof JmlTree.JmlSource) ? ((JmlTree.JmlSource) item).source() : null;
			a.associatedPos = feasibilityCheckCount;
			descs.add(a);
			currentStatements = prev;
		} else {
			JmlStatementExpr c = comment(item, "ACHECK " + feasibilityCheckCount, log.currentSourceFile());
			c.description = description;
			c.id = "ACHECK " + feasibilityCheckCount;
			addStat(c);
		}
	}

	/**
	 * Adds an assertion with the given label and (already translated) expression to
	 * 'currentStatements'. 'codepos' is the position within the code where the
	 * assertion is triggered; log.currentSource() is used as the sourcefile in
	 * which 'codepos' lies. The last two arguments give the file and position
	 * within the file of the associated specification that is potentially violated.
	 * The args are arguments for the resource key giving the error message
	 * corresponding to the given Label.
	 */
	public JmlStatementExpr addAssert(DiagnosticPosition codepos, Label label, JCExpression expr,
			DiagnosticPosition associatedPos, JavaFileObject associatedSource, Object... args) {
		return addAssert(true, codepos, label, expr, associatedPos, associatedSource, null, args);
	}

	/**
	 * Creates a call of org.jmlspecs.runtime.Utils.assertionFailure(s), where s is
	 * a literal containing the value of the argument, for RAC translations
	 * 
	 * @param sp  the string to make into the literal argument of the call
	 * @param pos the character position of the created AST
	 * @return an assert statement indication an assertion failure
	 */
	protected JCStatement assertFailure(JCExpression sp, DiagnosticPosition pos, Label label) {
		String n = label.info();
		JCFieldAccess m;
		if (rac && label == Label.PRECONDITION && JmlOption.isOption(context, JmlOption.RAC_PRECONDITION_ENTRY)) {
			n = "PreconditionEntry";
			m = findUtilsMethod(pos, "assertionFailureE");
		} else {
			m = findUtilsMethod(pos, "assertionFailureL");
		}
		JCExpression c = M.at(pos).Apply(null, m, List.<JCExpression>of(sp, treeutils.makeStringLiteral(0, n)))
				.setType(syms.voidType);
		return M.at(pos).Exec(c);
	}

	/**
	 * Creates an assumption that two expressions are equal, adding the assumption
	 * to 'currentStatements'.
	 */
	public JCStatement addAssumeEqual(DiagnosticPosition pos, Label label, JCExpression lhs, JCExpression rhs) {
		return addAssume(pos, label, treeutils.makeBinary(pos.getPreferredPosition(), JCTree.Tag.EQ, lhs, rhs), null,
				null, (Object[]) null);
	}

	/** Creates an assumption, adding it to 'currentStatements' */
	public JCStatement addAssume(DiagnosticPosition pos, Label label, JCExpression ex) {
		return addAssume(pos, label, ex, null, null, null, "");
	}

	/**
	 * Creates an assumption with an associated declaration (perhaps in a different
	 * file), adding it to 'currentStatements' (does nothing if esc and rac are
	 * false)
	 */
	public JmlStatementExpr addAssume(DiagnosticPosition pos, Label label, JCExpression ex,
			/* @nullable */ DiagnosticPosition associatedPos, /* @nullable */ JavaFileObject associatedSource,
			Object... args) {
		return addAssume(pos, label, ex, associatedPos, associatedSource, null, args);
	}

	/**
	 * Creates an assumption with an associated declaration (perhaps in a different
	 * file), adding it to 'currentStatements'
	 */
	public JmlStatementExpr addAssume(DiagnosticPosition pos, Label label, JCExpression translatedExpr,
			/* @nullable */ DiagnosticPosition associatedPosition, /* @nullable */ JavaFileObject associatedSource,
			/* @nullable */ JCExpression info, Object... args) {
		if (translatedExpr.toString().contains("maxTime == 0")) Utils.dumpStack();
		JmlStatementExpr stt = null;
		if ((infer || esc)) {
			JmlStatementExpr st = treeutils.makeAssume(pos, label, translatedExpr);
			st.source = log.currentSourceFile();
			st.associatedPos = associatedPosition == null ? Position.NOPOS : associatedPosition.getPreferredPosition();
			st.associatedSource = associatedSource;
			st.optionalExpression = info;
			st.id = Strings.assumePrefix + (++assertCount);
			// if (st.toString().contains("tmp9")) { System.out.println("ASSUME ST " + st);
			// Utils.dumpStack(); }
			if (currentStatements != null)
				currentStatements.add(st);
			else
				classDefs.add(st);
			stt = st;
			if (label != Label.FEASIBILITY_CHECK  && currentStatements != null && feasibilityContains(Strings.feas_debug)) {
			    addFeasibilityCheck(translatedExpr, currentStatements, "Extra-Assume");
			}
		}
		if (rac && methodEnv.racCheckAssumeStatements) {
			stt = addAssert(true, pos, label, translatedExpr, associatedPosition, associatedSource, info, args);
		}
		return stt;
	}

	/**
	 * Creates an AST for calling a method with the given name from the
	 * org.jmlspecs.runtime.Utils class (that is available at runtime)
	 * 
	 * @param methodName the name of the method
	 * @return the corresponding AST
	 */
	protected JCFieldAccess findUtilsMethod(DiagnosticPosition pos, String methodName) {
		JCIdent utilsClassIdent = M.Ident(utilsClass);
		Name n = names.fromString(methodName);
		Iterator<Symbol> e = utilsClass.members().getSymbolsByName(n).iterator();
		if (!e.hasNext()) {
			error(pos, "Method is not found in the runtime library: " + methodName);
			return null; // does not return
		} else {
			Symbol ms = e.next();
			JCFieldAccess m = M.at(pos).Select(utilsClassIdent, n);
			m.sym = ms;
			m.type = m.sym.type;
			return m;
		}
	}

	/**
	 * Creates an expression AST for a call of the given static method (from
	 * org.jmlspecs.runtime.Utils).
	 * 
	 * @param methodName     the name of the method to call
	 * @param translatedArgs the ASTs which are the (already translated) arguments
	 * @return the resulting AST
	 */
	protected JCExpression methodCallUtilsExpression(DiagnosticPosition pos, String methodName,
			JCExpression... translatedArgs) {
		JCFieldAccess m = findUtilsMethod(pos, methodName);
		List<JCExpression> args = new ListBuffer<JCExpression>().appendArray(translatedArgs).toList();
		JCMethodInvocation c = M.at(pos).Apply(null, m, args);
		Map<Symbol.TypeSymbol, Type> typemap = treeutils.accumulateTypeInstantiations(m.type.asMethodType().argtypes,
				args);
		if (m.type instanceof Type.MethodType) {
			Type t = ((Type.MethodType) m.type).restype;
			t = treeutils.mapTypeVars(t, typemap);
			c.setType(t);
		} else if (m.type instanceof Type.ForAll) {
			Type.ForAll tfa = (Type.ForAll) m.type;
			Type t = ((Type.MethodType) tfa.qtype).restype;
			t = treeutils.mapTypeVars(t, typemap);
			c.setType(t);
		} else {
			error(pos, "Unknown method type in methodCallUtilsExpression: " + methodName + " " + m.type.getClass());
		}
		return c;
	}

	/**
	 * Creates a statement AST for a call of the given method (from
	 * org.jmlspecs.runtime.Utils).
	 * 
	 * @param methodName     the name of the method to call
	 * @param translatedArgs the ASTs which are the (already translated) arguments
	 * @return the resulting AST
	 */
	protected JCStatement methodCallUtilsStatement(DiagnosticPosition pos, String methodName,
			JCExpression... translatedArg) {
		JCExpression c = methodCallUtilsExpression(pos, methodName, translatedArg);
		return M.at(pos).Exec(c);
	}

	protected String uniqueTempString() {
		//if (uniqueCount == 164) Utils.dumpStack();
		return Strings.tmpVarString + nextUnique();
	}

	protected JmlVariableDecl newTempDecl(DiagnosticPosition pos, Type t) {
		return newTempDecl(pos, uniqueTempString(), t);
	}

	protected JmlVariableDecl newTempDecl(DiagnosticPosition pos, String s, Type t) {
		Name n = M.Name(s);
		JmlVariableDecl d = (JmlVariableDecl) treeutils.makeVarDef(t, n, esc ? null : methodDecl != null ? methodDecl.sym : classDecl.sym, // FIXME - can a class own this?
				esc ? Position.NOPOS : pos.getPreferredPosition()); // FIXME - see note below
		return d;
	}

	/**
	 * Creates a declaration for a unique temporary name with the given type and
	 * position, with no initialization, adds it to currentStatements and returns an
	 * Ident for the new symbol.
	 */
	protected JCIdent newTemp(DiagnosticPosition pos, Type t) {
		JCVariableDecl d = newTempDecl(pos, t); // FIXME - see note below
		// We mark all temporaries as final, as an indication that they will
		// be used only once. // FIXME - do this or not? can we avoid the esc? check
		// above?
//        d.mods.flags |= Flags.FINAL;
//        d.sym.flags_field |= Flags.FINAL;
		currentStatements.add(d);
		JCIdent id = M.at(pos).Ident(d.sym);
		return id;
	}

	/**
	 * Creates a declaration for a unique temporary initialized to the given
	 * expression.
	 */
	public JCIdent newTemp(JCExpression expr) {
		return newTemp(uniqueTempString(), expr);
	}

	public JCIdent newTemp(String name, /* @ non_null */JCExpression expr) {
		return newTemp(expr.pos, name, expr);
	}

    public JCExpression newTempIfNeeded(JCExpression expr) {
        if (expr == null) return null;
        if (expr instanceof JCLiteral) return expr;
        if (expr instanceof JCIdent id && id.sym.owner == null) return id;
        return newTemp(uniqueTempString(), expr);
    }

	public Map<Symbol, JCLiteral> constants = new HashMap<>();

	public JCExpression simplifyAndSave(JmlVariableDecl d, JCExpression expr) {
		if (expr instanceof JCIdent) {
			Symbol sym = ((JCIdent) expr).sym;
			JCLiteral lit = constants.get(sym);
			if (lit != null)
				expr = lit;
		}
		if (expr instanceof JCLiteral) {
			constants.put(d.sym, (JCLiteral) expr);
		}
		return expr;
	}
	
	public boolean isIdOrLit(JCExpression expr) {
	    if (expr instanceof JCLiteral) return true;
	    if (expr instanceof JCIdent id) return true;
	    return false;
	}

	/**
	 * Creates a declaration for the given name initialized to the given expression.
	 */
	public JCIdent newTemp(int pos, String name, /* @ non_null */JCExpression expr) {
		Name n = M.Name(name);
		Type type = expr.type;
		if (type instanceof Type.WildcardType) {
			Type.WildcardType wtype = (Type.WildcardType) type;
			type = wtype.type;
		}
		// By having the owner be null, the BasicBlocker2 does not append any
		// unique-ifying suffix - FIXME - does this affect RAC?
		JmlVariableDecl d = (JmlVariableDecl) treeutils.makeVarDef(
				type.getTag() == TypeTag.BOT ? syms.objectType : type, n,
				(infer || esc) ? null : methodDecl != null ? methodDecl.sym : classDecl.sym, expr);
		d.init = expr;
//        d.init = simplifyAndSave(d,expr);
//        d.sym.flags_field |= Flags.FINAL;
//        d.mods.flags |= Flags.FINAL;
		d.pos = pos;
		d.sourcefile = log.currentSourceFile();
		d.sym.pos = Position.NOPOS; // We set the position to NOPOS so that the temporary name is not further
									// encoded
		int p = expr.getStartPosition();
		if (p == Position.NOPOS)
			p = expr.pos;
		JCIdent id = treeutils.makeIdent(p, d.sym);
		d.ident = id;
		currentStatements.add(d);
		treeutils.copyEndPosition(d, expr);
		treeutils.copyEndPosition(id, expr);
		transferInfo(expr, id);
		return id;
	}

	public void transferInfo(JCExpression src, JCExpression dest) {
		Type t = dynamicTypes.get(src);
		if (t != null) {
			dynamicTypes.put(dest, dynamicTypes.get(src));
		}
		if (isKnownNonNull(src))
			knownNonNull.add(dest);
	}

	/**
	 * Creates a declaration for a new name and type initialized to a
	 * zero-equivalent literal.
	 */
	protected JCIdent newTempNull(DiagnosticPosition pos, Type type) {
		Name n = M.Name(uniqueTempString());
		// By having the owner be null, the BasicBlocker2 does not append any
		// unique-ifying suffix - FIXME - does this affect RAC?
		JCVariableDecl d = treeutils.makeVarDef(type, n,
				esc || infer ? null : methodDecl != null ? methodDecl.sym : classDecl.sym, // FIXME - actually sholdn't
																							// stuff at the class level
																							// be put in an initializer
																							// block?
				treeutils.makeZeroEquivalentLit(pos.getPreferredPosition(), type));
		d.sym.pos = Position.NOPOS;
		currentStatements.add(d);
		JCIdent id = treeutils.makeIdent(pos.getPreferredPosition(), d.sym);
		return id;
	}

	/**
	 * Returns true if the given symbol is specified as Ghost
	 * annotation
	 */
	public boolean isGhost(VarSymbol symbol) {
		return attr.isGhost(symbol);
	}

	/**
	 * Returns true if the given symbol is specified as Helper or ???
	 * annotation
	 */
	public boolean isHelper(MethodSymbol symbol) {
		return utils.hasModifier(symbol, Modifiers.HELPER);
	}

	// Returns true if the symbol is a formal parameter of the given method,
	// or of any method if msym is null
	// not a local variable or a field
	public boolean isFormal(Symbol v, MethodSymbol msym) {
		if ((v.flags() & Flags.PARAMETER) == 0)
			return false;
		if (msym == null)
			return true;
		return v.owner == msym;
	}

	/** Returns true if the given symbol is pure (locally or globally) */
	public boolean isPure(MethodSymbol symbol) {
		return specs.isPureMethod(symbol);

	}

	/** Returns true if the given symbol has a Model annotation */
	public boolean isModel(Symbol symbol) {
		return utils.hasModifier(symbol, Modifiers.MODEL);
	}

	/** Returns true if the Java static modifier is set */
	public boolean hasStatic(JCModifiers mods) {
		return (mods.flags & Flags.STATIC) != 0;
	}

	/** Returns true if the block contains only comments */
	public boolean isOnlyComment(JCBlock block) {
		for (JCStatement st : block.stats) {
			if (st instanceof JmlStatementExpr && ((JmlStatementExpr) st).clauseType == commentClause)
				continue;
			if (st instanceof JCBlock && isOnlyComment((JCBlock) st))
				continue;
			return false;
		}
		return true;
	}

	/**
	 * Creates a try statement that wraps the given block and catches any
	 * RuntimeException; the catch block prints the given message; esc just returns
	 * the given block
	 */
	public JCStatement wrapRuntimeException(DiagnosticPosition pos, JCStatement statement, String message,
			/* @nullable */ JCBlock catchStats) {
		if (!rac) return statement;
		// methodDecl can be null if we are translating class specs or initalizer blocks (check this -- temp method?)
		// FIXME - why is superSymbol used here?
		var ownerSym = methodDecl != null ? methodDecl.sym : classDecl.superSymbol;
		JCBlock block = statement instanceof JCBlock ? (JCBlock) statement
				: M.at(statement).Block(0L, List.<JCStatement>of(statement));
		if (isOnlyComment(block))
			return statement;
		int p = pos.getPreferredPosition();
		Name n = names.fromString(Strings.runtimeException); // FIXME - this does not need to be repeated every time
		JCVariableDecl vd = treeutils.makeVarDef(syms.runtimeExceptionType, n, ownerSym, p);
		JCIdent ex = treeutils.makeIdent(p, vd.sym);
		JCExpression str = treeutils.makeStringLiteral(p, message);
		JCStatement st = methodCallUtilsStatement(pos, "reportException", str, ex);
		JCBlock bl = M.at(pos).Block(0,
				st != null ? (catchStats != null ? List.<JCStatement>of(st, catchStats) : List.<JCStatement>of(st))
						: (catchStats != null ? List.<JCStatement>of(catchStats) : List.<JCStatement>nil()));
		JCCatch catcher = M.at(pos).Catch(vd, bl);
		// FIXME - this report needs a position of clause and name of method
		boolean quiet = utils.jmlverbose == 0;
		JCCatch catcher1;
		vd = treeutils.makeVarDef(utils.createClassSymbol("java.lang.NoSuchMethodError").type,
				names.fromString("noSuchMethodError"), ownerSym, p);
		if (quiet) {
			catcher1 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>nil()));
		} else {
			JCExpression id = treeutils.makeIdent(pos.getPreferredPosition(), vd.sym);
			JCExpression location = treeutils.makeStringLiteral(pos.getPreferredPosition(),
					utils.locationString(pos, log.currentSourceFile()));
			location = treeutils.makeNullLiteral(pos.getPreferredPosition()); // FIXME - really need to propagate the
																				// location of the call
			JCMethodInvocation m = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "reportNoSuchMethod", id,
					location);
			catcher1 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>of(M.at(pos.getPreferredPosition()).Exec(m))));
		}
		JCCatch catcher2;
		vd = treeutils.makeVarDef(utils.createClassSymbol("java.lang.NoSuchFieldError").type,
				names.fromString("noSuchFieldError"), ownerSym, p);
		if (quiet) {
			catcher2 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>nil()));
		} else {
			JCExpression id = treeutils.makeIdent(pos.getPreferredPosition(), vd.sym);
			JCExpression location = treeutils.makeStringLiteral(pos.getPreferredPosition(),
					utils.locationString(pos, log.currentSourceFile()));
			if (Utils.testingMode)
				location = treeutils.makeNullLiteral(pos.getPreferredPosition());
			JCMethodInvocation m = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "reportNoSuchField", id,
					location);
			catcher2 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>of(M.at(pos.getPreferredPosition()).Exec(m))));
		}
		return M.at(pos).Try(block, List.<JCCatch>of(catcher, catcher1, catcher2), null);
	}

	/**
	 * Creates a try statement that wraps the given block and catches the given
	 * exception; the declaration is the declaration of the variable to use in the
	 * catch block; the catch block prints the given message and executes the given
	 * stats.
	 */
	public JCStatement wrapException(DiagnosticPosition pos, JCBlock block, JCVariableDecl exceptionDecl,
			/* @nullable */ JCBlock catchStats) {
		JCBlock bl = catchStats != null ? catchStats : M.at(pos).Block(0, List.<JCStatement>nil());
		JCCatch catcher = M.at(pos).Catch(exceptionDecl, bl);
		return M.at(pos).Try(block, List.<JCCatch>of(catcher), null);
	}

	//* Returns true if the Java final modifiers is set in the symbol */
	protected boolean isFinal(Symbol sym) {
		return (sym.flags() & Flags.FINAL) != 0;
	}

	// From outermost in, with the argument being last
	protected java.util.List<Pair<ClassSymbol, JCExpression>> getNonStaticEnclosingClasses(ClassSymbol bsym, JCExpression receiver) {
		Symbol esym = bsym.getEnclosingElement();
		Pair<ClassSymbol, JCExpression> elem = new Pair<>(bsym, receiver);
		java.util.List<Pair<ClassSymbol, JCExpression>> list;
		if (!bsym.isStatic() && esym instanceof ClassSymbol) {
			ClassSymbol csym = (ClassSymbol) esym;
			VarSymbol vsym = enclosingClassFieldSymbols.get(csym);
			if (vsym != null) {
				JCExpression fa = treeutils.makeSelect(Position.NOPOS, receiver, vsym);
				list = getNonStaticEnclosingClasses(csym, fa);
			} else {
				list = new LinkedList<>();
			}
		} else {
			list = new LinkedList<>();
		}
		list.add(elem);
		return list;

	}

	/**
	 * Adds in assumptions or assertions for the non_nullity of visible fields of
	 * the current and parent classes.
	 */
	public void addNonNullChecks(boolean assume, DiagnosticPosition pos, Type baseType, JCExpression receiver, boolean isConstructor) {
		JCExpression savedThisExpr = currentEnv.currentReceiver;
		TypeSymbol tsym = baseType.tsym;
		Symbol esym = tsym.getEnclosingElement();
		if (!tsym.isStatic() && tsym instanceof ClassSymbol) {
			ClassSymbol csym = (ClassSymbol) tsym;
			VarSymbol vsym = enclosingClassFieldSymbols.get(csym);
			if (vsym != null && esym instanceof ClassSymbol) {
				JCExpression fa = treeutils.makeSelect(Position.NOPOS, receiver, vsym);
				addNonNullChecks(assume, pos, ((ClassSymbol) esym).type, fa, false);
			}
		}
		currentEnv.currentReceiver = savedThisExpr;
		addNonNullChecks2(assume, pos, baseType, receiver, isConstructor);

	}

	public void addNonNullChecks2(boolean assume, DiagnosticPosition pos, Type baseType, JCExpression receiver, boolean isConstructor) {
		boolean contextIsStatic = receiver == null; // && !methodDecl.sym.isConstructor(); //|| (self &&
													// utils.isJMLStatic(methodDecl.sym));
		java.util.List<Type> parents = parents(baseType, false);
		for (Type ctype : parents) {
			if (!(ctype.tsym instanceof ClassSymbol))
				continue;
			// typevarMapping = typemapping(ctype, null, null);
			TypeSymbol csym = ctype.tsym;
			for (Symbol s : csym.getEnclosedElements()) {
				if (s instanceof VarSymbol) {
					boolean stat = utils.isJMLStatic(s);
					if (!utils.visible(classDecl.sym, csym, s.flags()/* , methodDecl.mods.flags */))
						continue;
					if (!stat && contextIsStatic)
						continue;
					if (!assume && isConstructor)
						continue;
					if (utils.isJavaOrJmlPrimitiveType(s.type) || jmltypes.isOnlyDataGroup(s.type))
						continue;
					VarSymbol v = (VarSymbol) s;
					JCExpression e;
					if (receiver == null)
						e = M.at(pos).Ident(v);
					else
						e = M.at(pos).Select(receiver, v);
					JCExpression e1 = treeutils.makeNotNull(pos.getPreferredPosition(), e);
					JCExpression e2 = treeutils.makeNonNullDynamicTypeInEquality(pos, e, e.type);
					if (specs.isNonNull(v)) {
						e = treeutils.makeAnd(pos.getPreferredPosition(), e1, e2);
					} else {
						e = treeutils.makeImplies(pos.getPreferredPosition(), e1, e2);
					}
					if (assume)
						addAssume(pos, Label.POSSIBLY_NULL_FIELD, e, null, null); // FIXME - no associated position?
					else
						addAssert(pos, Label.POSSIBLY_NULL_FIELD, e, null, null); // FIXME - no associated position?

				}
			}
		}

	}

	/**
	 * Adds invariants, constraints and initially clauses from a given class and its
	 * parents. This is used for pre and post conditions, in which case the
	 * invariants from a method's own class (and its parents) are used; it is also
	 * used for other relevant classes, such as the classes of method parameters.
	 * The value of 'methodDecl' (and 'classDecl') is the method for which a logical
	 * encoding is being constructed, but is not necessarily the callee class which
	 * is causing the invariants to be loaded.
	 * 
	 * @param pos            the code position which occasioned needing the
	 *                       invariants
	 * @param isConstructor  whether the callee (or the method itself if there is no
	 *                       callee) is a contructor
	 * @param isSuper        true if the callee method is a super() call
	 * @param basecsym       the base TypeSymbol from which to take invariants (this
	 *                       may or may not be the class containing the methodDecl)
	 * @param receiver       the THIS object to use when translating the invariants
	 *                       - this is either the receiver for the original method
	 *                       call or is the parameter or return value for which
	 *                       invariants are being loaded. This parameter is null iff
	 *                       the base method is static and not a constructor; if it
	 *                       is a constructor the value is the object being produced
	 *                       by the constructor.
	 * @param stats          the statement list into which to add the invariants
	 * @param isHelper       whether the callee or base method is a helper method
	 *                       (whichever one the invariants are for)
	 * @param prepost        true if we are inserting invariants as pre or post
	 *                       conditions (rather than on behalf of a called
	 *                       procedure)
	 * @param isPost         whether we are adding clauses after (post) or before
	 *                       the method
	 * @param assume         whether clauses are assumed or asserted
	 * @param invariantLabel the cause of needing the invariant
	 */
	protected void addInvariants(DiagnosticPosition pos, Type basetype, JCExpression receiver,
			ListBuffer<JCStatement> stats, boolean prepost, boolean isConstructor, boolean isSuper, boolean isHelper,
			boolean isPost, boolean assume, Label invariantLabel, Object... invariantDescription) {
		addInvariants(pos, basetype, receiver, stats, prepost, isConstructor, isSuper, isHelper, isPost, assume, false,
				invariantLabel, invariantDescription);
	}

	protected void addInvariants(DiagnosticPosition pos, Type basetype, JCExpression receiver,
			ListBuffer<JCStatement> stats, boolean prepost, boolean isConstructor, boolean isSuper, boolean isHelper,
			boolean isPost, boolean assume, boolean isReturn, Label invariantLabel, Object... invariantDescription) {
		TypeSymbol basecsym = basetype.tsym;
		ListBuffer<JCStatement> prevStats = currentStatements;
		if (utils.isExtensionValueType(basetype)) {
			// FIXME - should the following be a more general type/allocation condition? --
			// not if translates to an SMT type other than REF
			if (receiver != null && !utils.isJavaOrJmlPrimitiveType(receiver.type)) {
				addAssume(pos, Label.INVARIANT, treeutils.makeNotNull(pos, receiver));
			}
			JCExpression e = getInvariant(pos, classDecl.type, basetype, receiver, true); // FIXME - is classDecl always the
																					// calling environment?
			// e is null if there is no invariant (implicitly true)
			if (e != null)
				addAssume(pos, Label.INVARIANT, e);
			return;
		}
		if (basetype.isPrimitive()) return;
		if (!translatingJML) clearInvariants();
		// FIXME - if this is an initializer, methodDecl should not be null
		if (methodDecl == null || methodDecl.isInitializer) return;
		if (!isReturn && methodDecl.sym.isConstructor() && assume && types.isSameType(methodDecl.sym.type, basetype)) {
			return;
		}
		if (!isReturn && startInvariants(basecsym, pos))
			return;
		// if (basecsym.toString().contains("SassyOption")) System.out.println("START
		// SassyOption " + (scount++));

		java.util.List<Type> parents = parents(basetype, true);
		boolean contextIsStatic = receiver == null;

		// Iterate through parent classes and interfaces, assuming relevant axioms and
		// invariants
		// These are checked prior to calling the callee
		JCExpression prevThisExpr = currentEnv.currentReceiver;
		Map<TypeSymbol, Type> savedTypevarMapping = typevarMapping;
		try {
			ListBuffer<JCStatement> staticStats = stats;

			{
			    currentEnv.currentReceiver = receiver;
				for (Type ctype : parents) {
					if (!(ctype.tsym instanceof ClassSymbol))
						continue;
					if (isDataGroup(ctype))
						continue;

					typevarMapping = typemapping(ctype, null, null, null);
					ListBuffer<JCStatement> check = pushBlock();
					ListBuffer<JCStatement> instanceStats = currentStatements;
					try {
						ClassSymbol csym = (ClassSymbol) ctype.tsym;
						JmlSpecs.TypeSpecs tspecs = specs.getAttrSpecs(csym);
						if (tspecs == null) continue; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

						if (prepost && !isPost && !(isConstructor && types.isSubtype(basetype, ctype))) {
							// Adding in invariant about final fields
							instanceStats.add(comment(pos,
									(assume ? "Assume" : "Assert") + " final field invariants for " + csym, null));
							JCExpression conj = null;
							// JCExpression staticconj = null;
							for (Symbol s : csym.getEnclosedElements()) {
								if (s instanceof VarSymbol) {
									if (contextIsStatic && !utils.isJMLStatic(s)) continue;
									// FIXME - check visibility
									VarSymbol v = (VarSymbol) s;
									Object o = v.getConstValue(); // This call returns the raw underlying value, not the
																	// stated type (i.e. Integer for boolean and char)
									if (o != null) {
										JCExpression id = treeutils.makeIdent(v.pos, v);
										if (utils.isJMLStatic(v)) {
											JCExpression ty = treeutils.makeType(v.pos, v.owner.type);
											id = treeutils.makeSelect(v.pos, ty, v);
										}
										JCLiteral val = treeutils.makeLit(v.pos, v.type, o);
										JCExpression e = treeutils.makeEquality(v.pos, id, val);
										if (utils.isJMLStatic(s)) {
											// staticconj = staticconj == null ? e : treeutils.makeAnd(v.pos,
											// staticconj, e);
										} else {
											conj = conj == null ? e : treeutils.makeAnd(v.pos, conj, e);
										}
									}
								}
							}
							if (conj != null && !isHelper) {
								currentStatements = instanceStats;
								conj = convertJML(conj);
					            addStat(comment(pos, (assume?"Assume":"Assert") + " invariant " + conj, null));
								if (assume)
									addAssume(pos, invariantLabel, conj);
								else
									addAssert(pos, invariantLabel, conj);
							}
						}

						if (isHelper)
							staticStats.add(comment(pos, "Not " + (assume ? "Assuming" : "Asserting")
									+ " static invariants for helper method " + csym, null));
						else
							staticStats.add(comment(pos,
									(assume ? "Assume" : "Assert") + " invariants for " + csym, null));
						// Do the non_null fields
						// FIXME - not sure that we should exclue rac
						if (assume && !rac)
							addNullnessDynamicTypeConditions(pos, basetype, receiver, isConstructor, assume,
									contextIsStatic, ctype, csym);
						// Do the actual invariants
						for (JmlTypeClause clause : tspecs.clauses) {
							if (!utils.jmlvisible(classDecl.sym, csym,
									clause.modifiers.flags/* , methodDecl.mods.flags */))
								continue;
							JmlTypeClauseExpr t;
							DiagnosticPosition cpos = clause;
							boolean clauseIsStatic = utils.isJMLStatic(clause.modifiers, csym);
							boolean clauseIsFinal = (clause.modifiers.flags & Flags.FINAL) != 0;
							currentStatements = clauseIsStatic ? staticStats : instanceStats;
							// FIXME - guard against the receiver being null for non-static invariants
							if (clause.clauseType == invariantClause) {
								// invariants on both pre and post for all classes of parameters and return
								// value
								// Pre and post conditions:
								// helper - no invariants for class of method
								// non-helper constructor - invariants only on post
								// non-helper method - invariants on pre and post
								// Calling a method - caller invariants
								// same as pre and postconditions, except
								// when a constructor is calling super(), no invariants of containing class are
								// assumed in post
								// Calling a method - callee invariants
								// callee is helper - no invariants in pre or post for class containing method
								// callee is super() - invariants of super class on post
								// callee is constructor - invariants on post
								// callee is method - invariants on pre and post
								if (contextIsStatic && !clauseIsStatic)
									continue;
								if (clauseIsFinal && !assume && !isReturn)
									continue;
								if (clauseIsFinal && !contextIsStatic && clauseIsStatic)
									continue;
								if (isHelper && (!clauseIsFinal || !assume))
									continue;
								if (isSuper && !isPost)
									continue;
								boolean doit = false;
								if (!isConstructor || isPost)
									doit = true; // pre and postcondition case
								if (isConstructor) {
									if (clauseIsStatic)
										doit = true;
									if (utils.findModifier(classDecl.mods, Modifiers.CAPTURED) != null)
										doit = true;
									// FIXME - should not use erasure here, but pasrameterized dtypes do not seem to
									// work
									// properly even if ctype is obtrained by collecting super classes and super
									// interfaces of basetype
									boolean b = !types.isAssignable(types.erasure(basetype), types.erasure(ctype));
									if (b)
										doit = true;
								}
								if (doit) {
									// JavaFileObject prevSource = log.useSource(clause.source());
									try {
										t = (JmlTypeClauseExpr) copy(clause); // FIXME - why copy the clause
										addTraceableComment(t.expression, clause.toString());
										JCExpression e = convertJML(t.expression, treeutils.trueLit, isPost);
		                                addStat(comment(pos, (assume?"Assume":"Assert") + " invariant " + e, null));
										if (assume)
											addAssume(pos, invariantLabel, e, cpos, clause.source,
													invariantDescription);
										else
											addAssert(pos, invariantLabel, e, cpos, clause.source,
													invariantDescription);
									} catch (NoModelMethod e) {
										// log.error(clause.pos, "jml.message", e.getMessage());
									} catch (JmlNotImplementedException e) {
										notImplemented(clause.clauseType.keyword() + " clause containing ", e,
												clause.source());
									} finally {
										// log.useSource(prevSource);
									}
								}
							}
						}
					} finally {
						currentStatements = instanceStats;
						JCBlock bl = popBlock(pos, check);
						if (!onlyComments(bl.stats) && !infer) {
							if (contextIsStatic) {
								staticStats.add(bl);
							} else if (receiver == null) {
								// This can be because we are in a constructor
								staticStats.add(bl);
							} else {
								JCExpression ex = treeutils.makeNeqObject(pos.getPreferredPosition(), receiver,
										treeutils.nullLit);
//								pushBlock(staticStats);
//								ex = newTempIfNeeded(ex);
//								popBlock();
								JCStatement st = M.at(pos).If(ex, bl, null);
								staticStats.add(st); // FIXME _ why is this static?
							}
						}
					}

				}
//            } else {
//                notImplemented(receiver, "receiver of class " + (receiver == null ? "-null-" : receiver.getClass().getName()));
			}
		} finally {
			if (!isReturn)
				endInvariants(basecsym);
			if (!translatingJML)
				clearInvariants();
			currentStatements = prevStats;
			currentEnv.currentReceiver = prevThisExpr;
			typevarMapping = savedTypevarMapping;
		}

	}

	private void addNullnessDynamicTypeConditions(DiagnosticPosition pos, Type basetype, JCExpression receiver,
			boolean isConstructor, boolean assume, boolean contextIsStatic, Type ctype, ClassSymbol csym) {
		JCExpression savedThisExpr = currentEnv.currentReceiver;
		if (!csym.isStatic()) {
			Symbol esym = csym.getEnclosingElement();
			VarSymbol vsym = enclosingClassFieldSymbols.get(csym);
			if (vsym != null && esym instanceof ClassSymbol) {
				JCExpression fa = treeutils.makeSelect(Position.NOPOS, receiver, vsym);
				currentEnv.currentReceiver = fa;

				addNullnessDynamicTypeConditions(pos, ((ClassSymbol) esym).type, fa, false, assume, contextIsStatic,
						vsym.type, (ClassSymbol) esym);
			}
		}
		currentEnv.currentReceiver = savedThisExpr;
		addNullnessDynamicTypeConditions2(pos, basetype, receiver, isConstructor, assume, contextIsStatic, ctype, csym);
	}

	private void addNullnessDynamicTypeConditions2(DiagnosticPosition pos, Type basetype, JCExpression receiver,
			boolean isConstructor, boolean assume, boolean contextIsStatic, Type ctype, ClassSymbol csym) {
		if (isDataGroup(basetype) || isDataGroup(ctype))
			return;
		if (utils.isJavaOrJmlPrimitiveType(basetype))
			return;
		for (Symbol s : csym.getEnclosedElements()) {
			if (s instanceof VarSymbol) {
				if (!utils.visible(classDecl.sym, csym, s.flags()/* , methodDecl.mods.flags */))
					continue;
				if (!utils.isJMLStatic(s) && contextIsStatic)
					continue;
				if (isConstructor && (!assume || basetype == ctype))
					continue;
				if (isDataGroup(csym.type))
					continue;
				VarSymbol v = (VarSymbol) s;
				Type vartype = v.type;
				JCExpression field;
				if (utils.isJMLStatic(v))
					field = treeutils.makeSelect(v.pos, treeutils.makeType(v.pos, v.owner.type), v);
				else
					field = M.at(pos).Select(receiver, v);
				if (!utils.isJavaOrJmlPrimitiveType(vartype) && !isDataGroup(vartype)) {
					JCExpression e = treeutils.makeNotNull(pos.getStartPosition(), field); // FIXME - position not right
					if (specs.isNonNull(v)) {
						if (assume)
							addAssume(pos, Label.POSSIBLY_NULL_FIELD, e, null, null); // FIXME - no associated position?
						else
							addAssert(pos, Label.POSSIBLY_NULL_FIELD, e, null, null); // FIXME - no associated position?
					}
					if (assume) {
						addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeDynamicTypeInEquality(pos, field, vartype),
								null, null); // FIXME - associated position should be the declaration
					}

				} else {
					// FIXME - range constraints?
				}
			}
		}
	}

	protected void assertInvariants(JCExpression expr, JCExpression currentThis) {
		JCExpression saved = currentEnv.currentReceiver;
		currentEnv.currentReceiver = currentThis;
		ListBuffer<JCStatement> check10 = pushBlock();
		try {
			for (JmlTypeClause t : specs.getAttrSpecs((ClassSymbol) expr.type.tsym).clauses) {
				if (t.clauseType != invariantClause)
					continue;
				JavaFileObject prev = log.useSource(t.source);
				try {
					JCExpression e = convertJML(copy((JmlTypeClauseExpr) t).expression); // FIXME - why copy the
																								// caluse
					addAssert(t, Label.INVARIANT, e); // FIXME - CHnage the position to point to end point of method,
														// and associated position to invariant
				} finally {
					log.useSource(prev);
				}
			}
		} finally {
			JCBlock bl = popBlock(expr, check10);
			if (!bl.stats.isEmpty()) {
				JCExpression nn = treeutils.makeNeqObject(expr.pos, expr, treeutils.nullLit);
				JCStatement st = M.at(expr.pos).If(newTempIfNeeded(nn), bl, null);
				addStat(st);
			}
			currentEnv.currentReceiver = saved;
		}
	}

	protected void addRecInvariants(boolean assume, boolean staticOnly, boolean fieldInvariants, boolean helper,
			DiagnosticPosition d, TypeSymbol tsym, JCExpression currentThis) {
		JCExpression saved = currentEnv.currentReceiver;
		currentEnv.currentReceiver = currentThis;
		for (ClassSymbol csym : utils.parents(tsym, false)) {
			// if (esc) addNullnessAndTypeConditionsForFields(csym,false);
			// The following call adds in the nullness and type conditions of all fields
			addInvariants(assume, d, staticOnly, fieldInvariants, helper, csym, currentThis);
		}
		currentEnv.currentReceiver = saved;
	}

	protected void addRecInvariants(boolean assume, JCVariableDecl d, JCExpression currentThis) {
		JCExpression saved = currentEnv.currentReceiver;
		currentEnv.currentReceiver = currentThis;
		boolean staticOnly = utils.isJMLStatic(d.sym);
		for (ClassSymbol csym : utils.parents(d.type.tsym, false)) {
			// if (esc) addNullnessAndTypeConditionsForFields(csym,false);
			// The following call adds in the nullness and type conditions of all fields
			addInvariants(assume, d, staticOnly, false, false, csym, currentThis);
		}
		currentEnv.currentReceiver = saved;
	}

	protected void addInvariants(boolean assume, DiagnosticPosition d, boolean staticOnly, boolean fieldInvariants,
			boolean helper, ClassSymbol csym, JCExpression currentThis) {
		int pos = d == null ? Position.NOPOS : d.getPreferredPosition();
		JCExpression saved = currentEnv.currentReceiver;
		currentEnv.currentReceiver = currentThis;
		Scope cs = csym.members();
		if (esc) {
			for (Symbol s : cs.getSymbols()) {
				if (!(s instanceof VarSymbol)) continue;
				if (staticOnly && !utils.isJMLStatic(s)) continue;
				if (jmltypes.isOnlyDataGroup(s.type)) continue;
				JCExpression c = null;
//				if (!utils.isJMLStatic(s)) {
//				    c = treeutils.makeNotNull(currentThis,  currentThis);
//				}
				addNullnessAllocationTypeCondition2(d, s, false, c);
				if (fieldInvariants && !s.type.isPrimitive() && !isHelper(methodDecl.sym)) {
					JCExpression var = convertJML(treeutils.makeIdent(null, s));
					addRecInvariants(assume, false, false, helper, d, s.type.tsym, var);
				}
			}
		}
		ListBuffer<JCStatement> check = pushBlock();
		try {
			for (JmlTypeClause t : specs.getAttrSpecs(csym).clauses) {
				if (t.clauseType != invariantClause)
					continue;
				if (staticOnly && !utils.isJMLStatic(t.modifiers, csym))
					continue;
				if (helper && (t.modifiers.flags & Flags.FINAL) == 0)
					continue;
				if (!assume && (t.modifiers.flags & Flags.FINAL) != 0)
					continue;
				JavaFileObject prev = log.useSource(t.source);
				try {
					JCExpression e = convertJML(copy((JmlTypeClauseExpr) t).expression); // FIXME - really need
																								// the convertCopy?
					if (!utils.isJMLStatic(t.modifiers, csym)) {
						JCExpression ee = treeutils.makeNotNull(pos, copy(currentThis));
						e = treeutils.makeImplies(pos, ee, e);
					}
					if (assume)
						addAssume(t, Label.INVARIANT, e);
					else
						addAssert(t, Label.INVARIANT, e);
				} catch (NoModelMethod ex) {
					// Just skip
				} finally {
					log.useSource(prev);
				}
			}
		} finally {
			JCBlock bl = popBlock(d, check);
			if (!bl.stats.isEmpty()) {
				if (staticOnly) {
					addStat(bl);
				} else {
					JCExpression nn = (treeutils.makeNeqObject(pos, copy(currentEnv.currentReceiver), treeutils.nullLit));
					JCStatement st = M.at(pos).If(nn, bl, null);
					addStat(st);
				}
			}
			currentEnv.currentReceiver = saved;
		}
	}

//	// FIXME - not used?
//	protected void addInvariants(boolean assume, JCVariableDecl d, ClassSymbol csym, JCExpression currentThis) {
//		JCExpression saved = currentEnv.currentReceiver;
//		currentEnv.currentReceiver = currentThis;
//		ListBuffer<JCStatement> check = pushBlock();
//		try {
//			for (JmlTypeClause t : specs.getSpecs(csym).clauses) {
//				if (t.clauseType != invariantClause)
//					continue;
//				JavaFileObject prev = log.useSource(t.source);
//				try {
//					JCExpression e = convertJML(convertCopy((JmlTypeClauseExpr) t).expression); // FIXME - really need
//																								// the convertCopy?
//					if (!utils.isJMLStatic(t.modifiers, csym)) {
//						JCExpression ee = treeutils.makeNotNull(d.pos, convertCopy(currentThis));
//						e = treeutils.makeImplies(d.pos, ee, e);
//					}
//					if (assume)
//						addAssume(t, Label.INVARIANT, e);
//					else
//						addAssert(t, Label.INVARIANT, e);
//				} catch (NoModelMethod ex) {
//					// Just skip
//				} finally {
//					log.useSource(prev);
//				}
//			}
//			if (esc) {
//				Scope cs = csym.members();
//				for (Symbol s : cs.getSymbols()) {
//					if (!(s instanceof VarSymbol))
//						continue;
//					addNullnessAllocationTypeCondition2(d, s, false);
//				}
//			}
//		} finally {
//			JCBlock bl = popBlock(d, check);
//			if (!bl.stats.isEmpty()) {
//				if (utils.isJMLStatic(d.sym) || utils.isJavaOrJmlPrimitiveType(currentEnv.currentReceiver.type)) {
//					addStat(bl);
//				} else {
//					JCExpression nn = treeutils.makeNeqObject(d.pos, convertCopy(currentEnv.currentReceiver), treeutils.nullLit);
//					JCStatement st = M.at(d.pos).If(nn, bl, null);
//					addStat(st);
//				}
//			}
//			currentEnv.currentReceiver = saved;
//		}
//	}

	protected void addConstraintInitiallyChecks(DiagnosticPosition pos, TypeSymbol basecsym, JCExpression receiver,
			ListBuffer<JCStatement> stats, boolean prepost, boolean isConstructor, boolean isSuper, boolean isHelper,
			boolean isPost, boolean assume, Label invariantLabel, Object... invariantDescription) {
		if (basecsym.type.isPrimitive())
			return;
//        if (!translatingJML) clearInvariants();
		java.util.List<ClassSymbol> parents = utils.parents(basecsym, false);
		boolean self = basecsym == methodDecl.sym.owner; // true if we are inserting invariants for the base method,
															// either as pre and post conditions or prior to calling a
															// callee
		boolean contextIsStatic = receiver == null; // || (self && utils.isJMLStatic(methodDecl.sym));

		// Iterate through parent classes and interfaces, assuming relevant axioms and
		// invariants
		// These are checked prior to calling the callee
		ListBuffer<JCStatement> prevStats = currentStatements;
		JCExpression prevThisExpr = currentEnv.currentReceiver;
		try {
			ListBuffer<JCStatement> staticStats = stats;

			currentEnv.currentReceiver = receiver;

			for (ClassSymbol csym : parents) {
				ListBuffer<JCStatement> check = pushBlock();
				ListBuffer<JCStatement> instanceStats = currentStatements;
				boolean pv = checkAccessEnabled;
				checkAccessEnabled = false; // Do not check access in JML clauses
				try {

					JmlSpecs.TypeSpecs tspecs = specs.getAttrSpecs(csym);
					if (tspecs == null)
						continue; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

					staticStats.add(comment(pos, (assume ? "Assume" : "Assert") + " constraints for " + csym, null));
					for (JmlTypeClause clause : tspecs.clauses) {
					    if (!utils.visible(classDecl.sym, csym, clause.modifiers.flags/* , methodDecl.mods.flags */))
							continue;
						JmlTypeClauseExpr t;
						DiagnosticPosition cpos = clause;
						boolean clauseIsStatic = utils.isJMLStatic(clause.modifiers, csym);
						currentStatements = clauseIsStatic ? staticStats : instanceStats;
						try {
							// FIXME - guard against the receiver being null for non-static invariants
							if (clause.clauseType == constraintClause) {
								if (!isPost)
									break;
								if ((!isConstructor && !contextIsStatic) || clauseIsStatic) {
									JmlTypeClauseConstraint tt = (JmlTypeClauseConstraint) clause;
									if (tt.sigs != null) {
										boolean found = false;
										for (JmlMethodSig sig : tt.sigs) {
											if (sig.methodSymbol == methodDecl.sym) {
												found = true;
												break;
											}
										}
										if (found == tt.notlist)
											break;
									}
									ListBuffer<JCStatement> ch = pushBlock();
									try {
										addTraceableComment(tt.expression, clause.toString());
										JCExpression e = convertJML(tt.expression);
										if (assume)
											addAssume(pos, Label.CONSTRAINT, e, cpos, clause.source);
										else
											addAssert(pos, Label.CONSTRAINT, e, cpos, clause.source);
									} finally {
										addStat(popBlock(clause, ch));
									}
								}
							} else if (clause.clauseType == initiallyClause) {
								if (isPost && isConstructor && !contextIsStatic) {
									ListBuffer<JCStatement> ch = pushBlock();
									try {
										t = (JmlTypeClauseExpr) clause;
										addTraceableComment(t.expression, clause.toString());
										JCExpression e = convertJML(t.expression);
                                        if (assume)
                                            addAssume(pos, Label.INITIALLY, e, cpos, clause.source);
                                        else
                                            addAssert(pos, Label.INITIALLY, e, cpos, clause.source);
									} finally {
										addStat(popBlock(cpos, ch));
									}
								}
							}
						} catch (NoModelMethod e) {
							// FIXME - what to do.
						} catch (JmlNotImplementedException e) {
							notImplemented(clause.clauseType.keyword() + " clause containing ", e, clause.source());
						}
					}
				} finally {
					checkAccessEnabled = pv;
					currentStatements = instanceStats;
					JCBlock bl = popBlock(pos, check);
					if (!onlyComments(bl.stats)) {
						if (contextIsStatic) {
							staticStats.add(bl);
						} else {
							JCExpression ex = treeutils.makeNeqObject(pos.getPreferredPosition(), receiver,
									treeutils.nullLit);
							pushBlock(staticStats);
							ex = newTempIfNeeded(ex);
							popBlock();
							JCStatement st = M.at(pos).If(ex, bl, null);
							staticStats.add(st);
						}
					}
				}

			}
		} finally {
			currentStatements = prevStats;
			currentEnv.currentReceiver = prevThisExpr;
		}

	}

	protected void addAxioms(DiagnosticPosition pos, TypeSymbol basecsym, ListBuffer<JCStatement> stats,
			JCExpression receiver) {
		if (rac)
			return;
		java.util.List<ClassSymbol> parents = utils.parents(basecsym, true);
		// Iterate through parent classes and interfaces, assuming relevant axioms
		ListBuffer<JCStatement> prevStats = currentStatements;
		JCExpression prevThisExpr = currentEnv.currentReceiver;
		boolean pv = checkAccessEnabled;
		checkAccessEnabled = false; // Do not check access in JML clauses
		try {
			currentStatements = stats;
			currentEnv.currentReceiver = receiver;
			for (ClassSymbol csym : parents) {
				if (!addAxioms(heapCount, csym))
					continue;
				JmlSpecs.TypeSpecs tspecs = specs.getAttrSpecs(csym);
				if (tspecs == null)
					continue; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

				for (JmlTypeClause clause : tspecs.clauses) {
					DiagnosticPosition cpos = clause;
					try {
						// FIXME - guard against the receiver being null for non-static invariants
						if (clause.clauseType == axiomClause) {
							// Axioms are included only when assuming the preconditions
							// for a method body - both the main procedure and
							// any axioms for the classes of the parameters and return values
							if (rac) {
								notImplemented(clause, "axiom clause", clause.source());
							} else if (esc || infer) {
								addStat(comment(clause));
								JmlTypeClauseExpr t = (JmlTypeClauseExpr) clause;
								JCExpression e = convertJML(t.expression);
								addAssume(pos, Label.AXIOM, e, cpos, clause.source);
							}
						}
					} catch (NoModelMethod e) {
						// FIXME - what to do.
					} catch (JmlNotImplementedException e) {
						notImplemented(clause.clauseType.keyword() + " clause containing ", e, clause.source());
					}
				}
			}
		} finally {
			currentStatements = prevStats;
			currentEnv.currentReceiver = prevThisExpr;
			checkAccessEnabled = pv;
		}
	}

	public void addRepresentsAxioms(TypeSymbol clsym, Symbol varsym, JCTree that, JCExpression translatedSelector) {
        var check = pushBlock();
		addStat(comment(that, "Add represents translations for " + varsym + " " + currentEnv.stateLabel + " " + that, null));
		reps.add(0, varsym); // FIXME - as varsym can have different representations in different derived
								// classes
		boolean pv = checkAccessEnabled;
		checkAccessEnabled = false; // Do not check access in JML clauses

		// The basetype is the type of the class in which represents clauses occur.
		// For a static field (selector is null) we just use the owner, since there is
		// no inheritance.
		// For instance fields, we want the dynamic type of the selector, not the static
		// type
		// the selector is declared to be (clsym.type)
		Type basetype = translatedSelector == null ? varsym.owner.type : translatedSelector.type;

		// We use classDecl.type here in case we are in a derived class with a
		// represents clause;
		// clsym is the static class of the receiver, which may not have derived
		// represents clauses
		Type staticBasetype = clsym.type;
		if (classDecl != null) {
			if (classDecl.type.tsym.isSubClass(clsym, types))
				staticBasetype = classDecl.type;
		}
		try {
			if (rac) {
				Name mmName = names.fromString(Strings.modelFieldMethodPrefix + varsym.toString());
				java.util.List<Type> p = parents(staticBasetype, false);
				ListIterator<Type> iter = p.listIterator(p.size());
				while (iter.hasPrevious()) {
					JmlSpecs.TypeSpecs tyspecs = specs.getAttrSpecs((ClassSymbol) iter.previous().tsym);
					for (JmlTypeClauseDecl x : tyspecs.modelFieldMethods) {
						if (x.decl instanceof JmlMethodDecl) {
							JmlMethodDecl md = (JmlMethodDecl) x.decl;
							// THe DEFAULT Flag is used to indicate that the method is just the place-holder
							// method
							// created in JmlMemberEnter. It should be ignored as it is not a user supplied
							// method.
							if (md.name == mmName) { // && (md.mods.flags & Flags.DEFAULT) == 0) {
								JCMethodInvocation app = treeutils.makeMethodInvocation(that, translatedSelector,
										md.sym);
								result = eresult = app;
								treeutils.copyEndPosition(eresult, that);
								return;
							}
						}
					}
				}
				result = eresult = treeutils.makeSelect(that.pos, translatedSelector, varsym);
				Env<AttrContext> env = JmlEnter.instance(context).getEnv(clsym);
				// We don't warn if the problem is that we just have a binary class and
				// consequently no implementations of model fields
				// FIXME - need some tests for these options - not sure the binary ones have any
				// effect here???
				if (env != null && env.toplevel.sourcefile.getKind() != JavaFileObject.Kind.JML) { // FIXME - double check whether .jml files have Kind JML or OTHER?? 
					String opt = JmlOption.value(context, JmlOption.RAC_MISSING_MODEL_FIELD_REP_SOURCE);
					if ("skip".equals(opt)) {
						throw new NoModelMethod("No represents clause for model field " + varsym);
					} else {
						// already set the eresult
						if ("warn".equals(opt))
							utils.warning(that.pos, "jml.no.model.method.ignore",
									varsym.owner.getQualifiedName().toString() + "." + varsym.toString());
					}
				} else {
					String opt = JmlOption.value(context, JmlOption.RAC_MISSING_MODEL_FIELD_REP_BINARY);
					if ("skip".equals(opt)) {
						throw new NoModelMethod("No represents clause for model field " + varsym);
					} else {
						// already set the eresult
						if ("warn".equals(opt))
							utils.warning(that.pos, "jml.no.model.method.ignore",
									varsym.owner.getQualifiedName().toString() + "." + varsym.toString());
					}
				}
				return;
			}
			if (esc) {
				if (translatedSelector == null && varsym.owner instanceof ClassSymbol && utils.isJMLStatic(varsym)) {
					translatedSelector = treeutils.makeType(Position.NOPOS, varsym.owner.type);
				}
				java.util.List<Type> p = parents(basetype, false);
				ListIterator<Type> iter = p.listIterator(p.size());
				while (iter.hasPrevious()) {
					TypeSymbol ty = iter.previous().tsym;
					if (!(ty instanceof ClassSymbol)) continue; // FIXME - could be a TypeVariable
					TypeSpecs tspecs = specs.getAttrSpecs((ClassSymbol) ty);
					for (JmlTypeClause tc : tspecs.clauses) {
						if (tc.clauseType == representsClause) {
							JmlTypeClauseRepresents rep = (JmlTypeClauseRepresents) tc;
							// System.out.println("REP AXIOM " + translatedSelector + " " + rep);
							if (rep.ident instanceof JCIdent) {
								if (((JCIdent) rep.ident).sym != varsym)
									continue;
                                JCExpression copy = copy(rep.expression);
								if (rep.suchThat) {
									addAssume(that, Label.IMPLICIT_ASSUME, copy);
									result = eresult = treeutils.makeSelect(that.pos, translatedSelector, varsym);

								} else {
									// FIXME - This does not work if the model variable is used within a pure method
									// spec, because it ends up in the body of a constructed quantifier, but
									// localVariables is not used
									// if (localVariables.isEmpty()) {
									// addAssumeEqual(that,Label.IMPLICIT_ASSUME,
									// convertExpr(rep.ident),
									// convertExpr(rep.expression));
									// } else {
									JCExpression prev = currentEnv.currentReceiver;
									currentEnv.currentReceiver = translatedSelector;
									try {
										// JCIdent id = newTemp(convertExpr(rep.expression)); // New variable is
										// initialized - no assume statement needed
//                                        JCExpression e = treeutils.makeEquality(rep.pos,id,convertExpr(rep.expression));
//                                        addAssume(that,Label.IMPLICIT_ASSUME,e);
										// result = eresult = id;
									    //System.out.println("CONVERTING " + copy + " " + translatedSelector + " " + currentEnv.currentReceiver);
										JCExpression translatedExpr = convertExpr(copy);
										//System.out.println("CONVERTED REP " + translatedExpr);
										translatedExpr = addImplicitConversion(translatedExpr, rep.ident.type, translatedExpr);
										JCExpression sel = treeutils.makeSelect(that.pos, translatedSelector, varsym);
										JCExpression oldsel = sel;
										if (currentEnv.stateLabel != null) {
											JmlMethodInvocation ee = treeutils.makeJmlMethodInvocation(that.pos(),
													oldKind, oldsel.type, oldsel, M.at(that.pos).Ident(currentEnv.stateLabel));
											ee.labelProperties = labelPropertiesStore.get(currentEnv.stateLabel);
											oldsel = ee;
										}
										JCExpression e = treeutils.makeBinary(that.pos, JCTree.Tag.EQ, oldsel, translatedExpr);
                                        //System.out.println("CONVERTED ASSUMPTION " + e);
										// FIXME - should not issue this when in a qiuantified expression
										// FIXME - whjy is splitEAxpressions false?
										addAssume(that, Label.IMPLICIT_ASSUME, e); // FIXME - use a label aboiut
																					// REPRESENTS?
										result = eresult = sel;
									} finally {
										currentEnv.currentReceiver = prev;
									}
								}
							} else {
								log.error("jml.internal",
										"Kind of represents ID that is not implemented: " + rep.ident.getClass());
							}
							return;
						}
					}
				}
				result = eresult = treeutils.makeSelect(that.pos, translatedSelector, varsym);
				return;
			}
		} finally {
			addStat(comment(that, "End represents translations for " + varsym, null));
			reps.remove(varsym);
			checkAccessEnabled = pv;
            var block = popBlock(that,check);
            if (!block.stats.isEmpty()) {
                addStat(block);
//                if (currentEnv.label == null) {
//                    addStat(block);
//                } else {
//                    addToOldList(currentEnv.label, block);
//                }
            }
		}
		result = eresult = treeutils.makeSelect(that.pos, translatedSelector, varsym);
	}

//	protected void addInvariantsForVar(JCExpression thisExpr) {
//		assertInvariants(thisExpr, thisExpr);
//	}

    /** Returns true iff the declaration is explicitly or implicitly non_null */
    protected boolean addNullnessAllocationTypeConditionFormal(DiagnosticPosition d, VarSymbol sym,
            boolean instanceBeingConstructed, JCExpression condition) {
        boolean isNonNull = false;
        Symbol owner = sym.owner;
        var f = specs.getFormal(sym);
        if (f != null) {
            isNonNull =f.isNonNull;
        } else {
            if (owner instanceof MethodSymbol)
                owner = owner.owner;
            if (!sym.type.isPrimitive() && !jmltypes.isJmlType(sym.type) && !isDataGroup(sym.type)) {
                isNonNull = specs.isNonNullFormal(sym);
                //System.out.println("NULLNESS " + sym + " " + sym.type + " " + isNonNull + " " + owner);
            }
        }
        return addNullnessAllocationTypeCondition(d, sym, isNonNull, instanceBeingConstructed, true, condition);
    }

    /** Returns true iff the declaration is explicitly or implicitly non_null */
    protected boolean addNullnessAllocationTypeCondition2(DiagnosticPosition d, Symbol sym,
            boolean instanceBeingConstructed, JCExpression condition) {
        boolean isNonNull = true;
        Symbol owner = sym.owner;
        if (owner instanceof MethodSymbol)
            owner = owner.owner;
        if (!sym.type.isPrimitive() && !jmltypes.isJmlType(sym.type) && !isDataGroup(sym.type)) {
            isNonNull = specs.isNonNull(sym);
            //System.out.println("NULLNESS " + sym + " " + sym.type + " " + isNonNull);
        }

        return addNullnessAllocationTypeCondition(d, sym, isNonNull, instanceBeingConstructed, true, condition);
    }

	protected boolean addNullnessAllocationTypeCondition(DiagnosticPosition pos, Symbol sym,
			boolean instanceBeingConstructed) {
		boolean isNonNull = true;
		Symbol owner = sym.owner;
		if (owner instanceof MethodSymbol)
			owner = owner.owner;
		if (!utils.isJavaOrJmlPrimitiveType(sym.type)) {
			isNonNull = specs.isNonNull(sym);
		}
		return addNullnessAllocationTypeCondition(pos, sym, isNonNull, instanceBeingConstructed, true, null);
	}

	protected boolean addNullnessTypeCondition(DiagnosticPosition pos, Symbol sym, boolean instanceBeingConstructed) {
		boolean isNonNull = true;
		Symbol owner = sym.owner;
		if (owner instanceof MethodSymbol)
			owner = owner.owner;
		if (!utils.isJavaOrJmlPrimitiveType(sym.type)) {
			isNonNull = specs.isNonNull(sym);
		}
		return addNullnessAllocationTypeCondition(pos, sym, isNonNull, instanceBeingConstructed, false, null);
	}

	/** Returns true iff the declaration is explicitly or implicitly non_null */
	protected boolean addNullnessAllocationTypeCondition(DiagnosticPosition pos, Symbol sym, boolean isNonNull,
			boolean instanceBeingConstructed, boolean allocCheck, JCExpression condition) {
		int p = pos == null ? Position.NOPOS : pos.getPreferredPosition();
		JCExpression id;
		if (isDataGroup(sym.type)) return false;
		if (sym.owner instanceof MethodSymbol || sym.owner == null) {
			// Local variable
			id = treeutils.makeIdent(p, sym);
		} else if (utils.isJMLStatic(sym)) {
			// static field
			JCExpression etype = treeutils.makeType(p, sym.owner.type);
			id = treeutils.makeSelect(p, etype, sym);
		} else {
			// instance field
			id = treeutils.makeSelect(p, currentEnv.currentReceiver, sym);
		}
		return addNullnessAllocationTypeConditionId(id, pos, sym, isNonNull, instanceBeingConstructed, allocCheck, condition);
	}

	/** Returns true iff the declaration is explicitly or implicitly non_null */
	protected boolean addNullnessAllocationTypeConditionId(JCExpression id, DiagnosticPosition pos, Symbol sym,
			boolean isNonNull, boolean instanceBeingConstructed, boolean allocCheck, JCExpression condition) {
		if (isDataGroup(sym.type)) return false;
		// if (utils.isPrimitiveType(sym.type)) return false;
		if (pos == null) pos = id;
		int p = pos.getPreferredPosition();
		boolean nnull = true;
		if (!utils.isJavaOrJmlPrimitiveType(sym.type)) {
			// e2 : id.isAlloc
			// JCExpression e2 = treeutils.makeSelect(p, convertCopy(id), isAllocSym);
			JCExpression e2 = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.makeSelect(p, copy(id), allocSym),
					treeutils.makeIntLiteral(p, allocCounter));

			Symbol owner = sym.owner;
			if (owner instanceof MethodSymbol) owner = owner.owner;
			boolean nn = isNonNull && !instanceBeingConstructed;
			nnull = nn;
			if (nn) {
				// assume id != null
				addAssume(pos, Label.NULL_CHECK, treeutils.makeImpliesSimp(id, condition, treeutils.makeNotNull(p, copy(id))));
				// assume id.isAlloc
				if (allocCheck) addAssume(pos, Label.IMPLICIT_ASSUME, e2);
			} else if (allocCheck) {
				JCExpression e1 = treeutils.makeEqObject(p, id, treeutils.makeNullLiteral(p));
				// assume id == null || id._alloc__ <= allocCounter
				// addTraceableComment(e2);
				addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeOr(p, e1, e2));
			}

			// assume type information
			// e3: id == null || ( \typeof(id) <: \type(d.type) && id instanceof
			// \erasure('d.type')))
			JCExpression e3;
			if (utils.isJavaOrJmlPrimitiveType(sym.type) || (sym.type.getTag() == TypeTag.ARRAY
					&& ((Type.ArrayType) sym.type).getComponentType().isPrimitive())) {
				e3 = treeutils.makeDynamicTypeEquality(pos, copy(id), sym.type);
				JCStatement s = addAssume(pos, Label.IMPLICIT_ASSUME, e3);
				addTraceableComment(s);
			} else if (sym.type.getTag() == TypeTag.ARRAY) {
				Type compType = ((Type.ArrayType) sym.type).getComponentType();
                if (utils.isJavaOrJmlPrimitiveType(compType)) {
                    e3 = treeutils.makeDynamicTypeEquality(pos, copy(id), sym.type);
                } else {
                    e3 = treeutils.makeDynamicTypeInEquality(pos, copy(id), sym.type);
                    if (specs.isNonNull(compType, (ClassSymbol) enclosingClass)) {
						JCExpression e4 = wrapTranslatedNonnullelements(id, copy(id));
						e3 = treeutils.makeAnd(pos, e3, e4);
					}
				}
				JCStatement s = addAssume(pos, Label.IMPLICIT_ASSUME, e3);
				addTraceableComment(s);

				// FIXME - this should be in a recursive loop. Does it need nullness and
				// allocation checks?
				JCExpression typeofId = treeutils.makeTypeof(id);
				if (utils.isJavaOrJmlPrimitiveType(compType)) {
					e3 = treeutils.makeDynamicTypeEquality(pos, copy(typeofId), compType);
				} else {
					e3 = treeutils.makeDynamicTypeEquality(pos, copy(typeofId), compType);
				}
			} else {
				e3 = null;
				for (Type t : parents(sym.type.tsym.type, false)) { // OK - no enclsoing types
					if (t == null) {
						System.out.println("NULL PARENT " + sym + " " + sym.type.tsym.type);
						for (Type tt : parents(sym.type.tsym.type, false))
							System.out.println("    PARENTS " + tt);
					}
					try {
						JCExpression ee3 = treeutils.makeDynamicTypeInEquality(pos, copy(id), t);
						e3 = e3 == null ? ee3 : treeutils.makeAnd(ee3.pos, e3, ee3);
					} catch (AssertionError e) {
						System.out.println("NULL PARENT " + sym + " " + sym.type.tsym.type);
						for (Type tt : parents(sym.type.tsym.type, false))
							System.out.println("    PARENTS " + tt + " " + tt.getTag() + " " + tt.getClass());
					}
				}
				JCStatement s = addAssume(pos, Label.IMPLICIT_ASSUME, e3);
				addTraceableComment(s);
			}
			if (sym.type.getTag() == TypeTag.ARRAY) {
				JCExpression n = treeutils.makeNotNull(p, copy(id));
				JCExpression e = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol, treeutils.zero,
						treeutils.makeArrayLength(p, copy(id)));
				JCStatement s = addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeImplies(p, n, e));
				addTraceableComment(s);
				e = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeArrayLength(p, copy(id)),
						treeutils.makeIntLiteral(pos, Integer.MAX_VALUE));
				s = addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeImplies(p, n, e));
				addTraceableComment(s);
			}
		} else if (sym.type.isPrimitive()) {
			TypeTag tag = sym.type.getTag();
			JCExpression lo = null, hi = null;
			if (tag == TypeTag.INT) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeLit(p, syms.intType, Integer.MIN_VALUE), copy(id));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol, copy(id),
						treeutils.makeLit(p, syms.intType, Integer.MAX_VALUE));
			} else if (tag == TypeTag.LONG) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.longleSymbol,
						treeutils.makeLit(p, syms.longType, Long.MIN_VALUE), copy(id));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.longleSymbol, copy(id),
						treeutils.makeLit(p, syms.longType, Long.MAX_VALUE));
			} else if (tag == TypeTag.SHORT) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeLit(p, syms.intType, (int) Short.MIN_VALUE),
						treeutils.makeTypeCast(pos, syms.intType, copy(id)));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeTypeCast(pos, syms.intType, copy(id)),
						treeutils.makeLit(p, syms.intType, (int) Short.MAX_VALUE));
			} else if (tag == TypeTag.BYTE) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeLit(p, syms.intType, (int) Byte.MIN_VALUE),
						treeutils.makeTypeCast(pos, syms.intType, copy(id)));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeTypeCast(pos, syms.intType, copy(id)),
						treeutils.makeLit(p, syms.intType, (int) Byte.MAX_VALUE));
			} else if (tag == TypeTag.CHAR) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeLit(p, syms.intType, (int) Character.MIN_VALUE),
						treeutils.makeTypeCast(pos, syms.intType, copy(id)));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeTypeCast(pos, syms.intType, copy(id)),
						treeutils.makeLit(p, syms.intType, (int) Character.MAX_VALUE));
			}
			if (lo != null) {
				JCStatement s = addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeAnd(p, lo, hi));
				addTraceableComment(s);
			}
		}
		return nnull;
	}

	protected boolean addNullnessTypeConditionId(JCExpression id, DiagnosticPosition pos, Symbol sym, boolean isNonNull,
			boolean instanceBeingConstructed) {
		int p = pos.getPreferredPosition();
		boolean nnull = true;
		if (!utils.isJavaOrJmlPrimitiveType(sym.type) && !isDataGroup(sym.type)) {

			Symbol owner = sym.owner;
			if (owner instanceof MethodSymbol)
				owner = owner.owner;
			boolean nn = isNonNull && !instanceBeingConstructed;
			nnull = nn;
			if (nn) {
				// assume id != null
				addAssume(pos, Label.NULL_CHECK, treeutils.makeNotNull(p, copy(id)));
			}

			// assume type information
			// e3: id == null || ( \typeof(id) <: \type(d.type) && id instanceof
			// \erasure('d.type')))
			JCExpression e3;
			if (utils.isJavaOrJmlPrimitiveType(sym.type) || (sym.type.getTag() == TypeTag.ARRAY
					&& ((Type.ArrayType) sym.type).getComponentType().isPrimitive())) {
				e3 = treeutils.makeDynamicTypeEquality(pos, copy(id), sym.type);
				JCStatement s = addAssume(pos, Label.IMPLICIT_ASSUME, e3);
				addTraceableComment(s);
			} else if (sym.type.getTag() == TypeTag.ARRAY) {
				Type compType = ((Type.ArrayType) sym.type).getComponentType();
				if (utils.isJavaOrJmlPrimitiveType(compType)) {
					e3 = treeutils.makeDynamicTypeEquality(pos, copy(id), sym.type);
				} else {
					e3 = treeutils.makeDynamicTypeInEquality(pos, copy(id), sym.type);
				}
				JCStatement s = addAssume(pos, Label.IMPLICIT_ASSUME, e3);
				addTraceableComment(s);

				// FIXME - this should be in a recursive loop. Does it need nullness and
				// allocation checks?
				JCExpression typeofId = treeutils.makeTypeof(id);
				if (utils.isJavaOrJmlPrimitiveType(compType)) {
					e3 = treeutils.makeDynamicTypeEquality(pos, copy(typeofId), compType);
				} else {
					e3 = treeutils.makeDynamicTypeEquality(pos, copy(typeofId), compType);
				}
			} else {
				e3 = null;
				for (Type t : parents(sym.type.tsym.type, false)) { // OK - no enclsoing types
					JCExpression ee3 = treeutils.makeNonNullDynamicTypeInEquality(pos, copy(id), t);
					e3 = e3 == null ? ee3 : treeutils.makeAnd(ee3.pos, e3, ee3);
				}
				if (!nnull) {
					JCExpression ee = treeutils.makeEqNull(p, copy(id));
					e3 = treeutils.makeOr(pos, ee, e3);
				}
				JCStatement s = addAssume(pos, Label.IMPLICIT_ASSUME, e3);
				addTraceableComment(s);
			}
		} else {
			TypeTag tag = sym.type.getTag();
			JCExpression lo = null, hi = null;
			if (tag == TypeTag.INT) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeLit(p, syms.intType, Integer.MIN_VALUE), copy(id));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol, copy(id),
						treeutils.makeLit(p, syms.intType, Integer.MAX_VALUE));
			} else if (tag == TypeTag.LONG) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.longleSymbol,
						treeutils.makeLit(p, syms.intType, Long.MIN_VALUE), copy(id));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.longleSymbol, copy(id),
						treeutils.makeLit(p, syms.intType, Long.MAX_VALUE));
			} else if (tag == TypeTag.SHORT) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeLit(p, syms.intType, (int) Short.MIN_VALUE), copy(id));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol, copy(id),
						treeutils.makeLit(p, syms.intType, (int) Short.MAX_VALUE));
			} else if (tag == TypeTag.BYTE) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeLit(p, syms.intType, (int) Byte.MIN_VALUE), copy(id));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol, copy(id),
						treeutils.makeLit(p, syms.intType, (int) Byte.MAX_VALUE));
			} else if (tag == TypeTag.CHAR) {
				lo = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.makeLit(p, syms.intType, (int) Character.MIN_VALUE), copy(id));
				hi = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol, copy(id),
						treeutils.makeLit(p, syms.intType, (int) Character.MAX_VALUE));
			}
			if (lo != null) {
				JCStatement s = addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeAnd(p, lo, hi));
				addTraceableComment(s);
			}
		}
		return nnull;
	}

	/** Add all axioms from listed classes and their parents */
	public void addForClasses(java.util.Collection<ClassSymbol> classes, IClassOp op) {
		Set<ClassSymbol> done = new HashSet<ClassSymbol>();
		for (ClassSymbol csym : classes) {
			for (ClassSymbol cs : utils.parents(csym, true)) {
				if (done.add(cs))
					op.classOp(cs);
			}
		}
		done.clear();
	}

	boolean addingAxioms = false;

	/** Add all axioms from this specific class */
	protected void addClassAxioms(ClassSymbol csym) {
		if (!addAxioms(heapCount, csym))
			return;
		boolean prevAddingAxioms = addingAxioms;
		addingAxioms = true;
		try {
			JmlSpecs.TypeSpecs tspecs = specs.getAttrSpecs(csym);
			if (tspecs == null)
				return; // FIXME - why might this happen - see racnew.testElemtype & Cloneable
			for (JmlTypeClause clause : tspecs.clauses) {
				DiagnosticPosition cpos = clause;
				try {
					// Note: axioms have no modifiers but nonetheless must always be effectively
					// static
					if (clause.clauseType == axiomClause) {
						if (!classDecl.sym.isEnum() || !methodDecl.sym.isConstructor()
								|| (clause.modifiers.flags & Flags.ENUM) == 0) {
							addStat(comment(clause));
							JmlTypeClauseExpr t = (JmlTypeClauseExpr) clause;
							JCExpression e = convertJML(t.expression);
							addAssume(cpos, Label.AXIOM, e, cpos, clause.source);
						}
					}
				} catch (NoModelMethod e) {
					// FIXME - what to do.
				} catch (JmlNotImplementedException e) {
					notImplemented(clause.keyword + " clause containing ", e, clause.source());
				} catch (Exception e) {
				    e.printStackTrace(System.out);
					// FIXME - what to do -
				}
			}
			int pos = 0;
			if (false && csym.isEnum()) { // FIXME - these are already added in the parser?
				ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
				JCVariableDecl fdecl = newTempDecl(tspecs.specDecl, csym.type);
				JCIdent fid = treeutils.makeIdent(pos, fdecl.sym);
				JCExpression or = treeutils.makeEqNull(pos, fid);
				JCExpression ort = null;
				JCIdent tid = treeutils.makeIdent(pos, "this", csym.type);
				tid.sym.owner = csym;
				for (Symbol s : csym.getEnclosedElements()) {

					if (s instanceof VarSymbol && s.isEnum()) {
						JCIdent id = treeutils.makeIdent(pos, csym);
						JCFieldAccess fa = treeutils.makeSelect(pos, id, s);
						fa = treeutils.makeSelect(pos, fa, allocSym);
						JCExpression bin = treeutils.makeBinary(pos, JCTree.Tag.LE, fa, treeutils.zero);
						addAssume(tspecs.specDecl, Label.AXIOM, bin, null, null);
						id = treeutils.makeIdent(pos, csym);
						fa = treeutils.makeSelect(pos, id, s);
						newargs.add(fa);
						bin = treeutils.makeBinary(pos, JCTree.Tag.EQ, fid, fa);
						or = or == null ? bin : treeutils.makeBitOr(pos, or, bin);
						bin = treeutils.makeBinary(pos, JCTree.Tag.EQ, tid, fa);
						ort = ort == null ? bin : treeutils.makeBitOr(pos, ort, bin);
					}
				}
				newargs.add(treeutils.nullLit);
				JCExpression dist = M.at(pos).JmlMethodInvocation(distinctKind, newargs.toList());
				addAssume(tspecs.specDecl, Label.AXIOM, dist, null, null);
				or = M.at(pos).JmlQuantifiedExpr(qforallKind, List.<JCVariableDecl>of(fdecl), treeutils.trueLit, or);
				addAssume(tspecs.specDecl, Label.AXIOM, or, null, null);
				tspecs.clauses = tspecs.clauses.append(M.JmlTypeClauseExpr(M.Modifiers(Flags.PUBLIC | Flags.FINAL),
						TypeExprClauseExtension.invariantID, TypeExprClauseExtension.invariantClause, ort));
			}
		} finally {
			addingAxioms = prevAddingAxioms;
		}
	}

	protected void addLocalVar(JCIdent id) {
		ListBuffer<JCStatement> ch = pushBlock();
		addNullnessTypeCondition(id, id.sym, false);
		JCBlock bl = popBlock(id, ch);
		discoveredFields.stats = discoveredFields.stats.append(bl);
	}

	protected void addFinalStaticField(JCFieldAccess convertedfa) {
		// FIXME - check visibility? already checked?
		JmlStatementExpr st = null;
		DiagnosticPosition pos = convertedfa;
		int p = pos.getPreferredPosition();
		if (!(convertedfa.sym instanceof VarSymbol))
			return;
		VarSymbol vsym = ((VarSymbol) convertedfa.sym);
		Object value = vsym.getConstValue();

		//
		if (discoveredFields != null)
			discoveredFields.stats.appendList(collectStats(() -> {
				addNullnessAllocationTypeCondition(convertedfa, vsym, false);
			}));

		FieldSpecs fspecs = specs.getAttrSpecs(vsym);
//        if (fspecs != null && fspecs.decl.init != null) {
//        	JCExpression e = fspecs.decl.init;
//        	if (e instanceof JCLiteral) value = ((JCLiteral)e).value;
//        }

		if (value != null) {
			JCExpression lit = treeutils.makeLit(p, convertedfa.type, value);
			JCExpression eq = treeutils.makeEquality(p, convertedfa, lit);
			st = treeutils.makeAssume(pos, Label.IMPLICIT_ASSUME, eq);
			st.source = log.currentSourceFile(); // FIXME - or the source file where it is declared?
			st.associatedPos = p;
			st.associatedSource = null;
			st.optionalExpression = null;
		} else {
			if (JmlOption.isOption(context, JmlOption.STATIC_INIT_WARNING)) {
				if (!hasStaticInitializer((ClassSymbol) convertedfa.sym.owner) && !convertedfa.sym.isEnum()
						&& (convertedfa.sym.owner != attr.datagroupClass)
						&& (convertedfa.sym.flags() & Flags.PRIVATE) == 0) {
					utils.warning(convertedfa, "jml.message",
							"Use a static_initializer clause to specify the values of static final fields: "
									+ utils.qualifiedName(convertedfa.sym));
					if (utils.jmlverbose >= Utils.JMLVERBOSE)
						utils.note(convertedfa, "jml.message",
								"Warned about a non-constant initialized static final field: " + st.toString());
				}
			}
			discoveredFields.stats = discoveredFields.stats.append(st);
		}
		if (st == null) {
			xx: {
				Symbol owner = convertedfa.sym.owner;
				if (!(owner instanceof ClassSymbol))
					break xx;
				if (fspecs == null)
					break xx;
				JCExpression init = fspecs.decl.init;
				if (init == null)
					break xx;
				if (vsym.type instanceof Type.ArrayType && init instanceof JCTree.JCNewArray) {
					JCNewArray arr = (JCNewArray) init;
					if (arr.elems != null) {
						JCExpression lenexpr = treeutils.makeLength(convertedfa, convertedfa);
						JCExpression len = treeutils.makeIntLiteral(init, arr.elems.length());
						JCExpression eq = treeutils.makeEquality(init.getPreferredPosition(), lenexpr, len);
						// FIXME - could add information about nexted dimensions and about elements
						st = treeutils.makeAssume(init, Label.IMPLICIT_ASSUME, eq);
						st.source = log.currentSourceFile(); // FIXME - or the source file where it is declared?
						st.associatedPos = p;
						st.associatedSource = null;
						st.optionalExpression = null;
					}
				}
			}
		}
		if (st != null) {
			// FIXME - this repeatedly copies the list
			discoveredFields.stats = discoveredFields.stats.append(st);
			if (utils.jmlverbose >= Utils.JMLVERBOSE)
				utils.note(convertedfa, "jml.message", "Added an initalized static final field: " + st.toString());
		}

		return;
	}

	public boolean hasStaticInitializer(JmlClassDecl decl) {
		JmlSpecs.TypeSpecs ts = specs.getAttrSpecs(decl.sym);
		return ts.staticInitializerSpec != null;
	}

	public boolean hasStaticInitializer(ClassSymbol sym) {
		JmlSpecs.TypeSpecs ts = specs.getAttrSpecs(sym);
		return ts.staticInitializerSpec != null;
	}

	public boolean hasModelProgram(java.util.List<Pair<MethodSymbol, Type>> overridden) {
		for (Pair<MethodSymbol, Type> p : overridden) {
			JmlMethodSpecs mspecs = specs.getDenestedSpecs(p.first);
			if (mspecs != null)
				for (JmlSpecificationCase cs : mspecs.cases) {
					if (cs.code && p.first != methodDecl.sym)
						continue;
					if (cs.block != null)
						return true;
				}
		}
		return false;
	}

	/** Add all constant final static fields from this specific class */
	protected void addFinalStaticFields(ClassSymbol csym) {
		boolean isEnumConstructor = csym.isEnum() && methodDecl.sym.owner == csym && methodDecl.sym.isConstructor();
		if (isEnumConstructor)
			return;
		Env<AttrContext> enva = Enter.instance(context).getEnv(csym);
		if (enva == null)
			return;
		JmlClassDecl decl = (JmlClassDecl) enva.tree;
		if (decl == null)
			return;
		for (JCTree def : decl.defs) {
			if (def instanceof JmlVariableDecl) {
				JmlVariableDecl vd = (JmlVariableDecl) def;
				// FIXME - in testForeach2a1 vd.sym is null
				if (!utils.jmlvisible(vd.sym, methodDecl.sym.owner, csym, vd.mods.flags, methodDecl.mods.flags))
					continue;

				if (utils.isJMLStatic(vd.mods, decl.sym) && isFinal(vd.sym)) {
					alreadyDiscoveredFields.add(vd.sym);
					Symbol sym = vd.sym;
					if (sym.owner instanceof ClassSymbol) {
						JCFieldAccess newfa = treeutils.makeSelect(def.pos, treeutils.makeType(def.pos, sym.owner.type),
								sym);
						addFinalStaticField(newfa);
					}
//                    JCExpression e = vd.init;
//                    if (e != null) {
//                        Object constValue = e.type.constValue();
//                        if (constValue == null) continue;
//                        JCExpression lit = treeutils.makeLit(e.pos, e.type, constValue);
//                        lit = addImplicitConversion(e,vd.type,lit);
//                        addStat(treeutils.makeVariableDecl(vd.sym, lit));
//                        // Note - with the above declaration and initialization, BasicBlocker2 adds an assumption
////                        JCExpression expr = treeutils.makeEquality(vd.pos, treeutils.makeIdent(vd.pos,vd.sym), lit);
////                        addAssume(vd,Label.IMPLICIT_ASSUME,convertExpr(expr));
////                        vd.init = lit;
////                        vd.sym.owner = null; // This null makes the identifier not subject to havoc
////                        addStat(vd);
//                    }
				}
			}
		}
		JmlSpecs.TypeSpecs tspecs = specs.getAttrSpecs(csym);
		if (tspecs == null)
			return; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

		/*
		 * for (JmlTypeClause clause : tspecs.decls) { try { if (!(clause instanceof
		 * JmlTypeClauseDecl)) continue; JmlTypeClauseDecl tdecl =
		 * (JmlTypeClauseDecl)clause; if (!(tdecl.decl instanceof JmlVariableDecl))
		 * continue; JmlVariableDecl vdecl = (JmlVariableDecl)tdecl.decl; if (vdecl.init
		 * == null) continue; if (!utils.jmlvisible(null, methodDecl.sym.owner, csym,
		 * vdecl.mods.flags, methodDecl.mods.flags)) continue; if ((vdecl.sym.flags() &
		 * (Flags.FINAL | Flags.STATIC)) != (Flags.FINAL|Flags.STATIC)) continue; Object
		 * constValue = vdecl.init.type.constValue(); if (constValue == null) continue;
		 * addStat(vdecl); } catch (JmlNotImplementedException e) {
		 * notImplemented(clause.keyword + " clause containing ", e, clause.source()); }
		 * }
		 */
	}

	protected void assumeStaticInvariants(ClassSymbol csym) {
		JmlSpecs.TypeSpecs tspecs = specs.getAttrSpecs(csym);
		if (tspecs == null) {
			utils.error("jml.internal", "Null class specs for " + csym);
			return; // FIXME - why might this happen - see racnew.testElemtype & Cloneable
		}
		if (startInvariants(csym, methodDecl))
			return;
		try {
			for (JmlTypeClause t : tspecs.clauses) {
				if (t.clauseType != invariantClause)
					continue;
				if (!utils.isJMLStatic(t.modifiers, csym))
					continue;
				if (!utils.jmlvisible(null, methodDecl.sym.owner, csym, t.modifiers.flags, methodDecl.mods.flags))
					continue;
				addAssume(methodDecl, Label.INVARIANT_ENTRANCE,
						convertJML(copy((JmlTypeClauseExpr) t).expression), // FIXME - really need the
																					// convertCopy?
						t, t.source(), utils.qualifiedMethodSig(methodDecl.sym));
			}
		} finally {
			endInvariants(csym);
		}
		for (Symbol ccsym : csym.getEnclosedElements()) {
			if (ccsym instanceof ClassSymbol) {
				assumeStaticInvariants((ClassSymbol) ccsym);
			}
		}
	}

	public interface IClassOp {
		public void classOp(ClassSymbol csym);
	}

	public final IClassOp axiomAdder = new IClassOp() {
		public void classOp(ClassSymbol cs) {
			addClassAxioms(cs);
		}
	};
	public final IClassOp finalStaticFieldAdder = new IClassOp() {
		public void classOp(ClassSymbol cs) {
			addFinalStaticFields(cs);
		}
	};
	public final IClassOp staticInitializerAdder = new IClassOp() {
		public void classOp(ClassSymbol cs) {
			addStaticInitialization(cs);
		}
	};
	public final IClassOp staticInvariantAdder = new IClassOp() {
		public void classOp(ClassSymbol cs) {
			assumeStaticInvariants(cs);
		}
	};

	protected void addFormals(ListBuffer<JCStatement> initialStats) {
		pushBlock(initialStats);
		/*
		 * Declare new variables, initialized to the values of the formal parameters, so
		 * that they can be referred to in postconditions and other invariant checks.
		 */
		addStat(comment(methodDecl, "Declare formals", null));
		for (JCVariableDecl d : methodDecl.params) {
			JCVariableDecl dd = treeutils.makeVarDefWithSym(d.sym, null);
			addStat(dd);
//            dd.pos = d.pos;
//            if (esc) {
//                addNullnessAllocationTypeCondition2(dd,dd.sym,false,null);
//            }

//            dd = treeutils.makeVarDef(d.type,M.Name(Strings.formalPrefix+d.name.toString()),  
//                    d.sym.owner, M.Ident(d.sym));
//            dd.pos = dd.sym.pos = d.sym.pos;
//            preparams.put(d.sym,M.at(dd).Ident(dd.sym));
//            if (esc) dd.sym.owner = null; // FIXME - can get these straight from the labelmaps - do we need this?
//            addStat(dd);
//            // Declare allocation time of formals if they are not null
//            if (esc && !d.type.isPrimitive()) {
//                JCIdent id = treeutils.makeIdent(d.pos, d.sym);
//                JCExpression nn = treeutils.makeEqNull(d.pos,id);
//                JCExpression fa = M.at(d.pos).Select(id, allocSym);
//                fa = treeutils.makeBinary(d,JCTree.Tag.LE, fa, treeutils.makeIntLiteral(d,0));
//                fa = treeutils.makeOr(d.pos, nn, fa);
//                addStat(treeutils.makeAssume(d, Label.IMPLICIT_ASSUME, fa ));
//            }
		}

		popBlock();
	}

	protected void addFeasibility(JmlMethodDecl methodDecl, ListBuffer<JCStatement> initialStatements) {
		JmlSpecs.MethodSpecs mspecs = specs.getAttrSpecs(methodDecl.sym);
		if (mspecs.cases.feasible == null)
			return;
		ListBuffer<JCStatement> check = pushBlock();
		addStat(comment(methodDecl, "Feasibility assumptions", null));
		for (JmlMethodClause cl : mspecs.cases.feasible) {
			if (cl.clauseKind == requiresClauseKind) {
				JCExpression e = convertJML(((JmlMethodClauseExpr) cl).expression);
				addAssume(cl, Label.IMPLICIT_ASSUME, e);
			} else { // FIXME - should implement old clauses
				utils.warning(cl, "jml.message", "Ignoring clauses other than requires in feasibility section");
			}
		}
		DiagnosticPosition p = mspecs.cases;
		JCBlock bl = popBlock(p, check);
		JCIdent id = treeutils.makeIdent(p, feasCheckSym);
		JCExpression bin = treeutils.makeBinary(p, JCTree.Tag.NE, treeutils.intneqSymbol, id,
				treeutils.makeIntLiteral(p, 0));
		pushBlock(initialStatements);
		bin = newTempIfNeeded(bin);
		popBlock();
		JCStatement st = M.at(p).If(bin, bl, null);
		initialStatements.add(st);
	}
	
	// FIXME - can we unite the next two methods

	// Used only in addPre... and addPostConditions
	public Map<Object, JCExpression> specParamsToActuals(JmlMethodSpecs denestedSpecs, JCMethodDecl targetMethodDecl,
			MethodSymbol javaMethodSym) {
		var paramActuals = new HashMap<Object, JCExpression>();
		if (denestedSpecs.decl != null) {
			Iterator<VarSymbol> iter = denestedSpecs.decl.sym.params.iterator();
			for (JCVariableDecl dp : targetMethodDecl.params) {
			    if (!iter.hasNext()) {
			        System.out.println("MISMATCHED ARGUMENT LISTS: " + javaMethodSym + " : " + methodDecl.params + " VS " + denestedSpecs.decl.sym.params);
			        Utils.dumpStack();
			        break;
			    }
				VarSymbol specSym = iter.next();
				//System.out.println("MAPPING " + specSym + " " + specSym.hashCode() + " TO " + dp.sym + " " + dp.hashCode());
				paramActuals.put(specSym, treeutils.makeIdent(dp.pos, dp.sym));
			}
		} else { // denested specs may not have a declaration if the method is automatically
					// generated (e.g. default constructor, Enum.values() etc.)
			Iterator<VarSymbol> iter = javaMethodSym.params.iterator();
			for (JCVariableDecl dp : targetMethodDecl.params) {
                if (!iter.hasNext()) {
                  System.out.println("MISMATCHED ARGUMENT LISTS: " + javaMethodSym + " : " + methodDecl.params + " VS " + denestedSpecs.decl.sym.params);
                  Utils.dumpStack();
                    break;
                }
				VarSymbol newsym = iter.next();
				// System.out.println("MAPPINGB " + newsym + " " + newsym.hashCode() + " TO " + dp.sym + " " + dp.hashCode());
				paramActuals.put(newsym, treeutils.makeIdent(dp.pos, dp.sym));
			}
		}
		return paramActuals;
	}
	
//	// Adds to paramActuals
//	public Map<Object, JCExpression> mapFormals(JCMethodDecl to, JCMethodDecl from) {
//		//System.out.println("MAPFORMALS " + to.sym + " FROM " + from.sym);
//		if (to.sym == from.sym)
//			return paramActuals;
//		var fromIter = from.params.iterator();
//		var toIter = to.params.iterator();
//		var newMap = paramActuals == null ? new HashMap<Object, JCExpression>() : new HashMap<>(paramActuals);
//		while (fromIter.hasNext() && toIter.hasNext()) {
//			var fromSym = fromIter.next().sym;
//			var toDecl = toIter.next();
//			var toSym = toDecl.sym;
//			newMap.put(fromSym, M.at(toDecl.pos).Ident(toSym));
//		}
//		if (fromIter.hasNext() || toIter.hasNext()) {
//			// ERROR - mis matched lengths
//		}
//		var oldMap = paramActuals;
//		paramActuals = newMap;
//		return oldMap;
//	}

	public static record Info(MethodSymbol parentMethodSymbol, JmlSpecificationCase specCase, JmlMethodDecl decl) {}

	public class SpecCaseIterable implements Iterable<Info> {
		MethodSymbol methodSymbol;
        boolean computeParamActuals;
		public SpecCaseIterable(MethodSymbol methodSymbol, boolean computeParamActuals) {
			this.methodSymbol = methodSymbol;
            this.computeParamActuals = computeParamActuals;
		}
		@Override
		public SpecCaseIterator iterator() { return new SpecCaseIterator(methodSymbol,computeParamActuals); }
	}
	
	public class SpecCaseIterator implements Iterator<Info> {
		
		Iterator<MethodSymbol> methodIterator;
		Iterator<JmlSpecificationCase> specCaseIterator = null;
		
		MethodSymbol methodSymbol;
		MethodSymbol parentMethodSymbol;
		JmlMethodDecl specDecl;
		JmlSpecificationCase specCase;
		Map<Object,JCExpression> paramActuals;
		boolean computeParamActuals;
		JavaFileObject previousFile;
		
		public SpecCaseIterator(MethodSymbol methodSymbol, boolean computeParamActuals) {
			//System.out.println("CREATING ITERATOR " + methodSymbol);
			this.methodSymbol = methodSymbol;
			this.computeParamActuals = computeParamActuals;
			methodIterator = utils.parents(methodSymbol,true).iterator();
			parentMethodSymbol = null;
			previousFile = log.currentSourceFile();
			//System.out.println("DONE ITERATOR " + methodSymbol);
		}
		
		public void cleanup() {
			log.useSource(previousFile);
		}

		@Override
		public boolean hasNext() {
			while (true) {
				if (specCaseIterator == null) {
					if (!methodIterator.hasNext()) {
						cleanup();
						//System.out.println("HASNEXT-FALSE " + methodSymbol);
						return false;
					}
					parentMethodSymbol = methodIterator.next();
					if (parentMethodSymbol.params == null) continue; // FIXME - we should do something better? or does this mean binary with no specs?
					JmlMethodSpecs denestedSpecs = JmlSpecs.instance(context).getDenestedSpecs(parentMethodSymbol);
					specDecl = denestedSpecs.decl;
					specCaseIterator = denestedSpecs.cases.iterator();
					//if (computeParamActuals) paramActuals = specParamsToActuals(denestedSpecs, methodDecl, parentMethodSymbol);
				}
				if (!specCaseIterator.hasNext()) {
					specCaseIterator = null;
					continue;
				}
				specCase = specCaseIterator.next();
				if (!doSpecificationCase(methodDecl, methodSymbol, parentMethodSymbol, specCase)) continue;
				log.useSource(specCase.source());
				//System.out.println("HASNEXT-TRUE " + methodSymbol);
				return true;
			}
		}

		@Override
		public Info next() {
			//System.out.println("NEXT " + methodSymbol + " " + parentMethodSymbol + " " + specCase);
			return new Info(parentMethodSymbol,specCase,specDecl);
		}
		
		
//		for (MethodSymbol parentMethodSym : utils.parents(methodDecl.sym)) {
//			if (parentMethodSym.params == null)
//				continue; // FIXME - we should do something better? or does this mean binary with no
//							// specs?
//			JmlMethodSpecs denestedSpecs = JmlSpecs.instance(context).getDenestedSpecs(parentMethodSym);
//			// System.out.println("ADDPRE " + methodDecl.sym + " " + parentMethodSym.owner +
//			// " " + parentMethodSym + " # " + denestedSpecs);
//			if (denestedSpecs == null)
//				continue;
//			// denestedSpecs.decl.params.forEach(p -> System.out.println(" PARAM " + p.name
//			// + " " + p.type + " " + p.sym.name + " " + p.sym.type));
//			// denestedSpecs.decl.sym.params.forEach(p -> System.out.println(" PARAM-SYM " +
//			// p + " " + p.hashCode() + " " + p.name + " " + p.type));
//
//			// Set up the map from parameter symbol of the overridden method to
//			// corresponding parameter of the target method.
//			// We need this even if names have not changed, because the parameters
//			// will have been attributed with different symbols.
//			paramActuals = specParamsToActuals(denestedSpecs, methodDecl, parentMethodSym);
//			heapCount = preheapcount;
//			Map<JmlMethodClause, JCExpression> clauseIds = new HashMap<>();
//			elseExpression = treeutils.falseLit;
//			for (JmlSpecificationCase scase : denestedSpecs.cases) {
//				if (!doSpecificationCase(methodDecl, parentMethodSym, scase)) continue;
//				JavaFileObject prev = log.useSource(scase.source());
//
		
	}


	/** Computes and adds checks for all the pre and postcondition clauses. */
	// FIXME - review this
	protected void addPreConditions(ListBuffer<JCStatement> initialStats, ClassCollector collector,
			ListBuffer<Pair<JCExpression, JmlSource>> divergesExpressions) {

		JCMethodDecl methodDecl = this.methodDecl;
		int pos = methodDecl.pos;
		boolean isConstructor = methodDecl.sym.isConstructor();
		ListBuffer<JCStatement> check = pushBlock(initialStats);
		pushBlock(initialStats);
		changeState(methodDecl,null); // bumps heapCount // adds to currentStats
		popBlock();
		int preheapcount = heapCount;
		int savedheapcount = heapCount;
		try {

			{
				ListBuffer<JCStatement> ch = pushBlock();
				addStat(comment(methodDecl, "Invariants for discovered fields", null));
				discoveredFields = popBlock(methodDecl, ch);
				addStat(discoveredFields);
				alreadyDiscoveredFields.clear(); // FIXME - not going to work for nested method translations
			}

			// Assume all axioms of classes mentioned in the target method
			if (esc || infer) {
				addStat(comment(methodDecl, "Assume axioms", null));
				addForClasses(collector.classes, axiomAdder);
				if (isHelper(methodDecl.sym)) {
					addStat(comment(methodDecl, "Method is helper so not assuming static invariants", null));
				} else {
					addStat(comment(methodDecl, "Assume static invariants", null));
					addForClasses(collector.classes, staticInvariantAdder);
				}
				addStat(comment(methodDecl, "Assume static final constant fields", null));
				addForClasses(collector.classes, finalStaticFieldAdder);
				addStat(comment(methodDecl, "Assume static initialization", null));
				addForClasses(collector.classes, staticInitializerAdder);
				{
					addStat(comment(methodDecl.pos(), "Static initialization", log.currentSourceFile()));
					addStaticInitialization((ClassSymbol) methodDecl.sym.owner);
				}
			}

			// FIXME - include for rac also?
			if ((infer || esc)) {
				if (methodDecl.sym.isConstructor() || utils.isJMLStatic(methodDecl.sym)) {
					addStat(comment(methodDecl, "Assuming static initial state", null));
					assumeStaticInitialState(classDecl.sym);
				}
				if (!methodDecl.sym.isConstructor() && !utils.isJMLStatic(methodDecl.sym)) {
					// Add nullness, type, and allocation conditions for fields and inherited fields
					addStat(comment(methodDecl, "Assume field type, allocation, and nullness", null));
					addNullnessAndTypeConditionsForInheritedFields(classDecl.sym, isConstructor,
							currentEnv.currentReceiver == null);
				}

				// FIXME - this could be combined with populating preparams above
				// For the parameters of the method
				addStat(comment(methodDecl, "Assume parameter type, allocation, and nullness", null));
				boolean varargs = (methodDecl.sym.flags() & Flags.VARARGS) != 0;
				boolean isNonNull = true;
				for (JCVariableDecl d : methodDecl.params) {
					isNonNull = addNullnessAllocationTypeConditionFormal(d, d.sym, false, null);
				}
				if (varargs && !isNonNull) { // isNonNull is the nullness of the last parameter, so the varargs
												// parameter
					JCVariableDecl d = methodDecl.params.last();
					JCIdent id = treeutils.makeIdent(d.pos, d.sym);
					JCExpression nnex = treeutils.makeNeqObject(d.pos, id, treeutils.nullLit);
					addAssume(d.pos(), Label.IMPLICIT_ASSUME, nnex);
				}

				// FIXME - for the isConstructor case, it should be newly allocated
				if (isConstructor) {
				} else if (!utils.isJMLStatic(methodDecl.sym)) {
					// Assume that 'this' is allocated
					JCFieldAccess fa = treeutils.makeSelect(pos, copy(currentEnv.currentReceiver), isAllocSym);
					addAssume(methodDecl, Label.IMPLICIT_ASSUME, fa);

				}

			}

			if (!methodDecl.sym.isConstructor()) {
				assumeFieldInvariants(this.methodDecl, classDecl); // FIXME - do parent classes also?
			}

			// We collect the precondition evaluation in a separate list so that
			// we can wrap the evaluations in a try-catch block, in case there are
			// exceptions thrown
			ListBuffer<JCStatement> preStats = new ListBuffer<JCStatement>();
			currentStatements = preStats;

//        // Construct a condition, to be used later, that the method has not thrown an exception
//        DiagnosticPosition methodPos = methodDecl;
//        JCExpression noException = treeutils.makeEqObject(methodPos.getPreferredPosition(),
//                treeutils.makeIdent(methodPos.getPreferredPosition(), exceptionSym), treeutils.nullLit);

			// FIXME - what if the owning class is a TypeSymbol because it is a TypeVar
			TypeSymbol owner = (TypeSymbol) methodDecl.sym.owner;

			JCExpression receiver = utils.isJMLStatic(methodDecl.sym) ? null : currentEnv.currentReceiver;

			// Assuming invariants
            addStat(comment(methodDecl, "Adding instance invariants for method receiver " + methodDecl.sym.owner + "." + methodDecl.sym + " helper?: " + isHelper(methodDecl.sym), null));
            addInvariants(methodDecl, owner.type, receiver, currentStatements, true, methodDecl.sym.isConstructor(),
					false, isHelper(methodDecl.sym), false, true, Label.INVARIANT_ENTRANCE,
					utils.qualifiedMethodSig(methodDecl.sym));
            addStat(comment(methodDecl, "End instance invariants for method receiver " + methodDecl.sym.owner + "." + methodDecl.sym, null));
			// Assume invariants for the class of each parameter
			for (JCVariableDecl v : methodDecl.params) {
				// for (Symbol vsym: preparams.keySet()) {
				VarSymbol vsym = v.sym;
                addStat(comment(v, "Adding invariants for method parameter " + vsym, null));
				// JCIdent idd = preparams.get(vsym);
				if (utils.isNonExtPrimitiveType(vsym.type)) continue;
                if (utils.hasModifier(v.mods,Modifiers.HELPER)) continue;
				
				JCIdent idd = treeutils.makeIdent(v.pos, v.sym);
				// JCIdent d = preparams.get(vsym);
				if (isHelper(methodDecl.sym) && v.sym.type.tsym == methodDecl.sym.owner.type.tsym)
					continue;
				if (owner.type.tsym == vsym.type.tsym && methodDecl.sym.isConstructor()) {
					JCIdent id = treeutils.makeIdent(idd.pos, v.sym);
					addAssume(idd, Label.IMPLICIT_ASSUME, treeutils.makeNeqObject(idd.pos, id, currentEnv.currentReceiver));
				}
				JCIdent id = treeutils.makeIdent(idd.pos, v.sym);
				addInvariants(idd, idd.type, id, currentStatements, true, false, false, false, false, true,
						Label.INVARIANT_ENTRANCE,
						utils.qualifiedMethodSig(methodDecl.sym) + " (parameter " + idd.name + ")");
			}

			// Collect and check precondition

			java.util.List<JmlSpecificationCase> prelist = new LinkedList<>();
			int start_of_local_cases = 0;
			JCExpression savedThis = currentEnv.currentReceiver;
			currentEnv.currentReceiver = savedThis;
			JCExpression combinedPrecondition = null;
			JavaFileObject combinedPreconditionSource = null;
			addStat(comment(methodDecl, "Assume Preconditions", null));
			paramActuals_ = new HashMap<>();
			// Iterate over all methods that methodDecl overrides, collecting specs
			for (MethodSymbol parentMethodSym : utils.parents(methodDecl.sym,true)) {
			    if (parentMethodSym == methodDecl.sym) start_of_local_cases = prelist.size();
				if (parentMethodSym.params == null) continue; // FIXME - we should do something better? or does this mean binary with no specs?
				JmlMethodSpecs denestedSpecs = JmlSpecs.instance(context).getDenestedSpecs(parentMethodSym);
				//System.out.println("ADDPRE " + methodDecl.sym + " " + parentMethodSym.owner + " " + parentMethodSym + " # " + denestedSpecs);
				if (denestedSpecs == null) continue;
				// denestedSpecs.decl.params.forEach(p -> System.out.println(" PARAM " + p.name
				// + " " + p.type + " " + p.sym.name + " " + p.sym.type));
				// denestedSpecs.decl.sym.params.forEach(p -> System.out.println(" PARAM-SYM " +
				// p + " " + p.hashCode() + " " + p.name + " " + p.type));

				// Set up the map from parameter symbol of the overridden method to
				// corresponding parameter of the target method.
				// We need this even if names have not changed, because the parameters
				// will have been attributed with different symbols.
				//System.out.println("ADDD PRE FOR " + parentMethodSym);
				paramActuals_.putAll(specParamsToActuals(denestedSpecs, methodDecl, parentMethodSym));
				heapCount = preheapcount;
				Map<JmlMethodClause, JCExpression> clauseIds = new HashMap<>();
				elseExpression = treeutils.falseLit;
				for (JmlSpecificationCase scase : denestedSpecs.cases) {
				    //System.out.println("ITER " + parentMethodSym + " " + scase);
					if (!doSpecificationCase(methodDecl, methodDecl.sym, parentMethodSym, scase)) continue;
					
					for (JmlMethodClause clause: scase.clauses) {
					    //if (clause.clauseKind == invariantsClauseKind) System.out.println("HAVE INVS CLAUSE " + ((JmlMethodClauseInvariants)clause).expressions);
					}
                    //System.out.println("DOING " + parentMethodSym + " " + scase);
					JavaFileObject prev = log.useSource(scase.source());
					try {
						JCExpression preexpr = null;
						JCExpression diverges = null;
						JmlSource divergesPosition = scase;
						for (JmlMethodClause clause : scase.clauses) {
							IJmlClauseKind ct = clause.clauseKind;
							if (ct == MethodDeclClauseExtension.oldClause) {
								// NOTE: The name of the variable in the old clause is not changed or
								// unique-ified.
								// If the same name is used if different behaviors, as in this test, the names
								// will be the same,
								// though the symbol values will be different. The declarations will be in the
								// same scope in a
								// RAC translation, but this does not seem to cause any problem in RAC
								// code-generation.
								if (clauseIds.containsKey(clause))
									continue; // Don't reevaluate if we have nested specs
								for (JCVariableDecl decl : ((JmlMethodClauseDecl) clause).decls) {
									addTraceableComment(decl, clause.toString());
									Name name = names.fromString(
											decl.name.toString() + "__OLD_" + decl.pos + "_" + nextUnique());
									// JCVariableDecl newdecl = convertCopy(decl);
									JCVariableDecl newdecl = treeutils.makeDupDecl(decl, methodDecl.sym, name,
											clause.pos);
									if (!rac)
										newdecl.mods.flags |= Flags.FINAL;
									addStat(initialStats, newdecl);
									mapSymbols.put(decl.sym, newdecl.sym);
									JCIdent id = treeutils.makeIdent(clause.pos, newdecl.sym);
									ListBuffer<JCStatement> check2 = pushBlock();
									if (rac) {
										newdecl.init = treeutils.makeZeroEquivalentLit(decl.init.pos, decl.type);
									} else {
										addNullnessTypeCondition(id, id.sym, false);
									}
									alreadyDiscoveredFields.add(id.sym);
									if (decl.init != null) {
										JCExpression convertedInit = convertJML(decl.init);
										if (newdecl.sym.type.isReference() && specs.isNonNull(newdecl.sym)) {
											addAssert(decl.init, Label.UNDEFINED_NULL_INITIALIZATION,
													treeutils.makeNotNull(decl.init.pos, convertedInit));
										}
										pushArithMode();
										convertedInit = addImplicitConversion(decl.init, decl.type, convertedInit);
										popArithMode();
										if (rac) {
											JCExpressionStatement stat = treeutils.makeAssignStat(decl.init.pos, id,
													convertedInit);
											addStat(stat);
										} else {
											addAssume(clause, Label.PRECONDITION,
													treeutils.makeEquality(clause.pos, id, convertedInit));
										}
									}
									JCBlock bl = popBlock(clause, check2);
									if (preexpr == null) {
										addStat(bl);
									} else {
										addStat(M.at(clause).If(preexpr, bl, null));
									}
									// paramActuals.put(decl.sym,id);
									// preparams.put(decl.sym,id);
									saveMapping(decl, id);
									clauseIds.put(clause, id);
								}
							} else if (ct == divergesClauseKind) {
								divergesPosition = (JmlMethodClauseExpr) clause;
								JCExpression ex = ((JmlMethodClauseExpr) clause).expression;
								diverges = diverges == null ? ex : treeutils.makeAndSimp(ex, diverges, ex);
							} else if (ct == requiresClauseKind) {
								JCExpression ex = ((JmlMethodClauseExpr) clause).expression;
								addTraceableComment(ex, clause.toString());
								JCIdent nextPreExpr;
								if (clauseIds.containsKey(clause)) {
									preexpr = clauseIds.get(clause);
									continue; // Don't reevaluate if we have nested specs
								}
								boolean pv = checkAccessEnabled;
								checkAccessEnabled = false; // FIXME _ review what this is for
								ListBuffer<JCStatement> check2 = null;
								try {
									JCBlock thenbl, elsebl;
									if (rac) {
										// FIXME: The following does not work correctly (cf. testNonNullPrecondition)
										// unless a boxed type is used (a Boolean). It is not at all clear why this
										// should be.
										// The generated source code looks perfectly fine. See additional instance in
										// JmlAssertionAdder.
										JCVariableDecl d = newTempDecl(ex, boxedType(ex.type));
										// JCVariableDecl d = newTempDecl(ex,ex.type);
										d.init = treeutils.makeZeroEquivalentLit(ex.pos, ex.type);
										addStat(d);
										check2 = pushBlock();
										JCExpression convertedEx = convertJML(ex);
										nextPreExpr = treeutils.makeIdent(ex.pos, d.sym);
										addStat(treeutils.makeAssignStat(ex.pos, nextPreExpr, convertedEx));
										thenbl = popBlock(ex, check2);
										elsebl = null;
										check2 = null;
//                                    pushBlock();
//                                    addStat(treeutils.makeAssignStat(ex.pos,nextPreExpr,treeutils.falseLit));
//                                    JCBlock elsebl = popBlock(ex);
									} else {
										nextPreExpr = newTemp(ex, syms.booleanType);
										check2 = pushBlock();
										JCExpression convertedEx = convertJML(ex);
										convertedEx = addImplicitConversion(ex, syms.booleanType, convertedEx);
										addAssume(ex, Label.IMPLICIT_ASSUME,
												treeutils.makeEquality(ex.pos, nextPreExpr, convertedEx));
										// addStat(treeutils.makeAssignStat(ex.pos,nextPreExpr,convertedEx));
										thenbl = popBlock(ex, check2);
										check2 = pushBlock();
										addAssume(ex, Label.IMPLICIT_ASSUME,
												treeutils.makeEquality(ex.pos, nextPreExpr, treeutils.falseLit));
										// addStat(treeutils.makeAssignStat(ex.pos,nextPreExpr,treeutils.falseLit));
										elsebl = popBlock(ex, check2);
										check2 = null;
									}
									if (preexpr == null) {
										addStat(thenbl);
									} else {
										addStat(M.at(ex.pos).If(preexpr, thenbl, elsebl));
									}
									preexpr = nextPreExpr;
									clauseIds.put(clause, preexpr);
								} catch (NoModelMethod e) {
									// FIXME - what to do
								} catch (JmlNotImplementedException e) {
									notImplemented("requires clause containing ", e); // FIXME - needs source
								} finally {
									if (check2 != null)
										popBlock(null, check2);
									checkAccessEnabled = pv;
								}
							}
						}
						precount++;
						Name prename = names.fromString(Strings.prePrefix + precount); // Unique name for each
																						// specification case
						if (scase.pos <= 0) {
							// log.warning("jml.internal","Bad Position");
							scase.pos = 1;
						}
						JCIdent preident;
						if (rac) {
							JCVariableDecl dx = treeutils.makeVarDef(syms.booleanType, prename, methodDecl.sym,
									treeutils.falseLit);
							dx.pos = scase.pos;
							preident = treeutils.makeIdent(scase.pos, dx.sym);
							addStat(initialStats, dx);
							addStat(currentStatements, treeutils.makeAssignStat(scase.pos, preident,
									preexpr == null ? treeutils.trueLit : preexpr));
						} else {
							JCVariableDecl dx = treeutils.makeVarDef(syms.booleanType, prename, methodDecl.sym,
									preexpr == null ? treeutils.trueLit : preexpr);
							dx.pos = scase.pos;
							addStat(dx);
							preident = treeutils.makeIdent(scase.pos, dx.sym);
						}
						//System.out.println("CALLER PUT " + preident + " " + scase + " " + scase.hashCode());
						prelist.add(scase);
						preconditions.put(scase, preident);
						if (combinedPrecondition == null || preexpr == null) {
							combinedPrecondition = preident;
						} else {
							combinedPrecondition = treeutils.makeBitOr(scase.pos, combinedPrecondition, preident);
						}
						combinedPreconditionSource = scase.sourcefile;
						elseExpression = treeutils.makeBitOr(scase.pos, elseExpression, preident);
						{
							if (diverges == null)
								diverges = treeutils.falseLit;
							JCExpression e = treeutils.makeAnd(diverges.pos, preident,
									treeutils.makeOld(treeutils.makeNot(diverges, diverges)));
							divergesExpressions.add(new Pair<>(e, divergesPosition));
						}
					} finally {
						log.useSource(prev);
					}
					recordLabel(scase.name, null);
				}
				clauseIds.clear();
				elseExpression = null;
			}

			// If combinedPrecondition is null then there were no specs, so the implicit
			// precondition is true and does not
			// need to be assumed
			if (combinedPrecondition != null) {
	            if (!rac) {
	                var behaviors = specs.get(methodDecl.sym).cases.behaviors;
	                if (behaviors != null) {
	                    JmlMethodClauseBehaviors cl = null;
                        for (var b: behaviors) { if (b.command.equals("complete")) cl = b; };
                        if (cl != null) {
                            addCheck(cl, Label.COMPLETENESS, combinedPrecondition);
                        }
                        cl = null;
                        for (var b: behaviors) { if (b.command.equals("local_complete")) cl = b; };
                        if (cl != null) {
                            int n = start_of_local_cases;
                            JCExpression e = treeutils.falseLit;
                            for (var case1: prelist) {
                                if (n-- > 0) continue;
                                var pre1 = preconditions.get(case1);
                                e = treeutils.makeOr(cl, e, pre1);
                            }
                            addCheck(cl, Label.COMPLETENESS, e);
                        }
                        cl = null;
                        for (var b: behaviors) { if (b.command.equals("disjoint")) cl = b; };
                        if (cl != null) {
                            for (var case1: prelist) {
                                var pre1 = preconditions.get(case1);
                                for (var case2: prelist) {
                                    if (case1 == case2) break;
                                    var pre2 = preconditions.get(case2);
                                    JCExpression e = treeutils.makeNot(cl,
                                            treeutils.makeAnd(cl, pre1, pre2));
                                    var prev = log.useSource(case1.sourcefile);
                                    addCheck(case1, Label.DISJOINTNESS, e, case2, case2.sourcefile, null);
                                    log.useSource(prev);
                                }
                            }
                        }
                        cl = null;
                        for (var b: behaviors) { if (b.command.equals("local_disjoint")) cl = b; };
                        if (cl != null) {
                            int n = start_of_local_cases;
                            for (var case1: prelist) {
                                if (n-- > 0) continue;
                                var pre1 = preconditions.get(case1);
                                int nn = start_of_local_cases;
                                for (var case2: prelist) {
                                    if (nn-- > 0) continue;
                                    if (case1 == case2) break;
                                    var pre2 = preconditions.get(case2);
                                    JCExpression e = treeutils.makeNot(cl,
                                            treeutils.makeAnd(cl, pre1, pre2));
                                    var prev = log.useSource(case1.sourcefile);
                                    addCheck(case1, Label.DISJOINTNESS, e, case2, case2.sourcefile, null);
                                    log.useSource(prev);
                                }
                            }
                        }
	                }
	            }

			    // FIXME - associated location? where?
				JavaFileObject prev = log.useSource(combinedPreconditionSource);
				addAssume(combinedPrecondition, Label.PRECONDITION, combinedPrecondition);
				log.useSource(prev);
			}

			if (rac) {
				// If rac, we wrap all the precondition evaluation in a try block so we catch
				// any
				// undefined operations
				Name n;
				JCVariableDecl vd;
				JCIdent ex;
				// We can't use the try block approach in a constructor because a costructor
				// must
				// start with an implicit or explicit super call
				if (!isConstructor) {
					n = names.fromString("preEx");
					vd = treeutils.makeVarDef(syms.runtimeExceptionType, n, methodDecl.sym, methodDecl.pos);
					ex = treeutils.makeIdent(methodDecl.pos, vd.sym);
					JCExpression str = treeutils.makeStringLiteral(methodDecl.pos,
							"Runtime exception while evaluating preconditions - preconditions are undefined in JML");
					JCStatement st = methodCallUtilsStatement(methodDecl, "reportException", str, ex);
					JCBlock bl = M.at(methodDecl.pos).Block(0, List.<JCStatement>of(st));
					JCCatch catcher = M.at(methodDecl.pos).Catch(vd, bl);
					bl = M.at(methodDecl.pos).Block(0, preStats.toList());
					st = M.at(methodDecl.pos).Try(bl, List.<JCCatch>of(catcher), null);
					preStats = new ListBuffer<JCStatement>();
					preStats.add(st);
				}
			}
			
			initialStats.appendList(preStats);

		} catch (Exception e) {
			utils.unexpectedException("addPreCondition", e);
		} finally {
			//paramActuals_ = null;
			clearInvariants();

			heapCount = savedheapcount;
			popBlock(null, check);
		}
	}

	public void handleFrameConditions(JmlMethodDecl methodDecl, ListBuffer<JCStatement> initialStatements) {
		// This just checks that the frame conditions are well-defined
		pushBlock(initialStatements);
		addStat(comment(methodDecl, "Check that assignable, accessible, captures clauses are well-defined", null));
		SpecCaseIterable specCases = new SpecCaseIterable(methodDecl.sym, true);
		for (var info: specCases) {
			var parentMethodSym = info.parentMethodSymbol;
			var scase = info.specCase();
			//paramActuals = info.paramActuals();
			
//		for (MethodSymbol parentMethodSym : utils.parents(methodDecl.sym)) {
//			if (parentMethodSym.params == null)
//				continue; // FIXME - we should do something better? or does this mean binary with no
//							// specs?
//			JmlMethodSpecs denestedSpecs = JmlSpecs.instance(context).getDenestedSpecs(parentMethodSym);
//			if (denestedSpecs == null) continue;
//			paramActuals = specParamsToActuals(denestedSpecs, methodDecl, parentMethodSym);
//			for (JmlSpecificationCase scase : denestedSpecs.cases) {
//				if (!doSpecificationCase(methodDecl, parentMethodSym, scase)) continue;
				JCIdent preid = preconditions.get(scase);
				pushBlock();
				boolean anyClauses = false;
				currentEnv = currentEnv.pushEnvCopy();
				for (var clause : scase.clauses) {
					if (!(clause instanceof JmlMethodClauseStoreRef sc)) continue;
					currentEnv.enclosingClauseKind = sc.clauseKind;
					addStat(comment(methodDecl, "   Checking " + clause, null));
					anyClauses = true;
					var list = sc.list;
					//System.out.print("HFC "); list.forEach(s->System.out.print(" " + c)); System.out.println();
					//					var locsetExpr = convertAssignableToLocsetExpression(sc, list, (ClassSymbol) methodDecl.sym.owner, currentEnv.currentReceiver);
//					// System.out.println("HFC " + locsetExpr);
//					convertJML(locsetExpr); // This is just to get all the well-definedness checks
					var listsr = new LinkedList<JmlStoreRef>();
					list.forEach(s->listsr.addAll(makeJmlStoreRef(s,s,(ClassSymbol) methodDecl.sym.owner,false)));
					listsr.forEach(s-> convertJML(s) ); // FIXME - a better test for this?
				}
				currentEnv = currentEnv.popEnv();
				JCBlock b = popBlock(scase);
				if (anyClauses)
					addStat(M.at(scase).If(preid, b, null));
//			}
		}
		// FIXME - for RAC we need to wrap in a try block
		popBlock();
	}

	// methodDecl - method that is being translated
	// baseMethodSym - base method of which parent is a parent
	// parentMethodSym - symbol for the method or overriding method to which spec case belongs
	// scase - the particular specification case
	public boolean doSpecificationCase(JCMethodDecl methodDecl, MethodSymbol baseMethodSym, MethodSymbol parentMethodSym, JmlSpecificationCase scase) {
		if (!utils.jmlvisible(parentMethodSym, methodDecl.sym.owner, parentMethodSym.owner, scase.modifiers.flags, methodDecl.mods.flags)) return false;
		if (parentMethodSym != baseMethodSym && scase.code)  return false;
		if (translatingJML) {
            return attr.isEffectivelyNormal(scase);
		}
		return true;
	}

	/** This just tests whether the type is explicitly a JMLDataGroup */
	public boolean isDataGroup(Type type) {
		return type.toString().contains("JMLDataGroup"); // FIXME - something better than string comparison?
	}

	protected void assumeFieldInvariants(JCMethodDecl methodDecl, JCClassDecl classDecl) {
		// Assume invariants for the class of each field of the owning class
		// If methodDecl is static, then only consider static fields
		// If methodDecl is helper, then do not add fields of the same type as the owner
		// of the method
		JCExpression savedThis = currentEnv.currentReceiver;
		for (JCTree dd : classDecl.defs) {
			if (!(dd instanceof JCVariableDecl))continue;
			JCVariableDecl d = (JCVariableDecl) dd;
			if (utils.isJavaOrJmlPrimitiveType(d.sym.type)) continue;
			if (!utils.isJMLStatic(d.sym) && utils.isJMLStatic(methodDecl.sym))continue;
			if (isHelper(methodDecl.sym) && d.sym.type.tsym == methodDecl.sym.owner.type.tsym)continue;
			if (isDataGroup(d.type)) continue;
            if (attr.isHelper(d.sym)) continue;
            
			if (dd.type.isParameterized()) {
				List<Type> argtypes = dd.type.getTypeArguments();
				List<Type> formals = dd.type.tsym.type.getTypeArguments();

				for (Type t : formals) {
					Type target = argtypes.head;
					// map t to target
					typeActuals.put(t.tsym, target);
					argtypes = argtypes.tail;
				}
			}
			boolean pv = checkAccessEnabled;
			checkAccessEnabled = false;
			try {
				JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
				addStat(comment(dd, "Adding invariants for field " + d.sym.flatName(), null));
				addRecInvariants(true, d, fa);
			} finally {
				checkAccessEnabled = pv;
			}
		}
		currentEnv.currentReceiver = savedThis;
		/*
		 * for (JmlTypeClauseDecl dd: specs.getSpecs(classDecl.sym).decls) { JCTree tt =
		 * dd.decl; if (!(tt instanceof JCVariableDecl)) continue; JCVariableDecl d =
		 * (JCVariableDecl)tt; if (utils.isPrimitiveType(d.sym.type)) continue; if
		 * (!utils.isJMLStatic(d.sym) && utils.isJMLStatic(methodDecl.sym)) continue;
		 * 
		 * JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
		 * addStat(comment(dd,"Adding invariants for ghost field " +
		 * d.sym.flatName(),null)); addRecInvariants(true,d,fa); }
		 */
		currentEnv.currentReceiver = savedThis;
	}

	protected void assumeFieldInvariants(ClassSymbol classSym, boolean staticOnly, boolean noFinal) {
		// Assume invariants for the class of each field of the argument
		JCExpression savedThis = currentEnv.currentReceiver;
		JmlSpecs.TypeSpecs cspecs = specs.getAttrSpecs(classSym);
		if (cspecs.specDecl == null)
			return;
		JavaFileObject prevJFO = log.currentSourceFile();
		log.useSource(cspecs.specDecl.sourcefile);
		for (JCTree dd : cspecs.specDecl.defs) {
			if (!(dd instanceof JCVariableDecl))
				continue;
			JCVariableDecl d = (JCVariableDecl) dd;
			specs.getAttrSpecs(d.sym);
			if (utils.isJavaOrJmlPrimitiveType(d.sym.type))
				continue;
			if (staticOnly && !utils.isJMLStatic(d.sym)) continue;
			if (noFinal && isFinal(d.sym)) continue; // No need to repeat final invariants
			if (isDataGroup(d.type)) continue;
			if (attr.isHelper(d.sym)) continue;

			// if (isHelper(methodDecl.sym) && d.sym.type.tsym ==
			// methodDecl.sym.owner.type.tsym) continue;

			if (dd.type.isParameterized()) {
				List<Type> argtypes = dd.type.getTypeArguments();
				List<Type> formals = dd.type.tsym.type.getTypeArguments();

				for (Type t : formals) {
					Type target = argtypes.head;
					// map t to target
					typeActuals.put(t.tsym, target);
					argtypes = argtypes.tail;
				}
			}
			boolean pv = checkAccessEnabled;
			checkAccessEnabled = false;
			try {
				addStat(comment(dd, "Adding invariants for field " + d.sym.flatName(), null));
				JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
				addRecInvariants(true, d, fa);
			} finally {
				checkAccessEnabled = pv;
			}
		}
		log.useSource(prevJFO);
		currentEnv.currentReceiver = savedThis;
		/*
		 * for (JmlTypeClauseDecl dd: specs.getSpecs(classSym).decls) { JCTree tt =
		 * dd.decl; if (!(tt instanceof JCVariableDecl)) continue; JCVariableDecl d =
		 * (JCVariableDecl)tt; if (utils.isPrimitiveType(d.sym.type)) continue; if
		 * (staticOnly && !utils.isJMLStatic(d.sym)) continue;
		 * 
		 * JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
		 * addStat(comment(dd,"Adding invariants for ghost field " +
		 * d.sym.flatName(),null)); addRecInvariants(true,d,fa); }
		 */
		currentEnv.currentReceiver = savedThis;
	}

	protected void assumeStaticInitialState(TypeSymbol sym) {
		boolean helper = isHelper(methodDecl.sym);
		addRecInvariants(true, true, true, helper, methodDecl, sym, null);
//        for (ClassSymbol csym: utils.parents(sym, false)) { // FIXME - ??? false or true
//            addStat(comment(null,"Adding static initial state for " + sym + " from " + csym,null));
//
//            for (Symbol sy: csym.members().getElements()) {
//                if (!(sy instanceof VarSymbol)) continue;
//                if (!utils.isJMLStatic(sy)) continue;
//                // FIXME - does allocation also
//                addNullnessAndTypeConditionsForField(csym, (VarSymbol)sy, true);
////                // FIXME - why both of these?
////                addNullnessAllocationTypeCondition(methodDecl, sy, true && !utils.isJMLStatic(sy));
//            }
		// }
	}

	protected void addNullnessAndTypeConditionsForInheritedFields(TypeSymbol root, boolean beingConstructed,
			boolean staticOnly) {
		TypeSymbol sym = root;
		JCExpression thisExpr = currentEnv.currentReceiver;
		for (ClassSymbol csym : utils.parents(sym, false)) {
			addNullnessAndTypeConditionsForFields(csym, beingConstructed, staticOnly);
		}
		if (!utils.isJMLStatic(sym)) {
			Symbol esym = sym.getEnclosingElement();
			VarSymbol vsym = enclosingClassFieldSymbols.get(sym);
			if (vsym != null && esym instanceof TypeSymbol) {
				JCExpression fa = treeutils.makeSelect(Position.NOPOS, currentEnv.currentReceiver, vsym);
				currentEnv.currentReceiver = fa;
				addNullnessAndTypeConditionsForInheritedFields((TypeSymbol) esym, beingConstructed, staticOnly);
			}
		}
		currentEnv.currentReceiver = thisExpr;
	}

	protected void addNullnessAndTypeConditionsForFields(TypeSymbol csym, boolean beingConstructed,
			boolean staticOnly) {
		// For Java fields
		for (Symbol sy : csym.members().getSymbols()) {
			if (!(sy instanceof VarSymbol))
				continue;
			if (!utils.isJMLStatic(sy) && staticOnly)
				continue;
			if (jmltypes.isOnlyDataGroup(sy.type))
				continue;
			addNullnessAndTypeConditionsForField(csym, (VarSymbol) sy, beingConstructed);
			// FIXME - why both of these?
			addNullnessAllocationTypeCondition(methodDecl, sy, beingConstructed && !utils.isJMLStatic(sy));
		}

	}

	protected void addNullnessAndTypeConditionsForField(TypeSymbol csym, VarSymbol sy, boolean beingConstructed) {
		if (isDataGroup(sy.type))
			return;
		// Find the declaration for the variable symbol. This is only to hzve a
		// sensible diagnostic position for it.

		// For Java fields
		Env<AttrContext> e = Enter.instance(context).getEnv(csym);
		if (e != null && e.tree instanceof JmlClassDecl) {
			JmlClassDecl cdecl = (JmlClassDecl) e.tree;
			for (JCTree def : cdecl.defs) {
				if (def instanceof JmlVariableDecl) {
					if (((JmlVariableDecl) def).sym == sy) {
						addNullnessAllocationTypeCondition2((JmlVariableDecl) def, sy,
								beingConstructed && !utils.isJMLStatic(sy), null);
						return;
					}
				}
			}
		}
		// For JML fields
		for (JCTree dd : specs.getAttrSpecs((ClassSymbol) csym).clauses) {
			if (!(dd instanceof JmlTypeClauseDecl))
				continue;
			JCTree t = ((JmlTypeClauseDecl) dd).decl;
			if (!(t instanceof JCVariableDecl))
				continue;
			JCVariableDecl d = (JCVariableDecl) t;
			if (d.sym == null)
				continue; // FIXME - model fields, at least, can have null symbols, I think
			if (beingConstructed && !utils.isJMLStatic(d.sym))
				continue;
			if (isDataGroup(d.type)) {
				continue;
			}
			addNullnessAllocationTypeCondition(d, sy, false);
			return;
		}
		// FIXME - what if there is no declaration found?
	}

	protected void addPostConditions(ListBuffer<JCStatement> finalizeStats) {
		assumingPostConditions = false;
		JCMethodDecl methodDecl = this.methodDecl;
		boolean isConstructor = methodDecl.sym.isConstructor();
		ListBuffer<JCStatement> savedCurrentStatements = currentStatements;

		// FIXME - need to figure out what to do for Enums. But one issue is this
		// Constructors are constructors for individual enum values, not for the class.
		// The enum values are not yet initialized while stillin the constructor
		// (because the final assignment is not yet performed).
		// So postconditions are a different sort of thing.
		if (isConstructor && classDecl.sym.isEnum()) return;

		// Collect all classes that are mentioned in the method
		ClassCollector collector = ClassCollector.collect(this.classDecl, this.methodDecl, context);

//        if (esc) { // FIXME - what about inherited fields? fields of parameters? fields of anything else?
//            addStat(comment(methodDecl,"Assume field type, allocation, and nullness",null));
//            for (ClassSymbol csym: utils.parents(classDecl.sym)) {
//                // For Java fields
//                for (Symbol sy: csym.members().getElements()) {
//                    if (!(sy instanceof VarSymbol)) continue;
//                    // FIXME - should have a DiagnosticPosition for the actual declaration
//                    addNullnessAllocationTypeCondition(methodDecl,sy, isConstructor && !utils.isJMLStatic(sy));
//                }
////                // For JML fields
////                for (JCTree dd: classDecl.typeSpecs.clauses) {
////                    if (!(dd instanceof JmlTypeClauseDecl)) continue;
////                    JCTree t = ((JmlTypeClauseDecl)dd).decl;
////                    if (!(t instanceof JCVariableDecl)) continue;
////                    JCVariableDecl d = (JCVariableDecl)t;
////                    if (d.sym == null) continue; // FIXME - model fields, at least, can have null symbols, I think
////                    if (isConstructor && !utils.isJMLStatic(d.sym)) continue;
////                    addNullnessAllocationTypeCondition(d,isConstructor && !utils.isJMLStatic(d.sym));
////                }
//            }
//            // For the parameters of the method
//            addStat(comment(methodDecl,"Assume parameter type, allocation, and nullness",null));
//            boolean varargs = (methodDecl.sym.flags() & Flags.VARARGS) != 0;
//            boolean nn = true;
//            for (JCVariableDecl d: methodDecl.params) {
//                nn = addNullnessAllocationTypeCondition(d,false);
//            }
//            if (varargs && !nn) {
//                JCVariableDecl d = methodDecl.params.last();
//                JCIdent id = treeutils.makeIdent(d.pos,d.sym);
//                JCExpression nnex = treeutils.makeNeqObject(d.pos,id,treeutils.nullLit);
//                addAssume(d.pos(),Label.IMPLICIT_ASSUME,nnex);
//            }
//            
//            int pos = methodDecl.pos;
//            
//            // FIXME - for the isConstructor case, it should be newly allocated
//            if (isConstructor) {
//            } else if (!utils.isJMLStatic(methodDecl.sym)){
//                // Assume that 'this' is allocated
//                JCFieldAccess fa = treeutils.makeSelect(pos, convertCopy(currentEnv.currentReceiver), isAllocSym);
//                addAssume(methodDecl,Label.IMPLICIT_ASSUME,fa);
//
//                fa = treeutils.makeSelect(pos, convertCopy(currentEnv.currentReceiver), allocSym);
//                JCExpression comp = treeutils.makeBinary(pos,JCTree.Tag.EQ,treeutils.inteqSymbol,fa,treeutils.makeIntLiteral(pos, 0));
//                addAssume(methodDecl,Label.IMPLICIT_ASSUME,comp);
//            }
//
//        }

//        /* Declare new variables, initialized to the values of the formal 
//         * parameters, so that they can be referred to in postconditions. 
//         */
//        if (!methodDecl.params.isEmpty()) addStat(comment(methodDecl,"Declare pre-state value of formals",null));
//        for (JCVariableDecl d: methodDecl.params) {
//            JCVariableDecl dd = treeutils.makeVarDef(d.type,M.Name(Strings.formalPrefix+d.name.toString()),  
//                    d.sym.owner, M.Ident(d.sym));
//            dd.pos = dd.sym.pos = d.sym.pos;
//            preparams.put(d.sym,dd);
//            if (esc) dd.sym.owner = null; // FIXME - can get these straight from the labelmaps - do we need this?
//            addStat(dd);
//        }

		// Construct a condition, to be used later, that the method has not thrown an
		// exception
		DiagnosticPosition methodPos = methodDecl;
		JCExpression noException = treeutils.makeEqObject(methodPos.getPreferredPosition(),
				treeutils.makeIdent(methodPos.getPreferredPosition(), exceptionSym), treeutils.nullLit);

		// FIXME - what if the owning class is a TypeSymbol because it is a TypeVar
		TypeSymbol owner = (TypeSymbol) methodDecl.sym.owner;

		JCExpression receiver = utils.isJMLStatic(methodDecl.sym) ? null : currentEnv.currentReceiver;

		JCExpression savedThis = currentEnv.currentReceiver;

		// FIXME Don't replicate the invariants in ensures and exsuresStats

		currentStatements = null; // Just to make sure everything is assigned to either ensuresStats or
									// exsuresStats
		ListBuffer<JCStatement> ensuresStats = new ListBuffer<JCStatement>();
		ListBuffer<JCStatement> exsuresStats = new ListBuffer<JCStatement>();

		boolean isPure = isPure(methodDecl.sym);

		// Accumulate the invariants to be checked after the method returns
		clearInvariants();
		if (rac) {
			if (!isPure || isConstructor)
				addInvariants(methodDecl, owner.type, receiver, ensuresStats, true, methodDecl.sym.isConstructor(),
						false, isHelper(methodDecl.sym), true, false, Label.INVARIANT_EXIT,
						utils.qualifiedMethodSig(methodDecl.sym));
			addConstraintInitiallyChecks(methodDecl, owner, receiver, ensuresStats, true,
					methodDecl.sym.isConstructor(), false, isHelper(methodDecl.sym), true, false, null,
					utils.qualifiedMethodSig(methodDecl.sym));
		} else {
			if (!isPure || isConstructor)
				addInvariants(methodDecl, owner.type, receiver, ensuresStats, true, methodDecl.sym.isConstructor(),
						false, isHelper(methodDecl.sym), true, false, Label.INVARIANT_EXIT);
			addConstraintInitiallyChecks(methodDecl, owner, receiver, ensuresStats, true,
					methodDecl.sym.isConstructor(), false, isHelper(methodDecl.sym), true, false, null);
		}
		if (!isPure || isConstructor) {
			for (JCVariableDecl v : methodDecl.params) {
				if (utils.isJavaOrJmlPrimitiveType(v.type)) continue;
				if (isHelper(methodDecl.sym) && v.sym.type.tsym == methodDecl.sym.owner.type.tsym) continue;
				if (utils.hasModifier(v.mods,Modifiers.HELPER)) continue;

				JCIdent id = treeutils.makeIdent(v.pos, v.sym);
				JCExpression oldid = treeutils.makeOld(v.pos(), id, labelPropertiesStore.get(attr.preLabel));
				if (rac)
					oldid = convertExpr(oldid);
				addInvariants(v, v.type, oldid, ensuresStats, true, false, false, false, true, false,
						Label.INVARIANT_EXIT, utils.qualifiedMethodSig(methodDecl.sym) + " (parameter " + v.name + ")");
			}
		}
		clearInvariants();
		if (resultSym != null && !utils.isJavaOrJmlPrimitiveType(resultSym.type) && !isConstructor && !isPure) {
			JCIdent resultId = treeutils.makeIdent(methodDecl.pos, resultSym);
			addInvariants(methodDecl, resultSym.type, resultId, ensuresStats, false, false, false, false, true, false,
					Label.INVARIANT_EXIT, utils.qualifiedMethodSig(methodDecl.sym) + " (for result type)");
		}
		// We are doing exceptional postconditions, so if this is a constructor, we only
		// do static
		// invariants which we indicate by setting the receiver null.
		JCExpression treceiver = !isConstructor ? receiver : null;
		{
			if (rac) {
				if (!isPure || isConstructor)
					addInvariants(methodDecl, owner.type, treceiver, exsuresStats, true, methodDecl.sym.isConstructor(),
							false, isHelper(methodDecl.sym), true, false, Label.INVARIANT_EXCEPTION_EXIT,
							utils.qualifiedMethodSig(methodDecl.sym));
				addConstraintInitiallyChecks(methodDecl, owner, treceiver, exsuresStats, true,
						methodDecl.sym.isConstructor(), false, isHelper(methodDecl.sym), true, false, null,
						utils.qualifiedMethodSig(methodDecl.sym));
			} else {
				if (!isPure || isConstructor)
					addInvariants(methodDecl, owner.type, treceiver, exsuresStats, true, methodDecl.sym.isConstructor(),
							false, isHelper(methodDecl.sym), true, false, Label.INVARIANT_EXCEPTION_EXIT);
				addConstraintInitiallyChecks(methodDecl, owner, treceiver, exsuresStats, true,
						methodDecl.sym.isConstructor(), false, isHelper(methodDecl.sym), true, false, null);
			}
		}

		if (!isPure || isConstructor) {
			for (JCVariableDecl v : methodDecl.params) {
				if (utils.isJavaOrJmlPrimitiveType(v.type)) continue;
				// JCIdent d = preparams.get(v.sym);
				if (isHelper(methodDecl.sym) && v.sym.type.tsym == methodDecl.sym.owner.type.tsym) continue;
				if (attr.isHelper(v.sym)) continue;
				
				JCIdent id = treeutils.makeIdent(v.pos, v.sym);
				addInvariants(v, v.type, id, exsuresStats, false, false, false, false, true, false,
						Label.INVARIANT_EXCEPTION_EXIT,
						utils.qualifiedMethodSig(methodDecl.sym) + " (parameter " + v.name + ")");
				// addConstraintInitiallyChecks(v,v.type.tsym,id,exsuresStats,false,false,false,false,true,false,null,
				// utils.qualifiedMethodSig(methodDecl.sym) + " (parameter " + v.name + ")");
			}
		}

		// Invariants for fields
		savedThis = currentEnv.currentReceiver;
		currentStatements = ensuresStats; // FIXME - also exsuresStatements?
		for (int kk = 0; kk < 1; kk++) { // FIXME - extend to 2 for checking in exsures but need additional changes
			currentStatements = kk == 0 ? ensuresStats : exsuresStats;
			// FIXME - we repeat the computatinos in the normal and exceptinoal branches -
			// can we avoid that
			if (!isHelper(methodDecl.sym))
				for (JCTree dd : classDecl.defs) { // FIXME - review isHelper here, and visibility
					if (!(dd instanceof JCVariableDecl))
						continue;
					JCVariableDecl d = (JCVariableDecl) dd;
					if (utils.isJavaOrJmlPrimitiveType(d.sym.type))
						continue;
					if (!utils.isJMLStatic(d.sym) && utils.isJMLStatic(methodDecl.sym))
						continue;
					if (specs.isNonNull(d.sym)) {
						JCExpression id = treeutils.makeIdent(d.pos, d.sym);
						addAssert(d, Label.NULL_FIELD, convertJML(treeutils.makeNotNull(d.pos, id)));
					}
					if (isHelper(methodDecl.sym) && d.sym.type.tsym == methodDecl.sym.owner.type.tsym)
						continue;
					if (attr.isHelper(d.sym)) continue;
					boolean pv = checkAccessEnabled;
					checkAccessEnabled = false;
					try {
						JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
						addStat(comment(dd, "Adding exit invariants for " + d.sym, null));
						addRecInvariants(false, d, fa);
					} finally {
						checkAccessEnabled = pv;
					}
				}
			currentEnv.currentReceiver = savedThis;
			/*
			 * for (JmlTypeClauseDecl dd: specs.getSpecs(classDecl.sym).decls) { JCTree tt =
			 * dd.decl; if (!(tt instanceof JCVariableDecl)) continue; JCVariableDecl d =
			 * (JCVariableDecl)tt; if (utils.isPrimitiveType(d.sym.type)) continue; if
			 * (!utils.isJMLStatic(d.sym) && utils.isJMLStatic(methodDecl.sym)) continue;
			 * 
			 * JCExpression fa = convertJML(treeutils.makeIdent(d.pos, d.sym));
			 * addStat(comment(dd,"Adding exit invariants for " + d.sym,null));
			 * addRecInvariants(false,d,fa); }
			 */
			currentEnv.currentReceiver = savedThis;
		}

		JCBlock ensuresAxiomBlock = M.Block(0L, List.<JCStatement>nil());
		ensuresStats.add(ensuresAxiomBlock);
		JCBlock exsuresAxiomBlock = M.Block(0L, List.<JCStatement>nil());
		exsuresStats.add(exsuresAxiomBlock);

		// Note that methodDecl.resType.type appears to be unannotated
		Type rt = methodDecl.sym.getReturnType();
		if (rt != null && !utils.isPrimitiveOrVoidType(rt) && resultSym != null && specs.isNonNullReturn(methodDecl.sym)) {
		    //System.out.println("NN " + methodDecl.sym.owner + " " + methodDecl.restype.type + " " + methodDecl.sym + " " + specs.isNonNull(methodDecl.sym.getReturnType()) + " " + hasNullable(rt) + " " + hasNonNull(rt) );
			currentStatements = ensuresStats;
			addStat(comment(methodDecl.restype, "Adding null return check by callee " + methodDecl.sym, null));
			JCIdent ret = treeutils.makeIdent(methodDecl.restype.pos, resultSym);
			addAssert(methodDecl.restype, Label.POSSIBLY_NULL_RETURN,
					treeutils.makeNotNull(methodDecl.restype.pos, ret), methodDecl.pos(),
					((JmlMethodDecl) methodDecl).sourcefile, methodDecl.name);
		}

		// Iterate over all methods that methodDecl overrides, collecting specs
		boolean sawSomeSpecs = false;
		for (MethodSymbol parentMethodSym : utils.parents(methodDecl.sym,true)) {
			if (parentMethodSym.params == null) continue; // FIXME - we should do something better? or does this mean binary with no specs?
			JmlMethodSpecs denestedSpecs = JmlSpecs.instance(context).getDenestedSpecs(parentMethodSym);
			ensuresStats.add(comment(methodDecl, "Asserting postconditions for " + utils.qualifiedMethodSig(parentMethodSym), null));
			exsuresStats.add(comment(methodDecl, "Asserting exceptional postconditions for " + utils.qualifiedMethodSig(parentMethodSym), null));
			// Set up the map from parameter symbol of the overridden method to
			// corresponding parameter of the target method.
			// We need this even if names have not changed, because the parameters
			// will have been attributed with different symbols.
			if (denestedSpecs == null) { // CHECK - added for inference
				continue;
			}

//			paramActuals_ = specParamsToActuals(denestedSpecs, methodDecl, parentMethodSym);
			//            if (denestedSpecs.decl != null) {
//                Iterator<JCVariableDecl> iter = denestedSpecs.decl.params.iterator();
//                paramActuals = new HashMap<Object,JCExpression>();
//                for (JCVariableDecl dp: methodDecl.params) {
//                    JCVariableDecl newdecl = iter.next();
//                    paramActuals.put(newdecl.sym,treeutils.makeIdent(dp.pos, dp.sym));
//                }
//            } else { // FIXME - why should denestedSpecs ever not have a declaration if there are any specs to use
//                Iterator<VarSymbol> iter = msym.params.iterator();
//                paramActuals = new HashMap<Object,JCExpression>();
//                for (JCVariableDecl dp: methodDecl.params) {
//                    VarSymbol newsym = iter.next();
//                    paramActuals.put(newsym,treeutils.makeIdent(dp.pos, dp.sym));
//                }
//            }

//        	System.out.println("CASES FOR  " + msym.owner + " " + msym);
//        	System.out.println("PLAIN " + JmlSpecs.instance(context).getSpecs(msym));
//        	System.out.println("DENEST " + JmlSpecs.instance(context).getDenestedSpecs(msym));
			for (JmlSpecificationCase scase : denestedSpecs.cases) {
				sawSomeSpecs = true;
				if (!doSpecificationCase(methodDecl, methodDecl.sym, parentMethodSym, scase)) continue;
				JCIdent preident = preconditions.get(scase);
				if (preident == null) continue; // This happens if the precondition contains unimplemented material. But might
								// in other situations as well.
				boolean sawSignalsOnly = false;

				for (JmlMethodClause clause : scase.clauses) {
					try {
						conditionAssociatedClause = clause;
						IJmlClauseKind ct = clause.clauseKind;
						if (ct == MethodExprClauseExtensions.ensuresClauseKind) {
							{
								currentStatements = ensuresStats;
								axiomBlock = ensuresAxiomBlock;
								ListBuffer<JCStatement> ch = pushBlock();
								try {
									JCExpression ex = ((JmlMethodClauseExpr) clause).expression;
									JCExpression convertedex = convertJML(ex, preident, true);
									// ex = treeutils.makeImplies(clause.pos, preident, ex);
									addTraceableComment(ex, clause.toString());
									// FIXME - if the clause is synthetic, the source file may be null, and for
									// signals clause
									addAssert(true, methodDecl, Label.POSTCONDITION, convertedex, clause,
											clause.sourcefile, null);
								} catch (JmlNotImplementedException e) {
									notImplemented(clause.keyword + " clause containing ", e, clause.source());
									result = null;
								} catch (Throwable t) {
									utils.unexpectedException(t, "addPostConditions");
								} finally {
									JCBlock bl = popBlock(clause, ch);
									JCStatement st = M.at(clause.pos).If(preident, bl, null);
									addStat(st);
								}
							}

						} else if (ct == SignalsClauseExtension.signalsClauseKind) {
							// FIXME - need to check exception type of the exception
							{
								currentStatements = exsuresStats;
								axiomBlock = exsuresAxiomBlock;
								JCIdent exceptionId = treeutils.makeIdent(clause.pos, exceptionSym);
								{
									JCIdent nid = copy(exceptionId);
									saveMapping(nid, exceptionId);
									addTraceableComment(clause, nid, "Terminated with exception");
								}
								JCVariableDecl vdo = ((JmlMethodClauseSignals) clause).vardef;
								JCVariableDecl vd = vdo;
								JCExpression prevValue = null;
								if (vd != null) {
									vd = treeutils.makeVarDef(vd.type, vd.name, vd.sym.owner, vd.pos);
									JCIdent id = treeutils.makeIdent(vdo.pos, vd.sym);
									prevValue = paramActuals_.put(vdo.sym, id);
								}
								JCExpression ex = ((JmlMethodClauseSignals) clause).expression;
								addTraceableComment(ex, clause.toString());

								JCExpression test = vd == null
										? treeutils.makeInstanceOf(clause.pos, exceptionId, syms.exceptionType)
										: treeutils.makeInstanceOf(clause.pos, exceptionId, vd.type);
								ListBuffer<JCStatement> ch = pushBlock();
								try {
									if (vd != null) {
										JCTypeCast tc = M.at(clause).TypeCast(vd.type, exceptionId);
										vd.init = esc ? exceptionId : tc;
										addStat(vd);
									}

									ex = convertJML(ex, preident, true);
									ex = treeutils.makeImplies(clause.pos, preident, ex);
									addAssert(methodDecl, Label.SIGNALS, ex, clause, clause.sourcefile);
								} finally {
									JCBlock block = popBlock(clause, ch);
									if (test != null) {
										addStat(M.at(clause.pos).If(newTempIfNeeded(test), block, null));
									} else
										addStat(block);
									if (vdo != null) {
										paramActuals_.put(vdo.sym, prevValue);
									}
								}
							}

						} else if (ct == SignalsOnlyClauseExtension.signalsOnlyClauseKind) {
							{
								sawSignalsOnly = true;
								{
									currentStatements = exsuresStats;
									axiomBlock = exsuresAxiomBlock;
									ListBuffer<JCStatement> ch = pushBlock();
									try {
										JCIdent exceptionId = treeutils.makeIdent(clause.pos, exceptionSym);
										JCExpression condd = treeutils.falseLit;
										for (JCExpression t : ((JmlMethodClauseSignalsOnly) clause).list) {
										    if (t instanceof JCAnnotatedType at) {
										        // Perhaps only remove NonNull and Nullable
										        t = at.underlyingType;
										    }
											JCExpression tc = M.at(t).TypeTest(exceptionId, t)
													.setType(syms.booleanType);
											condd = treeutils.makeOr(clause.pos, condd, tc);
										}
										condd = treeutils.makeImplies(clause.pos, preident, condd);
										JCExpression extype = treeutils.makeType(clause.pos, syms.exceptionType);
										JCExpression isExcType = M.at(clause.pos).TypeTest(exceptionId, extype)
												.setType(syms.booleanType);
										condd = treeutils.makeOr(clause.pos, treeutils.makeNot(clause.pos, isExcType),
												condd);
										if (rac) {
											addAssert(methodDecl, Label.SIGNALS_ONLY, condd, clause, clause.sourcefile,
													treeutils.makeUtilsMethodCall(clause.pos, "getClassName",
															exceptionId));
										} else {
											addAssert(methodDecl, Label.SIGNALS_ONLY, condd, clause, clause.sourcefile);
										}
									} finally {
										addStat(popBlock(methodDecl, ch));
									}
								}
							}

						} else if (ct == MethodResourceClauseExtension.workingspaceClause
								|| ct == MethodResourceClauseExtension.durationClause) {

							{
								// FIXME _ implement
								JCExpression ex = ((JmlMethodClauseConditional) clause).expression;
								JCExpression pred = ((JmlMethodClauseConditional) clause).predicate;
								{ // Avoid complaints or any implementation if the expression is 'true'
									currentStatements = ensuresStats;
									axiomBlock = ensuresAxiomBlock;
									ListBuffer<JCStatement> ch = pushBlock();
									try {
										// addTraceableComment(ex,clause.toString());
										convertJML(ex, preident, true);
										convertJML(pred, preident, true);
										ex = treeutils.makeImplies(clause.pos, preident, ex);
										// addAssert(methodDecl,Label.SIGNALS,ex,currentStatements,clause,clause.sourcefile);
									} finally {
										popBlock(clause, ch);
									}
									notImplemented(clause, clause.keyword + " clause", clause.source());
								}
							}

						}
					} catch (NoModelMethod e) {
						JavaFileObject orig = log.useSource(clause.source());
						warning(clause, "jml.skipping.no.model", ""); // FIXME - can we tell which field is not
																		// implemented?
						log.useSource(orig);
						// continue - ignore any clause containing a model field that is not represented
					} catch (JmlNotImplementedException e) {
						notImplemented(clause.clauseKind.keyword() + " clause containing ", e, clause.source());
						continue;
					} finally {
						conditionAssociatedClause = null;
					}

				}
				if (!sawSignalsOnly && rac) {
					sawSomeSpecs = true;
					currentStatements = exsuresStats;
					axiomBlock = exsuresAxiomBlock;
					ListBuffer<JCStatement> ch = pushBlock();
					try {
						JCIdent exceptionId = treeutils.makeIdent(scase.pos, exceptionSym);
						DiagnosticPosition pos = null;
						JCExpression condd = treeutils.makeThrownPredicate(scase, exceptionId, methodDecl);
						addAssert(methodDecl, Label.SIGNALS_ONLY, condd, pos == null ? methodDecl : pos,
								log.currentSourceFile(),
								treeutils.makeUtilsMethodCall(methodDecl.pos, "getClassName", exceptionId));
					} finally {
						addStat(popBlock(methodDecl, ch));
					}
				}
			}
			if (!sawSomeSpecs) {
				currentStatements = exsuresStats;
				axiomBlock = exsuresAxiomBlock;
				ListBuffer<JCStatement> ch = pushBlock();
				try {
					JCIdent exceptionId = treeutils.makeIdent(methodDecl.pos, exceptionSym);
					JCExpression rex = treeutils.makeType(methodDecl.pos, syms.runtimeExceptionType);
					JCExpression condd = M.at(methodDecl).TypeTest(exceptionId, rex).setType(syms.booleanType);
					DiagnosticPosition pos = null;
					for (JCExpression ex : methodDecl.thrown) {
						if (pos == null)
							pos = ex;
						JCExpression tc = M.at(ex).TypeTest(exceptionId, ex).setType(syms.booleanType);
						condd = treeutils.makeOr(ex.pos, condd, tc);
					}
					if (rac) {
						addAssert(methodDecl, Label.SIGNALS_ONLY, condd, pos == null ? methodDecl : pos,
								log.currentSourceFile(),
								treeutils.makeUtilsMethodCall(methodDecl.pos, "getClassName", exceptionId));
					} else {
						addAssert(methodDecl, Label.SIGNALS_ONLY, condd, pos == null ? methodDecl : pos,
								log.currentSourceFile());
					}
				} finally {
					addStat(popBlock(methodDecl, ch));
				}
			}

		}

		methodPos = methodDecl;

		if (rac) {
			Name n;
			JCVariableDecl vd;
			JCIdent ex;

			{
				n = names.fromString("postEx");
				vd = treeutils.makeVarDef(syms.runtimeExceptionType, n, methodDecl.sym, methodDecl.pos);
				ex = treeutils.makeIdent(methodDecl.pos, vd.sym);
				JCExpression str = treeutils.makeStringLiteral(methodDecl.pos,
						"Runtime exception while evaluating postconditions - postconditions are undefined in JML");
				JCStatement st = methodCallUtilsStatement(methodDecl, "reportException", str, ex);
				JCBlock bl = M.at(methodDecl.pos).Block(0, List.<JCStatement>of(st));
				JCCatch catcher = M.at(methodDecl.pos).Catch(vd, bl);
				bl = M.at(methodDecl.pos).Block(0, ensuresStats.toList());
				ensuresStats = new ListBuffer<JCStatement>();
				boolean quiet = utils.jmlverbose == 0;
				DiagnosticPosition pos = methodDecl;
				JCCatch catcher1;
				vd = treeutils.makeVarDef(utils.createClassSymbol("java.lang.NoSuchMethodError").type,
						names.fromString("noSuchMethodError"), methodDecl.sym, pos.getPreferredPosition());
				if (quiet) {
					catcher1 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>nil()));
				} else {
					JCExpression id = treeutils.makeIdent(pos.getPreferredPosition(), vd.sym);
					JCExpression location = treeutils.makeStringLiteral(pos.getPreferredPosition(),
							utils.locationString(pos, log.currentSourceFile()));
					location = treeutils.makeNullLiteral(pos.getPreferredPosition()); // FIXME - really need to
																						// propagate the location of the
																						// call
					JCMethodInvocation m = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(),
							"reportNoSuchMethod", id, location);
					catcher1 = M.at(pos).Catch(vd,
							M.Block(0L, List.<JCStatement>of(M.at(pos.getPreferredPosition()).Exec(m))));
				}
				JCCatch catcher2;
				vd = treeutils.makeVarDef(utils.createClassSymbol("java.lang.NoSuchFieldError").type,
						names.fromString("noSuchFieldError"), methodDecl.sym, pos.getPreferredPosition());
				if (quiet) {
					catcher2 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>nil()));
				} else {
					JCExpression id = treeutils.makeIdent(pos.getPreferredPosition(), vd.sym);
					JCExpression location = treeutils.makeStringLiteral(pos.getPreferredPosition(),
							utils.locationString(pos, log.currentSourceFile()));
					if (Utils.testingMode)
						location = treeutils.makeNullLiteral(pos.getPreferredPosition());
					JCMethodInvocation m = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(),
							"reportNoSuchField", id, location);
					catcher2 = M.at(pos).Catch(vd,
							M.Block(0L, List.<JCStatement>of(M.at(pos.getPreferredPosition()).Exec(m))));
				}
				if (!bl.stats.isEmpty()) {
					if (isOnlyComment(bl)) {
						ensuresStats.add(bl);
					} else {
						st = M.at(methodDecl.pos).Try(bl, List.<JCCatch>of(catcher, catcher1, catcher2), null);
						ensuresStats.add(st);
					}
				}
			}

			if (!isConstructor) {

				n = names.fromString("sigEx");
				vd = treeutils.makeVarDef(syms.runtimeExceptionType, n, methodDecl.sym, methodDecl.pos);
				ex = treeutils.makeIdent(methodDecl.pos, vd.sym);
				JCExpression str = treeutils.makeStringLiteral(methodDecl.pos,
						"Runtime exception while evaluating exceptional postconditions - signals clauses are undefined in JML");
				JCStatement st = methodCallUtilsStatement(methodDecl, "reportException", str, ex);
				JCBlock bl = M.at(methodDecl.pos).Block(0, List.<JCStatement>of(st));
				JCCatch catcher = M.at(methodDecl.pos).Catch(vd, bl);
				bl = M.at(methodDecl.pos).Block(0, exsuresStats.toList());
				exsuresStats = new ListBuffer<JCStatement>();
				boolean quiet = utils.jmlverbose == 0;
				DiagnosticPosition pos = methodDecl;
				JCCatch catcher1;
				vd = treeutils.makeVarDef(utils.createClassSymbol("java.lang.NoSuchMethodError").type,
						names.fromString("noSuchMethodError"), methodDecl.sym, pos.getPreferredPosition());
				if (quiet) {
					catcher1 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>nil()));
				} else {
					JCExpression id = treeutils.makeIdent(pos.getPreferredPosition(), vd.sym);
					JCExpression location = treeutils.makeStringLiteral(pos.getPreferredPosition(),
							utils.locationString(pos, log.currentSourceFile()));
					location = treeutils.makeNullLiteral(pos.getPreferredPosition()); // FIXME - really need to
																						// propagate the location of the
																						// call
					JCMethodInvocation m = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(),
							"reportNoSuchMethod", id, location);
					catcher1 = M.at(pos).Catch(vd,
							M.Block(0L, List.<JCStatement>of(M.at(pos.getPreferredPosition()).Exec(m))));
				}
				JCCatch catcher2;
				vd = treeutils.makeVarDef(utils.createClassSymbol("java.lang.NoSuchFieldError").type,
						names.fromString("noSuchFieldError"), methodDecl.sym, pos.getPreferredPosition());
				if (quiet) {
					catcher2 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>nil()));
				} else {
					JCExpression id = treeutils.makeIdent(pos.getPreferredPosition(), vd.sym);
					JCExpression location = treeutils.makeStringLiteral(pos.getPreferredPosition(),
							utils.locationString(pos, log.currentSourceFile()));
					if (Utils.testingMode)
						location = treeutils.makeNullLiteral(pos.getPreferredPosition());
					JCMethodInvocation m = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(),
							"reportNoSuchField", id, location);
					catcher2 = M.at(pos).Catch(vd,
							M.Block(0L, List.<JCStatement>of(M.at(pos.getPreferredPosition()).Exec(m))));
				}
				if (!bl.stats.isEmpty()) {
					if (isOnlyComment(bl)) {
						exsuresStats.add(bl);
					} else {
						st = M.at(methodDecl.pos).Try(bl, List.<JCCatch>of(catcher, catcher1, catcher2), null);
						exsuresStats.add(st);
					}
				}

			}

		}

		if (ensuresStats.isEmpty() && exsuresStats.isEmpty()) {
			// skip
		} else {
			ensuresStats.prepend(comment(methodDecl.pos(), "Checking normal postconditions", null));
			exsuresStats.prepend(comment(methodDecl.pos(), "Checking exceptional postconditions", null));
			pushBlock(finalizeStats);
			noException = newTempIfNeeded(noException);
			popBlock();
			JCStatement ifstat = M.at(methodPos).If(noException, M.Block(0, ensuresStats.toList()),
					M.Block(0, exsuresStats.toList()));
			finalizeStats.add(ifstat);
		}
//		paramActuals_ = null;
		clearInvariants();
		currentStatements = savedCurrentStatements;
		axiomBlock = null;
		assumingPostConditions = true;
	}

	protected void addInstanceInitialization(Symbol methodSym) {
		JmlSpecs.TypeSpecs tspecs = specs.getAttrSpecs(classDecl.sym);

		addStat(comment(methodDecl, "Class fields for constructor", null));
		// First pass sets everything to zero-equivalent
		for (JCTree t : classDecl.defs) {
			if (!(t instanceof JCVariableDecl))
				continue;
			JCVariableDecl vd = (JCVariableDecl) t;
			if (utils.isJMLStatic(vd.sym)) continue; // FIXME - static fields have to be created sooner
			if (isModel(vd.sym) && vd.init == null) continue;
			JCExpression field = treeutils.makeIdent(vd.pos, vd.sym);
			field = convertJML(field);
			JCExpression z = treeutils.makeZeroEquivalentLit(vd.pos, vd.type);
			addAssumeEqual(vd.pos(), Label.IMPLICIT_ASSUME, field, z);
		}
	}

	protected void addInstanceInitializationPass2() {
		JmlSpecs.TypeSpecs tspecs = specs.getAttrSpecs(classDecl.sym);

		// If there is an initializer, use it
		if (tspecs != null) {
			for (JmlTypeClause tc : tspecs.clauses) {
				if (tc instanceof JmlTypeClauseInitializer && (tc.modifiers.flags & Flags.STATIC) == 0) {
					JmlTypeClauseInitializer tci = (JmlTypeClauseInitializer) tc;
					addStat(comment(methodDecl, "Instance initializer: " + classDecl.sym, null));
					if (tci.specs != null)
						for (JmlSpecificationCase cs : tci.specs.cases) {
							// FIXME - visibility?
							JCExpression pre = null;
							JCExpression post = null;
							for (JmlMethodClause clause : cs.clauses) {
								if (clause.clauseKind == requiresClauseKind) {
									JCExpression p = convertJML(((JmlMethodClauseExpr) clause).expression);
									pre = pre == null ? p : treeutils.makeAnd(clause.pos, pre, p);
								} else if (clause.clauseKind == MethodExprClauseExtensions.ensuresClauseKind) {
									JCExpression p = convertJML(((JmlMethodClauseExpr) clause).expression);
									post = post == null ? p : treeutils.makeAnd(clause.pos, post, p);
								} else {
									notImplemented(clause,
											"Clause not implemented in an initializer: " + clause.keyword);
								}
							}
							if (post == null)
								post = treeutils.trueLit;
							addAssume(tc, Label.POSTCONDITION, post);
						}
					return; // There must be at most one initializer
				}
			}
		}
		addStat(comment(methodDecl, "Initializing Class fields for constructors", null));
		// Second pass computes the initialized result
		for (JCTree t : classDecl.defs) {
			if (t instanceof JCVariableDecl) {
				JCVariableDecl vd = (JCVariableDecl) t;
				if (vd.init == null) continue;
				if (utils.isJMLStatic(vd.sym)) continue; // FIXME - static fields have to be created sooner
				// if (isModel(vd.sym)) continue;
				JCExpression receiver;
				receiver = treeutils.makeIdent(vd.pos, vd.sym);
				receiver = convertJML(receiver);
				JCExpression e = convertExpr(vd.init);
				e = addImplicitConversion(e, vd.type, e);
				addStat(treeutils.makeAssignStat(vd.pos, receiver, e));
			} else if (t instanceof JCBlock) {
				if (((JCBlock) t).isStatic())
					continue;
				convert(t);
			}
		}
	}

	protected void addStaticInitialization(ClassSymbol csym) {
		JmlSpecs.TypeSpecs tspecs = specs.getAttrSpecs(csym);

		// If there is a static initializer, use it
		if (tspecs != null) {
			{
				JmlTypeClauseInitializer tci = tspecs.staticInitializerSpec;
				if (tci != null && tci.specs != null) { // FIXME check that tci.specs == null when there is a naked
														// static_initializer clause -- should it be null or empty?
					JavaFileObject prev = log.currentSourceFile();
					for (JmlSpecificationCase cs : tci.specs.cases) {
						log.useSource(cs.source());
						// FIXME - visibility?
						JCExpression pre = null;
						JCExpression post = null;
						for (JmlMethodClause clause : cs.clauses) {
							if (clause.clauseKind == requiresClauseKind) {
								JCExpression p = convertJML(((JmlMethodClauseExpr) clause).expression);
								pre = pre == null ? p : treeutils.makeAnd(clause.pos, pre, p);
							} else if (clause.clauseKind == MethodExprClauseExtensions.ensuresClauseKind) {
								JCExpression p = convertJML(((JmlMethodClauseExpr) clause).expression);
								post = post == null ? p : treeutils.makeAndSimp(clause.pos, post, p);
							} else {
								notImplemented(clause, "Clause not implemented in an initializer: " + clause.keyword);
							}
						}
						if (post == null)
							post = treeutils.trueLit;
						addAssume(tci, Label.POSTCONDITION, post);
					}
					log.useSource(prev);
					return; // There must be at most one static initializer
				}
			}
		}

		// We could declare and initialize all the static fields here, but that results
		// in
		// declarations of many fields that may not be needed. So static final fields
		// are
		// declared on demand (as part of 'discovered' fields)

//        if (true) return;
//        
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
//                if (!d.sym.isStatic()) continue;   // FIXME _ JML static?
//                alreadyDiscoveredFields.add(d.sym);
//                JCIdent id = treeutils.makeIdent(d.pos, d.sym);
//                JCExpression z = treeutils.makeZeroEquivalentLit(d.pos,d.type);
//                addStat(treeutils.makeAssignStat(d.pos, id, z));
//            }
//        }
//        
//        pushBlock();
//        for (JCTree t: decl.defs) {
//            if (t instanceof JmlVariableDecl) {
//                JmlVariableDecl d = (JmlVariableDecl)t;
//                if (!d.sym.isStatic()) continue;   // FIXME _ JML static?
//                if (d.init == null) continue;
//                JCIdent id = treeutils.makeIdent(d.pos, d.sym);
//                JCExpression z = addImplicitConversion(d, d.type, convertExpr(d.init));
//                addAssumeCheck(t,currentStatements,"Extra-Assume");  
//                addStat(treeutils.makeAssignStat(d.pos, id, z));
//                addAssumeCheck(t,currentStatements,"Extra-Assume");  
//           }
//        }
//        DiagnosticPosition p = decl.pos();
//        JCBlock bl = popBlock(p);
//        pushBlock();
//        addAssert(p,Label.EXPLICIT_ASSERT,treeutils.makeBooleanLiteral(p.getPreferredPosition(),false));
//        JCBlock cb = popBlock(p);
//
//        JCVariableDecl exceptionDecl = newTempDecl(p,syms.exceptionType);
//        JCCatch catcher = M.Catch(exceptionDecl,cb);
//        JCStatement t = M.Try(bl,List.<JCCatch>of(catcher),null);
//        addStat(t);
	}

	// VISITOR METHODS

	// OK
	@Override
	public void visitTopLevel(JCCompilationUnit that) {
		if (translatingJML) {
			error(that, "Unexpected call of JmlAssertionAdder.visitTopLevel while translating JML: " + that.getClass());
			result = that;
		} else {
			JmlCompilationUnit jcu = (JmlCompilationUnit) that;
			List<JCTree> defs = convert(that.defs);
			JmlCompilationUnit n = M.at(that).TopLevel(defs);
			n.docComments = that.docComments; // FIXME: need to translate map
			n.endPositions = that.endPositions; // FIXME: need to convert map?
			// n.flags = that.flags;
			n.pid = jcu.pid;
			n.lineMap = that.lineMap;
			n.namedImportScope = that.namedImportScope;
			n.packge = that.packge;
			n.setType(that.type);
			// n.parsedTopLevelModelTypes = that.parsedTopLevelModelTypes; // FIXME: need to
			// convert
			n.sourcefile = that.sourcefile;
			n.starImportScope = that.starImportScope;
			n.specsCompilationUnit = jcu.specsCompilationUnit; // FIXME: need to convert
			// n.specsTopLevelModelTypes = convert(that.specsTopLevelModelTypes);
			result = n;
		}
	}

	// OK
	@Override
	public void visitImport(JCImport that) {

		JCTree qualid = that.qualid;
        // FIXME - need to rewrite qualid - might have a *; might have a method name
		if (fullTranslation)
			qualid = convert(qualid);
        result = M.at(that).JmlImport(qualid, that.staticImport, ((JmlImport)that).isModel).setType(that.type);
	}

	// OK
	@Override
	public void visitClassDef(JCClassDecl that) {
		// OpenJML should never call this, because JCClassDecl nodes should be
		// replaced by JmlClassDecl nodes. We implement this just in case, but
		// always produce a JmlClassDecl node.

		if (translatingJML) {
			error(that, "Unexpected call of JmlAssertionAdder.visitClassDef while translating JML: " + that.getClass());
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
		if (translatingJML) {
			error(that,
					"Unexpected call of JmlAssertionAdder.visitMethodDef while translating JML: " + that.getClass());
		} else {
			error(that, "Unexpected visit call in JmlAssertionAdder.visitMethodDef: " + that.getClass());
		}
		return;
	}

	// OK
	@Override
	public void visitVarDef(JCVariableDecl that) {
		if (translatingJML) {
			error(that, "Unexpected call of JmlAssertionAdder.visitVarDef while translating JML: " + that.getClass());
		} else {
			error(that, "Unexpected visit call in JmlAssertionAdder.visitVarDef: " + that.getClass());
		}
		return;
	}

	// OK
	@Override
	public void visitSkip(JCSkip that) {
		addTraceableComment(that);
		result = addStat(M.at(that).Skip());
		// Caution - JML statements are subclasses of JCSkip
	}

	/**
	 * Produces a MethodSym for an initialization block; any variables declared
	 * within an initialization block need a 'method' as an owner rather than a
	 * class, or they will be interpreted as class fields.
	 */
	protected JmlMethodDecl methodSymForInitBlock(DiagnosticPosition pos, long flags, JCClassDecl classDecl) {
		MethodSymbol msym = new MethodSymbol(flags, classDecl.name, null, classDecl.sym);
		methodDecl = M.MethodDef(
				M.Modifiers(flags, M.Annotations(List.<com.sun.tools.javac.code.Attribute.Compound>nil())),
				classDecl.name, null, null, null, null, null, null, // body,
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

	// OK
	@Override
	public void visitBlock(JCBlock that) {
		JmlMethodDecl prev = this.methodDecl;
		boolean isInInitializerBlock = currentStatements == null;
		if (isInInitializerBlock) {
			// We are in an initializer block
			// We need a method symbol to be the owner of declarations
			// (otherwise they will have the class as owner and be thought to
			// be fields)
			methodDecl = methodSymForInitBlock(that, that.flags, classDecl);

		}
		ListBuffer<JCStatement> check = pushBlock();
		boolean pv = checkAccessEnabled; // FIXME - when to check access of initializer stastements?
		checkAccessEnabled = false;
		try {
			if (isInInitializerBlock) {
				initialize2(that.flags & Flags.STATIC);
			}
			for (JCStatement s : that.stats) {
				scan(s);
				if (continuation != Continuation.CONTINUE) {
					break;
				}
			}
		} catch (Exception e) {
			utils.unexpectedException(e, "Exception: inlining");
			throw e;
		} finally {
			checkAccessEnabled = pv;
			JCBlock bl = popBlock(that.flags, that, check);
			if (isInInitializerBlock) { // FIXME - need a better way to tell which kind of block we are in
				classDefs.add(bl);
			} else {
				addStat(bl); // FIXME - don't always want this
			}
			methodDecl = prev;
			result = bl;
		}
	}

	// OK - should call visitJmlDoWhileLoop instead
	@Override
	public void visitDoLoop(JCDoWhileLoop that) {
		error(that, "Unexpected visit call in JmlAssertionAdder.visitDoLoop: " + that.getClass());
	}

	// OK - should call visitJmlWhileLoop instead
	@Override
	public void visitWhileLoop(JCWhileLoop that) {
		error(that, "Unexpected visit call in JmlAssertionAdder.visitWhileLoop: " + that.getClass());
	}

	// OK - should call visitJmlForLoop instead
	@Override
	public void visitForLoop(JCForLoop that) {
		error(that, "Unexpected visit call in JmlAssertionAdder.visitForLoop: " + that.getClass());
	}

	// OK - should call visitJmlEnhancedForLoop instead
	@Override
	public void visitForeachLoop(JCEnhancedForLoop that) {
		error(that, "Unexpected visit call in JmlAssertionAdder.visitForeachLoop: " + that.getClass());
	}

	/**
	 * This map contains an entry for all labels that are in scope. It is used when
	 * an \old expression appears that references the label: in RAC mode we need to
	 * insert a computation of the desired quantity.
	 */ // FIXME - determine if these need to be two separate lists. The difference at
		// present is that those in the active list are not yet closed.

	public static class LabelProperties {
		int allocCounter;
		int heapCount;
		JmlLabeledStatement labeledStatement;
		TranslationEnv labelEnv;
		public Name name;
		public ListBuffer<JCStatement> extraStats() {
			return labeledStatement.extraStatements;
		}
	}

	public static class LabelPropertyStore {
		Map<Name, Stack<LabelProperties>> map = new HashMap<>();

		public void put(Name label, LabelProperties props) {
			Stack<LabelProperties> st = map.get(label);
			if (st == null)
				map.put(label, st = new Stack<LabelProperties>());
			st.push(props);
		}

		public LabelProperties get(Name label) {
			Stack<LabelProperties> st = map.get(label);
			if (st == null)
				return null;
			// FIXME _ error if sst is null or st.isEmpty()
			return st.peek();
		}

		public void pop(Name label) {
			Stack<LabelProperties> st = map.get(label);
			// FIXME _ error if st == null
			st.pop();
			// FIXME _ error if sts.isEmpty();
		}
		
        public String toString() {
            String s = "[ ";
            for (var e: map.entrySet()) { s += e.getKey() + "->" + e.getValue() + " "; }
            return s + "]";
        }
        
        public String keysToString() {
            String s = "[ ";
            for (var e: map.entrySet()) { s += e.getKey() + " "; }
            return s + "]";
        }
	}

	protected LabelPropertyStore labelPropertiesStore = new LabelPropertyStore();

	protected LabelProperties recordLabel(Name labelName, JmlLabeledStatement stat) {
		LabelProperties lp = new LabelProperties();
		labelPropertiesStore.put(labelName, lp);
		lp.labeledStatement = stat;
		lp.name = labelName;
		lp.heapCount = heapCount;
		lp.allocCounter = allocCounter;
		lp.labelEnv = currentEnv.newEnvCopy();
		lp.labelEnv.stateLabel = labelName;
		return lp;
	}

	// OK
	@Override
	public void visitLabelled(JCLabeledStatement that) {
		addStat(comment(that, "label:: " + that.label + ": ...", null));
		// Note that the labeled statement will turn into a block
		// Since declarations may not be labelled statements, there are no
		// declarations in the labelled statement that need to be in scope after
		// the labelled statement.
		JmlLabeledStatement stat = M.at(that).JmlLabeledStatement(that.label, null, null);
		recordLabel(that.label, stat);
		markLocation(that.label, currentStatements, stat);
		treeMap.put(that, stat); // we store the mapping from old to new so that we can appropriately translate
									// the targets of break and continue statements

		JCBlock block;
		try {
			boolean isLoop = that.body instanceof IJmlLoop;
			block = convertIntoBlock(that, that.body);
			if (isLoop) {
				JCStatement s = block.stats.last();
				List<JCStatement> list = ((JCBlock) s).stats;
				int len = list.size();
				JCStatement ss = list.last();
				Name label2 = names.fromString("_$" + that.label.toString());
				JmlLabeledStatement stat2 = M.at(that).JmlLabeledStatement(label2, null, ss);
				((JCBlock) s).stats = len == 1 ? List.<JCStatement>of(list.get(0), stat2)
						: List.<JCStatement>of(list.get(0), list.get(1), stat2);
				result = addStat(block);
				recordLabel(label2, stat2);
			} else {
				stat.body = block;
				result = addStat(stat);
			}
		} finally {
			treeMap.remove(that); // Remove the statement because we are leaving the scope of the label
		}
	}

	Type getLambdaReturnType(JCLambda that) {
		ClassType ctype = (ClassType) that.type;
		TypeSymbol csym = ctype.tsym;
		for (Symbol sym : csym.getEnclosedElements()) {
			if (sym instanceof MethodSymbol) {
				MethodSymbol msym = (MethodSymbol) sym;
				if (msym.isDefault())
					continue;
				if ((msym.flags() & Flags.ABSTRACT) != 0) {
					// Should check that ther is just one abstract method,
					// but it would not be the type of a lmbda if that were not the case

					return msym.getReturnType();
				}
			}
		}
		return null; // ERROR
	}

	boolean translatingLambda = false;

	Map<String, Pair<JCLambda, JCExpression>> lambdaLiterals = new HashMap<>();

	@Override
	public void visitLambda(JCLambda that) {
		if (convertingAssignable) {
			result = eresult = that;
			return;
		}
		if (rac) {
			// FIXME - currently there is no rewriting for checking within RAC
			result = eresult = copy(that);
			return;
		}

		boolean b = JmlOption.isOption(context, JmlOption.INLINE_FUNCTION_LITERAL);

		int n = lambdaLiterals.size();
		String nm = "$$JML$LAMBDALIT_" + n;
		lambdaLiterals.put(nm, new Pair<>(that, currentEnv.currentReceiver));
		JCVariableDecl d = treeutils.makeVarDef(that.type, names.fromString(nm), methodDecl.sym, Flags.FINAL, that.pos);
		addStat(d);
		JCIdent id = treeutils.makeIdent(that.pos, d.sym);
		id.type = that.type;
		addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeNotNull(that.pos, id));

		JCExpression savedExpr = resultExpr;
		resultExpr = null;
		Type returnType = getLambdaReturnType(that);
		;
		JCTree body = that.body;
		if (that.body instanceof JCExpression) {
			if (returnType == null || returnType.getTag() == TypeTag.VOID) {
				returnType = syms.voidType;
				JCStatement stat = M.Exec((JCExpression) that.body);
				body = M.Block(0L, List.<JCStatement>of(stat));
			} else {
				JCStatement stat = M.Return((JCExpression) that.body);
				body = M.Block(0L, List.<JCStatement>of(stat));
			}
		} else if (that.type.getTypeArguments().size() == 0) {
			// returnType = null; // FIXME - perhaps needed if returnType is a type variable
		} else {
			List<Type> typeargs = that.type.getTypeArguments();
			returnType = typeargs.get(typeargs.size() - 1); // FIXME M- tyhis is only coprtrectx for Function typoes./
		}
		boolean isVoid = returnType == null || returnType.getTag() == TypeTag.VOID;
		if (!isVoid)
			addStat(comment(that, "return result for inlined lambda expression", log.currentSourceFile()));
		JCIdent localResult = isVoid ? null : M.Ident("");
		if (!isVoid)
			localResult.setType(returnType);
		resultExpr = localResult;

		ListBuffer<JCStatement> saved = collectedAxioms;
		collectedAxioms = new ListBuffer<JCStatement>();
//        ListBuffer<JCStatement> check = pushBlock();
//        resultExpr = localResult;
//        resultSym = localResult == null ? null : (VarSymbol)localResult.sym;
		boolean savedTL = translatingLambda;
		int saveHC = heapCount;
		try {
			translatingLambda = true;
			body = copy(body);
//            if (!isVoid && that.body instanceof JCExpression) {
//                addStat(treeutils.makeAssignStat(that.body.pos,localResult,eresult));
//            }
//            JCBlock bl = popBlock(that.pos(), check);
//            JCStatement stat = M.JmlLabeledStatement(breakName, null, bl);
//            bl = M.at(that).Block(0L, List.<JCStatement>of(stat));
			JmlLambda lam = M.Lambda(that.params, body);
			lam.sourceLocation = ((JmlLambda) that).sourceLocation;
			lam.literal = id;
			result = eresult = lam;
			eresult.pos = that.pos;
			eresult.type = that.type;
//            addStat(bl);
//            JCLambda newlambda = M.at(that.pos).Lambda(that.params,bl);
//            newlambda.type = that.type;
//            result = eresult = localResult;
		} finally {
			heapCount = saveHC;
			translatingLambda = savedTL;
			addStat(M.Block(0L, collectedAxioms.toList()));
			resultExpr = savedExpr;
			collectedAxioms = saved;
//            resultExpr = inlinedReturns.pop();
//            resultSym = resultExpr == null ? null : (VarSymbol)(((JCIdent)resultExpr).sym);
//            for (JCVariableDecl param: that.params) {
//                localVariables.remove(param.sym);
//            }
		}
	}

	Map<Name, JmlLabeledStatement> breakNames = new HashMap<>();

	public JCExpression inlineBlock(JCBlock block, Map<Object, JCExpression> replacements, Type returnType) {
		DiagnosticPosition pos = block;
		Name breakName = names.fromString("JMLBreakForReturn_" + (++lblUnique));
		JCIdent returnId = null;
		if (returnType.getTag() != TypeTag.VOID)
			returnId = newTemp(pos, returnType);
		JmlLabeledStatement labeled = M.JmlLabeledStatement(breakName, null, null);
		treeMap.put(labeled, labeled);
		breakNames.put(breakName, labeled);
		JmlTreeInline inliner = new JmlTreeInline(M, replacements, returnId, breakName, labeled);
		JCTree outBlock = inliner.copy(block);
		breakNames.remove(breakName);
		labeled.body = (JCBlock) outBlock;
		addStat(labeled);
		JCExpression ex = null;
		if (returnId != null)
			ex = addImplicitConversion(block, returnType, returnId);
		return ex;
	}

	public JCExpression inlineConvertBlock(JCBlock block, Map<Object, JCExpression> replacements, Type returnType) {
		if (!splitExpressions && block.stats.size() == 1 && block.stats.head instanceof JCReturn) {
			// Simple expression block
			JCExpression expr = ((JCReturn) block.stats.head).expr;
			JCExpression newexpr = JmlTreeSubstitute.substitute(M, expr, replacements);
			return newexpr;
		}
		DiagnosticPosition pos = block;
		Name breakName = names.fromString("JMLBreakForReturn_" + (++lblUnique));
		JCIdent returnId = null;
		if (returnType.getTag() != TypeTag.VOID)
			returnId = newTemp(pos, returnType);
		JmlLabeledStatement labeled = M.JmlLabeledStatement(breakName, null, null);
		treeMap.put(labeled, labeled);
		breakNames.put(breakName, labeled);
		JmlTreeInline inliner = new JmlTreeInline(M, replacements, returnId, breakName, labeled);
		JCTree outBlock = inliner.copy(block);
		breakNames.remove(breakName);
		outBlock = convertBlock((JCBlock) outBlock);
		labeled.body = (JCBlock) outBlock;
		addStat(labeled);
		JCExpression ex = null;
		if (returnId != null)
			ex = addImplicitConversion(block, returnType, returnId);
		return ex;
	}

	public void inlineConvertBlock(DiagnosticPosition pos, JCExpression pre, JCBlock block, String place) {
		ListBuffer<JCStatement> checkInline = pushBlock();
		Name savedName = breakName;
		breakName = names.fromString("JMLBreakForReturn_" + (++lblUnique));
		JmlLabeledStatement labeled = M.JmlLabeledStatement(breakName, null, null);
		breakNames.put(breakName, labeled);
		treeMap.put(labeled, labeled);
		try {
			visitBlock(block);

		} catch (Exception e) {
			System.out.println("BLCK: " + block);
			e.printStackTrace(System.out);
			error(pos, "Unexpected exception while inlining " + place + ":" + e.toString());
		} catch (Error e) {
			error(pos, "Unexpected exception while inlining " + place + ":" + e.toString());
			throw e;
		} finally {
			breakNames.remove(breakName);
			breakName = savedName;
		}
		JCBlock b = popBlock(pos, checkInline);
		labeled.body = b;
		if (treeutils.isTrueLit(pre)) {
			addStat(labeled);
		} else {
			b = M.Block(0L, List.<JCStatement>of(labeled));
			JCStatement stat = M.If(pre, b, null);
			addStat(stat);
		}
	}

	@Override
	public void visitReference(JCTree.JCMemberReference that) {
		JCExpression expr = convertExpr(that.expr);
		JCTree.JCMemberReference mref = M.Reference(that.mode, that.name, expr, that.typeargs);
		mref.type = that.type;
		mref.sym = that.sym;
		result = eresult = mref;
	}

	protected void checkCompatibleSpecs(JCTree.JCMemberReference that, Type inface) {
		if (!(inface instanceof Type.ClassType))
			return;
		// JmlMethodSpecs mspecs = specs.getDenestedSpecs((MethodSymbol)that.sym,false);
		MethodSymbol targetSym = getFunctional((Type.ClassType) inface);
		if (targetSym == null) {
			log.error(that.pos, "jml.bad.method.reference.conversion", that.toString(), inface.tsym.toString());
			return;
		}
		JCExpression e = treeutils.trueLit;
		e = makeAssertionOptional(e);
		addAssert(false, that, Label.POSSIBLY_INCOMPATIBLE_FUNCTIONAL_SPECS, e, null, null, null);
	}

	protected void checkCompatibleSpecs(JCTree.JCLambda that, Type inface) {
		MethodSymbol targetSym = getFunctional((Type.ClassType) inface);
		if (targetSym == null) {
			log.error(that.pos, "jml.bad.lambda.conversion", inface.tsym.toString());
			;
			return;
		}
		JCExpression e = treeutils.trueLit;
		e = makeAssertionOptional(e);
		addAssert(false, that, Label.POSSIBLY_INCOMPATIBLE_FUNCTIONAL_SPECS, e, null, null, null);
	}

	protected /* @ nullable */ MethodSymbol getFunctional(Type.ClassType inface) {
		MethodSymbol functional = null;
		for (Symbol sym : inface.tsym.getEnclosedElements()) {
			if (sym instanceof MethodSymbol && (sym.flags() & Flags.ABSTRACT) != 0
					&& (sym.flags() & Flags.DEFAULT) == 0) {
				if (functional != null) {
					return null;
				}
				functional = (MethodSymbol) sym;
			}
		}
		return functional;
	}
	
	// FIXME - pattern matching - statement and expression
	// FIXME - symbolic names for patterns
	// FIXME - inline expressions
	// FIXME - RAC
	
	@Override
	public void visitSwitchExpression(JCSwitchExpression that) {
        addStat(traceableComment(that, that, "switch " + that.getExpression() + " ...", "Selection"));
        currentEnv = currentEnv.pushEnvCopy();
        try {
            currentEnv.yieldIdent = treeutils.makeIdent(that.pos,  "`switchResult_"+nextUnique(), that.type);
            if (splitExpressions) {
                addStat(switchHelper(that, that.selector, that.cases).setType(that.type));
                result = eresult = currentEnv.yieldIdent;
            } else {
                notImplemented(that,  "Switch expression in a quantified expression");
            }
        } finally {
            currentEnv = currentEnv.popEnv();
        }
    }
	
	public JCExpression switchCheck(JCExpression switchExpr) {
        JCExpression selector = convertExpr(switchExpr);
        // FIXME - will need fixing for pattern matching
        if (selector.type.equals(syms.stringType)) {
            JCExpression e = treeutils.makeNeqObject(switchExpr.pos, selector, treeutils.nullLit);
            addJavaCheck(switchExpr, e, Label.POSSIBLY_NULL_VALUE, Label.POSSIBLY_NULL_VALUE,
                                    "java.lang.NullPointerException");
        } else if ((switchExpr.type.tsym.flags_field & Flags.ENUM) != 0) {
            JCExpression e = treeutils.makeNeqObject(switchExpr.pos, selector, treeutils.nullLit);
            addJavaCheck(switchExpr, e, Label.POSSIBLY_NULL_VALUE, Label.POSSIBLY_NULL_VALUE,
                                    "java.lang.NullPointerException");
        } else {
            selector = addImplicitConversion(switchExpr, syms.intType, selector);
        }
        return selector;
	}
	
	public JCSwitch switchHelper(DiagnosticPosition pos, JCExpression switchExpr, List<JCCase> cases) {
	    JCExpression selector = switchCheck(switchExpr);
	    JCSwitch newswitch = M.at(pos).Switch(selector, null); // cases filled in later, but we need the new tree reference now
	    // treeMap is used to map break statements to their target statements
        treeMap.put((JCTree)pos, newswitch); // pos must also be the  JCSwitch or JCSwitchExpression
	    try {
	        ListBuffer<JCCase> newcases = new ListBuffer<>();
	        // The value of Continuation says whether it is possible for control flow to continue after the switch
	        // HALT if all branches HALT; otherwise CONTINUE
	        // FIXME - what about the situation of a missing default case and the cases do not cover all possibilities
	        Continuation combined = Continuation.HALT;
	        for (var _case: cases) {
	            continuation = Continuation.CONTINUE;
	            boolean isArrow = _case.caseKind != com.sun.source.tree.CaseTree.CaseKind.STATEMENT;

	            pushBlock();
	            addFeasibilityCheck(_case, currentStatements, Strings.feas_switch, "after case condition");
	            convert(_case.stats); // This might change 'continuation'
	            if (isArrow && _case.completesNormally) {
	                addStat(M.at(_case).Break(null));
	            }
	            JCBlock bl = popBlock(_case);
	            // Have to be careful about blocks
	            // If the case had a block, it must still have a block
	            // If the case did not have a block and is not an arrow case, then it must stay not a block
	            // Otherwise it does not matter.
	            var newcase = M.at(_case).Case(com.sun.source.tree.CaseTree.CaseKind.STATEMENT, _case.labels, _case.guard, bl.stats, bl);
	            newcases.add(newcase);
	            combined = combined.combine(continuation); // FIXME - does this all work for fall-through cases
	        }
	        continuation = combined;
	        newswitch.cases = newcases.toList();
	    } finally {
	        treeMap.remove(pos);
	    }
	    return newswitch;
	}

	// OK
	@Override
	public void visitSwitch(JCSwitch that) {
        addStat(traceableComment(that, that, "switch " + that.getExpression() + " ...", "Selection"));
		boolean split = that instanceof JmlSwitchStatement && ((JmlSwitchStatement) that).split;
		if (!split || currentSplit == null || rac || infer) {
		    JCSwitch newSwitch = switchHelper(that, that.selector, that.cases);
		    ((JmlSwitchStatement) newSwitch).split = ((JmlSwitchStatement) that).split;
		    // record the translation from old to new AST  // FIXME - this used to be before trabnslating the body. Does it matter?
		    result = addStat(newSwitch.setType(that.type)); // But actually, statements do not have a type
		} else {
	        JCExpression selector = switchCheck(that.selector);
	        JCSwitch newswitch = M.at(that).Switch(selector, null); // cases filled in later, but we need the new tree reference now
	        // treeMap is used to map break statements to their target statements
	        treeMap.put(that, newswitch); // pos must also be the  JCSwitch or JCSwitchExpression
	        pushBlock();
		    boolean hasDefault = that.cases.stream().anyMatch(cs -> cs.labels.isEmpty()|| cs.labels.head instanceof JCDefaultCaseLabel);
		    
		    
		    // Since we are doing a split, then we check just one switch case
		    int doCase = 0;
		    if (currentSplit.isEmpty()) {
		        adjustSplit(that.cases.size() + (hasDefault ? 0 : 1));
		    } else {
		        doCase = currentSplit.charAt(0) - 'A';
		        currentSplit = currentSplit.substring(1);
		    }

		    JCCase caseToDo = doCase < that.cases.size() ? that.cases.get(doCase) : null;
		    // caseToDo == null when the original switch has no default case -- so skip everything if no case condition matches
		    // FIXME - only works for traditional enums or ints, not strings or patterns
		    JCExpression caseCondition = null;
		    if (caseToDo != null && !caseToDo.labels.isEmpty()) {
		        for (JCCaseLabel pat : caseToDo.labels) {
	        		if (pat instanceof JCConstantCaseLabel patc) {
	        			JCExpression e = treeutils.makeEquality(pat.pos, selector, convertExpr(patc.expr));
	        			caseCondition = caseCondition == null ? e : treeutils.makeOr(that, caseCondition, e);
	        		}
		        }
		    } else {
		        // default
		        for (JCCase c : that.cases) {
		        	for (var pat : c.labels) {
		        		if (pat instanceof JCConstantCaseLabel patc) {
		                    JCExpression e = treeutils.makeEquality(pat.pos, copy(selector), convertExpr(patc.expr));
		                    caseCondition = caseCondition == null ? e : treeutils.makeOr(that, caseCondition, e);
		        		}
		            }
		        }
		        caseCondition = treeutils.makeNot(that, caseCondition);
		    }

		    if (caseCondition != null) {
		        addAssume(that.pos(), Label.IMPLICIT_ASSUME, caseCondition);
	            addFeasibilityCheck(caseToDo, currentStatements, Strings.feas_switch, "after case condition");
		    }
		    if (caseToDo != null) {
		        convert(caseToDo.stats); // FIXME - does not work for fall through cases
		    }
		    JCBlock newblock = popBlock(that);

		    // From the block we make a single default case
		    JCCase newcase = M.at(that).Case(com.sun.source.tree.CaseTree.CaseKind.STATEMENT, List.<JCCaseLabel>nil(), null, newblock.stats, newblock); // FIXME - check the arguments
		    newswitch.cases = List.<JCCase>of(newcase);
            treeMap.remove(that);
            addStat(newswitch);
            result = newswitch;
		}
	}

	// OK
	@Override
	public void visitCase(JCCase that) {
		// JCCase is handled directly in visitSwitch
		error(that, "JmlAssertionAdder.visitCase should not be called");
	}

	// OK except concurrency checks
	@Override
	public void visitSynchronized(JCSynchronized that) {
		addTraceableComment(that, "synchronized " + that.getExpression() + " ...");
		JCExpression lock = convertExpr(that.lock);
		if (that.lock instanceof JCParens && ((JCParens) that.lock).expr instanceof JCIdent
				&& ((JCIdent) ((JCParens) that.lock).expr).name.toString().equals("this")) {
			// Don't need to check that 'this' is not null, though this is a complicated and
			// error-prone check
		} else {
			JCExpression e = treeutils.makeNeqObject(that.lock.pos, lock, treeutils.nullLit);
			addJavaCheck(that.lock, e, Label.POSSIBLY_NULL_VALUE, Label.POSSIBLY_NULL_VALUE,
					"java.lang.NullPointerException");
		}
		JCBlock block = convertBlock(that.body);
		result = addStat(M.at(that).Synchronized(lock, block).setType(that.type));
		// FIXME - need to add concurrency checks
	}

	protected Name closeName;

	// This translation follows
	// https://docs.oracle.com/javase/specs/jls/se8/html/jls-14.html#jls-ResourceList
	protected void transformTryWithResources(JCTry that) {
		if (that.resources == null || that.resources.isEmpty()) return;

		if (closeName == null) closeName = names.fromString("close");

		JCTree resource = that.resources.head;
		List<JCTree> resourceRest = that.resources.tail;
		int pos = resource.pos;
		JCVariableDecl decl = (JCVariableDecl) resource;
		decl.mods.flags |= Flags.FINAL; // implicitly final

		ListBuffer<JCStatement> stats = new ListBuffer<>();
		stats.add((JCStatement) resource);

		Name throwableName = names.fromString("__JMLthrowableException_" + resource.pos);
		JCVariableDecl throwableDecl = treeutils.makeVarDef(syms.throwableType, throwableName,
				methodDecl != null ? methodDecl.sym : classDecl.sym, resource.pos);
		Type atype = attr.nullableAnnotationSymbol.type;
		throwableDecl.mods.annotations = throwableDecl.mods.annotations
				.append(M.Annotation(M.Type(atype), List.<JCExpression>nil()));
		List<com.sun.tools.javac.util.Pair<Symbol.MethodSymbol, Attribute>> nlist = List.<com.sun.tools.javac.util.Pair<MethodSymbol, Attribute>>nil();
		Compound c = new Attribute.Compound(atype, nlist);
		throwableDecl.sym.appendAttributes(List.<Compound>of(c));
		throwableDecl.init = treeutils.nullLit;
		stats.add(throwableDecl);

		Name catchName = names.fromString("__JMLthrowableCatch_" + resource.pos);
		JCVariableDecl catchDecl = treeutils.makeVarDef(syms.throwableType, catchName,
				methodDecl != null ? methodDecl.sym : classDecl.sym, resource.pos);

		JCExpression exAssign = M.Assign(treeutils.makeIdent(pos, throwableDecl.sym),
				treeutils.makeIdent(pos, catchDecl.sym));
		exAssign.pos = pos;

		JCStatement exStat = M.at(pos).Exec(exAssign);

		JCStatement exThrow = M.Throw(treeutils.makeIdent(pos, throwableDecl.sym));
		exThrow.pos = pos;

		JCCatch newCatch = M.at(pos).Catch(catchDecl, M.at(pos).Block(0L, List.<JCStatement>of(exStat, exThrow)));

		JCIdent id = treeutils.makeIdent(pos, decl.sym);
		MethodSymbol msym = findCloseMethod((ClassSymbol) resource.type.tsym);
		M.at(pos);
		JCExpression fcn1 = M.Select(id, msym);
		fcn1.type = msym.type;
		JCMethodInvocation closeCallExpr1 = M.Apply(List.<JCExpression>nil(), fcn1, List.<JCExpression>nil());
		closeCallExpr1.type = syms.voidType;
		JCExpressionStatement closeCall1 = M.Exec(closeCallExpr1);
		JCExpression fcn2 = M.Select(id, msym);
		fcn2.type = msym.type;
		JCMethodInvocation closeCallExpr2 = M.Apply(List.<JCExpression>nil(), fcn2, List.<JCExpression>nil());
		closeCallExpr2.type = syms.voidType;
		JCExpressionStatement closeCall2 = M.Exec(closeCallExpr2);

		Name closeCatchName = names.fromString("__JMLcloseCatch_" + resource.pos);
		JCVariableDecl closeCatchDecl = treeutils.makeVarDef(syms.throwableType, closeCatchName,
				esc ? null : methodDecl != null ? methodDecl.sym : classDecl.sym, resource.pos);
		JCCatch resourceCloseCatch = M.at(pos).Catch(closeCatchDecl, M.at(pos).Block(0L, List.<JCStatement>nil())); // FIXME
																													// -
																													// should
																													// save
																													// the
																													// suppressed
																													// exception
		JCTry closetry = M.at(pos).Try(List.<JCTree>nil(), M.at(pos).Block(0L, List.<JCStatement>of(closeCall1)),
				List.<JCCatch>of(resourceCloseCatch), null);

        ListBuffer<JCStatement> finalstats = new ListBuffer<>();
        pushBlock(finalstats);
		JCExpression comp = newTempIfNeeded(treeutils.makeNotNull(pos, treeutils.makeIdent(pos, throwableDecl.sym)));
		JCStatement thenpart = M.at(pos).Block(0L, List.<JCStatement>of(
				M.If(comp, M.at(pos).Block(0L, List.<JCStatement>of(closetry)), closeCall2).setType(syms.booleanType)));

		comp = newTempIfNeeded(treeutils.makeNotNull(pos, treeutils.makeIdent(pos, decl.sym)));
		addStat(M.at(pos).If(comp, thenpart, null).setType(syms.booleanType));
		popBlock();
        JCBlock finalBlock = M.at(pos).Block(0L, finalstats.toList());
		
		JCTry newtry = M.at(pos).Try(resourceRest, that.body, List.<JCCatch>of(newCatch), finalBlock);
		stats.add(newtry);

		that.resources = List.<JCTree>nil();
		that.body = M.at(pos).Block(0L, stats.toList());

		if (that.catchers.isEmpty() && that.finalizer == null)
			that.finalizer = M.at(pos).Block(0L, List.<JCStatement>nil());

		// FIXME - if the original try does not have catchers or finally, it can be
		// converted to just a block
		// FIXME - what about finallyCanCompleteNormally in all of the above
		// FIXME - add position, types, symbols
	}

	protected MethodSymbol findParentConstructor(JmlNewClass newcl) {
		JmlMethodDecl md = null;
		x: {
			for (JCTree o : newcl.def.defs) {
				if (o instanceof JmlMethodDecl) {
					md = (JmlMethodDecl) o;
					if (md.sym.isConstructor())
						break x;
				}
			}
			return null;
		}
		JCStatement st = md.body.stats.head;
		JCExpression ex = ((JCMethodInvocation) ((JCExpressionStatement) st).expr).meth;
		if (ex instanceof JCIdent)
			return (MethodSymbol) ((JCIdent) ex).sym;
		if (ex instanceof JCFieldAccess)
			return (MethodSymbol) ((JCFieldAccess) ex).sym;
		return null;
	}

	protected MethodSymbol findCloseMethod(ClassSymbol csym) {
		MethodSymbol msym = null;
		for (Symbol sym : csym.members().getSymbolsByName(closeName)) {
			if (sym instanceof MethodSymbol) {
				MethodSymbol m = (MethodSymbol) sym;
				if (m.getParameters().isEmpty()) {
					return m;
				}
			}
		}
		Type sup = csym.getSuperclass();
		if (sup != null && sup.tsym instanceof ClassSymbol) {
			msym = findCloseMethod((ClassSymbol) sup.tsym);
			if (msym != null)
				return msym;
		}
		for (Type t : csym.getInterfaces()) {
			if (t.tsym instanceof ClassSymbol) {
				msym = findCloseMethod((ClassSymbol) t.tsym);
				if (msym != null)
					return msym;
			}
		}
		log.error("jml.internal", "No close method found for  " + csym);
		return msym;
	}

	// OK
	// FIXME - review and cleanup for both esc and rac
	@Override
	public void visitTry(JCTry that) {
		Set<Type> savedActiveExceptions = activeExceptions;
		activeExceptions = new HashSet<>();
		activeExceptions.addAll(savedActiveExceptions);
		if (that.catchers != null)
			for (JCCatch catcher : that.catchers) {
				// FIXME - what about multiple types in one declaration
				activeExceptions.add(catcher.getParameter().type);
			}

		try {

			if (that.resources != null && !that.resources.isEmpty())
				transformTryWithResources(that);
			addStat(comment(that, "try ...", null)); // Don't need to trace the try keyword
			JCBlock body = convertBlock(that.body);

			List<JCCatch> catchers = null;
			if (that.catchers != null) {
				ListBuffer<JCCatch> ncatchers = new ListBuffer<JCCatch>();
				for (JCCatch catcher : that.catchers) {

					int sp = catcher.getParameter().getStartPosition();
					ListBuffer<JCStatement> check = pushBlock();
					addStat(comment(catcher.getParameter(), "catch (" + catcher.param + ") ...", null));

					JCIdent id = treeutils.makeIdent(catcher.param, catcher.param.sym);

					// local exception = EXCEPTION
//                JCExpression e = treeutils.makeEqObject(catcher.pos, id, treeutils.makeIdent(catcher.pos, exceptionSym));
//                addStat(treeutils.makeAssume(catcher.pos(),Label.IMPLICIT_ASSUME,e));

					Type ct = catcher.param.type;
					JCExpression e = treeutils.falseLit;
					if (ct.isUnion()) {
						Type.UnionClassType uct = ((Type.UnionClassType) ct);
						for (TypeMirror t : uct.getAlternatives()) {
							Type tt = (Type) t;
							e = treeutils.makeOrSimp(catcher.pos, e,
									treeutils.makeInstanceOf(catcher.param.pos, id, tt));
						}
						addAssume(catcher.pos(), Label.IMPLICIT_ASSUME, e);
					} else if (rac) {
						e = treeutils.makeInstanceOf(catcher.param.pos, id, ct);
						addAssume(catcher.pos(), Label.IMPLICIT_ASSUME, e);
					}

					addStat(traceableComment(catcher.getParameter(), id, "Exception caught", ""));
		            addFeasibilityCheck(catcher, currentStatements, Strings.feas_catch, "at beginning of catch block");


					if (rac) {
						// These assignments must be duplicated here because they are needed by RAC
						// TerminationPos = 0
						JCIdent termid = treeutils.makeIdent(catcher.pos, terminationSym);
						addStat(treeutils.makeAssignStat(catcher.pos, termid, treeutils.zero));

						// EXCEPTION = NULL
						JCIdent exId = treeutils.makeIdent(sp, exceptionSym);
						treeutils.copyEndPosition(exId, catcher.getParameter());
						JCStatement st = treeutils.makeAssignStat(sp, exId, treeutils.nullLit);
						addStat(st);
					}

					addRecInvariants(true, catcher.param, id); // This only adds invariants for the union type

					continuation = Continuation.CONTINUE;
					JCBlock bl = convertBlock(catcher.getBlock());
					addStat(bl);

					JCIdent nid = treeutils.makeIdent(sp, catcher.getParameter().sym);
					treeutils.copyEndPosition(nid, catcher.getParameter());
					saveMapping(nid, copy(nid));

					JCBlock block = popBlock(catcher.param, check);

					JCVariableDecl odecl = catcher.getParameter();
					JmlVariableDecl decl = M.at(odecl).VarDef(odecl.sym, null); // Catcher declarations have no
																				// initializer
					JCCatch ncatcher = M.at(catcher).Catch(decl, block);
					ncatcher.setType(catcher.type);
					ncatchers.add(ncatcher);
				}
				catchers = ncatchers.toList();
			}
			continuation = Continuation.CONTINUE;
			JCBlock finalizer = convertBlock(that.finalizer);
			if (that.finalizer != null) addFeasibilityCheck(that.finalizer, finalizer, Strings.feas_finally, "at beginning of finally block");
			List<JCTree> newResources = copy(that.resources);
			// FIXME - no checks implemented on the resources
			JCTry st = M.at(that).Try(newResources, body, catchers, finalizer);
			st.setType(that.type);
			result = addStat(st);
			return;
		} finally {
			activeExceptions.clear();
			activeExceptions = savedActiveExceptions;
			continuation = Continuation.CONTINUE; // TODO _ can do better than this, e.g. using
													// finallyCanCompleteNormally
		}
	}

	// OK
	@Override
	public void visitCatch(JCCatch that) {
		// Catch statements are handled along with Try
		error(that, "JmlAssertionAdder.visitCatch should not be called");
	}

	// FIXME - these are not fully developed yet
	protected void adjustWellDefinedConditions(JCExpression cond) {
		adjustWellDefinedConditions(cond, wellDefinedConditions);
	}

	protected void adjustWellDefinedConditions(JCExpression cond, java.util.List<JmlStatementExpr> conds) {
		for (JmlStatementExpr st : conds) {
			st.expression = treeutils.makeImplies(st.expression.pos, cond, st.expression);
		}
	}

	// OK
	@Override
	public void visitConditional(JCConditional that) {
	    try {
	        addStat(comment(that, " ... conditional ...", null));

	        JCExpression cond = convertExpr(that.cond);
	        if (cond instanceof JCLiteral) {
	            Boolean v = (Boolean) ((JCLiteral) cond).getValue();
	            if (v) {
	                result = eresult = convertExpr(that.truepart);
	            } else {
	                result = eresult = convertExpr(that.falsepart);
	            }
	        } else if (!splitExpressions) {
	            JCExpression prev = condition;
	            try {
	                java.util.List<JmlStatementExpr> listf = new java.util.LinkedList<JmlStatementExpr>();
	                listf.addAll(wellDefinedConditions);

	                var ccond = addImplicitConversion(cond, syms.booleanType, copy(cond)); // FIXME - what about oldenv?
	                addToCondition(that.pos, ccond);
	                JCExpression truepart = convertExpr(that.truepart);
	                if (truepart == null) System.out.println("NO TYPE " + that + " " + that.type + " " + that.truepart.type + " " + that.truepart + " " + truepart);
	                truepart = addImplicitConversion(that.truepart, that.type, truepart);
	                adjustWellDefinedConditions(cond);
	                condition = prev;
	                addToCondition(that.pos, treeutils.makeNot(that.falsepart.pos, cond));
	                JCExpression falsepart = convertExpr(that.falsepart);
	                falsepart = addImplicitConversion(that.falsepart, that.type, falsepart);
	                adjustWellDefinedConditions(cond, listf);
	                wellDefinedConditions.addAll(listf);
	                result = eresult = M.at(that).Conditional(cond, truepart, falsepart).setType(that.type);
	            } finally {
	                condition = prev;
	            }
	        } else {
	            cond = addImplicitConversion(cond, syms.booleanType, cond);
	            if (that.type.getTag() == TypeTag.BOT) {
	                // For the rare case in which the conditional is condition ? null : null
	                // so that that.type is <nulltype> and we cannot declare a temporary of that
	                // type.
	                result = eresult = convertExpr(that.truepart);
	            } else {

	                Name resultname = names.fromString(Strings.conditionalResult + nextUnique());
	                JCVariableDecl vdecl = treeutils.makeVarDef(that.type, resultname,
	                    methodDecl == null ? classDecl.sym : methodDecl.sym, that.pos);
	                addStat(vdecl);

	                ListBuffer<JCStatement> checkA = pushBlock();
	                JCBlock trueblock = null;
	                try {
	                    JCExpression tres = convertExpr(that.truepart);
	                    tres = addImplicitConversion(that.truepart, that.type, tres);
	                    JCIdent id = treeutils.makeIdent(that.truepart.pos, vdecl.sym);
	                    addStat(treeutils.makeAssignStat(that.truepart.pos, id, tres));
	                } finally {
	                    trueblock = popBlock(that.truepart, checkA);
	                }

	                checkA = pushBlock();
	                JCBlock falseblock = null;
	                try {
	                    JCExpression fres = convertExpr(that.falsepart);
	                    fres = addImplicitConversion(that.falsepart, that.type, fres);
	                    JCIdent id = treeutils.makeIdent(that.falsepart.pos, vdecl.sym);
	                    addStat(treeutils.makeAssignStat(that.falsepart.pos, id, fres));
	                } finally {
	                    falseblock = popBlock(that.falsepart, checkA);
	                }

	                if (!translatingJML) cond = newTempIfNeeded(cond);
	                JCStatement stat = M.at(that).If(cond, trueblock, falseblock);

	                addStat(stat);
	                result = eresult = treeutils.makeIdent(that.pos, vdecl.sym);
	            }
	        }
	    } catch (Throwable e) {
	        utils.warning(that,"jml.message","Unexpected exception in visitConditional: " +  that + " : " + that.type);
	        e.printStackTrace(System.out);
	    }

	}

	// OK
	@Override
	public void visitIf(JCIf that) {
	    var ifthat = (JmlIfStatement)that;
		boolean split = ifthat.split;
		addStat(traceableComment(that.getCondition(), that.getCondition() , "if " + that.getCondition() + " ...", "Condition"));
		JCExpression cond = convertExpr(that.cond);
		cond = addImplicitConversion(that.cond, syms.booleanType, cond);
		cond = newTempIfNeeded(cond);

		// The scanned result of the then and else parts must always be a block
		// because multiple statements might be produced, even from a single
		// statement in the branch.
		int savedHeapCount = heapCount;

		if (!split || currentSplit == null || rac || infer) {
	        currentEnv = currentEnv.pushEnvCopy();
			continuation = Continuation.CONTINUE;
            //System.out.println("IF " + heapCount + " " + currentEnv.heap.heapID + " " + that);
			JCBlock thenpart = convertIntoBlock(that.thenpart, that.thenpart);
            addFeasibilityCheck(that, thenpart, Strings.feas_if, "at then branch");
			Continuation thenContinuation = continuation;
			continuation = Continuation.CONTINUE;
            //System.out.println("IF END OF THEN " + heapCount + " " + currentEnv.heap.heapID);
			int thenBranchHeapCount = heapCount;
			currentEnv = currentEnv.popEnv();
            heapCount = savedHeapCount;
            //System.out.println("STARTING ELSE BRANCH " + heapCount + " " + currentEnv.heap.heapID);
            if (heapCount != currentEnv.heap.heapID) System.out.println("MISMATCHED HEAP ID " + heapCount + " " +  currentEnv.heap.heapID + " " + thenBranchHeapCount);
            currentEnv = currentEnv.pushEnvCopy();
			JCBlock elsepart = that.elsepart == null ? null : convertIntoBlock(that.elsepart, that.elsepart);
			if (elsepart != null) addFeasibilityCheck(that, elsepart, Strings.feas_if, "at else branch");

			Continuation elseContinuation = continuation;
            //System.out.println("IF END OF ELSE " + heapCount + " " + currentEnv.heap.heapID);

			JCStatement st = M.at(that).If(newTempIfNeeded(cond), thenpart, elsepart).setType(that.type);
			var r = addStat(st);
            continuation = thenContinuation.combine(elseContinuation);
            int elseBranchHeapCount = heapCount;
            currentEnv = currentEnv.popEnv();
            if (thenBranchHeapCount != elseBranchHeapCount) {
                pushBlock();
                addStat(comment(that, "If heap change", null));
                JmlLabeledStatement sttt = markUniqueLocation();
                addStat(sttt);
                changeState(that, null, sttt.label);
                currentEnv.heap.previousHeaps.clear();
                //System.out.println("ENDED IF " + heapCount + " " + thenBranchHeapCount + " " + elseBranchHeapCount);
                addStat(popBlock(that));
                HeapInfo thenHeapInfo = methodEnv.allHeaps.get(thenBranchHeapCount);
                thenHeapInfo.condition = cond;
                currentEnv.heap.previousHeaps.add(thenHeapInfo);
                HeapInfo elseHeapInfo = methodEnv.allHeaps.get(elseBranchHeapCount);
                elseHeapInfo.condition = treeutils.makeNot(cond, cond);
                currentEnv.heap.previousHeaps.add(elseHeapInfo);
            }
            result = r;
		} else {
			boolean doThen = true;
			if (currentSplit.isEmpty()) {
				adjustSplit(2);
			} else {
				doThen = currentSplit.charAt(0) == 'A';
				currentSplit = currentSplit.substring(1);
			}
			if (doThen) {
				addAssume(that.cond.pos(), Label.IMPLICIT_ASSUME, cond);
				JCBlock thenpart = convertIntoBlock(that.thenpart, that.thenpart);

				JCStatement st = thenpart.setType(that.thenpart.type);
				result = addStat(st);
				// Keep the same value of continuation
			} else {
				addAssume(that.cond.pos(), Label.IMPLICIT_ASSUME, treeutils.makeNot(that.cond, cond));
				if (that.elsepart != null) {
					JCBlock elsepart = convertIntoBlock(that.elsepart, that.elsepart);
					JCStatement st = elsepart.setType(that.elsepart.type);
					result = addStat(st);
				}
				// Keep the same value of continuation
			}
		}
	}

	// FIXME - document these
	protected void addTraceableComment(JCTree t) {
		JCStatement c = comment(t);
		pathMap.put(t, c);
		addStat(c);
	}

	protected void addTraceableComment(JCTree t, String description) {
		addStat(traceableComment(t, t, description, null));
	}

	protected void addTraceableComment(JCTree t, JCExpression expr, String description) {
		addStat(traceableComment(t, expr, description, null));
	}

	protected void addTraceableComment(JCTree t, JCTree expr, String description, String info) {
		addStat(traceableComment(t, expr, description, info));
	}

	/**
	 * Create a comment that is used for tracing; the value of the given expression
	 * (and subexpressions) is printed as part of the trace.
	 * 
	 * @param t           the source location to cite for the comment
	 * @param expr        the expression to trace
	 * @param description the description of the expression to give (typically a
	 *                    string representation of the symbolic expression)
	 * @param info        additional information to be provided with the comment
	 * @return
	 */
	protected JCStatement traceableComment(JCTree t, JCTree expr, String description, String info) {
		JavaFileObject source = null;
		if (t instanceof JmlTree.JmlSource)
			source = ((JmlTree.JmlSource) t).source();
		JmlStatementExpr c = comment(t, description, source);
		c.id = info;
		pathMap.put(expr, c);
		return c;
	}

	@Override
	public void visitExec(JCExpressionStatement that) {
		addTraceableComment(that);
		JCExpression arg = convertExpr(that.getExpression());

		// For rac and esc, assignments become a new variable,
		// so no exec statement is needed, and arg is then an ident.

		// Similarly, method invocations that return a value become a
		// temporary id, and no additional Exec statement is needed

		// Otherwise we create an Exec statement

		if (arg instanceof JCMethodInvocation || arg instanceof JCAssign || arg instanceof JCAssignOp
				|| arg instanceof JCUnary) {
			result = addStat(M.at(that).Exec(arg).setType(that.type));
		}
	}

	public Set<JCTree> knownNonNull = new HashSet<>();

	public boolean isKnownNonNull(JCTree r) {
	    if (r.type == null || 
	            utils.isJavaOrJmlPrimitiveOrVoidType(r.type)) return true;
        //System.out.println("ISKNOWN " + r.type + " # " + r + " # " + r.getClass());
		if (r instanceof JCMethodInvocation m) {
            if (m.type != null && m.type.isAnnotated()) {
                var tcl = m.type.getAnnotationMirrors();
                boolean nullable = false;
                for (var tc: tcl) {
                    if (tc.toString().equals("@org.jmlspecs.annotation.Nullable")) nullable = true;
                }
                boolean nonnull = false;
                for (var tc: tcl) {
                    if (tc.toString().equals("@org.jmlspecs.annotation.NonNull")) nonnull = true;
                }
                //System.out.println("KNOWN " + nonnull + " " + nullable + " " + m.type + " " + 
                //   (m.meth instanceof JCFieldAccess fa ? fa.type: null));
                if (nonnull) return true;
                return false; // FIXME: should we use a default?
            }
		}
		if (!(r instanceof JCIdent))
			return false;
		if (lambdaLiterals.get(((JCIdent) r).getName().toString()) != null)
			return true;
		return knownNonNull.contains(r);
	}

	public Map<JCExpression, Type> dynamicTypes = new HashMap<>();

	public Type knownDynamicType(JCExpression r) {
		return dynamicTypes.get(r);
	}

	// OK
	@Override
	public void visitBreak(JCBreak that) {
		addTraceableComment(that);
		// Turn off any current exception if there is a break,
		// including breaks without labels in switch and loop statements
		// (The only way these can get executed is if they are in a catch or finally
		// block

		{
			JCIdent id = treeutils.makeIdent(that, exceptionSym);
			JCStatement stat = treeutils.makeAssignStat(that.pos, id, treeutils.nullLit);
			addStat(stat);
		}

		JCBreak st = M.at(that).Break(that.label);
		st.target = treeMap.get(that.target);
		if (st.target == null) {
			error(that, "Unknown break target: " + that.label);
		}
		st.setType(that.type);
		addStat(st);
		result = st;
	}

	// OK
	@Override
	public void visitContinue(JCContinue that) {
		addTraceableComment(that);
		// Turn off any current exception if there is a break,
		// including breaks without labels in switch and loop statements
		// (The only way these can get executed is if they are in a catch or finally
		// block:wq

		JCIdent id = treeutils.makeIdent(that, exceptionSym);
		JCStatement stat = treeutils.makeAssignStat(that.pos, id, treeutils.nullLit);
		addStat(stat);
		if (that.label == null) {
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
				error(that, "Unknown continue target");
			}
			result = addStat(st);
		}
	}

	// OK
	@Override
	public void visitReturn(JCReturn that) {
		// Cases:
		// breakName == null ==> return in the method being converted: convertexpr,
		// assign to resultExpr, keep return statement
		addTraceableComment(that);
		JCExpression retValue = convertExpr(that.getExpression());
		int p = that.pos;
		if (retValue != null) {
			retValue = addImplicitConversion(that, resultExpr.type, retValue);
			if (resultSym != null && !translatingLambda) {
				JCIdent resultId;
				resultId = treeutils.makeIdent(p, resultSym);
				JCStatement stat = treeutils.makeAssignStat(p, resultId, retValue);
				addStat(stat);
				retValue = treeutils.makeIdent(p, resultSym);
			}
			if (resultSym == null && !translatingLambda) {
				addAssumeEqual(that, Label.IMPLICIT_ASSUME, resultExpr, retValue);
			}
		}

		if (breakName != null) {
			JCBreak br = addStat(M.at(p).Break(breakName));
			br.target = breakNames.get(breakName);
			if (br.target == null) {
				// FIXME - error
			}
			addFeasibilityCheck(that, currentStatements, Strings.feas_return, "at return statement");
			result = br;
			return;

		} else if (resultExpr != null && !translatingLambda) {

			// Record the value of the termination location
			JCIdent id = treeutils.makeIdent(p, terminationSym);
			JCLiteral intlit = treeutils.makeIntLiteral(p, that.pos);
			JCStatement stat = treeutils.makeAssignStat(p, id, intlit);
			addStat(stat);

			// If the return statement is in a finally block, there may have been an
			// exception
			// in the process of being thrown - so we set EXCEPTION to null.
			id = treeutils.makeIdent(p, exceptionSym);
			stat = treeutils.makeAssignStat(p, id, treeutils.nullLit);
			addStat(stat);
		}
		continuation = Continuation.EXIT;

        addFeasibilityCheck(that, currentStatements, Strings.feas_return, "at return statement");
		result = addStat(M.at(that).Return(retValue).setType(that.type));
	}
	
	@Override
	public void visitYield(JCYield that) {
	    if (currentEnv.yieldIdent != null) {
	        var e = convertExpr(that.value);
            e = addImplicitConversion(that, currentEnv.yieldIdent.type, e);
	        addStat(treeutils.makeAssignStat(that.pos, copy(currentEnv.yieldIdent), e));
	        addStat(M.at(that.pos).Break(null));
	    } else {
	        // This error should always have been caught by JmlAttr
	        utils.error(that, "jml.internal", "This yield statement is not inside a switch");
	    }
	}

	// OK
	// FIXME - review for esc
	@Override
	public void visitThrow(JCThrow that) {

//       if (rac) {
//            addTraceableComment(that);
//
//            JCExpression expr = convertExpr(that.getExpression());
//            JCIdent id = treeutils.makeIdent(that.pos,exceptionSym);
//            addStat( treeutils.makeAssignStat(that.pos,id,expr) );
//            JCExpression e = treeutils.makeNeqObject(that.expr.pos, expr, treeutils.makeNullLiteral(that.expr.getEndPosition(log.currentSource().getEndPosTable())));
//            if (javaChecks) addAssert(e, Label.POSSIBLY_NULL_VALUE, e);
//            result = addStat(M.at(that).Throw(expr).setType(that.type));

//		} else 
		if (esc && jmltypes.isSubtype(that.expr.type, syms.assertionErrorType)) {
			// The case of throwing an AssertionError - convert it to an assert check
			JCExpression exceptionExpr = convertExpr(that.getExpression()); // convert and check for null
			// assert expr != null;
			if (!(that.expr instanceof JCNewClass)) {
				JCExpression e = treeutils.makeNeqObject(that.expr.pos, exceptionExpr,
						treeutils.makeNullLiteral(that.expr.getEndPosition(log.currentSource().getEndPosTable())));
				addJavaCheck(that.expr, e, Label.POSSIBLY_NULL_VALUE, Label.POSSIBLY_NULL_VALUE,
						"java.lang.NullPointerException");
			}
			if (that.expr.type.getTag() != TypeTag.BOT) {
				result = addAssert(true, that, Label.EXPLICIT_ASSERT, treeutils.falseLit, null, null, null);
			} else {
				JCThrow thrw = M.at(that).Throw(exceptionExpr);
				addStat(thrw);
			}
			continuation = Continuation.EXIT;

		} else {

			addTraceableComment(that);
			ListBuffer<JCStatement> check = pushBlock();
			try {
				JCExpression exceptionExpr = convertExpr(that.expr);
				// assert expr != null;
				if (!(that.expr instanceof JCNewClass)) {
					JCExpression e = treeutils.makeNeqObject(that.expr.pos, exceptionExpr,
							treeutils.makeNullLiteral(that.expr.getEndPosition(log.currentSource().getEndPosTable())));
					addJavaCheck(that.expr, e, Label.POSSIBLY_NULL_VALUE, Label.POSSIBLY_NULL_VALUE,
							"java.lang.NullPointerException");
				}

				if (that.expr.type.getTag() != TypeTag.BOT) {
					// Declare a local variable of the type of the exception expression, initialized
					// to the expression
					Name local = names.fromString(Strings.exceptionLocalVarString + that.pos);
					JCVariableDecl decl = treeutils.makeVarDef(that.expr.type, local, exceptionSym.owner,
							exceptionExpr);
					addStat(decl);

					// Set the value of the global EXCEPTION variable to the expression
					JCIdent id = treeutils.makeIdent(that.pos, exceptionSym);
					JCIdent localid = treeutils.makeIdent(exceptionExpr.pos, decl.sym);
					JCExpressionStatement assign = treeutils.makeAssignStat(that.pos, id, localid);
					saveMapping(that, assign);
					saveMapping(that, assign.expr);
					addStat(assign);

					// Assign the termination value
					JCIdent tid = treeutils.makeIdent(that.pos, terminationSym);
					JCStatement term = treeutils.makeAssignStat(that.pos, tid,
							treeutils.makeIntLiteral(that.pos, -that.pos));
					addStat(term);

					// throw the local expression value
					localid = treeutils.makeIdent(that.pos, decl.sym);
					exceptionExpr = localid;
				}
	            addFeasibilityCheck(that, currentStatements, Strings.feas_throw, "at throw statement");
				JCThrow thrw = M.at(that).Throw(exceptionExpr);
				addStat(thrw);
			} finally {
				JCBlock block = popBlock(that, check);
				result = addStat(block);
				continuation = Continuation.EXIT;
			}
		}
		return;
	}

	// OK - this is a Java assert statement
	@Override
	public void visitAssert(JCAssert that) {
		// FIXME - in esc we may want to treat this as an exception throwing Java
		// statement

		// ESC will eventually convert this to a Jml assertion, but RAC wants
		// it left as a Java assertion statement
		addTraceableComment(that);

		JCExpression cond = convertExpr(that.getCondition());

		JCExpression opt = that.getDetail();
		JCExpression info = // We don't convert literals to avoid bloat when the literal is an explicit null
							// or constant String
				!(opt instanceof JCLiteral) ? convertExpr(opt)
						: fullTranslation ? treeutils.makeDuplicateLiteral(opt.pos, (JCLiteral) opt) : opt;

		if (rac) {
			if (JmlOption.isOption(context, JmlOption.RAC_JAVA_CHECKS)) {
				result = addAssert(true, that, Label.EXPLICIT_ASSERT, cond, null, null, info);
				if (info != null)
					newTemp(info); // The detail expression is evaluated but not used anywhere
			}
			result = addStat(M.at(that).Assert(cond, info).setType(that.type));
		} else { // esc
			result = addAssert(true, that, Label.EXPLICIT_ASSERT, cond, null, null, info);
			if (info != null)
				newTemp(info); // The detail expression is evaluated but not used anywhere
		}
	}

	// FIXME - review all the assignable checks for appropriate use of translations
	// and this
	/** Returns true if x is contained in the datagroup y */
	protected boolean isContainedIn(Symbol x, Symbol y) {
		if (x == y) return true;
		if (x == null) return false;
		if (y == null) return true;
		if (currentEnv.currentReceiver instanceof JCIdent && x == classDecl.thisSymbol && y == ((JCIdent) currentEnv.currentReceiver).sym) return true;
		FieldSpecs fs = specs.getAttrSpecs((VarSymbol) x);
		if (fs == null) {
			// null can happen for a private field of a class without source
			// and without a declaration in the corresponding jml file
			return false;
		}
		for (JmlTypeClause tc : fs.list) {
			if (tc.clauseType == inClause) {
				JmlTypeClauseIn inclause = (JmlTypeClauseIn) tc;
				for (JmlGroupName gn : inclause.list) {
					if (isContainedIn(gn.sym, y))
						return true;
				}
			}
		}
		return false;
	}

	/** Returns a list of field access expressions that are the contents of 'fa',
	 * which is presumed to be a datagroup, when viewed from the given class.
	 * That is all 'in' declarations in 'csym' and its parents that have 'fs' as its target.
	 */
	java.util.List<JCFieldAccess> datagroupContents(JCFieldAccess fa, ClassSymbol csym) {
		java.util.List<JCFieldAccess> list = new LinkedList<>();
		list.add(fa); // FIXME - I don't think we need this
		for (Type parent : parents(csym.type, false)) {
			if (!(parent.tsym instanceof ClassSymbol))
				continue; // TODO - Review - what to do with type variables
			TypeSpecs tspecs = JmlSpecs.instance(context).getAttrSpecs((ClassSymbol) parent.tsym);
			if (tspecs.specDecl == null)
				continue;
			for (JCTree tree : tspecs.specDecl.defs) {
				if (tree instanceof JCVariableDecl) {
					JCVariableDecl vd = (JCVariableDecl) tree;
					if (isContainedIn(vd.sym, fa.sym)) {
						if (list.stream().allMatch(f -> vd.sym != f.sym)) {
							JCFieldAccess nfa = M.at(fa.pos).Select(fa.selected, vd.sym);
							nfa.type = vd.type;
							list.add(nfa);
						}
					}
				}
			}
		}
		return list;
	}


//	public boolean containsRange(JCExpression e) {
//		var r = false;
//		if (e instanceof JCFieldAccess fa) {
//			r = containsRange(fa.selected);
//		} else if (e instanceof JCArrayAccess aa) {
//			if (aa.index instanceof JmlRange)
//				r = true;
//			else
//				r = containsRange(aa.indexed);
//		}
//		// System.out.println("CONTAINSRANGE " + e + " " + r);
//		return r;
//	}



	protected boolean recursiveCall = false;

	protected boolean checkAccessEnabled;

	public JCExpression toRepresentationForAssignable(JCFieldAccess fa) {
		Type seltype = fa.selected.type;
		// System.out.println("TRFA " + fa + " " + seltype + " " + seltype.getClass() +
		// " " + seltype.tsym + " " + seltype.tsym.getClass());
		if (seltype instanceof Type.TypeVar) {
			seltype = ((Type.TypeVar) seltype).getUpperBound(); // FIXME - try to lookup the type var to something
																// concrete -- not just the upper bounc (which is likely
																// Object)
			// System.out.println("TRFA-UP " + " " + seltype + " " + seltype.tsym);
		}
		TypeSymbol owner = seltype.tsym;
		TypeSpecs tspecs = specs.getAttrSpecs((ClassSymbol) owner); // FIXME - we get null specs if owner is a TypeVar --
																// need a type mapping?
		if (tspecs != null)
			for (JmlTypeClause t : tspecs.clauses) {
				if (t.clauseType == representsClause) {
					JmlTypeClauseRepresents rep = (JmlTypeClauseRepresents) t;
					if (rep.suchThat)
						continue;
					if (((JCIdent) rep.ident).sym == fa.sym) { // FIXME - why is rep.ident not a JCIdent?
						if (rep.expression instanceof JCFieldAccess)
							return rep.expression;
					}
				}
			}
		return fa;
	}


	/**
	 * Returns an expression indicating whether the object being dereferenced in the
	 * storeref is allocated now but was not in the prestate.
	 */
	protected JCExpression isFreshlyAllocated(DiagnosticPosition pos, JCExpression storeref) {
		if (rac)
			return treeutils.falseLit; // FIXME - how do we handle this aspect of assignment checking in RAC.
//        if (storeref instanceof JmlStoreRefKeyword) return treeutils.falseLit;
//        if (storeref.type.hasTag(TypeTag.BOT) || storeref.type.isPrimitive()) return treeutils.falseLit;

		JCExpression obj = null;
		if (storeref instanceof JCFieldAccess && !utils.isJMLStatic(((JCFieldAccess) storeref).sym)) {
			obj = ((JCFieldAccess) storeref).selected;
		} else if (storeref instanceof JCArrayAccess) {
			obj = ((JCArrayAccess) storeref).indexed;
		} else if (storeref instanceof JmlStoreRefArrayRange) {
			obj = ((JmlStoreRefArrayRange) storeref).expression;
		} else if (storeref instanceof JCIdent) {
			if (((JCIdent) storeref).name == names._this)
				return treeutils.falseLit;
			obj = storeref;
		}
		if (obj == null)
			return treeutils.falseLit;
		if (enclosingMethod == null)
			return treeutils.trueLit; // initializer block
		if (enclosingMethod.isConstructor() && obj instanceof JCIdent
				&& ((JCIdent) obj).sym.toString().equals(Strings.THIS))
			return treeutils.trueLit; // Fields of an object being constructed are always assignable
//        obj = convertJML(obj);  // FIXME - in some cases at least this is a second conversion
		if (true || !convertingAssignable)
			obj = newTemp(obj);

		if (false) {
			// FIXME - don't bother with the following if obj is 'this'
			JCExpression allocNow = M.at(pos).Select(obj, isAllocSym).setType(syms.booleanType);
			JCExpression allocOld = makeOld(pos.getPreferredPosition(),
					M.at(pos).Select(copy(obj), isAllocSym).setType(syms.booleanType), attr.oldLabel);
			return treeutils.makeAnd(pos.getPreferredPosition(), allocNow,
					treeutils.makeNot(pos.getPreferredPosition(), allocOld));
		} else {
			JCExpression allocCountExpr = M.at(pos).Select(obj, allocSym).setType(syms.intType);
			JCExpression fresh = treeutils.makeBinary(pos, JCTree.Tag.GT, allocCountExpr,
					treeutils.makeIntLiteral(pos, freshnessReferenceCount)); // FIXME - should this be using the
																				// oldLabel somehow?
			return fresh;
		}
	}
	
	public JCExpression freshTest(DiagnosticPosition pos, JCExpression obj, int freshnessReferenceCount) {
		if (rac) return null; // freshness not supported by rac
		//System.out.println("FRESH " + obj + " " + obj.type + " " + utils.isJavaOrJmlPrimitiveType(obj.type));
		if (utils.isJavaOrJmlPrimitiveType(obj.type)) return null; // no test for primitive types
		//if (freshnessReferenceCount >= 0 && obj instanceof JCIdent id && (id.name == names._this || id.name == names._super || id.name.toString().equals(Strings.THIS))) return treeutils.makeBooleanLiteral(pos, false);
		JCExpression allocCountExpr = M.at(pos).Select(obj, allocSym).setType(syms.intType);
		JCExpression isfresh = treeutils.makeBinary(pos, JCTree.Tag.GT, allocCountExpr,
				treeutils.makeIntLiteral(pos, freshnessReferenceCount));
		return isfresh;

	}

	/**
	 * Returns an expression indicating whether an object is allocated in the
	 * current state (obj.isalloc__).
	 */
	protected JCFieldAccess isAllocated(DiagnosticPosition pos, JCExpression obj) {
		// if (rac) return treeutils.falseLit; // FIXME - how do we handle this aspect
		// of assignment checking in RAC.
		// obj = convertJML(obj);
		return (JCFieldAccess) M.at(pos).Select(obj, isAllocSym).setType(syms.booleanType);
	}

	/**
	 * Expands any store-ref wildcard items and optionally datagroups, since they
	 * depend on the base location and visibility
	 */
	protected List<JCExpression> expandStoreRefList(List<JCExpression> list, MethodSymbol base,
			boolean expandDataGroup) {
		ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
		for (JCExpression item : list) {
			if (expandDataGroup) {
				if (item instanceof JCIdent) {
					JCIdent id = (JCIdent) item;
					if (id.sym.owner instanceof Symbol.ClassSymbol) {
						if (utils.isJMLStatic(id.sym)) {
							JCExpression sel = M.at(item.pos).Type(id.sym.owner.type);
							item = M.at(item.pos).Select(sel, id.sym);
							item.type = id.type;
						} else {
							item = M.at(item.pos).Select(currentEnv.currentReceiver, id.sym);
							item.type = id.type;
						}
					}
				}
			}
			if (item instanceof JCFieldAccess && ((JCFieldAccess) item).name == null) {
				JCFieldAccess fa = (JCFieldAccess) item;
				java.util.List<VarSymbol> exlist;
				TypeSymbol csym = fa.selected.type.tsym;
				exlist = utils.listJmlVisibleFields(csym, (TypeSymbol) base.owner, base.flags() & Flags.AccessFlags,
						treeutils.isATypeTree(((JCFieldAccess) item).selected), true);
				for (VarSymbol vsym : exlist) {
					newlist.add(M.at(item).Select(fa.selected, vsym));
				}
			} else if (expandDataGroup && item instanceof JCFieldAccess) {
				JCFieldAccess fa = (JCFieldAccess) item;
				// FIXME - what class declaration to use here?
				java.util.List<JCFieldAccess> clist = datagroupContents(fa, (ClassSymbol) base.owner);
				newlist.addAll(clist);
				//System.out.println("EXPANDED " + item + " TO " + clist);
			} else {
				newlist.add(item);
			}
		}
		return newlist.toList();
	}
	
	protected List<JCExpression> expandStoreRefWithMaps(List<JCExpression> items, Type base) {
	    ListBuffer<JCExpression> out = new ListBuffer<>();
	    for (var item: items) {
            if (item instanceof JCIdent) {
                JCIdent id = (JCIdent) item;
                if (id.sym.owner instanceof Symbol.ClassSymbol) {
                    if (utils.isJMLStatic(id.sym)) {
                        JCExpression sel = M.at(item.pos).Type(id.sym.owner.type);
                        item = M.at(item.pos).Select(sel, id.sym);
                        item.type = id.type;
                    } else {
                        item = M.at(item.pos).Select(currentEnv.currentReceiver, id.sym);
                        item.type = id.type;
                    }
                }
                //System.out.println("  ITEM " + item );
            }
            if (item instanceof JCFieldAccess && ((JCFieldAccess) item).name == null) {
                JCFieldAccess fa = (JCFieldAccess) item;
                java.util.List<VarSymbol> exlist;
                TypeSymbol csym = fa.selected.type.tsym;
                exlist = utils.listJmlVisibleFields(csym, base.tsym, base.tsym.flags() & Flags.AccessFlags,
                        treeutils.isATypeTree(((JCFieldAccess) item).selected), true);
                for (VarSymbol vsym : exlist) {
                    out.add(M.at(item).Select(fa.selected, vsym));
                }
            } else if (item instanceof JCFieldAccess) {
               JCFieldAccess fa = (JCFieldAccess) item;
               if (fa.sym.isStatic()) {
                   expandModelField(fa, out, fa.sym.owner.type); // FIXME - the base should be the type that is seeing the symbol, but should include the sysmbol
               } else {
                // FIXME - what class declaration to use here?
                   //System.out.println("  EXPANDING " + fa + " " + base);
                   expandModelField(fa, out, base); // FIXME - should probably use the receiver type
                   //System.out.println("  EXPANDED " + item + " NOW " + out);
               }
            } else {
                out.add(item);
            }
	    }
	    return out.toList();
	}

	protected List<JCExpression> expandStoreRefListAll(List<JCExpression> list, MethodSymbol base) {
		ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
		for (JCExpression item : list) {
			if (item instanceof JCFieldAccess && ((JCFieldAccess) item).name == null) {
				JCFieldAccess fa = (JCFieldAccess) item;
				// FIXME - use jml visibility (spec_public and spec_protected?)
				java.util.List<VarSymbol> exlist = utils.listAllFields((TypeSymbol) base.owner,
						treeutils.isATypeTree(((JCFieldAccess) item).selected));
				for (VarSymbol vsym : exlist) {
					newlist.add(M.at(item).Select(fa.selected, vsym));
				}
			} else {
				newlist.add(item);
			}
		}
		return newlist.toList();
	}

//	protected List<JCExpression> expandModelFields(List<JCExpression> list, Type refClass) {
//		ListBuffer<JCExpression> out = new ListBuffer<>();
//		for (JCExpression e : list) {
//			out.add(e);
//			if (!(e instanceof JCFieldAccess) || isDataGroup(e.type)) {
//				// do nothing more
//			} else {
//				expandModelField((JCFieldAccess) e, out, refClass);
//			}
//		}
//		return out.toList();
//	}

	// Add all fields that from the vantage point of refClass are "in" (perhaps
	// recursively) the model field e.
	// FIXME - this only finds datagroup members that are in parent types of
	// refClass and subtypes of e.selected.type
    protected void expandModelField(JCFieldAccess e, ListBuffer<JCExpression> out, Type refClass) {
        for (Type t : parents(refClass, false)) {
            //System.out.println("    TYPE " + refClass + " " + t + " " + t.tsym + " " + e + " " + e.selected.type);
            if (true || jmltypes.isSubtype(t, e.selected.type) || jmltypes.isSubtype(e.selected.type, t)) {
                var scope = t.tsym.members();
                if (scope == null) {
                    out.add(e);
                } else for (Symbol s : scope.getSymbols()) {
                    //System.out.println("       SYM " + s + " IN? " + e.sym);
                    if (s instanceof VarSymbol && isContainedIn(s, e.sym)) {
                        JCFieldAccess fa = M.Select(e.selected, s.name);
                        fa.sym = s;
                        fa.type = s.type;
                        fa.pos = e.pos;
                        out.add(fa);
                    }
                    if (s instanceof VarSymbol vs) {
                        JmlSpecs.FieldSpecs fs = specs.getAttrSpecs(vs);
                        if (fs != null) {
                            for (var cl : fs.list) {
                                if (cl instanceof JmlTypeClauseMaps m) {
                                    for (JmlGroupName g : m.list) {
                                        //System.out.println("       CHECKING " + g + " " + e.sym + " " + m);
                                        if (isContainedIn(g.sym, e.sym)) {
                                            //System.out.println("       ADDING " + g.sym + " " + e.sym + " " + m.expression);
                                            out.addAll(m.expressions);
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

//    protected ListBuffer<JCExpression> expandModelField(VarSymbol v, Type refClass) {
//        var out = new ListBuffer<JCExpression>();
//        for (Type t : parents(refClass, false)) {
//            if (jmltypes.isSubtype(t, v.owner.type)) {
//                for (Symbol s : t.tsym.getEnclosedElements()) {
//                    if (s instanceof VarSymbol vs) {
//                        JmlSpecs.FieldSpecs fs = specs.getAttrSpecs(vs);
//                        if (fs != null) for (var cl : fs.list) {
//                            if (cl instanceof JmlTypeClauseIn in && isContainedIn(vs, v)) {
//                                JCIdent id = M.at(in).Ident(s);
//                                out.add(id);
//                            }
//                            if (cl instanceof JmlTypeClauseMaps m) {
//                                for (JmlGroupName g : m.list) {
//                                    if (isContainedIn(g.sym, v)) {
//                                        out.add(m.expression);
//                                        break;
//                                    }
//                                }
//                            }
//                        }
//                    }
//                }
//            }
//        }
//        return out;
//    }

	Type locsetType = JMLPrimitiveTypes.locsetTypeKind.getType(context);

	/* Makes a JmlStoreRef value from a store-ref-expression -- no expansion */
	public List<JmlStoreRef> makeJmlStoreRef(DiagnosticPosition pos, JCExpression e, ClassSymbol baseClassSym, boolean expand) {
		ListBuffer<JmlStoreRef> list = new ListBuffer<>();
		JmlStoreRef sr = null;
		if (e instanceof JCIdent id) {
			if (e.type == locsetType) {
				// A JCIdent that is a locset type  // FIXME - should we check that we need to add a receiver?
				sr = M.at(e.pos).JmlStoreRef(false, null, e, null, null, null, e);
			} else {
				if (id.sym instanceof VarSymbol v && id.sym.owner instanceof TypeSymbol) {
					// A JCIdent that is a field
					if (utils.isJMLStatic(id.sym)) {
						// A static field
						sr = M.at(e.pos).JmlStoreRef(false, null, null, null, null, v, e);
					} else {
						// A non-static field
						JCIdent t = M.at(pos).Ident(names._this);
						t.sym = baseClassSym;
						t.setType(baseClassSym.type);
						sr = M.at(e.pos).JmlStoreRef(false, null, null, t, null, v, e);
					}
					//if (!expand) list.add(M.at(sr).JmlStoreRef(false,null,null,sr.receiver,null,v,null));
					if (expand) list.addAll(collectModelFieldContents(sr,baseClassSym, sr.receiver, v)); // Does not include itself
					//System.out.println("MJSR-A " + e + " : " + list);
				} else { // Local variable or 'this'
					sr = M.at(e.pos).JmlStoreRef(false, id.sym, null, null, null, null, e);
				}
			}
			list.add(sr);
		} else if (e instanceof JCArrayAccess aa) {
			// An array store-ref, perhaps with a range
			JmlRange r;
			if (aa.index == null) {
				r = M.at(aa.index).JmlRange(
						treeutils.makeZeroEquivalentLit(aa.pos, JmlTypes.instance(context).BIGINT),
						treeutils.makeLengthM1(e.pos(), aa.indexed));
			} else if (!(aa.index instanceof JmlRange rr)) {
				r = M.at(aa.index).JmlRange(aa.index, aa.index);
			} else {
				r = M.at(aa.index)
						.JmlRange(
								rr.lo != null ? rr.lo
										: treeutils.makeZeroEquivalentLit(rr.pos,
												JmlTypes.instance(context).BIGINT),
								rr.hi != null ? rr.hi : treeutils.makeLengthM1(e.pos(), aa.indexed));
			}
			sr = M.at(e.pos).JmlStoreRef(false, null, null, aa.indexed, r, null, e);
			list.add(sr);
		} else if (e instanceof JCFieldAccess fa) {
			//System.out.println("STAT " + fa + " " + fa.name + " " + e.type);
			if (fa.name == null) {
				// Wild-card field access store-ref
				JCExpression s = fa.selected;
				Symbol sym = treeutils.getSym(s);
				boolean isStatic = sym instanceof TypeSymbol && !(fa.selected instanceof JCIdent id
						&& (id.name == names._this || id.name == names._super));
				//System.out.println("STAT" + fa + " " + sym + " " + sym.getClass() + " " + isStatic);

				if (isStatic) {
					sr = M.at(e.pos).JmlStoreRef(false, null, null, null, null, null, e);
				} else {
					sr = M.at(e.pos).JmlStoreRef(false, null, null, fa.selected, null, null, e);
				}
				if (expand) list.addAll(collectModelFieldContents(fa,(ClassSymbol)(isStatic ? sym : fa.selected.type.tsym), sr.receiver, null));
				else list.add(sr);
				//System.out.println("MJSR-B " + e + " : " + list);

			} else if (e.type == locsetType) {
				// field access that is a locset
				sr = M.at(e.pos).JmlStoreRef(false, null, e, null, null, null, e);
				list.add(sr);
			} else {
				// field access store-ref
				if (fa.sym instanceof VarSymbol v) {
					boolean isStatic = utils.isJMLStatic(v);
					sr = M.at(e.pos).JmlStoreRef(false, null, null, isStatic ? null : fa.selected, null, v, e);
					list.add(sr);
					if (expand && fa.selected.type.tsym instanceof ClassSymbol ccsym) {
					    list.addAll(collectModelFieldContents(fa,ccsym, sr.receiver, v)); // Does not include itself
					}
					//System.out.println("MJSR-C " + fa.selected.type.tsym + " " + e + " : " + list);
				} else {
					// skip presuming an error already given
					if (utils.jmlverbose == Utils.JMLVERBOSE) log.error(fa.pos, "jml.message", "Not a VarSymbol: " + fa.sym);
				}
			}
		} else if (e instanceof JmlSingleton s) {
			// \nothing or \everything
			if (s.kind == JMLPrimitiveTypes.everythingKind) {
				sr = M.at(e.pos).JmlStoreRef(true, null, null, null, null, null, e);
				sr.setType(locsetType);
				list.add(sr);
			} else if (s.kind == JMLPrimitiveTypes.nothingKind) {
				// skip
			} else {
				// skip presuming an error already given
				if (utils.jmlverbose == Utils.JMLVERBOSE) log.error(s.pos, "jml.message", "Not a store-ref expression: " + e);
			}
		} else if (e.type != locsetType) {
			// skip presuming an error already given
			if (utils.jmlverbose == Utils.JMLVERBOSE) log.error(e.pos, "jml.message", "expected a \\locset type: " + e + " " + e.type);
		} else if (e instanceof JmlMethodInvocation mi && mi.kind == LocsetExtensions.unionKind) {
			// A call of union -- we flatten the call
			mi.args.stream().forEach(arg -> list.addAll(makeJmlStoreRef(pos, arg, baseClassSym, expand)));
		} else {
			// A locset expression
			sr = M.at(e.pos).JmlStoreRef(false, null, e, null, null, null, e);
			list.add(sr);
		}
		return list.toList();
	}


	public JCExpression convertAssignableToLocsetExpression(JmlSource pos, List<JCExpression> list,
			ClassSymbol baseType, JCExpression zzz) {
		var locsetType = JMLPrimitiveTypes.locsetTypeKind.getType(context);
		var previousSource = log.useSource(pos.source());
		ListBuffer<JCExpression> locsets = new ListBuffer<>();
		try {
			//System.out.println("CONVERTASSIGNABLE " + list);
			for (JCExpression e : list) {
			    var srs = makeJmlStoreRef(pos.pos(), e, baseType, true);
			    //System.out.println("   RES " + e + " : " + srs);
				locsets.addAll(srs);
			}
		} catch (PropagatedException | JmlNotImplementedException e) { // FIXME JmlCanceledException
			throw e;
		} catch (Exception e) {
			utils.error("jml.internal",
					"Unexpected exception while handling frame conditions: " + e.getMessage());
			e.printStackTrace(System.out);
		} finally {
			log.useSource(previousSource);
		}
		javax.tools.JavaFileObject jfo = pos.source();
		for (var ls : locsets) {
			((JmlStoreRef) ls).source = jfo;
			ls.type = locsetType;
		}
		JCExpression e = treeutils.makeLocsetUnion(pos.pos(), locsets.toList());
		//System.out.println("   FINAL " + e);
		return M.at(e.pos).JmlStoreRef(false, null, e, null, null, null, null).setType(locsetType);
	}
	
	public StoreRefGroup convertFrameConditionList(DiagnosticPosition pos, JCExpression guard, List<JCExpression> list) {
	    var out = new ListBuffer<StoreRefGroup.Item>();
	    for (JCExpression sr: list) {
	        StoreRefGroup.Item item;
	        if (sr instanceof JmlSingleton s) {
	            if (s.kind == nothingKind) {
	                item = new StoreRefGroup.Item(StoreRefGroup.Kind.NOTHING);
	            } else if (s.kind == everythingKind) {
                    item = new StoreRefGroup.Item(StoreRefGroup.Kind.EVERYTHING);
	            } else {
	                // ERROR
	                item = null;
	            }
	        } else if (sr instanceof JCIdent id) {
	            if (id.sym.owner == null) {
	                // A local temporary -- ignore
	                item = null;
	            } else if (id.sym.owner instanceof MethodSymbol) {
	                item = new StoreRefGroup.Item((VarSymbol)id.sym); // local
	            } else if (id.sym.isStatic()) {
                    item = new StoreRefGroup.Item((VarSymbol)id.sym); // static field
	            } else {
                    item = new StoreRefGroup.Item(currentEnv.currentReceiver, (VarSymbol)id.sym); // instance field
	            }
	        } else if (sr instanceof JCFieldAccess fa) {
	            if (fa.sym == null) {
	                // FIXME - instance or static?
                    var r = convertJML(fa.selected);
                    item = new StoreRefGroup.Item(r,(VarSymbol)fa.sym); // instance field
	            } else if (fa.sym.isStatic()) {
	                item = new StoreRefGroup.Item((VarSymbol)fa.sym); // static field
	            } else {
	                var r = convertJML(fa.selected);
	                item = new StoreRefGroup.Item(r,(VarSymbol)fa.sym); // instance field
	            }
	        } else if (sr instanceof JCArrayAccess aa) {
	            var arr = convertJML(aa.indexed);
	            if (aa.index instanceof JmlRange range) {
                    var lo = convertJML(range.lo);
                    var hi = convertJML(range.hi);
                    item =  new StoreRefGroup.Item(arr,M.at(range).JmlRange(lo, hi));
	            } else {
	                var index = convertJML(aa.index);
                    item =  new StoreRefGroup.Item(arr,M.at(aa.index).JmlRange(index,index));
	            }
	        } else {
	            // ERORR 
	            item = null;
	        }
	        if (item != null) out.add(item);
	    }
        return new StoreRefGroup(guard, out.toList());
	}

//	/** Returns the list of store-ref items corresponding to this.* */
//	// FIXME - should we expand data groups?
//	protected List<JCExpression> thisStarStoreRefs(DiagnosticPosition pos, MethodSymbol base,
//			boolean includeDataGroups) {
//		ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
//		for (VarSymbol vsym : utils.listJmlVisibleFields((TypeSymbol) base.owner, (TypeSymbol) base.owner,
//				base.flags() & Flags.AccessFlags, utils.isJMLStatic(base), includeDataGroups)) {
//			newlist.add(M.at(pos).Select(currentEnv.currentReceiver, vsym));
//		}
//		return newlist.toList();
//	}

	// FIXME - needs work
	@Override
	public void visitApply(JCMethodInvocation that) {
//        JCExpression savedCondition = condition;
//        try {
//        condition = treeutils.trueLit;

		if (that.meth.type.isErroneous()) {
			System.out.println("ERRONEOUS TYPE " + that);
			if (that.meth instanceof JCFieldAccess fa) System.out.println("  RECV " + fa + " " + fa.type);
			that.args.forEach(a-> System.out.println("  ARG " + a + " " + a.type));
			return;
		}

//        if (oldenv != null && rac) {
//            String msg = "RAC does not currently implement method calls in \\old expressions: " + treeutils.getSym(that.meth);
//            notImplemented(that,msg);
//            throw new JmlNotImplementedException(that,msg);
//        }

		if (!translatingJML)
			checkThatMethodIsCallable(that, treeutils.getSym(that.meth));
		if (translatingJML && rac) {
			// FIXME - need to check definedness by testing preconditions
			List<JCExpression> typeargs = convertExprList(that.typeargs);
			JCExpression meth = convertExpr(that.meth);
			List<JCExpression> args = convertExprList(that.args);
			JCMethodInvocation app = M.at(that).Apply(typeargs, meth, args).setType(that.type);
			app.varargsElement = that.varargsElement; // a Type
			result = eresult = app;
			if (rac && splitExpressions && app.type != null && app.type != syms.voidType) {
				JCIdent id = newTemp(app);
				result = eresult = id;
			}
			return;
		}
		Symbol sym = treeutils.getSym(that.meth);
		if (sym instanceof MethodSymbol && ((MethodSymbol) sym).isVarArgs()) {
			MethodSymbol msym = (MethodSymbol) sym;
			int actualLength = that.args.length();
			int formalLength = msym.type.asMethodType().argtypes.length(); // msym.params can be null if there are
																			// varargs
			Type varargType = msym.type.getParameterTypes().last();
			if (actualLength != formalLength || (!types.isSameType(that.args.last().type, varargType)
					&& !(that.args.last().type instanceof Type.ArrayType))) {
				int p = that.meth.pos;
				JCExpression len = treeutils.makeIntLiteral(p, actualLength + 1 - formalLength);
				Type compType = ((Type.ArrayType) varargType).getComponentType();
				JCExpression ty = treeutils.makeType(p, compType);
				ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
				ListBuffer<JCExpression> varargs = new ListBuffer<JCExpression>();
				Iterator<JCExpression> iter = that.args.iterator();
				int i = formalLength - 1;
				while ((i--) > 0)
					newargs.add(iter.next());
				while (iter.hasNext())
					varargs.add(iter.next());
				JCExpression array = M.at(p).NewArray(ty, List.<JCExpression>nil(), varargs.toList());
				array.type = varargType;
				newargs.add(array);
				that.args = newargs.toList();
			}
		}
		if (sym.name == names.fromString("clone") && sym.owner.name == names.fromString("Array")) {
			// Special case of the special class Array
			((JCFieldAccess) that.meth).sym = syms.objectType.tsym.members().findFirst(names.fromString("clone"));
		}
		if (classDecl.sym.isEnum() && methodDecl.sym.isConstructor() && that.meth instanceof JCIdent
				&& ((JCIdent) that.meth).name.equals(names._super)) {
			// OpenJDK inserts default constructors in classes and
			// inserts super() calls in constructors. For enums, this
			// super() call seems incorrect, since java.lang.Enum does not
			// have such a constructor. The effect of the constructor is to
			// set the name and ordinal fields.
			// TODO: For now we avoid processing the erroneous? super call.

			return;
		}
		if (that.meth instanceof JCIdent) {
			Symbol msym = ((JCIdent) that.meth).sym;
			if (msym.isStatic()) {
				that.meth = M.at(that).Select(M.at(that).Type(msym.owner.type), msym);
			} else {
				// TODO _ substitute the QTHIS argument
			}
		}
		Map<Symbol, Symbol> saved = pushMapSymbols();
		try {
			//System.out.println("CALLING APPLYHELPER " + that);
			applyHelper(that);
            //System.out.println("END APPLYHELPER " + that);
	        addFeasibilityCheck(that, currentStatements, Strings.feas_call, "after call");
		} finally {
			popMapSymbols(saved);
		}
	}

	java.util.List<String> callStack = new LinkedList<>();
	java.util.List<Symbol> callStackSym = new LinkedList<>();
	Map<Name, String> callStacks = new HashMap<>();

	public boolean checkCodeModifier(MethodSymbol calleeMethodSym, MethodSymbol mpsym, JmlSpecificationCase cs) {
		return !(mpsym != calleeMethodSym && cs.code);
	}

	// sym == null means \everything must be callable
	protected void checkThatMethodIsCallable(DiagnosticPosition pos, Symbol sym) {
		// Method might be called in an initializer??? FIXME - what do we do then?
		// FIXME - not sure how to detect this
		if (methodDecl == null || methodDecl.body == null)
			return;

		// GO through all of the caller's spec cases, testing that the call is
		// legitimate for each one
		// If there are no specification cases, then the default is that
		// everything is callable
		var mspecs = specs.getDenestedSpecs(methodDecl.sym);
		if (mspecs != null)
			for (JmlSpecificationCase specCase : mspecs.cases) {
				// FIXME - visibility?
				JCIdent pre = preconditions.get(specCase);
				pre = pre == null ? null : treeutils.makeIdent(pre.pos, pre.sym); // a new id for the same symbol
				for (JmlMethodClause mclause : specCase.clauses) {
					try {
						// We have to satisfy each callable clause individually
						JCExpression asg = null;
						if (mclause.clauseKind == CallableClauseExtension.callableClause) {
							JmlMethodClauseCallable c = (JmlMethodClauseCallable) mclause;
							if (c.keyword != null) {
								if (c.keyword.kind == nothingKind) {
									asg = treeutils.falseLit;
								} else if (c.keyword.kind == everythingKind) {
									asg = null;
								}
							} else if (sym == null) {
								asg = treeutils.falseLit;
							} else {
								asg = treeutils.falseLit;
								for (JmlMethodSig sig : c.methodSignatures) {
									if (sig.methodSymbol == sym) {
										asg = null;
										break;
									}
								}
							}
						}
						// asg == null means OK
						if (asg == null) {
							// OK
						} else { // asg is false, but under the current precondition
							asg = treeutils.makeNot(mclause.pos, pre);
							asg = makeAssertionOptional(asg);
							String msg = sym == null ? everythingID : utils.qualifiedMethodSig((MethodSymbol) sym);
							msg = msg + " is not callable";
							addAssert(pos, Label.CALLABLE, asg, mclause, specCase.sourcefile, msg);
						}
					} catch (JmlNotImplementedException e) {
						notImplemented("callable clause containing ", e); // FIXME - clause source
					}
				}
			}
	}

	protected boolean isFunctional(Type t) {
		if (t.tsym.getAnnotationMirrors() == null)
			return false;
		for (Attribute.Compound a : t.tsym.getAnnotationMirrors()) {
			if (a.getAnnotationType().toString().contains("FunctionalInterface"))
				return true; // FIXME - need a better way to do this
		}
		return false;
	}

	protected List<JCExpression> convertArgs(DiagnosticPosition pos, List<JCExpression> args, List<Type> argtypes,
			boolean hasVarArgs) {
		// Note: because the declaration may have a last varargs element,
		// args.size() may be greater than argtypes.size() But since everything
		// has typechecked OK, it is OK to implicitly use the last element of
		// argtypes for any additional args.
		ListBuffer<JCExpression> out = new ListBuffer<JCExpression>();
		Iterator<Type> iter = argtypes.iterator();
		boolean last = false;
		Type currentArgType = null;
		boolean usedVarArgs = args.size() == 0 && argtypes.size() != 0 && hasVarArgs;
		for (JCExpression a : args) {
			if (iter.hasNext())
				currentArgType = iter.next(); // handles varargs
			last = !iter.hasNext();
			if (currentArgType != null && isFunctional(currentArgType) && a instanceof JCMemberReference) { // FIXME -
																											// some bug
																											// causes
																											// the
																											// argtyep
																											// to be
																											// null for
																											// created
																											// functions,
																											// sometimes
				if (a instanceof JCMemberReference) {
					JCMemberReference mref = (JCMemberReference) a;
					JCExpression aa = convertExpr(mref.getQualifierExpression());
					JCMemberReference newa = M.at(a.pos).Reference(mref.mode, mref.name, aa, mref.typeargs);
					newa.sym = mref.sym;
					newa.setType(mref.type);
					a = newa;
				}
				out.add(a);
				continue;
			}
			a = convertExpr(a);
			if (last && hasVarArgs && !(a.type instanceof Type.ArrayType)) {
				currentArgType = ((Type.ArrayType) argtypes.last()).getComponentType();
				a = addImplicitConversion(a, currentArgType, a);
				usedVarArgs = true;
			} else if (a instanceof JCLambda) {
				// No casts - obscures the fact that the atranslated arg is a JCLambda
				// also a.type ihas type variables resolved
				// Just continue
			} else {
				if (currentArgType != null)
					a = addImplicitConversion(a, currentArgType, a); // FIXME - currentArgType should not be null
			}
			if (useMethodAxioms && translatingJML) {
			} else if ((a instanceof JCIdent) && ((JCIdent) a).name.toString().startsWith(Strings.tmpVarString)) {
			} else if ((a instanceof JCIdent) && localVariables.containsKey(((JCIdent) a).sym)) {
			} else if (!localVariables.isEmpty() || a instanceof JCLambda || a instanceof JCMemberReference) {
			} else if (splitExpressions) { // FIXME - at least we need to prevent temporaries when formulating Method
											// axioms
				// This check is a hack and a bit expensive. It makes sure that
				// every argument is represented by a temporary variable.
				// Without this an argument that is just an Ident or a Literal
				// and is not used ends up without its value captured for
				// tracing <<< THis all is no longer true I think, at least for literals
				if (!(a instanceof JCLiteral) && treeutils.typeLiteral(a) == null)
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
			currentArgType = ((Type.ArrayType) argtypes.last()).getComponentType();
			List<JCExpression> dims = List.<JCExpression>nil(); // FIXME - what if the array is multi-dimensional
			int p = pos.getPreferredPosition();
			JCExpression t = treeutils.makeType(p, currentArgType);
			JCExpression e = M.at(p).NewArray(t, dims, out.toList());
			e.type = argtypes.last();
			if (esc || infer)
				e = convertExpr(e);
			newout.add(newTemp(e)); // FIXME - see comment above about newTemp
			out = newout;
		}
		return out.toList();
	}

	public boolean useMethodAxioms;

	public java.util.List<Symbol> completedInvariants = new LinkedList<Symbol>();
	public java.util.Set<Symbol> inProcessInvariants = new HashSet<Symbol>();


	protected boolean startInvariants(Symbol csym, DiagnosticPosition pos) {
		if (completedInvariants.contains(csym))
			return true; // skip processing
		if (inProcessInvariants.add(csym))
			return false; // ok to do processing
		utils.warning(pos, "jml.recursive.invariants", csym.getQualifiedName());
		MethodSymbol msym = null;
		if (pos instanceof JCMethodInvocation) {
			msym = (MethodSymbol) treeutils.getSym(((JCMethodInvocation) pos).meth);
		} else if (pos instanceof JmlMethodDecl) {
			msym = ((JmlMethodDecl) pos).sym;
		}
		// utils.warning(pos, "jml.recursive.invariants", msym.toString());
		// Utils.dumpStack();
		if (msym != null) {
			// We add helper to avoid further recursive loops; it is unsound, but we have
			// already given the error message
			utils.setHelper(msym);
			if (!utils.isHelper(msym)) {
				utils.warning("jml.internal",
						"Internal problem: isHelper failed after adding HELPER annotation: " + msym);
			}
		}
		return true; // skip processing
	}

	protected boolean startInvariantsNoError(Symbol csym, DiagnosticPosition pos) {
		if (completedInvariants.contains(csym))
			return true; // skip processing
		if (inProcessInvariants.add(csym))
			return false; // ok to do processing
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

	// havocs might be: JCIdent, JCFieldAccess, JCArrayAccess, List of such, Loop specs, method call
	protected void changeState(DiagnosticPosition pos, Object havocs) {
	    changeState(pos, havocs, null);
	}
    protected void changeState(DiagnosticPosition pos, Object havocs, Name label) {
        int p = pos.getPreferredPosition();
        heapCount = nextHeapCount();
        currentEnv.heap = new HeapInfo(heapCount, currentEnv.heap, label);
        //System.out.println("CHANGE STATE " + heapCount + " NEW HI " + currentEnv.heap.heapID);
        methodEnv.allHeaps.put(heapCount, currentEnv.heap);
		if (infer || esc) {
			JCStatement assign = treeutils.makeAssignStat(p, treeutils.makeIdent(pos, heapSym),
					treeutils.makeIntLiteral(pos, heapCount));
			currentStatements.add(assign);
			JCBlock bl = M.at(p).Block(0L, List.<JCStatement>nil());
			currentEnv.heap.methodAxiomsBlock = bl;
	        currentStatements.add(bl);
		}
        currentEnv.heap.havocs = havocs;
        wellDefinedCheck.clear();
//        addAxioms(heapCount, null);
//        determinismSymbols.clear(); // FIXME - might need them again in  \old expressions
		clearInvariants(); // FIXME - is this needed for rac?
	}
    
    protected void changeStateForLoop(DiagnosticPosition pos, List<JmlStatementLoop> loopSpecs) {
        JmlStatementLoopModifies clause = (JmlStatementLoopModifies)loopSpecs.stream().filter(cl->(cl.clauseType == StatementLocationsExtension.loopwritesStatement)).findFirst().orElse(null);
        changeState(pos, List.<StoreRefGroup>of(clause == null
                ? new StoreRefGroup(treeutils.trueLit, StoreRefGroup.Kind.EVERYTHING)
                : convertFrameConditionList(pos, treeutils.trueLit, clause.storerefs)),
            null);
    }

	protected JCIdent currentFresh = null;

	protected JCExpression allocCounterLE(DiagnosticPosition pos, JCExpression expr, int counter) {
		JCFieldAccess fa = treeutils.makeSelect(pos.getPreferredPosition(), expr, allocSym);
		return treeutils.makeBinary(pos, JCTree.Tag.LE, treeutils.intleSymbol, fa,
				treeutils.makeIntLiteral(pos, counter));
	}

	// expr.alloc == counter (that is, expr was allocated in the state corresponding
	// to counter)
	protected JCExpression allocCounterEQ(DiagnosticPosition pos, JCExpression expr, int counter) {
		JCFieldAccess fa = treeutils.makeSelect(pos.getPreferredPosition(), expr, allocSym);
		JCExpression e = treeutils.makeBinary(pos, JCTree.Tag.EQ, treeutils.inteqSymbol, fa,
				treeutils.makeIntLiteral(pos, counter));
		return treeutils.makeOr(pos.getPreferredPosition(), treeutils.makeEqNull(pos.getPreferredPosition(), expr), e);
	}

	// expr.alloc > counter (that is, expr was allocated after the state
	// corresponding to counter)
	protected JCExpression allocCounterGT(DiagnosticPosition pos, JCExpression expr, int counter) {
		JCFieldAccess fa = treeutils.makeSelect(pos.getPreferredPosition(), expr, allocSym);
		JCExpression e = treeutils.makeBinary(pos, JCTree.Tag.GT, treeutils.intgtSymbol, fa,
				treeutils.makeIntLiteral(pos, counter));
		return treeutils.makeOr(pos.getPreferredPosition(), treeutils.makeEqNull(pos.getPreferredPosition(), expr), e);
	}

	Map<String, JavaFileObject> preconditionDetailClauses = new HashMap<>();

	protected JCExpression insertLabelsOnConjunctions(JCExpression expr, String prefix) {
		if (expr instanceof JCBinary) {
			JCBinary e = (JCBinary) expr;
			if (e.getTag() == JCTree.Tag.AND
					|| (e.getTag() == JCTree.Tag.BITAND && e.type.getTag() == TypeTag.BOOLEAN)) {
				JCExpression lhs = insertLabelsOnConjunctions(e.lhs, prefix);
				JCExpression rhs = insertLabelsOnConjunctions(e.rhs, prefix);
				JCBinary newexpr = M.at(expr.pos).Binary(e.getTag(), lhs, rhs);
				newexpr.setType(expr.type);
				newexpr.operator = e.operator;
				return newexpr;
			}
		}
		cpreindex3++;
		String label = prefix + "_" + cpreindex3;
		return M.at(expr.pos).JmlLblExpression(expr.pos, lblanyKind, names.fromString(label), expr).setType(expr.type);
	}

	protected java.util.List<JCExpression> findConjunctions(JCExpression expr) {
		java.util.List<JCExpression> list = new LinkedList<>();
		// findConjunctions(expr,list);
		list.add(expr);
		return list;
	}

	protected void findConjunctions(JCExpression expr, java.util.List<JCExpression> list) {
		if (expr instanceof JCBinary) {
			JCBinary e = (JCBinary) expr;
			if (e.getTag() == JCTree.Tag.AND
					|| (e.getTag() == JCTree.Tag.BITAND && e.type.getTag() == TypeTag.BOOLEAN)) {
				findConjunctions(e.lhs, list);
				findConjunctions(e.rhs, list);
				return;
			}
		}
		list.add(expr);
		return;
	}

//    protected JCExpression splitConjunctions(JCExpression expr, JCExpression condition, int index, int index2, int index3X, JavaFileObject source) {
//        if (expr instanceof JCBinary) {
//            JCBinary bin = (JCBinary)expr;
//            if (bin.getTag() == JCTree.Tag.AND) {
//                JCExpression convertedLHS = splitConjunctions(bin.lhs, condition, index, index2, index3, source );
//                JCIdent id = newTemp(bin.rhs, syms.booleanType);
//                ListBuffer<JCStatement> check = pushBlock();
//                JCExpression convertedRHS = splitConjunctions(bin.rhs, treeutils.makeAnd(bin.lhs, condition, convertedLHS), index, index2, index3, source );
//                addStat(treeutils.makeAssignStat(bin.rhs.pos,id,convertedRHS));
//                JCBlock bl = popBlock(bin.rhs,check);
//                JCStatement st = treeutils.makeAssignStat(bin.rhs.pos,convertCopy(id),treeutils.falseLit);
//                addStat(M.at(bin.rhs).If(convertedLHS,bl,st));
//                return treeutils.makeAnd(bin.lhs, convertedLHS, convertCopy(id));
//            }
//        } 
//        
//            index3++;
//            String nm = "_$CPRE__" + index + "_" + index2 + "_" + index3;
//            int localIndex3 = index3;
//            JCExpression e = convertJML(expr, condition, false);
//            preconditionDetailClauses.put(nm,source);
//            JCIdent id = newTemp(expr.pos, nm, e);
//            saveMappingOverride(convertCopy(expr),id);
//            index3 = localIndex3;
//        return id;
//    }

	protected void addToStats(ListBuffer<JCStatement> stats, Runnable action) {
		ListBuffer<JCStatement> prev = currentStatements;
		currentStatements = stats;
		action.run();
		;
		currentStatements = prev;
	}

	protected List<JCStatement> collectStats(Runnable action) {
		ListBuffer<JCStatement> prev = currentStatements;
		currentStatements = new ListBuffer<JCStatement>();
		try {
			action.run();
            return currentStatements.toList();
		} catch (Exception e) {
		    utils.error("jml.internal","Exception while collecting stats");
		    e.printStackTrace(System.out);
            return currentStatements.toList();
		} finally {
			currentStatements = prev;
		}
	}

	protected JCBlock collectBlock(DiagnosticPosition pos, Runnable action) {
		List<JCStatement> stats = collectStats(action);
		return M.at(pos).Block(0L, stats);
	}

	Map<JmlSpecificationCase, JCExpression> calleePreconditions;

	int cpreindex3 = 0;

	/** Helper method to do the work of visitApply and visitNewObject */
	protected void applyHelper(JCExpression that) {
		boolean print =  Utils.debug("trans");
        boolean printb = print ;//|| that.toString().contains("cops.id");
        //print |= that.toString().contains("cops.id");
    	if (print) System.out.println("APPLY HELPER: " + that);
//    	if (that instanceof JCMethodInvocation) {
//    		JCMethodInvocation m = (JCMethodInvocation)that;
//    		JCExpression sel = m.meth instanceof JCFieldAccess ? ((JCFieldAccess)m.meth).selected : currentEnv.currentReceiver;
//    		Symbol sym = m.meth instanceof JCFieldAccess ? ((JCFieldAccess)m.meth).sym : ((JCIdent)m.meth).sym;
//    		System.out.println("APPLY TYPES: " +  m.meth.type + " # " + sym.type + " # " + sym.owner.type + " # " + m.meth.type.tsym + " # " + sel + " # " + sel.type);
//    	}
		// if
		// (that.toString().equals("ListSeq<E>.java_util_ArrayList_size_H4_3582(QQHIS.list)"))
		// Utils.dumpStack();
		// if (that.toString().equals("list.size()")) Utils.dumpStack();
		boolean pushedMethod = false;
		preconditionDetail++;
		int preconditionDetailLocal = preconditionDetail;
		// We need to save the context of many variables because in the case of
		// new object creation there may be nested methods that are converted
		// before we return to complete the translation of method declaration
		// we are now in (methodDecl)

		ListBuffer<JCStatement> check0 = pushBlock();
		var stack0 = markBlock();

		ListBuffer<JCStatement> outerDeclarations = new ListBuffer<JCStatement>();

		JCExpression savedCondition = this.condition;
		// This is the logical context in which this method is called - only used for
		// JML expressions
		/* @ nullable */ VarSymbol savedResultSym = this.resultSym;
		// This is the symbol of the JCIdent representing the result of the method call,
		// null if the method is void
		/* @ nullable */ JCExpression savedResultExpr = this.resultExpr;
		/* @ nullable */ VarSymbol savedExceptionSym = this.exceptionSym;
		// The symbol that holds the active exception (or null) // FIXME - doesnot get
		// changed so why save it?
		/* @ nullable */ JCExpression savedThisExpr = this.currentEnv.currentReceiver;
		// The JCIdent holding what 'this' means in the current context (already
		// translated)
		/* @ nullable */ JCTree savedNestedCallLocation = this.nestedCallLocation;
		int savedFreshnessReferenceCount = this.freshnessReferenceCount;
		Map<Object, JCExpression> savedParamActuals = this.paramActuals_; // Mapping from formal parameter symbols to the
																			// actual arguments
		ListBuffer<JCStatement> savedOldStatements = this.oldStatements;
		JCIdent savedFresh = this.currentFresh;
		Symbol savedEnclosingMethod = this.enclosingMethod;
		Symbol savedEnclosingClass = this.enclosingClass;
		Map<TypeSymbol, Type> savedTypeVarMapping = this.typevarMapping;
		Map<TypeSymbol, Type> newTypeVarMapping = this.typevarMapping;
		var savedCurrentOldLabel = currentOldLabel;

		nestedCallLocation = null;

		applyNesting++;

//		Map<Symbol, Map<Object, JCExpression>> mapParamActuals = new HashMap<Symbol, Map<Object, JCExpression>>();

		// Set to true later if the callee is a super(...) call
		boolean isSuperCall = false;
		// Set to true later if the callee is a this(...) call
		boolean isThisCall = false;

		/* @ nullable */
		JCVariableDecl exceptionDeclCall = translatingJML && esc ? null
				: treeutils.makeVarDef(syms.exceptionType, exceptionNameCall,
						methodDecl == null ? classDecl.sym : methodDecl.sym, that.pos);

		// A map to hold the preconditions for the callee, indexed by specification case
		// Since we might have a recursive call, we need to distinguish these from the
		// caller preconditions
		Map<JmlSpecificationCase, JCExpression> calleePreconditions = new HashMap<>();
		Map<JmlSpecificationCase, JCExpression> savedPreexpressions = this.calleePreconditions;
		this.calleePreconditions = calleePreconditions;

		JCExpression convertedReceiver = null;
		MethodSymbol calleeMethodSym = null; // The method symbol of the callee method or constructor
		try {
			// Translate the method name, and determine the receiver for the method call

			JCIdent newThisId = null; // The translated receiver
			JCExpression newThisExpr = null; // The translated receiver
			List<JCExpression> untrArgs; // The untranslated arguments
			List<JCExpression> trArgs; // The untranslated arguments
			List<JCExpression> typeargs;
			// The un/translated type arguments
			/* @ nullable */ JCExpression meth = null;
			// the qualified method name, if this is a method call
			/* @ nullable */ JCMethodInvocation apply = null;
			// non-null if this is a method call
			/* @ nullable */ JCNewClass newclass = null; // non-null if this a new object call

			if (that instanceof JCMethodInvocation) {
				apply = (JCMethodInvocation) that;
				meth = apply.meth;
				var symx = meth instanceof JCFieldAccess ? ((JCFieldAccess) meth).sym
						: meth instanceof JCIdent ? ((JCIdent) meth).sym : null;
				if (print) System.out.println("VAPP " + that + " " + symx.type + " " + symx + " " + symx.isStatic() + " " + symx.owner);
				untrArgs = apply.args;
				typeargs = apply.typeargs;
			} else if (that instanceof JCNewClass) {
				newclass = (JCNewClass) that;
				untrArgs = newclass.args;
				typeargs = newclass.typeargs;
			} else {
				error(that, "Invalid argument type for JmlAssertionAdder.applyHelper");
				return;
			}

			// Note: that.type will have type variables resolved for this call site,
			// courtesy of the type attribution phase, whereas meth.type will
			// still contain type variables
			Type resultType = that.type;
			boolean isVoid = resultType.getTag() == TypeTag.VOID;

			// FIXME - do we need to convert the varargsElement or its associated
			// expressions
			// Convert all the expressions
			// There is duplicate code because we have to be sure to evaluate everything in
			// order
			JCExpression trExpr = null; // Will hold the translated method call (for RAC)
			Type receiverType;

			if (print) System.out.println("APPLYHELPER-A " + calleeMethodSym);
			if (meth instanceof JCIdent) {
				receiverType = currentEnv.currentReceiver != null ? currentEnv.currentReceiver.type : classDecl.type;
				convertedReceiver = currentEnv.currentReceiver;

				JCIdent id = (JCIdent) meth;
				isSuperCall = id.name.equals(names._super);
				isThisCall = id.name.equals(names._this);

				typeargs = convert(typeargs);
				trArgs = convertArgs(that, untrArgs, meth.type.asMethodType().argtypes,
						(id.sym.flags() & Flags.VARARGS) != 0);

				calleeMethodSym = (MethodSymbol) id.sym;
				newTypeVarMapping = typevarMapping = typemapping(apply, null);
				// newTypeVarMapping = typevarMapping = typemapping(receiverType,
				// calleeMethodSym, typeargs);

				if (meth instanceof JCTree.JCLambda) {
					// An identifier as the method being applied should never be a lambda
					// expression.
					// Lambdas are always functinoal objects applied through a method such as run()
					// or apply()
					// But could it be a method reference???

					utils.error(that, "jml.internal", "Did not expect to encounter a lambda expression here");
					result = eresult = null; // FIXME WHAT should this be?
				}

				JCMethodInvocation mExpr = M.at(that).Apply(typeargs, meth, trArgs);
				mExpr.setType(that.type);
				mExpr.varargsElement = null; // We have combined the varargs elements into an array
				trExpr = mExpr;
				newThisExpr = utils.isJMLStatic(id.sym) ? null
						: (splitExpressions && currentEnv.currentReceiver != explicitThisId) ? newTemp(currentEnv.currentReceiver)
								: currentEnv.currentReceiver;
				newThisId = newThisExpr instanceof JCIdent ? (JCIdent) newThisExpr : null;
				enclosingMethod = id.sym;
				enclosingClass = id.sym.owner;
				if (print)
					System.out.println("APPLYHELPER-B " + calleeMethodSym.owner + " " + calleeMethodSym + " "
							+ specs.status(calleeMethodSym) );

			} else if (meth instanceof JCFieldAccess fa) {
                calleeMethodSym = (MethodSymbol) fa.sym;
				if (fa.selected instanceof JCIdent faid && (faid.name == names._this || faid.name == names._super)) {
					// We make a special case of this so that when 'this' is explicitly used in a
					// parent class,
					// the children see 'this' with the type of the child and see the combined specs
					// accordingly
					convertedReceiver = currentEnv.currentReceiver;
					receiverType = currentEnv.currentReceiver.type;
				} else if (calleeMethodSym.isStatic()) {
                    receiverType = fa.selected.type;
                    // This is static, but we still convert the receiver so that any errors in its evaluation are discovered
                    // However the value is not used; it may even be null.
                    Symbol s = TreeInfo.symbol(fa.selected);
                    //System.out.println("STATIC " + fa.selected + " " + fa.selected.type + " " + s + " " + (s == null ? "?" : s.getClass()));
                    //if (!alreadyConverted && !(s instanceof TypeSymbol)) convertExpr(fa.selected);
                    convertedReceiver = alreadyConverted ? fa.selected : convertExpr(fa.selected);
				} else {
					receiverType = fa.selected.type;
					convertedReceiver = alreadyConverted ? fa.selected : convertExpr(fa.selected);
					//if (calleeMethodSym.toString().contains("empty")) System.out.println("METHSEL " + that + " " + fa.selected + " " + fa.selected.type + " " + convertedReceiver);
				}

				typeargs = convert(typeargs); // FIXME - should this be translated before or after the receiver, here
												// and elsewhere
				trArgs = convertArgs(that, untrArgs, meth.type.asMethodType().argtypes,
						(fa.sym.flags() & Flags.VARARGS) != 0);
				newTypeVarMapping = typevarMapping = typemapping(apply, null);
				// newTypeVarMapping = typevarMapping = typemapping(receiverType, fa.sym, null,
				// meth.type.asMethodType());

				if (convertedReceiver instanceof JCTree.JCLambda
						|| convertedReceiver instanceof JCTree.JCMemberReference) {
					applyLambda(that, convertedReceiver, untrArgs, trArgs, resultType);
					return;
				}
				if (!utils.isJMLStatic(fa.sym)) {
					if (rac && convertedReceiver.toString().equals("super")) { // FIXME - need a better way to check
																				// this
						newThisExpr = convertedReceiver;
						newThisId = (JCIdent) convertedReceiver;
					} else if (!splitExpressions || convertedReceiver instanceof JCLambda) {
						newThisExpr = convertedReceiver;
						newThisId = null; // This is going to cause trouble - FIXME - geet rid of uses of newThisId
					} else {
						newThisExpr = newTemp(convertedReceiver);
						newThisId = (JCIdent) newThisExpr;
					}
					if (translatingJML && (fa.selected instanceof JCIdent
							&& localVariables.containsKey(((JCIdent) fa.selected).sym))) {
						// Local variables are presumed non-null
					} else if (utils.isJavaOrJmlPrimitiveType(fa.selected.type)) {
						// JML primitive types are not null
					} else {
						// Check that receiver is not null
						JCExpression e = treeutils.makeNotNull(fa.selected.pos, newThisExpr);
						addJavaCheck(fa, e, Label.POSSIBLY_NULL_DEREFERENCE, Label.UNDEFINED_NULL_DEREFERENCE,
								"java.lang.NullPointerException");
					}
				}
				if (print) System.out.println("APPLY " + calleeMethodSym.owner + "#" + calleeMethodSym + " " + System.identityHashCode(calleeMethodSym));

				JCFieldAccess fameth = M.at(meth.pos).Select( // Select sets to fa,sym.type, kinstead of
																				// resolved type
						!utils.isJMLStatic(fa.sym) ? newThisExpr : convertedReceiver, fa.sym);
				fameth.setType(meth.type);

				JCMethodInvocation mExpr = M.at(that).Apply(typeargs, fameth, trArgs);
				mExpr.setType(that.type);
				mExpr.varargsElement = null; // We have combined the arargs elements into an array
				trExpr = mExpr; // rewritten expression - for RAC
				enclosingMethod = fa.sym;
				enclosingClass = fa.sym.owner;

			} else if (newclass != null) {
				if (print) System.out.println("APPLYHELPER-NEWCLASS " + calleeMethodSym + " " + newclass);

				// FIXME - this does not handle qualified constructors of inner classes

				convertedReceiver = convertExpr(newclass.encl);
				receiverType = newclass.clazz.type;
				calleeMethodSym = (MethodSymbol) newclass.constructor;
				// newTypeVarMapping = typevarMapping = typemapping(newclass, null);
				newTypeVarMapping = typevarMapping = typemapping(newclass.clazz.type, null, null, null);

				if (convertedReceiver != null && !treeutils.isATypeTree(convertedReceiver)) {
					// Check that receiver is not null
					JCExpression e = treeutils.makeNotNull(newclass.encl.pos, convertedReceiver);
					addJavaCheck(newclass.encl, e, Label.POSSIBLY_NULL_DEREFERENCE, Label.UNDEFINED_NULL_DEREFERENCE,
							"java.lang.NullPointerException");
				}

				typeargs = convert(typeargs);
				trArgs = convertArgs(that, untrArgs, calleeMethodSym.type.asMethodType().argtypes,
						(calleeMethodSym.flags() & Flags.VARARGS) != 0);

				JCNewClass expr = M.at(that).NewClass(convertedReceiver, typeargs, convert(newclass.clazz), trArgs,
						convert(newclass.def)); // This call will recursively translate the methods in the body of the
												// new (anonymous) class
				expr.constructor = newclass.constructor;
				expr.constructorType = newclass.constructorType;
				expr.varargsElement = null; // We have combined the varargs elements into an array
				expr.setType(that.type);
				trExpr = expr;
				enclosingMethod = calleeMethodSym;
				enclosingClass = calleeMethodSym.owner;
				if (print) System.out.println("APPLYHELPER-NEWCLASS-Z " + calleeMethodSym.owner + " " + calleeMethodSym + " " + newclass);

				// newThisId, newThisExpr are assigned the resultId later - can only be used in
				// post-conditions
			} else {
				error(that, "Unknown alternative in interpreting method call");
				return;
			}
//	        if (!receiverType.toString().contains("<") && calleeMethodSym.owner.type.toString().contains("<")
//	                                && calleeMethodSym.owner.type.toString().startsWith(receiverType.toString())) {
//	            //System.out.println("REPLACING " + receiverType + " WITH " + calleeMethodSym.owner.type);  // FIXME - a temporary hack
//	            receiverType = calleeMethodSym.owner.type;
//	        }

			if (print)
				System.out.println("APPLYHELPER-D " + calleeMethodSym.owner + " " + calleeMethodSym);

			nestedCallLocation = that;

			var mspecs = specs.getAttrSpecs(calleeMethodSym);
			if (print) System.out.println("MSPECS " + calleeMethodSym.owner + " " + calleeMethodSym + " " + mspecs);
			boolean inliningCall = mspecs != null && mspecs.specDecl != null && mspecs.specDecl.mods != null
					&& utils.hasModifier(mspecs.specDecl.mods, Modifiers.INLINE);

			// Collect all the methods overridden by the method being called, including the
			// method itself
			Type rt = dynamicTypes.get(convertedReceiver);
			if (rt == null) rt = receiverType;
			// In the case of a call inside a lambda expression that is the argument of a
			// method (cf gitbug550)
			// rt is just a typevar with an upper bound of Object (the type of the outer
			// call) rather than
			// a resolved type. Not sure how to get the resolved type, so do the next line
			// as a fallback FIXME
			if (rt instanceof Type.TypeVar) rt = calleeMethodSym.owner.type;
			java.util.List<Pair<MethodSymbol, Type>> overridden = parents(calleeMethodSym, rt);
			
            boolean calleeIsPure = specs.isPureMethod(calleeMethodSym);
            //if (calleeMethodSym.toString().contains("ok")) System.out.println("ISPURE-Z " + calleeIsPure + " " + calleeMethodSym.owner + "." + calleeMethodSym);
            boolean effectivelyPure = true;
			{
			var pmap = paramActuals_ = new HashMap<Object,JCExpression>();
			if (savedParamActuals != null) pmap.putAll(savedParamActuals); // FIXME - I think we need this in the case where the current call can see out to an outer call -- but review and document the cases where this is needed
			if (print) System.out.println("INHERTIED PA " + paramActuals_);
			var specsIter = new SpecCaseIterator(calleeMethodSym, false);
			//if (print) System.out.println("ITERATOR HAS NEXT " + specsIter.hasNext() + " " + calleeIsPure + " " + effectivelyPure);
			while (specsIter.hasNext()) {
			    var info = specsIter.next();
			    x: if (!calleeIsPure) {
			        if (print) System.out.println("SPECCASE " + info.parentMethodSymbol + " " + info.specCase);
			        boolean hasAssignable = false;
			        boolean isEverything = true;
			        for (var clause: info.specCase.clauses) {
			            if (printb) System.out.println("CLAUSE " + clause);
			            if (clause.clauseKind == assignableClauseKind && clause instanceof JmlMethodClauseStoreRef ext) {
			                hasAssignable = true;
			                if (ext.list != null) {
			                    for (var sr: ext.list) {
			                        if (printb) System.out.println("   SR " + sr + " " + (sr instanceof JmlSingleton s && s.kind == everythingKind));
                                    effectivelyPure &= (!(sr instanceof JmlSingleton s && s.kind == nothingKind));
                                    isEverything &= (sr instanceof JmlSingleton s && s.kind == everythingKind);
			                    }
			                }
			            }
			        }
			        if (printb) System.out.println("EVERYTHING? " + isEverything + " " + hasAssignable);
			        if (!hasAssignable) effectivelyPure = false;
			        // FIXME - enable the following when we can adjust all the tests. Also decide whether to issue the warning if the caller has assignable \everythig; also find the name of the caller
//                    if (!hasAssignable && utils.esc) {
//                        utils.warningAndAssociatedDeclaration(info.specCase.sourcefile, info.specCase, log.currentSourceFile(), that,
//                                "jml.message", "Method " + calleeMethodSym + " has no assignable clause, so it is implicitly 'assignable \\everything', making its caller likely impossible to verify");
//
//                    }
//                    if (hasAssignable && isEverything && utils.esc) {
//                        utils.warningAndAssociatedDeclaration(info.specCase.sourcefile, info.specCase, log.currentSourceFile(), that,
//                                "jml.message", "Method " + calleeMethodSym + " has 'assignable \\everything', making its caller likely impossible to verify");
//
//                    }
			    }
                if (print) System.out.println("   MAPPING " + info.decl.params + " -> " + trArgs);
                // presuming all parameter symbols across all methods are unique
			    // map params of info.parentMethodSymbol to trArgs
			    var iter = trArgs.iterator();
			    if (info.decl != null) {
			        for (JCVariableDecl vd: info.decl.params) {
			            if (!iter.hasNext()) {
			                System.out.println("MISMATCHED PARAMETER LENGTHS-A " + calleeMethodSym + " " + info.decl.params + " " + trArgs);
			                Utils.dumpStack();
			                break;
			            }
			            pmap.put(vd.sym, iter.next());
			            //System.out.println("  PARAM MAP " + vd + " " + vd.sym.hashCode() + " -> " + paramActuals.get(vd.sym));
			        }
			    } else {
                    for (VarSymbol vsym: info.parentMethodSymbol.params) {
                        if (!iter.hasNext()) {
                            System.out.println("MISMATCHED PARAMETER LENGTHS-B " + calleeMethodSym + " " + info.parentMethodSymbol + " " + trArgs);
                            Utils.dumpStack();
                            break;
                        }
                        pmap.put(vsym, iter.next());
                        //System.out.println("  PARAM MAP " + vsym + " " + vsym.hashCode() + " -> " + paramActuals.get(vsym));
                    }
			    }
			    if (iter.hasNext()) {
			        System.out.println("MISMATCHED PARAMETER LENGTHS-C " + calleeMethodSym + " " + info.parentMethodSymbol + " " + trArgs);
			        Utils.dumpStack();
			    }
			}
            if (print) System.out.println("ALL PA " + paramActuals_);
			}
            //System.out.println("MAP " + calleeMethodSym + " " + paramActuals_);

			//System.out.println("PARAM MAPPINGS " + calleeMethodSym + " " + trArgs + " " + paramActuals_);
			// // The following line is needed for the case of new object expression with an
			// anonymous class without a constructor
			// if (overridden.isEmpty())
			// overridden.add(pair(calleeMethodSym,calleeMethodSym.owner.type));
			// System.out.print("OVERRIDDEN FOR " + calleeMethodSym.owner + " " +
			// calleeMethodSym);
			// overridden.iterator().forEachRemaining(p->System.out.print(" [" + p.first + "
			// # " + p.second + "]")); System.out.println();

			/**
			 * We can either try to keep subexpressions as subexpressions, or break them out
			 * into statements with temporary variables. Java code is broken into statements
			 * so that side-effects can be handled straightforwardly. Quantified expressions
			 * have to be kept as sub-expressions. Other JML expressions can be handled
			 * either way - the 'nodoTranslations' variable indicates what mode we are in:
			 * false means expand subexpresions, true means try to represent functions with
			 * axioms We currently expand non-quantified JML statements because method calls
			 * in JML expressions are easier to handle.
			 */
//            boolean uma = useMethodAxioms
////                  // FIXME - org.jmlspecs.JML has special functions - we want to inline them, not represent as methods; could do this test more efficiently
//                    && !calleeMethodSym.owner.getQualifiedName().toString().equals(Strings.jmlSpecsPackage + ".JML")
//                    && calleeMethodSym.params != null; // FIXME - why this?
			boolean calleeIsConstructor = calleeMethodSym.isConstructor();
			boolean calleeIsFunction = attr.isHeapIndependent(calleeMethodSym);
			boolean nodoTranslations = !rac && translatingJML
					&& (calleeIsFunction || (!(that instanceof JCNewClass) && isPure(calleeMethodSym)));
			boolean hasAModelProgram = hasModelProgram(overridden);
			if (hasAModelProgram)
				nodoTranslations = false;
			boolean isRecursive = isRecursiveCall(calleeMethodSym); // Checks whether this method has already been
																	// called in the call stack
			//nodoTranslations = nodoTranslations || isRecursive;
			if (!splitExpressions)
				nodoTranslations = true;
			boolean hasTypeArgs = calleeMethodSym.type instanceof Type.ForAll;
			if (calleeIsConstructor && !localVariables.isEmpty()) {
				utils.error(that, "jml.message",
						"Quantifier bodies may not contain constructors: " + calleeMethodSym.toString());
				throw new JmlInternalAbort(); // This problem is su[osed to be caught in JmlAttr
			}
			boolean addMethodAxioms = nodoTranslations && !calleeIsConstructor && !isSuperCall
					&& !isThisCall && !isVoid;
//            boolean addMethodAxioms = !rac && !calleeMethodSym.isConstructor() && !hasTypeArgs && !isSuperCall && !isThisCall && isPure(calleeMethodSym)
//                    && (!calleeMethodSym.getReturnType().isReference() || translatingJML);
			boolean inlineSpecs = !isRecursive && splitExpressions && localVariables.isEmpty(); // !addMethodAxioms;
			boolean strictlyPure = utils.isJavaOrJmlPrimitiveType(calleeMethodSym.getReturnType());
			boolean includeDeterminism = !rac && !calleeIsConstructor && !isSuperCall && !isThisCall
					&& (calleeIsPure || effectivelyPure) && !isVoid;
			boolean details = true && !calleeMethodSym.owner.getQualifiedName().toString().equals(Strings.JMLClass);

			addToCallStack(that);
			pushedMethod = true; // Must be after the check of isRecursive
			
			if (!calleeIsConstructor && isPure(calleeMethodSym) && !isVoid) {
			    // FIXME - that.type is not always parameterized
			    makeAndSaveMethodSymbol(that, calleeMethodSym, receiverType, calleeMethodSym.getReturnType());
			}

//            ListBuffer<JCStatement> saved = currentStatements;
			oldStatements = currentStatements; // FIXME - why twice
			initialInvariantCheck(that, isSuperCall, isThisCall, calleeMethodSym, savedThisExpr, newThisExpr, trArgs,
					apply);

			List<JCExpression> extendedArgs = extendArguments(that, calleeMethodSym, newThisExpr, trArgs);
//            if (!addMethodAxioms && !translatingJML && calleeIsFunction && !rac) {
//                addMethodAxiomsPlus(that, calleeMethodSym, newThisExpr, extendedArgs,
//                        receiverType, overridden, true);
//            }
			
			{
//		         ListBuffer<Type> newparamtypes = new ListBuffer<Type>();
//		            for (JCExpression e : newParamsWithHeap) {
//		                newparamtypes.add(e.type);
//		            }
//		            List<Type> newParamTypes = newparamtypes.toList();
//		            int calleeDeclPos = calleeSpecs != null && calleeSpecs.decl != null ? calleeSpecs.decl.pos : methodDecl.pos;		            
//		            MethodSymbol newsym = makeAndSaveNewMethodName(calleeMethodSym, that.type, calleeIsFunction, 
//		                calleeSpecs, calleeSpecs.javaDecl, newParamTypes);
			}
			if (print) {
				System.out.println("APPLYHELPER-E " + calleeMethodSym.owner + " " + calleeMethodSym + " translatingJML="
						+ translatingJML + " splitExpr=" + splitExpressions + " isFunction=" + calleeIsFunction + " addMethodAxioms=" + addMethodAxioms + " isRecursive=" + isRecursive + " nodoTrans=" + nodoTranslations);
//                var x = oldHeapMethods.get(oldenv == null ? null : oldenv.name);
//                if (x != null) System.out.println("     -E-NNULL " + x.get(calleeMethodSym));
	            if (print) System.out.println("ALL PA-E " + paramActuals_);
			}
			try {
				if (addMethodAxioms) {
					if (print)
						System.out.println("APPLYHELPER-E1 " + (calleeMethodSym == null ? " NULL"
								: (calleeMethodSym.owner + " " + calleeMethodSym)));
					addMethodAxiomsPlus(that, calleeMethodSym, newThisExpr, extendedArgs, receiverType, overridden,
							details);
					if (print)
						System.out.println("APPLYHELPER-E2 " + (calleeMethodSym == null ? " NULL"
								: (calleeMethodSym.owner + " " + calleeMethodSym)));
				}
				if (addMethodAxioms) {
					if ((useMethodAxioms || !localVariables.isEmpty() || calleeIsFunction)) {

//						if (print)
//							System.out.println("APPLYHELPER-E3 " + (calleeMethodSym == null ? " NULL"
//									: (calleeMethodSym.owner + " " + calleeMethodSym)));
//						var ex = makeDeterminismCall(that, calleeMethodSym, newThisExpr, extendedArgs);
//						result = eresult = ex;
//						currentEnv.currentReceiver = newThisExpr;
//						if (condition == null)
//							condition = treeutils.trueLit;
					} else {
						if (utils.isJMLStatic(calleeMethodSym) || trArgs.isEmpty()) {
							result = eresult = trExpr;
						} else {
							// FIXME - this does not rename the call and leaves the receiver outside the arg
							// list ???
							result = eresult = treeutils.makeMethodInvocation(that, newThisExpr, calleeMethodSym,
									trArgs);
						}
					}
				}
			} catch (Throwable eee) {
				utils.unexpectedException(eee, "APPLYHELPER-EE");
				eee.printStackTrace(System.out);
			}
			if (print)
				System.out.println("APPLYHELPER-F "
						+ (calleeMethodSym == null ? " NULL" : (calleeMethodSym.owner + " " + calleeMethodSym)));
			if (addMethodAxioms && !inlineSpecs) {
				JCExpression convertedResult = eresult;
				// Do any inlining
				JCExpression savedRE = resultExpr;
				VarSymbol savedSym = resultSym;
				resultSym = null;
				resultExpr = convertedResult;
				JCExpression res = insertAllModelProgramInlines(that, null, calleePreconditions,
						calleeMethodSym, typeargs, meth, inliningCall, overridden);
				if (res != null) {
					addAssumeEqual(that, Label.IMPLICIT_ASSUME, res, convertedResult);
				}
				resultExpr = savedRE;
				resultSym = savedSym;
				result = eresult = convertedResult;
			}
//            if (addMethodAxioms) {
//                return;
//            } // End of function section

			// Set up the result variable - for RAC we have to do this
			// outside the block that starts a few lines down, because the
			// result is a temporary ident that is used in subsequent
			// expressions - at least if the method returns a value and the
			// method call is a subexpression of a larger expression

			// If there is a possiblity that something will be allocated in the call we bump
			// up the allocation counter:
			// No if the method is pure and does not return an object.

			int preAllocCounter = allocCounter;
			if (!calleeIsPure || newclass != null || resultType.isReference() || isSuperCall || isThisCall) {
				++allocCounter;
			}

			// A variable for the method call result is declared, and then
			// everything else is within a block.
			resultExpr = null;
			if (!isVoid) {
				if (print)
					System.out.println("APPLYHELPER-G "
							+ (calleeMethodSym == null ? " NULL" : (calleeMethodSym.owner + " " + calleeMethodSym)));
				// The following line is used by spec inference to know what the newly declared
				// variable is the
				// result of. The : in the comment is essential and used to delineate the
				// descriptive text from the text of the expression
				addStat(comment(that, "Declaration for return value: " + that.toString(), methodDecl != null ? methodDecl.source() : classDecl.source()));
				if (rac) {
					// RAC
					if (resultType instanceof Type.CapturedType) {
						resultType = ((Type.CapturedType) resultType).getUpperBound();
					}
//                    if (resultType instanceof Type.TypeVar){
//                        resultType = syms.objectType;  // FIXME - use upperbound?
//                    }
					JCIdent resultId = currentFresh = newTempNull(that, resultType); // initialized to null
					resultSym = (VarSymbol) resultId.sym;
					resultExpr = resultId;
				} else if (newclass == null) {
					// ESC - Non-constructor call
					if (resultType instanceof Type.CapturedType) {
						resultType = ((Type.CapturedType) resultType).getUpperBound();
					}
//                    if (resultType instanceof Type.TypeVar){
//                        resultType = syms.objectType;  // FIXME - use upperbound?  // use paramActuals?
//                    }
					if (splitExpressions) {
						JCIdent resultId = newTemp(that, resultType);
						resultSym = (VarSymbol) resultId.sym;
						resultExpr = resultId;
						boolean nn;
						if (types.isSubtype(resultType, attr.JMLPrimitive))
							nn = true;
						else {
							nn = specs.isNonNull(that.type, calleeMethodSym);
//							System.out.println("VAP-NN " + that + " " + that.type + " " +
//							 calleeMethodSym.getReturnType() + " " +
//							 specs.isNonNull(that.type,(ClassSymbol)calleeMethodSym.owner) + " " +
//							 specs.isNonNull(calleeMethodSym) + " " + nn);
						}
						addNullnessAllocationTypeCondition(that, resultSym, false, false, false, null);
					} else {
						resultSym = null;
						resultExpr = that;
					}
				} else {
					// ESC - Constructor call
					Type t = that.type;
					if (t instanceof Type.TypeVar)
						t = paramActuals_.get(t.toString()).type;
					JCVariableDecl decl = treeutils.makeVarDef(t,
							names.fromString(Strings.newObjectVarString + that.pos + "_" + nextUnique()), null,
							that.pos);
					addStat(decl);
					resultSym = decl.sym;
					resultExpr = treeutils.makeIdent(that.pos, decl.sym);
					dynamicTypes.put(resultExpr, t);
					addNullnessAllocationTypeCondition(that, resultSym, false, false, false, null);
					{
						JCExpression cr = convertedReceiver;
						if (cr == null && !calleeMethodSym.owner.isStatic()
								&& !(calleeMethodSym.owner.owner instanceof MethodSymbol)) {
							cr = savedThisExpr;
						}
						if (cr != null) {
							VarSymbol vsym = makeEnclosingSymbol((ClassSymbol) calleeMethodSym.owner, cr);
							if (vsym != null) {
								JCExpression fa = treeutils.makeSelect(that.pos, resultExpr, vsym);
								JCExpression bin = treeutils.makeEqObject(that.pos, fa, cr);
								addAssume(that.pos(), Label.IMPLICIT_ASSUME, bin);
							}
						}
					}
				}
				if (print)
					System.out.println("APPLYHELPER-H " + calleeMethodSym.owner + " " + calleeMethodSym);
			}

			if (newclass != null) {
				newThisId = (JCIdent) resultExpr;
				newThisExpr = resultExpr;
				// FIXME - what about newclass.encl
			}

			if (print) System.out.println("APPLYHELPER-I " + calleeMethodSym.owner + " " + calleeMethodSym + " " + (!inlineSpecs) + " " + (!isVoid));
			if (!inlineSpecs && !isVoid) {
				if (addMethodAxioms)
					assertCalledMethodPrecondition(that, calleeMethodSym, extendedArgs);

//                JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(calleeMethodSym);
//                makeAndSaveNewMethodName(calleeMethodSym, resultType,
//                        calleeIsFunction, calleeSpecs,
//                        calleeSpecs.decl != null ? calleeSpecs.decl.pos : that.pos, newParamTypes);
				JCExpression e = makeDeterminismCall(that, calleeMethodSym, newThisExpr, extendedArgs);
				if (print) System.out.println("DETERMINISM CALL FOR " + includeDeterminism + " " + calleeMethodSym + " " + e);
				if (!calleeMethodSym.isConstructor() && calleeMethodSym.getReturnType().isReference()) {
					// makeFreshExpression()
				}
				if (includeDeterminism && strictlyPure) addAssumeEqual(that, Label.IMPLICIT_ASSUME, resultExpr, e);
				result = eresult = e;
				currentEnv.currentReceiver = newThisExpr;
				return;
			}
			if (print) System.out.println("APPLYHELPER-J " + calleeMethodSym.owner + " " + calleeMethodSym);

			// FIXME - comment?
			// FIXME - don't duplicate what is in visitLabelled
			checkBlock(stack0);
			ListBuffer<JCStatement> check1 = pushBlock(); // FIXME - needs a try block?

			// Add nullness and type assumptions about the result, for new operations
			// FIXME - what about for method calls
			// FIXME - rac should have the option of checking these assumptions

			if (esc && newclass != null) {
				if (print)
					System.out.println("APPLYHELPER-K " + calleeMethodSym.owner + " " + calleeMethodSym);

				// Result of a new operation is not null
				addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeNotNull(that.pos, copy(resultExpr)));

				// Type of result equals the type of the class of the new operation
				// FIXME - what about anonymous types
				JmlMethodInvocation typeof = M.at(that).JmlMethodInvocation(typeofKind, copy(resultExpr));
				typeof.javaType = false;
				typeof.type = jmltypes.TYPE;
				JmlMethodInvocation stype = M.at(that).JmlMethodInvocation(typelcKind,
						treeutils.makeType(that.pos, newclass.type));
				stype.javaType = false;
				stype.type = jmltypes.TYPE;
				stype.kind = typelcKind;
				addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeEqObject(that.pos, typeof, stype));

				// Java type of the result equals the java type of the new operation
				// FIXME - what about anonymous types
				typeof = M.at(that).JmlMethodInvocation(typeofKind, copy(resultExpr));
				typeof.javaType = true;
				typeof.type = jmltypes.TYPE;
				stype = M.at(that).JmlMethodInvocation(typelcKind, treeutils.makeType(that.pos, newclass.type));
				stype.javaType = true;
				stype.type = jmltypes.TYPE;
				addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeEqObject(that.pos, typeof, stype));

				if (resultExpr != null && !utils.isJavaOrJmlPrimitiveType(resultExpr.type)) { // FIXME - expect this to
																								// be always true
					newAllocation2(that, resultExpr); // FIXME - should have an JCIdent?
					JCExpression e = allocCounterEQ(that, resultExpr, allocCounter);
					addAssume(that, Label.IMPLICIT_ASSUME, e);
				}

				if (newclass.def != null)
					for (JCTree t : newclass.def.defs) {
						if (!(t instanceof JmlVariableDecl))
							continue;
						JmlVariableDecl vd = (JmlVariableDecl) t;
						if (!attr.isCaptured(vd))
							continue;
						JCExpression fa = M.at(vd.pos).Select(resultExpr, vd.sym);
						JCExpression init = ((JmlNewClass) newclass).capturedExpressions.get(vd.name);
						addAssumeEqual(vd.pos(), Label.IMPLICIT_ASSUME, fa, init);
					}
			}
			if (print)
				System.out.println("APPLYHELPER-L " + calleeMethodSym.owner + " " + calleeMethodSym);

			ListBuffer<JCStatement> saved = currentStatements;
//            oldStatements = currentStatements; // FIXME - why twice
//            initialInvariantCheck(that, isSuperCall, isThisCall, calleeMethodSym, newThisExpr, trArgs, apply);

			ClassSymbol calleeClass = (ClassSymbol) calleeMethodSym.owner;
			// Before the actual method call, check caller invariants and the invariants of
			// the caller's parameters

			// The following assumptions state that non-primitive arguments of a constructor
			// call
			// cannot be equal to the newly constructed object. We don't check this for RAC
			// because
			// at this point the value of the new object is still null, and might be equal
			// to a null
			// argument.
			// FIXME - why don't the stipulations about allocation time suffice?
			if (calleeMethodSym.isConstructor() && esc) {
				for (JCExpression arg : trArgs) {
					if (utils.isJavaOrJmlPrimitiveType(arg.type))
						continue;
					if (arg instanceof JCLambda)
						continue;
					JCExpression neq = treeutils.makeNeqObject(arg.pos, arg, newThisExpr);
					addAssume(arg, Label.IMPLICIT_ASSUME, neq);
				}
			}

			currentEnv.currentReceiver = newThisExpr;

			// Collects the complete precondition over all specification cases
			JCExpression combinedPrecondition = treeutils.falseLit;

			// Identify the clause to point to as the associated declaration if the
			// precondition fails.
			// The combinedPrecondition may be an OR of many specification cases,
			// each of which may be an AND of clauses - so if the precondition is
			// false, every specification case must be false.
			JmlMethodClauseExpr clauseToReference = null;
			boolean anyFound = false;
			for (Pair<MethodSymbol, Type> pair : overridden) {
				MethodSymbol mpsym = pair.first;

				JmlMethodSpecs s = specs.getDenestedSpecs(mpsym);
				if (s != null && !s.cases.isEmpty()) { // FIXME - should not count any 'code' specs
					anyFound = true;
					break;
				}
			}
			if (!anyFound && !inliningCall) {
				// No specs - set default

				JmlSpecs.MethodSpecs s = specs.getAttrSpecs(calleeMethodSym);
				// System.out.println("GETTING SPECS FOR CALLEE " + calleeMethodSym + " " +
				// calleeMethodSym.hashCode() + " " + s);
				if (s == null) {
					JmlMethodSpecs defaults = JmlSpecs.instance(context).defaultSpecs(methodDecl, methodDecl.sym,
							methodDecl.pos).cases;
					s = new JmlSpecs.MethodSpecs(methodDecl.mods, defaults);
					specs.putAttrSpecs(calleeMethodSym, s); // FIXME - are these specs all attributed? Should we mark
																// the specs status? will we actually need the specsEnv?
					s.cases.deSugared = null;
				} else {
					JmlMethodDecl decl = s.cases.decl;
					JmlMethodSpecs defaults = JmlSpecs.instance(context).defaultSpecs(decl,
							decl == null ? calleeMethodSym : decl.sym, // FIXME - why is decl ever null?
							decl == null ? methodDecl.pos : decl.pos).cases;
					s.cases = defaults;
					s.cases.deSugared = null;
				}
			}
			if (print)
				System.out.println("APPLYHELPER-M " + calleeMethodSym.owner + " " + calleeMethodSym);

			boolean hasModelProgram = hasModelProgram(overridden);

			// Iterate over all specs to find preconditions
			int callLabelReferenceCount = preAllocCounter; // FIXME _ is this too early?
			boolean allCasesNormal = true;
			boolean someCasesNormal = false;
			int numCases = 0;
			try { // In quantifications, splitExpressions is set to false
				boolean combinedNoModel = false;
				addStat(comment(that, "Checking preconditions of callee " + calleeMethodSym + " by the caller", null));

				var paramTypes = meth != null ? meth.type.getParameterTypes()
						: newclass != null ? newclass.type.getParameterTypes() : null;
				if (paramTypes != null) {
					// Type checks (e.g. NonNull) on assignments to formal parameters
					if (calleeMethodSym.params == null) {
						System.out.println(
								"NULL PARAMS " + calleeMethodSym.owner + " # " + calleeMethodSym.owner.members() + " # "
										+ calleeMethodSym.owner.members().getSymbols() + " # " + calleeMethodSym);
					} else {
						var calleeSpecs = specs.getAttrSpecs(calleeMethodSym);
						for (int i = 0; i < calleeMethodSym.params.size(); i++) {
							VarSymbol v = calleeMethodSym.params.get(i);
							boolean nn = specs.isCheckNonNullFormal(v.type, i, calleeSpecs, calleeMethodSym);
							if (nn) {
							    // FIXME - why this if?
								if (calleeSpecs.specDecl == null) {
									// There are no specs to point to
									addAssert(trArgs.get(i), Label.NULL_FORMAL,
											treeutils.makeNotNull(trArgs.get(i).pos, trArgs.get(i)),
											v.name + " in " + calleeMethodSym);
								} else {
								    var formal = calleeSpecs.specDecl.params.get(i);
								    var p = utils.locNonNullAnnotation(formal);
								    if (p == Position.NOPOS) p = formal.getStartPosition();
								    addAssert(trArgs.get(i), Label.NULL_FORMAL,
											treeutils.makeNotNull(trArgs.get(i).pos, trArgs.get(i)),
											new JCDiagnostic.SimpleDiagnosticPosition(p), 
											calleeSpecs.specDecl.sourcefile,
											v.name + " in " + calleeMethodSym);
								}
							}
						}
					}
				}

				boolean anyVisibleSpecCases = false;
				int preconditionDetail2 = 0;
				// System.out.print("OVERRIDDEN-A " + calleeMethodSym.owner + " " +
				// calleeMethodSym);
				// overridden.iterator().forEachRemaining(p->System.out.print(" [" + p.first + "
				// # " + p.second + "]")); System.out.println();
				for (Pair<MethodSymbol, Type> pair : overridden) {
					MethodSymbol mpsym = pair.first;
					Type classType = pair.second;
					if (mpsym.isConstructor() && mpsym.owner.isAnonymous() && mpsym == calleeMethodSym
							&& that instanceof JmlNewClass) {
						MethodSymbol m = findParentConstructor((JmlNewClass) that);
						if (m != null) {
							mpsym = m;
							classType = m.owner.type;
						}
					}
					addStat(comment(that, "... Preconditions of callee " + calleeMethodSym.owner + " " + calleeMethodSym
							+ " in " + classType.toString() + " " + mpsym.owner + " " + mpsym, null));
					if (print)
						System.out.println("... Preconditions of callee " + calleeMethodSym + " in "
								+ classType.toString() + " " + mpsym.owner + " " + mpsym);
					// FIXME - meth is null for constructors - fix that also; also generic types
					typevarMapping = typemapping(classType, calleeMethodSym, typeargs, meth == null ? null
							: meth.type instanceof Type.MethodType ? (Type.MethodType) meth.type : null, null);
					if (apply != null)
						typevarMapping = typemapping(apply, typevarMapping);
					// This initial logic must match that below for postconditions

					JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
					if (calleeSpecs == null)
						continue; // FIXME - not sure about this - should get a default?
//					paramActuals_ = new HashMap<Object, JCExpression>();
//					if (savedParamActuals != null)
//						paramActuals_.putAll(savedParamActuals); // In cases that we are capturing the environment, such
//																// as inlining lambdas or model programs, we still need
//																// the mappings from the outer call // NOt sure this is
//																// needed
//					mapParamActuals.put(mpsym, paramActuals_);

					var ssym = specs.getAttrSpecs(mpsym).specSym;
//					if (ssym != null) {
//						// Map the formals for this particular method to the corresponding translated
//						// actual argument
//						// The MethodSymbol used to iterate over the parameter VarSymbols must
//						// correspond to the Env
//						// used to attribute the specifications. We use the specSym because the javaSym
//						// might belong to
//						// a binary and thus have different parameter names (which it might if it has a
//						// java declaration as well)
//						if (ssym.params == null) {
//							// For some reason, calls to clone() have ssym.params == null instead of an
//							// empty parameter list
//						} else {
//							Iterator<VarSymbol> iter = ssym.params.iterator();
//							for (JCExpression arg : trArgs) {
//								VarSymbol v = null;
//								if (iter.hasNext())
//									paramActuals.put(v = iter.next(), arg);
//								else {
//									// FIXME - mismatch in number of arguments; what about varargs?
//								}
//								// if (v != null) System.out.println("MAPPED FORMAL SYM " + v + " " + arg + " "
//								// + (arg!=null?arg.getClass().toString():"?") + " " + mpsym.owner + "." + mpsym
//								// + " " + methodDecl.sym);
//							}
//						}
//					}
					if (esc) {
						// Map type variables for this particular method declaration to the
						// corresponding type, already determined by type attribution
						if (newclass != null && newclass.clazz instanceof JCTypeApply) {
							Iterator<Symbol.TypeVariableSymbol> tpiter;
							if (calleeClass.isAnonymous()) {
								tpiter = newclass.clazz.type.tsym.getTypeParameters().iterator();
							} else {
								tpiter = calleeClass.getTypeParameters().iterator(); // calleeSpecs.decl.typarams.iterator();
							}
							for (JCExpression tp : ((JCTypeApply) newclass.clazz).arguments) {
								paramActuals_.put(tpiter.next(), tp);
							}
						}
						if (newclass == null && (typeargs == null || typeargs.isEmpty())) {
							Type.MethodType t = null;
							if (calleeMethodSym.type instanceof Type.MethodType) {
								t = (Type.MethodType) calleeMethodSym.type;
							} else if (calleeMethodSym.type instanceof Type.ForAll) {
								t = ((Type.ForAll) calleeMethodSym.type).asMethodType();
							}
							List<Type> list = t.getTypeArguments();
							Iterator<Type> tpiter = list.iterator();
							List<Type> formals = null;
							if (meth.type instanceof Type.MethodType)
								formals = ((Type.MethodType) meth.type).getTypeArguments();
							else if (meth.type instanceof Type.ForAll)
								formals = ((Type.ForAll) meth.type).getTypeArguments();
							if (list.isEmpty()) {
								// No actual type arguments
							} else if (list.size() != formals.size()) {
								// ERROR: lists have different length
							} else {
								for (Type tp : formals) {
									Type tt = tpiter.next();
									if (tt instanceof Type.TypeVar) {
										paramActuals_.put(tt.toString(), treeutils.makeType(that.pos, tp));
									}
								}
							}
						}
						if (typeargs != null && !typeargs.isEmpty()) {
							Iterator<Symbol.TypeVariableSymbol> tpiter = calleeMethodSym.getTypeParameters().iterator();
							for (JCExpression tp : typeargs) {
								paramActuals_.put(tpiter.next(), tp);
							}
						}
					}
					if (print) System.out.println("APPLYHELPER-N " + calleeMethodSym.owner + " " + calleeMethodSym);

					// We need to calculate all the preconditions before doing any assignable
					// clauses because we need to check each assignable clause against all the
					// others

					// For each specification case, we accumulate the precondition and save the
					// expression for later use
					Map<Object, JCExpression> clauseIds = new HashMap<>();
					JCExpression savedElseExpression = elseExpression;
					elseExpression = treeutils.falseLit;
					for (JmlSpecificationCase cs : calleeSpecs.cases) {
						// System.out.println("CALCPRE-A " + mpsym.owner + " " + mpsym + " " +
						// cs.hashCode() + " " + cs);
                        if (!doSpecificationCase(methodDecl, calleeMethodSym, mpsym, cs)) continue;
//						if (!utils.jmlvisible(mpsym, classDecl.sym, mpsym.owner, cs.modifiers.flags,
//								methodDecl != null ? methodDecl.mods.flags : Flags.PUBLIC)) // FIXME - review this for when not in a method
//							continue;
//						if (translatingJML && cs.token == exceptionalBehaviorClause)
//							continue; // exceptional behavior clauses are not used for pure functions within JML
//										// expressions
//						if (mpsym != calleeMethodSym && cs.code)
//							continue;
						addStat(comment(cs, "Spec Case: " + cs, cs.sourcefile));
						// System.out.println("CALCPRE " + mpsym.owner + " " + mpsym + " " +
						// cs.hashCode() + " " + cs);
						if (cs.block != null)
							hasAModelProgram = true;
						numCases++;
						if (cs.token != normalBehaviorClause)
							allCasesNormal = false;
						if (cs.token == normalBehaviorClause)
							someCasesNormal = true;
						preconditionDetail2++;
						anyVisibleSpecCases = true;
						JCExpression preId = null; // JCIdent or JCLiteral
						ListBuffer<JCStatement> oldStatements = currentStatements;
						if (rac) {
							ListBuffer<JCStatement> save = currentStatements;
							currentStatements = outerDeclarations;
							preId = newTemp(treeutils.falseLit);
							currentStatements = save;
							pushBlock();
						}
						JCExpression pre = copy(translatingJML ? savedCondition : treeutils.trueLit);
						JCExpression prex = treeutils.trueLit;
						boolean noModel = false;
						JavaFileObject prev = log.useSource(cs.source());
						try {
							JCExpression diverges = null;
							JmlSource divergesPosition = cs;
							JmlMethodClauseExpr mcc = null; // Remember the first clause in the specification case
							int preconditionDetailLocal3 = 0;
							for (JmlMethodClause clause : cs.clauses) {
								IJmlClauseKind ct = clause.clauseKind;
								if (ct == MethodDeclClauseExtension.oldClause) {
									if (clauseIds.containsKey(clause)) continue; // Don't repeat
									clauseIds.put(clause, null);
									for (JCVariableDecl decl : ((JmlMethodClauseDecl) clause).decls) {
										addTraceableComment(decl, clause.toString());
										// Name name = names.fromString(decl.name.toString() + "__OLD_" + decl.pos);
										// JCVariableDecl newdecl = convertCopy(decl);
										Name name = names.fromString(
												decl.name.toString() + "__OLD_" + decl.pos + "_" + nextUnique());
										// FIXME - does the declzaration really need to be duplicated -- it is only used
										// once
										JCVariableDecl newdecl = treeutils.makeDupDecl(decl, methodDecl.sym, name,
												clause.pos);
										if (!rac)
											newdecl.mods.flags |= Flags.FINAL;
										addStat(oldStatements, newdecl);
										mapSymbols.put(decl.sym, newdecl.sym);
										JCIdent id = treeutils.makeIdent(clause.pos, newdecl.sym);
										ListBuffer<JCStatement> check = pushBlock();
										if (rac) {
											newdecl.init = treeutils.makeZeroEquivalentLit(decl.init.pos, decl.type);
										} else {
											addNullnessTypeCondition(id, id.sym, false);
										}
										alreadyDiscoveredFields.add(id.sym);
										if (decl.init != null) {
											JCExpression convertedInit = convertJML(decl.init);
											if (newdecl.sym.type.isReference() && specs.isNonNull(newdecl.sym)) {
												addAssert(decl.init, Label.POSSIBLY_NULL_ASSIGNMENT,
														treeutils.makeNotNull(decl.init.pos, convertedInit));
											}
											pushArithMode();
											convertedInit = addImplicitConversion(decl.init, decl.type, convertedInit);
											popArithMode();
											if (rac) {
												JCExpressionStatement stat = treeutils.makeAssignStat(decl.init.pos, id,
														convertedInit);
												addStat(stat);
											} else {
												addAssume(clause, Label.PRECONDITION,
														treeutils.makeEquality(clause.pos, id, convertedInit));
											}
										}
										JCBlock bl = popBlock(clause, check);
										if (treeutils.isTrueLit(prex)) {
											addStat(bl);
										} else {
											addStat(M.at(clause).If(prex, bl, null));
										}
										// paramActuals.put(decl.sym,id);
										// preparams.put(decl.sym,id);
										saveMapping(decl, id);
										clauseIds.put(clause, id);

									}
								} else if (ct == divergesClauseKind) {
									// FIXME - visibility?
									divergesPosition = clause;
									JCExpression ex = ((JmlMethodClauseExpr) clause).expression;
									diverges = diverges == null ? ex : treeutils.makeAndSimp(ex, diverges, ex);
								} else if (ct == requiresClauseKind) {
									// FIXME - need to include the requires expression in the condition for the sake
									// of old expressions - also below
									JmlMethodClauseExpr requiresClause = (JmlMethodClauseExpr) clause;
//                                        JCExpression e = convertJML(mce.expression,pre,false); // Might throw an exception
//                                        prex = treeutils.makeAndSimp(mce.expression.pos, prex, e);
									if (mcc == null)
										mcc = requiresClause;
									clauseToReference = (JmlMethodClauseExpr) clause;
									if (clauseIds.containsKey(clause)) {
										prex = clauseIds.get(clause);
										JCExpression ex = ((JmlMethodClauseExpr) clause).expression;
										java.util.List<JCExpression> conjuncts = findConjunctions(ex);
										cpreindex3 += conjuncts.size();
//                                            for (JCExpression conjunct: conjuncts) {
//                                                cpreindex3++;
//                                                JCTree ast = getMapping(conjunct);
//                                                if (ast instanceof JCIdent) {
//                                                    JCIdent idcpre = (JCIdent)ast;
//                                                    String nm = "_$CPRE__" + preconditionDetailLocal + "_" + cpreindex2 + "_" + cpreindex3;
//                                                    JCIdent vd = newTemp(nm, idcpre);
//                                                    saveMapping(treeutils.makeIdent(conjunct, vd.sym), conjunct);
//                                                    preconditionDetailClauses.put(nm,clause.sourcefile);
//                                                }
//                                            }
										continue; // Don't reevaluate if we have nested specs
									}
									boolean pv = checkAccessEnabled;
									checkAccessEnabled = false; // FIXME _ review what this is for
									ListBuffer<JCStatement> check = null;
									try {
										JCExpression ex = requiresClause.expression;
										addTraceableComment(ex, clause.toString());
										JCExpression nextPreExpr;
										JCBlock thenbl, elsebl;
										JCExpression convertedEx;
										if (rac) {
											// FIXME: The following does not work correctly (cf.
											// testNonNullPrecondition)
											// unless a boxed type is used (a Boolean). It is not at all clear why this
											// should be.
											// The generated source code looks perfectly fine. See additional instance
											// in JmlAssertionAdder.
											JCVariableDecl d = newTempDecl(ex, boxedType(ex.type));
											// JCVariableDecl d = newTempDecl(ex,(ex.type));
											d.init = treeutils.makeZeroEquivalentLit(ex.pos, ex.type);
											addStat(oldStatements, d);
											check = pushBlock();
											convertedEx = convertJML(ex);
											nextPreExpr = treeutils.makeIdent(ex.pos, d.sym);
											JCExpressionStatement stat = treeutils.makeAssignStat(ex.pos, nextPreExpr,
													convertedEx);
											addStat(stat);
											// addStat(treeutils.makeUtilsMethodStat(ex.pos, "report",
											// treeutils.makeStringLiteral(ex.pos, "then")));
											// addStat(treeutils.makeUtilsMethodStat(ex.pos, "reportBoolean",
											// treeutils.makeStringLiteral(ex.pos, "A"), nextPreExpr));
											thenbl = popBlock(ex, check);
											elsebl = null;
//                                                pushBlock();
//                                                addStat(treeutils.makeAssignStat(ex.pos,nextPreExpr,treeutils.falseLit));
//                                                //addStat(treeutils.makeUtilsMethodStat(ex.pos, "report", treeutils.makeStringLiteral(ex.pos, "else")));
//                                                //addStat(treeutils.makeUtilsMethodStat(ex.pos, "reportBoolean", treeutils.makeStringLiteral(ex.pos, "B"), nextPreExpr));
//                                                JCBlock elsebl = popBlock(ex);
										} else {
											nextPreExpr = newTemp(ex, ex.type); // Arguments give position and type, no
																				// initial value
											cpreindex3 = preconditionDetailLocal3;
											JCExpression labeledPrecondition = insertLabelsOnConjunctions(ex,
													"_$CPRE__" + preconditionDetailLocal + "_" + preconditionDetail2);
											preconditionDetailLocal3 = cpreindex3;
											check = pushBlock();
											convertedEx = convertJML(labeledPrecondition);
											addAssume(ex, Label.IMPLICIT_ASSUME,
													treeutils.makeEquality(ex.pos, nextPreExpr, convertedEx));
											thenbl = popBlock(ex, check);
											ListBuffer<JCStatement> ch = pushBlock();
											addAssume(ex, Label.IMPLICIT_ASSUME,
													treeutils.makeEquality(ex.pos, nextPreExpr, treeutils.falseLit));
											elsebl = popBlock(ex, ch);
										}
										if (prex == null || treeutils.isTrueLit(prex)) {
											addStat(thenbl);
											if (treeutils.isLiteral(convertedEx))
												nextPreExpr = convertedEx;
										} else {
											addStat(M.at(ex.pos).If(prex, thenbl, elsebl));
										}
										check = null;
										prex = nextPreExpr;
										clauseIds.put(clause, nextPreExpr);
									} catch (NoModelMethod ex) {
										// FIXME - what to do
									} catch (JmlNotImplementedException ex) {
										notImplemented("requires clause containing ", ex); // FIXME - needs source
									} finally {
										if (check != null)
											popBlock(clause, check);
										checkAccessEnabled = pv;
									}
								}
							}
							pre = prex;
							if (diverges != null) {
								diverges = treeutils.makeAnd(diverges.pos, pre, treeutils.makeNot(diverges, diverges));
								for (var callerDiverges : divergesExpressions) {
									JCExpression e = convertJML(
											treeutils.makeImplies(diverges.pos, callerDiverges.first, diverges));
									addAssert(divergesPosition.pos(), Label.DIVERGES, e, callerDiverges.second.pos(),
											callerDiverges.second.source());
								}
							}
						} catch (NoModelMethod e) {
							pre = treeutils.falseLit;
							noModel = true;
							combinedNoModel = true;
						} catch (JmlNotImplementedException e) {
							notImplemented("requires clause containing ", e); // FIXME - clause source
							pre = treeutils.falseLit;
						} catch (Exception e) {
							System.out.println("EXCEPTION-Q " + e);
							e.printStackTrace(System.out);
						} finally {
							log.useSource(prev);
						}
						if (!rac) {
							if (pre instanceof JCLiteral || pre instanceof JCIdent)
								preId = pre;
							else
								preId = newTemp(pre);
						} else if (noModel) {
							popBlock();
							// pre = preId; // FIXME - should we say the the case is not being checked
							// because ther eis a missing model method
						} else { // FIXME - not sure why this fails for esc (see rac-guarded statements above as
									// well)
							preId.pos = pre.pos;
							addStat(treeutils.makeAssignStat(pre.pos, copy(preId), pre));
							addStat(wrapRuntimeException(pre, popBlock(pre),
									"JML undefined precondition - exception thrown", null));
						}
						elseExpression = treeutils.makeBitOrSimp(cs.pos, elseExpression, preId);
						//System.out.println("PUTPRE " + preId + " " + mpsym.owner + "." + mpsym + " " + cs.hashCode() + " " + cs);
						calleePreconditions.put(cs, preId);
						pre = preId;
						combinedPrecondition = treeutils.makeOrSimp(pre.pos, combinedPrecondition, pre);

						// addStat(treeutils.makeUtilsMethodStat(pre.pos, "reportBoolean",
						// treeutils.makeStringLiteral(that.pos, "C"), combinedPrecondition));
						if (esc) {
							String nm = "_$CPRE__" + preconditionDetailLocal + "_" + preconditionDetail2;
							JCIdent cpreId = newTemp(cs.pos, nm, pre);
							saveMapping(cpreId, cpreId);
							preconditionDetailClauses.put(nm, cs.sourcefile);
						}
					}
					clauseIds.clear();
					elseExpression = savedElseExpression;
				}
				if (print) System.out.println("APPLYHELPER-P " + calleeMethodSym.owner + " " + calleeMethodSym);

				if (!anyVisibleSpecCases) {
					utils.warning(that.pos, "jml.message",
							"No visible specifications for this call site: " + utils.qualifiedMethodSig(calleeMethodSym)
									+ " called from " + utils.qualifiedMethodSig(methodDecl.sym));
				}
				// Issue the overall precondition check (which is an OR of all the preconditions
				// for each spec case, acrsoss all overriding methods).
				// clauseToReference is null if the precondition is just a true literal // FIXME
				// - this is confusing if there is more than one clause in one spec case
				if (anyVisibleSpecCases) {
					ListBuffer<JCStatement> check3 = pushBlock();
					if (splitExpressions) {
						String nm = "_$CPRE__" + preconditionDetailLocal;
						preconditionDetailClauses.put(nm, log.currentSourceFile()); // methodDecl might be null, so no methodDecl.sourcefile
						JCExpression temp = newTemp(combinedPrecondition.pos, nm, combinedPrecondition);
						saveMapping(temp, temp);
						combinedPrecondition = temp;
					}
					if (combinedNoModel) {
						// skip
//                    } else if (translatingJML) {
//                        //JCExpression conj = treeutils.makeAnd(methodDecl.pos, collectedInvariants, combinedPrecondition);
//                        addAssert(that,Label.UNDEFINED_PRECONDITION,
//                                conditionedAssertion(methodDecl, combinedPrecondition),
//                                clauseToReference,clauseToReference.source());

					} else {
//						System.out.println("CALLEE " + calleeMethodSym + " " + calleeMethodSym.owner + " " + that + " " + that.getClass() );
//						var cns = (MethodSymbol)((JCNewClass)that).constructor;
//						System.out.println("EXPR " + cns + " " + cns.owner + " " + specs.get(cns) + " " + specs.get(cns).javaDecl);
						JmlSource loc = mspecs == null ? null : mspecs.specDecl;
						if (loc == null)
							loc = clauseToReference;
						// addStat(treeutils.makeUtilsMethodStat(that.pos, "reportBoolean",
						// treeutils.makeStringLiteral(that.pos, "D"), combinedPrecondition));
						var prev = log.useSource(methodDecl != null ? methodDecl.sourcefile : classDecl.sourcefile); // FIXME - probably should be the containing clause sourcefile
						JCStatement stat = loc != null
								? addAssert(that, translatingJML ? Label.UNDEFINED_PRECONDITION : Label.PRECONDITION,
										combinedPrecondition, (DiagnosticPosition) loc, loc.source())
								: addAssert(that, translatingJML ? Label.UNDEFINED_PRECONDITION : Label.PRECONDITION,
										combinedPrecondition);
						log.useSource(prev);
						if (stat instanceof JmlStatementExpr)
							((JmlStatementExpr) stat).description = combinedPrecondition.toString();
						else if (stat instanceof JCTree.JCIf && ((JCIf) stat).thenpart instanceof JmlStatementExpr)
							((JmlStatementExpr) ((JCIf) stat).thenpart).description = combinedPrecondition.toString();
					}
					JCBlock bl = popBlock(that, check3);
					addStat(wrapRuntimeException(that, bl, "JML undefined precondition - exception thrown", null));
				}
			} catch (Exception e) {
				utils.unexpectedException("TETS", e);
			}
			if (print) System.out.println("APPLYHELPER-Q " + calleeMethodSym.owner + " " + calleeMethodSym);

			// Add a label that signifies the state before the method call
			// This label defines the pre-state for the method call computations, so it
			// must be after computations of 'OLD' clauses but before processing the
			// assignable clauses
			Name calllabel = null;
			if (splitExpressions) { //if (!translatingJML) {
				JCBlock bl = M.at(that).Block(0L, com.sun.tools.javac.util.List.<JCStatement>nil());
				String label = "_JMLCALL_" + that.pos + "_" + nextUnique();
				calllabel = names.fromString(label);
				JmlLabeledStatement stat = M.at(that).JmlLabeledStatement(calllabel, null, bl);
				addStat(stat);
				LabelProperties lp = recordLabel(calllabel, stat);
				lp.allocCounter = preAllocCounter;

				oldStatements = currentStatements;

//                stat.extraStatements.addAll(currentStatements);

				markLocation(calllabel, currentStatements, stat);
			}
			currentOldLabel = calllabel;
			//System.out.println("CURRENTOLDENV-B " + currentOldEnv.name + " " + calllabel + " " + allocCounter + " " + preAllocCounter);
			if (print) System.out.println("APPLYHELPER-R " + calleeMethodSym.owner + " " + calleeMethodSym);

            var assignsListsBuffer = new ListBuffer<StoreRefGroup>();
            var readsListsBuffer = new ListBuffer<StoreRefGroup>();
            TranslationEnv calleeEnv = new TranslationEnv(newThisId,null,allocCounter,calleeMethodSym);
            calleeEnv.stateLabel = calllabel;
            currentEnv = currentEnv.pushEnvCopy(calleeEnv);
			try {
                for (Pair<MethodSymbol, Type> pair : overridden) {
                    MethodSymbol parentSym = pair.first;
                    Type classType = pair.second;
                    
//              for (var info: new SpecCaseIterable(calleeMethodSym)) {
//                  MethodSymbol parentSym = info.parentMethodSymbol();
//                  Type classType = mpsym.owner.type;
                    
                    if (parentSym.isConstructor() && parentSym.owner.isAnonymous() && parentSym == calleeMethodSym
                            && that instanceof JmlNewClass) {
                        MethodSymbol m = findParentConstructor((JmlNewClass) that);
                        if (m != null) {
                            parentSym = m;
                            classType = m.owner.type;
                        }
                    }
                    //System.out.println("PARENT " + calleeMethodSym + " " + parentSym);
                    addStat(comment(that,"... Processing frame conditions of callee " + calleeMethodSym + " in " + classType.toString(),null));
                    
                    // FIXME - from here down to loop is duplicated from above

                    // FIXME - meth is null for constructors - fix that also; also generic types
                    typevarMapping = typemapping(classType, calleeMethodSym, typeargs,
                            meth == null ? null
                                    : meth.type instanceof Type.MethodType ? (Type.MethodType) meth.type : null,
                            null);
                    if (apply != null)
                        typevarMapping = typemapping(apply, typevarMapping);
                    // This initial logic must match that below for postconditions

                    JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(parentSym);
                    if (calleeSpecs == null)
                        continue; // FIXME - not sure about this - should get a default?

                    currentEnv.arithmeticMode = Arithmetic.Math.instance(context).defaultArithmeticMode(parentSym, true);
                    for (JmlSpecificationCase cs : calleeSpecs.cases) {
                        //System.out.println("   SPECCASE " + cs);
                        if (!doSpecificationCase(methodDecl, calleeMethodSym, parentSym, cs)) continue;
                        //if (translatingJML && cs.token == exceptionalBehaviorClause) continue;

                        JavaFileObject prev = log.useSource(cs.source());
                        JCExpression pre = calleePreconditions.get(cs);
                        if (pre == null) continue; // anonymous class without specs
                        if (treeutils.isFalseLit(pre)) continue;
                        var check8 = pushBlock();
                        try {
                            if (cs.block == null) { // FIXME - not quite sure of this guard // FIXME - what
                                                            // should we check for field initializers
                                //System.out.println("   SPECCASE USED " + cs);
                                // Handle assignable & accessible clauses
                                boolean anyReads = false;
                                boolean anyAssigns = false;
                                for (JmlMethodClause clause : cs.clauses) {
                                    JavaFileObject prevSource = log.useSource(clause.source());
                                    // We iterate over each storeref item in each assignable clause
                                    // of each specification case of the callee - for each item we check
                                    // that assigning to it (under the appropriate preconditions)
                                    // is allowed by each of the specification cases of the callee and caller specs.
                                    if (clause instanceof JmlMethodClauseStoreRef cst) {

                                        if (clause.clauseKind == accessibleClauseKind) {
                                            anyReads = true;
                                            readsListsBuffer.add(convertFrameConditionList(clause, copy(pre), cst.list));
                                        } else if (clause.clauseKind == assignableClauseKind) {
                                            anyAssigns = true;
                                            assignsListsBuffer.add(convertFrameConditionList(clause, copy(pre), cst.list));
                                        }
                                    }
                                }
                                if (!anyReads) {
                                    readsListsBuffer.add(new StoreRefGroup(copy(pre), List.<StoreRefGroup.Item>of(new StoreRefGroup.Item(
                                        isHeapIndependent(parentSym) ? StoreRefGroup.Kind.NOTHING : StoreRefGroup.Kind.EVERYTHING))));
                                }
                                if (!anyAssigns) {
                                    readsListsBuffer.add(new StoreRefGroup(copy(pre), List.<StoreRefGroup.Item>of(new StoreRefGroup.Item(
                                        isPure(parentSym) ? StoreRefGroup.Kind.NOTHING : StoreRefGroup.Kind.EVERYTHING))));
                                }
                            }
                        } finally {
                            addStat(popBlock(cs, check8));
                            log.useSource(prev);
                        }
                    }
                }
			} catch (Throwable e) {
			    System.out.println("CRASH");
			    e.printStackTrace(System.out);
			}
			var readsLists = readsListsBuffer.toList();
			//System.out.println("READSLIST " + calleeMethodSym + " " + overridden.size() + " " + readsLists);
			var assignsLists = assignsListsBuffer.toList();
            //System.out.println("ASSIGNSLIST " + calleeMethodSym + " " + overridden.size() + " " + assignsLists);
			currentEnv = currentEnv.popEnv();
			currentEnv = currentEnv.pushEnvCopy();
            //System.out.println(" PURE? " + calleeMethodSym.owner + " " + calleeMethodSym + " " + calleeIsPure);
			{
				// System.out.print("OVERRIDDEN-C " + calleeMethodSym.owner + " " +
				// calleeMethodSym);
				// overridden.iterator().forEachRemaining(p->System.out.print(" [" + p.first + "
				// # " + p.second + "]")); System.out.println();
				if (hasAModelProgram) {
					addStat(comment(that,
							"... Not checking assignables where there is a model_program " + calleeMethodSym, null));
				} else if (convertedReceiver instanceof JCLambda) {
					addStat(comment(that, "... Not checking assignables when inlining a lambda " + calleeMethodSym,
							null));
				} else if (!rac) {
					for (Pair<MethodSymbol, Type> pair : overridden) {
						MethodSymbol mpsym = pair.first;
						Type classType = pair.second;
//					for (var info: new SpecCaseIterable(calleeMethodSym)) {
//						MethodSymbol mpsym = info.parentMethodSymbol();
//						Type classType = mpsym.owner.type;
						
						//System.out.println("FROM OVERRIDDEN " + calleeMethodSym + " " + mpsym);
						
						if (mpsym.isConstructor() && mpsym.owner.isAnonymous() && mpsym == calleeMethodSym
								&& that instanceof JmlNewClass) {
							MethodSymbol m = findParentConstructor((JmlNewClass) that);
							if (m != null) {
								mpsym = m;
								classType = m.owner.type;
							}
						}
						if (calleeIsPure) {
		                    addStat(comment(that, "... Not checking assignables of pure callee " + calleeMethodSym, null));
		                } else {
		                    addStat(comment(that,"... Checking assignables of callee " + calleeMethodSym + " in " + classType.toString(),null));
		                }
						//System.out.println("... Checking assignables of callee " + calleeMethodSym + " in " + classType.toString());
						
						// FIXME - from here down to loop is duplicated from above

						// FIXME - meth is null for constructors - fix that also; also generic types
						typevarMapping = typemapping(classType, calleeMethodSym, typeargs,
								meth == null ? null
										: meth.type instanceof Type.MethodType ? (Type.MethodType) meth.type : null,
								null);
						if (apply != null)
							typevarMapping = typemapping(apply, typevarMapping);
						// This initial logic must match that below for postconditions

						JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
						if (calleeSpecs == null)
							continue; // FIXME - not sure about this - should get a default?
						//System.out.println("SPECS OF " + calleeMethodSym + " " + mpsym + " " + calleeSpecs);
//						paramActuals = mapParamActuals.get(mpsym);
						//System.out.println("PARAMACTUALS-A " + mpsym + " " + paramActuals);
                        currentEnv.arithmeticMode = calleeEnv.arithmeticMode = Arithmetic.Math.instance(context).defaultArithmeticMode(mpsym, true);

						for (JmlSpecificationCase cs : calleeSpecs.cases) {
						    if (!doSpecificationCase(methodDecl, calleeMethodSym, mpsym, cs)) continue;
							//if (!utils.jmlvisible(mpsym, classDecl.sym, mpsym.owner, cs.modifiers.flags, methodDecl.mods.flags)) continue;
							//if (translatingJML && cs.token == exceptionalBehaviorClause) continue;
							//if (mpsym != calleeMethodSym && cs.code) continue;
							JavaFileObject prev = log.useSource(cs.source());
							JCExpression pre = calleePreconditions.get(cs);
							if (pre == null) continue; // anonymous class without specs
							//System.out.println("CS-Q " + mpsym.owner + " " + mpsym + " " + pre);
							if (treeutils.isFalseLit(pre)) continue;
							var check8 = pushBlock();
							try {
								if (cs.block == null) { // FIXME - not quite sure of this guard // FIXME - what
																// should we check for field initializers
									// Handle assignable & accessible clauses
									ListBuffer<JCStatement> check2 = pushBlock(); // A block for assignable and
																					// accessible tests
									boolean anyCallableClauses = false;
									for (JmlMethodClause clause : cs.clauses) {
										JavaFileObject prevSource = log.useSource(clause.source());
										// We iterate over each storeref item in each assignable clause
										// of each specification case of the callee - for each item we check
										// that assigning to it (under the appropriate preconditions)
										// is allowed by each of the specification cases of the callee and caller specs.
										try {
											if (clause instanceof JmlMethodClauseStoreRef cst) {
                                                if (calleeIsPure && clause.clauseKind == assignableClauseKind) continue;
                                                if ((translatingJML || isHeapIndependent(calleeMethodSym)) && clause.clauseKind == accessibleClauseKind) continue;
												
												List<JCExpression> storerefs = cst.list ; // expandStoreRefList(cst.list, calleeMethodSym, false);
												//System.out.println("STOREREFS TO CHECK " + cst);
												for (JCExpression item : storerefs) {
												    String msg = "Is " + item + " " + clause.clauseKind + "? " + utils.locationString(item.pos, clause.source());
												    //System.out.println("CHECKING " + msg);
													addStat(comment(item, msg, clause.source()));
													//System.out.println("Is " + newThisId + "." + item + " " + clause.clauseKind + "? "
													//		+ utils.locationString(item.pos, clause.source()));
													JCExpression allowed = treeutils.trueLit;

													if (pre == null) {
														System.out.println("NO STORED PRECONDITION " + calleeMethodSym + " " + cs);
														pre = treeutils.trueLit;
													}
													try {
														//System.out.println("CURRENTTHIS " + currentEnv.currentReceiver + " " + newThisId);
														//System.out.println("PARAMACTUALS " + paramActuals);
														allowed = checkAccess2(clause.clauseKind, that, item, item, false, 
																treeutils.makeBooleanLiteral(item, true), false, calleeEnv, true);
														//System.out.println("ALLOWED " + allowed);
														//System.out.println("CHECKING " + calleeMethodSym + " " + isPure(calleeMethodSym) + " " + methodDecl.sym + " " + item + " " + that);
														checkAccess2(clause.clauseKind, that, item, item, false, allowed, true, null, false);
													} catch (Exception e) {
														e.printStackTrace(System.out);
													}
												}
											} else if (clause.clauseKind == CallableClauseExtension.callableClause) {
											    if (translatingJML) continue;
												// We have already checked, at the beginning of visitApply, that the callee is callable
												// Here we check that anything listed in the in callee's spec cases is callable
												anyCallableClauses = true;
												JmlMethodClauseCallable callableClause = (JmlMethodClauseCallable) clause;
												if (callableClause.keyword != null) {
													if (callableClause.keyword.kind == nothingKind) {
														// callee is callable \nothing - no problem
													} else if (callableClause.keyword.kind == everythingKind) {
														checkThatMethodIsCallable(callableClause.keyword, null);
													}
												} else {
													List<JmlMethodSig> sigs = callableClause.methodSignatures;
													if (sigs != null) {
														for (JmlMethodSig item : sigs) {
															addStat(comment(item, "Is " + item + " callable?",
																	clause.source()));
															checkThatMethodIsCallable(item, item.methodSymbol);
														}
													}
												}
											}
										} catch (NoModelMethod e) {
											// continue // FIXME - warn?
										} catch (JmlNotImplementedException e) {
											notImplemented(clause.keyword + " clause containing ", e); // FIXME - clause
																										// source
										} catch (Exception e) {
											System.out.println("Exception in frame clauses");
											e.printStackTrace(System.out);
											utils.unexpectedException(e,
													"Frame clauses for " + mpsym.owner + "." + mpsym);
										} finally {
											log.useSource(prevSource);
										}
									}
									if (cs.block == null) { // no defaults if there is a model program,
										if (!anyCallableClauses) {
											// The callee is implicitly callable \everything,
											// so the caller must be also be implicitly callable \everything
											checkThatMethodIsCallable(that, null);
										}
									}
									JCBlock bl = popBlock(cs, check2); // Ending the assignable tests block
									if (!bl.stats.isEmpty())
										addStat(M.at(cs).If(pre, bl, null));
								}
							} catch (Exception ee) {
								ee.printStackTrace(System.out);
								throw ee;
							} finally {
								JCBlock bl = popBlock(cs, check8);
								if (!onlyComments(bl.stats)) {
								    if (treeutils.isTrueLit(pre)) {
								        addStat(bl);
								    } else if (treeutils.isFalseLit(pre)) {
								        // do nothing
								    } else {
                                        addStat(M.at(cs.pos).If(pre, bl, null));
								    }
								}
								log.useSource(prev);
							}
						}
						//paramActuals_ = null;
					}
				}
				if (print) System.out.println("APPLYHELPER-S " + calleeMethodSym.owner + " " + calleeMethodSym);

				// Do any inlining
				VarSymbol savedSym = resultSym;
				JCExpression res = insertAllModelProgramInlines(that, null, calleePreconditions,
						calleeMethodSym, typeargs, meth, inliningCall, overridden);
				resultSym = savedSym;
				if (res != null && resultSym != null && resultSym.type.getTag() != TypeTag.VOID) {
					addAssumeEqual(that, Label.IMPLICIT_ASSUME, res, treeutils.makeIdent(that.pos, resultSym));
				}

			}
            currentEnv = currentEnv.popEnv(); // FIXME - in a finally block?


			if (print) System.out.println("APPLYHELPER-T " + calleeMethodSym.owner + " " + calleeMethodSym);
			ListBuffer<JCStatement> ensuresStatsOuter = new ListBuffer<JCStatement>();
			ListBuffer<JCStatement> exsuresStatsOuter = new ListBuffer<JCStatement>();

			// Now put in the actual method call
			// For esc, the resultSym is used in the postconditions; there is
			// no actual call of the method. Similarly for new object expressions.

			// FIXME - do need to state something about the allocation of the result of the
			// new object expression
			typevarMapping = newTypeVarMapping;

			if (rac) {
				ListBuffer<JCStatement> s = currentStatements;
				currentStatements = ensuresStatsOuter;
				if (apply != null)
					addStat(comment(apply, "converted method call", null));
				if (newclass != null)
					addStat(comment(newclass, "converted new-object call", null));

				JCStatement call;
				if (newclass != null) {
					addStat(treeutils.makeAssignStat(that.pos, resultExpr, trExpr));
					trExpr = resultExpr;
//                    currentEnv.currentReceiver = newThisExpr = resultId;
//                    addAssume(that,Label.IMPLICIT_ASSUME,
//                            treeutils.makeNeqObject(that.pos,resultId,treeutils.nullLit));
				} else if (isVoid) {
					call = M.at(that).Exec(trExpr);
					addStat(call);
				} else {
					call = treeutils.makeAssignStat(that.pos, resultExpr, trExpr);
					addStat(call);
				}
				currentStatements = s;
			}

			ensuresStatsOuter.add(comment(that, "Assuming callee normal postconditions for " + calleeMethodSym, null));
			exsuresStatsOuter
					.add(comment(that, "Assuming callee exceptional postconditions for " + calleeMethodSym, null));

			if (!rac && newclass == null && !calleeMethodSym.isConstructor() && resultSym != null
					&& resultType.getTag() != TypeTag.VOID) {
				final boolean heap = !calleeIsFunction
						&& !calleeMethodSym.owner.toString().startsWith("org.jmlspecs.lang");
				pushBlock();
			    {
					JmlMethodDecl mdecl = specs.getAttrSpecs(calleeMethodSym).cases.decl;
					int p = (mdecl != null) ? mdecl.pos : 0;
					Name newMethodName = newNameForCallee(p, calleeMethodSym, heap);
					ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
					if (!utils.isJMLStatic(calleeMethodSym)) newargs.add(newThisExpr);
					newargs.addAll(trArgs);
                    if (includeDeterminism) {
                        JCExpression sp = treeutils.trueLit;
                        if (!strictlyPure) {
                            sp = treeutils.makeNot(that.pos, makeFreshExpression(that, resultExpr, currentOldLabel));
                        }
                        JCIdent id = M.at(p).Ident(newMethodName);
                        id.sym = calleeMethodSym;
                        JCExpression newCall = M.at(p).Apply(List.<JCExpression>nil(), id, newargs.toList());
                        newCall.setType(that.type);
                        JCIdent resultId = M.at(p).Ident(resultSym);
                        JCExpression eq = treeutils.makeEquality(that.pos,  resultId,  newCall);
                        addAssume(that, Label.METHOD_ASSUME, treeutils.makeImpliesSimp(eq, sp, eq));
			        }
	                if (!calleeIsConstructor && (calleeIsPure||effectivelyPure) && !calleeIsFunction) {
	                    makeMethodHavocAxiom(that, receiverType, calleeMethodSym, that.type, that, readsLists, newargs.toList());
	                }
				}
				JCBlock bl = popBlock(that);
				if (!resultSym.type.isPrimitiveOrVoid() && !utils.isJavaOrJmlPrimitiveType(resultSym.type)) {
					JCExpression isNotFresh = treeutils.makeNot(that.pos, makeFreshExpression(that, resultExpr, currentOldLabel));
					pushBlock(ensuresStatsOuter);
					isNotFresh = newTempIfNeeded(isNotFresh);
					popBlock();
					JCStatement stat = M.at(that.pos).If(isNotFresh, bl, null);
					ensuresStatsOuter.add(stat);
				} else {
					ensuresStatsOuter.add(bl);
				}
			}
			if (print) System.out.println("APPLYHELPER-U " + calleeMethodSym.owner + " " + calleeMethodSym);

			if (!nodoTranslations) {

				if (exceptionSym != null && exceptionDeclCall != null) {
					exsuresStatsOuter
							.add(treeutils.makeAssignStat(that.pos, treeutils.makeIdent(that.pos, exceptionSym),
									treeutils.makeIdent(that.pos, exceptionDeclCall.sym)));
				}

				// TERMINATION
				// The termination symbol will be null if a method call is present in
				// class-level declaration
				// FIXME - not sure what precisely should be done - should we declare a
				// termination symbol in this case? RAC probably needs it.
				if (terminationSym != null) {
					JCIdent tid = treeutils.makeIdent(that.pos, terminationSym);
					JCStatement term = treeutils.makeAssignStat(that.pos, tid,
							treeutils.makeIntLiteral(that.pos, -that.pos));
					exsuresStatsOuter.add(term);
				}

				{
					// This states the allowed types of any exception according to the
					// Java declaration
					if (exceptionSym != null) { // FIXME - what situation has this symbol null?
						ListBuffer<JCStatement> s = currentStatements;
						currentStatements = exsuresStatsOuter;
						if (translatingJML && calleeIsPure) {
							addAssume(that, Label.IMPLICIT_ASSUME, treeutils.falseLit);
						} else {
							JCIdent exceptionId = treeutils.makeIdent(that.pos, exceptionSym);
							JCExpression expr = treeutils.makeThrownPredicate(that, exceptionId, calleeMethodSym);
							addAssume(that, Label.IMPLICIT_ASSUME, expr);
						}
						currentStatements = s;
					}
				}

			}

			if (esc && calleeIsPure) {
				addStat(comment(that, "... Not adding havoc statements for pure callee " + calleeMethodSym + " in "
						+ calleeMethodSym.owner.toString(), null));
			}
			if (print) System.out.println("APPLYHELPER-V " + calleeMethodSym.owner + " " + calleeMethodSym);
			boolean anyHavocs = false;
			if (esc && !calleeIsPure && !(convertedReceiver instanceof JCLambda)) {
				// Now we iterate over all specification cases in all parent
				// methods again, this time putting in the assignable havoc statements
				// These havocs need to be after we do all the checking of assignability
				// but before we do the actual postcondition assertions

				// FIXME - what about interaction of assignables with model programs or inlined
				// content?

				ListBuffer<JCStatement> havocBlockCheck = pushBlock();
				addStat(comment(that,
						"... Adding havoc statements for the call of " + calleeMethodSym.owner + "." + calleeMethodSym,
						null));
//                ListBuffer<JCStatement> havocs = new ListBuffer<>();
				currentEnv = currentEnv.pushEnvCopy();
				for (Pair<MethodSymbol, Type> pair : overridden) {
					MethodSymbol mpsym = pair.first;
					if (print)
						System.out.println("APPLYHELPER-V1 " + calleeMethodSym + " " + mpsym);
					Type classType = pair.second;
					typevarMapping = typemapping(classType, null, null, null);
					if (apply != null)
						typevarMapping = typemapping(apply, typevarMapping);
					addStat(comment(that,
							"... Adding havoc statements for the call of " + calleeMethodSym + " from " + classType,
							null));

					// This initial logic must match that above for preconditions/"RET
					JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
					if (calleeSpecs == null) continue; // FIXME - not sure about this
					currentEnv.arithmeticMode = Arithmetic.Math.instance(context).defaultArithmeticMode(mpsym, true);

//					paramActuals = mapParamActuals.get(mpsym);

					boolean isPure = isPure(mpsym);
					// FIXME - we should set condition
					calleeEnv.arithmeticMode = Arithmetic.Math.instance(context).defaultArithmeticMode(mpsym, true);
					for (JmlSpecificationCase cs : calleeSpecs.cases) {
						if (print)
							System.out.println("APPLYHELPER-V2 " + mpsym + " " + cs);
						if (!doSpecificationCase(methodDecl, calleeMethodSym, mpsym, cs)) continue;
						//if (translatingJML && cs.token == exceptionalBehaviorClause) continue;

						JCExpression precond = calleePreconditions.get(cs); // Can be null for constructors of anonymous
																			// classes
						JCExpression pre = precond != null ? copy(precond) : treeutils.trueLit;
						if (treeutils.isFalseLit(pre)) continue;
						addStat(comment(that, "... Adding havoc statements: spec case: " + cs, null));
						JavaFileObject prev = log.useSource(cs.source());
						var check9 = pushBlock();
						//var savedOldEnv = evalStateLabel;
						currentEnv = currentEnv.pushEnvCopy();
						try {
						    currentEnv.stateLabel = calleeEnv.stateLabel;
							if (pre == treeutils.falseLit)
								continue; // Don't bother with checks if corresponding precondition is explicitly false
							condition = pre; // FIXME - is this right? what about the havoc statement?

							boolean useDefault = true;
							for (JmlMethodClause clause : cs.clauses) {
								if (print) System.out.println("APPLYHELPER-V3 " + mpsym + " " + clause);
								try {
									IJmlClauseKind token = clause.clauseKind;
									if (token == assignableClauseKind) {
										// Don't translate assignable if we are in a pure method or constructor
										if (!translatingJML) {
                                            //System.out.println("CALL " + methodDecl.sym.owner + "." + methodDecl.sym + " " + calleeMethodSym.owner + "." + calleeMethodSym);
											//System.out.println(" ASSIGNABLE CLAUSE " + classType + " " + mpsym.owner + " " + clause);
											useDefault = false;
											addStat(comment(null, "Assignable clause: " + clause, null));
//                                        ListBuffer<JCStatement> elses = new ListBuffer<>();
											List<JCExpression> storerefs = expandStoreRefWithMaps(
													((JmlMethodClauseStoreRef) clause).list, 
													currentEnv.currentReceiver != null ? currentEnv.currentReceiver.type : calleeMethodSym.owner.type);
											//System.out.println(" EXPANDED LIST " + storerefs);
											ListBuffer<JCStatement> check4 = null;
											Symbol tsym = newThisId == null ? calleeMethodSym.owner : newThisId.type.tsym;
											while (tsym instanceof TypeVariableSymbol tv) tsym = ((Type.TypeVar)tv.type).getUpperBound().tsym;
											//System.out.println("   WAS " + ((JmlMethodClauseStoreRef) clause).list);
											//System.out.println("   NOW " + storerefs);
											JmlStoreRef lsexpr = (JmlStoreRef)convertAssignableToLocsetExpression(clause, storerefs, (ClassSymbol)tsym, null);
											for (var i: ((JmlMethodInvocation)lsexpr.expression).args) {
											  if (i instanceof JmlStoreRef item) {
												boolean containsEverything = false;

												ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
												var prex = checkAccess2(clause.clauseKind, that, item, item, false, 
															treeutils.makeBooleanLiteral(item, true), false, calleeEnv, true);
												//prex = convertJML(prex, calleeEnv);
												addStat(comment(item, ".......... Havocing " + item + " " + prex, null));
												if (item.field != null) {
													boolean isStatic = utils.isJMLStatic(item.field);
													if (!isStatic) {
														JCIdent recXout = newTemp(item, item.receiver.type);
														check4 = pushBlock();
														addAssume(item, Label.IMPLICIT_ASSUME, treeutils.makeEquality(item.pos, recXout, convertJML(item.receiver,calleeEnv)));
														JCFieldAccess newloc = treeutils.makeSelect(item.pos, recXout, item.field);
														newlist.add(newloc);
													} else {
														check4 = pushBlock();
														JCFieldAccess newloc = treeutils.makeSelect(item.pos, treeutils.makeType(item.pos,item.field.owner.type), item.field);
														newlist.add(newloc);
													}
												} else if (item.range != null && item.range.lo == item.range.hi && item.range.lo != null) {
													Type elemtype = jmltypes.elemtype(item.receiver.type);
													JCIdent arrayXout = newTemp(item, item.receiver.type);
													JCIdent loXout = newTemp(item, jmltypes.BIGINT);
													check4 = pushBlock();
													addAssume(item, Label.IMPLICIT_ASSUME, treeutils.makeEquality(item.pos, arrayXout, convertJML(item.receiver, calleeEnv)));
													addAssume(item, Label.IMPLICIT_ASSUME, treeutils.makeEquality(item.pos, loXout, convertJML(item.range.lo, calleeEnv)));

													JmlBBArrayAccess newloc = new JmlBBArrayAccess(null, arrayXout, loXout); // FIXME - switch to factory
													newloc.pos = item.pos;
													newloc.setType(elemtype);
													newloc.arraysId = null;
													newlist.add(newloc);
												} else if (item.range != null ) {
													// An array range: [ i .. j] [i .. ] [*]
													Type elemtype = jmltypes.elemtype(item.receiver.type);
													JCIdent arrayXout = newTemp(item, item.receiver.type);
													JCIdent loXout = newTemp(item, jmltypes.BIGINT);
													JCIdent hiXout = newTemp(item, jmltypes.BIGINT);
													check4 = pushBlock();
													addAssume(item, Label.IMPLICIT_ASSUME, treeutils.makeEquality(item.pos, arrayXout, convertJML(item.receiver, calleeEnv)));
													if (item.range.lo != null)
														addAssume(item, Label.IMPLICIT_ASSUME,
																treeutils.makeEquality(item.pos, loXout, convertJML(item.range.lo, calleeEnv)));
													if (item.range.hi != null)
														addAssume(item, Label.IMPLICIT_ASSUME,
																treeutils.makeEquality(item.pos, hiXout, convertJML(item.range.hi, calleeEnv)));

													JCExpression range = M.at(item.pos).JmlRange(loXout, hiXout); 
													range.type = JMLPrimitiveTypes.rangeTypeKind.getType(context);
															
													JCExpression newloc = M.at(item.pos).Indexed(arrayXout, range);
													//JmlBBArrayRange newloc = new JmlBBArrayAccess(null, arrayXout, loXout); // FIXME - switch to factory
													newloc.pos = item.pos;
													newloc.setType(elemtype);
													newlist.add(newloc);
													//System.out.println("HAVOCRANGE " + newloc + " " + newlist);
												} else if (item.local != null) {
													newlist.add(M.at(item.pos).Ident(item.local));
												} else if (item.isEverything) {
													containsEverything = true;
													check4 = pushBlock();
													newlist.add(M.at(item.pos).JmlSingleton(everythingKind));
												} else  {
													check4 = pushBlock();
													log.error(item.pos, "jml.message", "Unknown item for havoc: " + item);
												}
												// addAssume(location,Label.IMPLICIT_ASSUME,
												// treeutils.makeEquality(location.pos, preXout, prex));
												if (esc) {
													JCStatement havoc = M.at(clause.pos).JmlHavocStatement(newlist.toList());
													addStat(havoc);
													if (containsEverything) {
														addNullnessAndTypeConditionsForInheritedFields(classDecl.sym,
																false, currentEnv.currentReceiver == null);
													}
//													for (JCExpression hv : newlist) {
//														if (hv instanceof JCFieldAccess) {
//															var fa = (JCFieldAccess) hv;
//															havocModelFields(fa);
//														}
//													}
												}
												JCBlock bl = popBlock(cs, check4);
												//System.out.println("HAVOCBLOCK " + prex + " " + bl);
												if (!bl.stats.isEmpty()) {
													JCStatement st = M.at(cs.pos + 1).If(prex, bl, null);
													if (rac)
														st = wrapRuntimeException(cs, st,
																"JML undefined precondition while checking postconditions - exception thrown",
																null); // FIXME - this needs to be checked
													addStat(st);
													anyHavocs = true;
												}

												// addToStats(elses, () -> {
//                                                addAssume(location,Label.IMPLICIT_ASSUME, treeutils.makeEquality(location.pos, preXout, treeutils.falseLit));
//                                            });
//                                            JCBlock bl = popBlock(cs,check4);
//                                            JCStatement st = M.at(cs.pos+1).If(pre,bl,M.Block(0L,elses.toList()));
//                                            currentStatements.add( wrapRuntimeException(cs, st, "JML undefined precondition while checking postconditions - exception thrown", null));
//                                            ListBuffer<JCStatement> checkbl = pushBlock();
//                                            JCStatement havoc = M.at(clause.pos).JmlHavocStatement(newlist.toList());
//                                            addStat(havoc);
//                                            if (containsEverything) {
//                                            	addNullnessAndTypeConditionsForInheritedFields(classDecl.sym, false, currentEnv.currentReceiver == null);
//                                            }
//                                            for (JCExpression hv: newlist) {
//                                                if (hv instanceof JCFieldAccess) havocModelFields((JCFieldAccess)hv);
//                                            }
//                                            bl = popBlock(cs,checkbl);
//                                            if (!bl.stats.isEmpty()) {
//                                                st = M.at(cs.pos+1).If(preXout,bl,null);
//                                                havocs.add(st);
//                                                anyHavocs = true;
//                                            }
											  }
											}
										}
									} else {
										// skip everything else
									}
								} catch (JmlNotImplementedException e) {
									notImplemented(clause.keyword + " clause containing ", e, clause.source());
								}
							}
							if (useDefault && !translatingJML && cs.token != modelprogramClause && cs.block == null
									&& !inliningCall) {
								utils.warning(cs, "jml.internal",
										"Unexpected absence of an assignable clause after desugaring: " + mpsym.owner
												+ " " + mpsym.toString());
							}
						} catch (Exception e) {
							System.out.println("UNEXPECTED EXCEPTION " + e);
							e.printStackTrace(System.out);
						} finally {
							//evalStateLabel = savedOldEnv;
						    currentEnv = currentEnv.popEnv();
							JCBlock bl = popBlock(cs, check9);
							if (numCases == 1 && !rac)
								addStat(bl);
							else
								addStat(M.at(cs.pos).If(pre, bl, null));
							log.useSource(prev);
						}

						// FIXME - is that the right statement list?
					}
//					paramActuals = null;
				}
//                currentStatements.addAll(havocs);
				addStat(popBlock(that, havocBlockCheck));
				currentEnv = currentEnv.popEnv();  // FIXME - put in finally block?
			}
			typevarMapping = newTypeVarMapping;
            if (!rac && newclass != null && inProcessInvariants.isEmpty() && !translatingJML) {
                    changeState(that, assignsLists, calllabel);
            }
            if (!rac && !calleeIsPure && !effectivelyPure && !calleeMethodSym.isConstructor()) {
                if (anyHavocs && inProcessInvariants.isEmpty() && !translatingJML)
                    changeState(that, assignsLists, calllabel);
            }

			if (print) System.out.println("APPLYHELPER-W " + calleeMethodSym.owner + " " + calleeMethodSym);

			String msg = utils.qualifiedMethodSig(calleeMethodSym) + ", returning to "
					+ utils.qualifiedMethodSig(methodDecl.sym);
			ListBuffer<JCStatement> check5 = pushBlock();
			if (!nodoTranslations && !(convertedReceiver instanceof JCLambda)) {

				currentStatements
						.add(comment(that,
								"Assuming callee invariants by the caller " + utils.qualifiedMethodSig(methodDecl.sym)
										+ " after exiting the callee " + utils.qualifiedMethodSig(calleeMethodSym),
								null));
				if (!rac && !infer) {
					// After a call, we assume invariants, which includes assuming that
					// non-null fields are null. However, we do not do make these assumptions if
					// (a) the callee is helper or (b) the caller and callee are the same object
					// and the caller is a constructor
					// (They are just assumptions, so they are not enabled for rac or inference)
					if (!isHelper(calleeMethodSym)) {
						addNonNullChecks(true, that, calleeClass.type, newThisExpr, calleeMethodSym.isConstructor());
					}
				}

				if (esc && !methodDecl.sym.isConstructor()) {
					JCExpression saved2 = currentEnv.currentReceiver;
					currentEnv.currentReceiver = newThisExpr;
					int savedCount = freshnessReferenceCount;
					try {
						if (calleeIsPure) { // Seems sensible, but causes failures in current work
							currentStatements.add(comment(classDecl,
									"Not assuming invariants for caller fields after exiting the pure callee "
											+ utils.qualifiedMethodSig(calleeMethodSym),
									null));
						} else {
							currentStatements.add(
									comment(classDecl, "Assuming invariants for caller fields after exiting the callee "
											+ utils.qualifiedMethodSig(calleeMethodSym), null));
							freshnessReferenceCount = preAllocCounter;
							assumeFieldInvariants((ClassSymbol) calleeMethodSym.owner,
									utils.isJMLStatic(calleeMethodSym), true); // FIXME - do parent classes also?
						}
					} finally {
						currentEnv.currentReceiver = saved2;
						freshnessReferenceCount = savedCount;
					}
				}
	            if (print) System.out.println("APPLYHELPER-WA " + calleeMethodSym.owner + " " + calleeMethodSym);

				boolean isObjectConstructor = calleeMethodSym.isConstructor() && calleeMethodSym.owner == syms.objectType.tsym && calleeMethodSym.params.size() == 0;
				
				if (!isHelper(calleeMethodSym) && !isObjectConstructor) {
					addInvariants(that, calleeClass.type, newThisExpr, currentStatements, false,
							calleeMethodSym.isConstructor(), false, isHelper(calleeMethodSym), true, true,
							Label.INVARIANT_EXIT, msg);
				}
                if (print) System.out.println("APPLYHELPER-WB " + calleeMethodSym.owner + " " + calleeMethodSym);
				addConstraintInitiallyChecks(that, calleeClass, newThisExpr, currentStatements, false,
						calleeMethodSym.isConstructor(), false, isHelper(calleeMethodSym), true, true, null, msg);
                if (print) System.out.println("APPLYHELPER-WC " + calleeMethodSym.owner + " " + calleeMethodSym);

				if (!isHelper(calleeMethodSym) && !isObjectConstructor)
					for (JCExpression arg : trArgs) {
						if (utils.isJavaOrJmlPrimitiveType(arg.type))
							continue;
						currentStatements
								.add(comment(arg, "Assuming invariants for callee parameter after exiting the callee "
										+ utils.qualifiedMethodSig(calleeMethodSym), null));
						if (!(arg instanceof JCIdent))
							continue; // FIXME - do better? - see testbigint
						JCIdent id = (JCIdent) arg;
						addInvariants(id, arg.type, id, currentStatements, false, false, false, false, true, true,
								Label.INVARIANT_EXIT, msg);
					}

			}
			if (!(convertedReceiver instanceof JCLambda)) {
				Type retType = that.type;
				currentStatements.add(comment(that,
						"Checking for return callee invariants by the caller "
								+ utils.qualifiedMethodSig(methodDecl.sym) + " after exiting the callee "
								+ utils.qualifiedMethodSig(calleeMethodSym),
						null));

				if (calleeMethodSym.isConstructor()) {
					if (resultExpr != null) {
						currentStatements.add(comment(that,
								"Assuming invariants for the constructed value by the caller after exiting the callee "
										+ utils.qualifiedMethodSig(calleeMethodSym),
								null));
						addInvariants(that, retType, resultExpr, currentStatements, false, false, false, false, true,
								true, true, Label.INVARIANT_EXIT, msg);
					}
				} else if (retType.getTag() != TypeTag.VOID) {
					// Add invariants on the type of the return value only if normal termination
					ListBuffer<JCStatement> check6 = pushBlock();
					if (esc && !utils.isJavaOrJmlPrimitiveType(retType)) {
						boolean nnull = specs.isCheckNonNullReturn(retType, calleeMethodSym);
						//System.out.println("RET TYPE " + calleeMethodSym + " " + calleeMethodSym.type
						//+ " " + calleeMethodSym.getReturnType() + " " + retType + " " + nnull);
						addStat(comment(that, "Return is " + (nnull?"non-null":"nullable") + ": " + calleeMethodSym, null));
						if (nnull) {
							addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeNotNull(that, resultExpr));
						}
						JCExpression nn = treeutils.makeEqNull(that.pos, resultExpr);
						nn = treeutils.makeOr(that.pos, nn, isAllocated(that, resultExpr));
						addAssume(that, Label.IMPLICIT_ASSUME, nn);

						addAssume(that, Label.IMPLICIT_ASSUME, allocCounterLE(that.pos(), resultExpr, allocCounter));

						nn = treeutils.makeDynamicTypeInEquality(that, resultExpr, retType);
						addAssume(that, Label.IMPLICIT_ASSUME, nn);
					}

					currentStatements.add(comment(that,
							"Assuming invariants for the return value by the caller after exiting the callee "
									+ utils.qualifiedMethodSig(calleeMethodSym),
							null));
					boolean savedAPM = assumingPureMethod;
					assumingPureMethod = true;
					addInvariants(that, retType, resultExpr, currentStatements, false, false, false, false, true, true,
							true, Label.INVARIANT_EXIT, msg);
					assumingPureMethod = savedAPM;
					JCBlock bl = popBlock(that, check6);
					if (exceptionSym == null) {
						currentStatements.add(bl);
					} else {
						JCIdent exceptionId = treeutils.makeIdent(that.pos, exceptionSym);
						JCExpression e = newTempIfNeeded(treeutils.makeEqObject(that.pos, exceptionId, treeutils.nullLit));
						JCStatement ifstat = M.at(that.pos).If(e, bl, null);
						currentStatements.add(ifstat);
					}
				}

				// Now assume that the callee has maintained all the caller invariants
				// both explicit invariants and invariants of the classes of the parameters

				if (!isSuperCall && !isThisCall
						&& (!isHelper(calleeMethodSym) || methodDecl.sym.owner != calleeMethodSym.owner)) {
					if (!calleeIsPure || calleeMethodSym.isConstructor()) {
						currentStatements.add(comment(that,
								"Assuming caller invariants upon reentering the caller "
										+ utils.qualifiedMethodSig(methodDecl.sym) + " after exiting the callee "
										+ utils.qualifiedMethodSig(calleeMethodSym),
								null));
						var invariantsNeededByCallee = invariantsNeeded(newThisExpr, calleeMethodSym);
						for (var r : invariantsNeededByCallee.first) {
							if (r != newThisExpr || !calleeMethodSym.isConstructor())
								addInvariants(that, r.type, r, currentStatements, true, methodDecl.sym.isConstructor(),
										isSuperCall, isHelper(methodDecl.sym), false, true,
										Label.INVARIANT_REENTER_CALLER,
										"(Caller: " + utils.qualifiedMethodSig(methodDecl.sym) + ", Callee: "
												+ utils.qualifiedMethodSig(calleeMethodSym) + ")");
						}
						for (var r : invariantsNeededByCallee.second) {
							addInvariants(that, r.type, null, currentStatements, true, methodDecl.sym.isConstructor(),
									isSuperCall, isHelper(methodDecl.sym), false, true, Label.INVARIANT_REENTER_CALLER,
									"(Caller: " + utils.qualifiedMethodSig(methodDecl.sym) + ", Callee: "
											+ utils.qualifiedMethodSig(calleeMethodSym) + ")");
						}
//                    addInvariants(that,savedEnclosingClass.type,
//                            utils.isJMLStatic(methodDecl.sym)  ? null : savedThisExpr,
//                            currentStatements,
//                            true,
//                            methodDecl.sym.isConstructor(),
//                            isSuperCall,
//                            isHelper(methodDecl.sym),false,true,Label.INVARIANT_REENTER_CALLER, 
//                            "(Caller: " + utils.qualifiedMethodSig(methodDecl.sym) + ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");
//                    addInvariants(that,savedEnclosingClass.type,
//                            savedEnclosingMethod == null || utils.isJMLStatic(savedEnclosingMethod)  ? null : savedThisExpr,
//                            currentStatements,
//                            true,savedEnclosingMethod != null && savedEnclosingMethod.isConstructor(),isSuperCall,isHelper(methodDecl.sym),false,true,Label.INVARIANT_REENTER_CALLER, "(Caller: " + utils.qualifiedMethodSig(methodDecl.sym) + ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");

						// Note that methodDecl.params will be null for initializer blocks
						if (methodDecl.params != null)
							for (JCVariableDecl v : methodDecl.params) {
								if (utils.isJavaOrJmlPrimitiveType(v.type))
									continue;
								// FIXME - it is an open question which invariants to check here - in principle
								// all invariants must hold - but which might not? - need the pack/unpack
								// capability
								// FIXME - for now we check the invariants of the parameters in the prestate
								// JCIdent d = preparams.get(v.sym);
								JCIdent id = treeutils.makeIdent(v.pos, v.sym);
								JCExpression oldid = treeutils.makeOld(v.pos(), id,
										labelPropertiesStore.get(attr.preLabel));
								if (rac)
									oldid = convertExpr(oldid);
								JCExpression recv = utils.isJMLStatic(methodDecl.sym) ? null : savedThisExpr;
								currentStatements.add(comment(that, "Assuming invariants for caller parameter " + id
										+ " upon reentering the caller " + utils.qualifiedMethodSig(methodDecl.sym)
										+ " after exiting the callee " + utils.qualifiedMethodSig(calleeMethodSym),
										null));
								addInvariants(v, v.type, oldid, currentStatements, false, false, false, false, false,
										true, Label.INVARIANT_REENTER_CALLER,
										"(Parameter: " + v.sym + ", Caller: " + utils.qualifiedMethodSig(methodDecl.sym)
												+ ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");
							}
					} else {
						currentStatements.add(comment(that,
								"Not assuming caller and parameter invariants upon reentering the caller because callee is pure: "
										+ utils.qualifiedMethodSig(methodDecl.sym) + " after exiting the callee "
										+ utils.qualifiedMethodSig(calleeMethodSym),
								null));
					}
				}

				if (isSuperCall) {
					currentStatements.add(comment(that,
							"Assuming field invariants after super call: " + utils.qualifiedMethodSig(methodDecl.sym)
									+ " after exiting the callee " + utils.qualifiedMethodSig(calleeMethodSym),
							null));
					for (Type parentType : parents(calleeMethodSym.owner.type, false)) {
						Scope s = parentType.tsym.members();
						for (Symbol sym : s.getSymbols()) {
							if (!(sym instanceof VarSymbol))
								continue;
							if (utils.isJavaOrJmlPrimitiveType(sym.type) || jmltypes.isOnlyDataGroup(sym.type))
								continue; // FIXME should be isJMLPrimitivie?
							DiagnosticPosition pos = that; // FIXME - is this a good position?
							JCExpression expr = treeutils.makeSelect(pos.getPreferredPosition(), currentEnv.currentReceiver, sym);
							addInvariants(pos, sym.type, expr, currentStatements, false, false, true, false, true, true,
									Label.INVARIANT_REENTER_CALLER,
									"(Field: " + sym + ", Caller: " + utils.qualifiedMethodSig(methodDecl.sym)
											+ ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");
						}
					}
				}

			}
			// FIXME - could optimize if the block is empty except comments
			JCBlock invariantBlock = popBlock(methodDecl, check5);
			// FIXME - why are these put in different statement lists?
			if (esc)
				currentStatements.add(wrapRuntimeException(that, invariantBlock,
						"JML undefined invariant while checking postconditions - exception thrown", null));
			if (rac)
				ensuresStatsOuter.add(wrapRuntimeException(that, invariantBlock,
						"JML undefined invariant while checking postconditions - exception thrown", null));
			
			if (print) System.out.println("APPLYHELPER-X " + calleeMethodSym.owner + " " + calleeMethodSym);

			this.freshnessReferenceCount = callLabelReferenceCount;
			boolean hasModelProgramBlocks = false;
			try {
				if (esc && resultExpr != null && !utils.isJavaOrJmlPrimitiveType(resultExpr.type)) {
					JCExpression nn = treeutils.makeEqNull(resultExpr.pos, copy(resultExpr));
					JCExpression ty = treeutils.makeTypeof(copy(resultExpr));
					JCExpression typ = treeutils.makeTypelc(treeutils.makeType(resultExpr.pos, resultExpr.type));
					JCExpression inst = treeutils.makeSubtype(ty, ty, typ);
					ListBuffer<JCStatement> s = currentStatements;
					currentStatements = ensuresStatsOuter;
					addAssume(resultExpr, Label.IMPLICIT_ASSUME, treeutils.makeOr(resultExpr.pos, nn, inst));
					currentStatements = s;
				}
				if (print) System.out.println("APPLYHELPER-X1 " + calleeMethodSym.owner + " " + calleeMethodSym);
				// Now we iterate over all specification cases in all parent
				// methods again, this time putting in the post-condition checks

				for (Pair<MethodSymbol, Type> pair : overridden) {
					if (print) System.out.println("APPLYHELPER-X2");
					MethodSymbol mpsym = pair.first;
					Type classType = pair.second;
					typevarMapping = typemapping(classType, calleeMethodSym, typeargs, meth == null ? null
							: meth.type instanceof Type.MethodType ? (Type.MethodType) meth.type : null, null);
					if (apply != null)
						typevarMapping = typemapping(apply, typevarMapping);

					// This initial logic must match that above for preconditions
					JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
					if (calleeSpecs == null)
						continue; // FIXME - not sure about this

					ensuresStatsOuter.add(comment(methodDecl,
							"Assuming postconditions for " + utils.qualifiedMethodSig(mpsym), null));
					exsuresStatsOuter.add(comment(methodDecl,
							"Assuming exceptional postconditions for " + utils.qualifiedMethodSig(mpsym), null));

					if (apply != null && calleeMethodSym.getReturnType() != null
							&& !utils.isJavaOrJmlPrimitiveOrVoidType(calleeMethodSym.getReturnType())
							&& resultExpr != null && meth != null && 
							(specs.isNonNullReturn(calleeMethodSym) || specs.isNonNull(that.type))) {
						JCExpression nn = treeutils.makeNotNull(that.pos, resultExpr);
						var p = (mspecs != null && mspecs.specDecl != null) ? mspecs.specDecl.pos() : that.pos(); // FIXME - sort out cases
																								// where specDecl is
																								// null -- implicit
																								// methods like
																								// Enum.values()?
						var psource = (mspecs != null && mspecs.specDecl != null) ? mspecs.specDecl.sourcefile : null;
						currentStatements = ensuresStatsOuter;
						addStat(comment(meth, "Assuming non-null return value in " + methodDecl.sym
								+ " on return from callee " + calleeMethodSym, null));
						addAssume(meth, Label.POSSIBLY_NULL_RETURN, nn, p, psource,
								calleeMethodSym + ", checked in caller " + methodDecl.sym);
					}

//					paramActuals = mapParamActuals.get(mpsym);

					// FIXME - we should set condition
					// Be sure to do assignable (havoc) clauses, then invariants, and then
					// postcondition clauses
					for (JmlSpecificationCase cs : calleeSpecs.cases) {
						if (print) System.out.println("APPLYHELPER-X3");
						if (cs.block != null)
							hasModelProgramBlocks = true;
                        if (!doSpecificationCase(methodDecl, calleeMethodSym, mpsym, cs)) continue; 
//						if (!utils.jmlvisible(mpsym, classDecl.sym, mpsym.owner, cs.modifiers.flags,
//								methodDecl.mods.flags))
//							continue;
//						if (translatingJML && cs.token == exceptionalBehaviorClause)
//							continue;
//						if (mpsym != calleeMethodSym && cs.code)
//							continue;
						// System.out.println("GET CALLEE PRE " + mpsym.owner + " " + mpsym + " " +
						// classType + " " + cs.hashCode() + " " + calleePreconditions.get(cs) + " " +
						// cs);
						JCExpression pre = copy(calleePreconditions.get(cs));
						if (pre == null)
							continue; // anonymous class
						if (treeutils.isFalseLit(pre))
							continue; // Don't bother with postconditions if corresponding precondition is explicitly
										// false
						condition = pre; // FIXME - is this right? what about the havoc statement?
						ListBuffer<JCStatement> ensuresStats = new ListBuffer<JCStatement>();
						ListBuffer<JCStatement> exsuresStats = new ListBuffer<JCStatement>();
						ensuresStats.add(comment(cs, "CASE " + cs, cs.sourcefile));
						exsuresStats.add(comment(cs, "CASE " + cs, cs.sourcefile));

						currentStatements = ensuresStats;
						for (JmlMethodClause clause : cs.clauses) {
							JavaFileObject clauseSource = clause.sourcefile == null ? log.currentSourceFile()
									: clause.sourcefile;
							JavaFileObject prevSource = null;
							try {
								IJmlClauseKind ct = clause.clauseKind;
								if (ct == MethodExprClauseExtensions.ensuresClauseKind) {
									currentStatements = ensuresStats;
									LinkedList<ListBuffer<JCStatement>> temp = markBlock();
									ListBuffer<JCStatement> check7 = pushBlock();
									try {
										addStat(comment(clause));
										boolean savedAssuming = assumingPureMethod;
										try {
											prevSource = log.useSource(clauseSource);
											assumingPureMethod = true;
											conditionAssociatedClause = clause;
											log.useSource(clause.sourcefile);
											JCExpression e = convertJML(((JmlMethodClauseExpr) clause).expression,
													condition, false);
											log.useSource(prevSource);
											addAssume(that, Label.POSTCONDITION, e, clause, clauseSource);
										} catch (NoModelMethod e) { // FIXME - need this elsewhere as well, e.g.,
																	// signals
											// continue
											// } catch (Exception e) {
											// System.out.println(e);
										} finally {
											if (prevSource != null)
												log.useSource(prevSource);
											assumingPureMethod = savedAssuming;
											conditionAssociatedClause = null;
										}
										JCBlock bl = popBlock(that, check7);
										addStat(wrapRuntimeException(clause, bl, // wrapRuntimeException is a no-op
																					// except for rac
												"JML undefined postcondition - exception thrown", null));
									} catch (JmlNotImplementedException e) {
										popBlock(that, check7);
										notImplemented(clause.keyword + " clause containing ", e, clause.source());
									}
									if (!checkBlock(temp))
										Utils.print("BLOCKS DO NOT MATCH");
								}
							} catch (NoModelMethod e) {
								// FIXME - need to catch to skip the clause
							} catch (JmlNotImplementedException e) {
								// FIXME - should not need this anymore
								notImplemented(clause.keyword + " clause containing ", e, clause.source());
							}
						}

						if (print) System.out.println("APPLYHELPER-X4");
						currentStatements = exsuresStats;
						for (JmlMethodClause clause : cs.clauses) {
							if (print) System.out.println("APPLYHELPER-X4A " + clause);
							JavaFileObject clauseSource = clause.sourcefile == null ? log.currentSourceFile()
									: clause.sourcefile;
							JavaFileObject prevSource = null;
							try {
								IJmlClauseKind ct = clause.clauseKind;
								if (print) System.out.println("APPLYHELPER-X4B " + clause);
								if (ct == SignalsClauseExtension.signalsClauseKind) {
									// FIXME - review this
									ListBuffer<JCStatement> check8 = pushBlock();
									try {
										addStat(comment(clause));

										JCExpression ex = ((JmlMethodClauseSignals) clause).expression;
										if (ex instanceof JmlSingleton)
											ex = treeutils.trueLit;
										JCVariableDecl vdo = ((JmlMethodClauseSignals) clause).vardef;
										Type vdtype = syms.exceptionType;
										if (vdo != null && vdo.name != null && !treeutils.isFalseLit(ex)
												&& exceptionDeclCall != null) {
											JCIdent exceptionId = treeutils.makeIdent(clause.pos,
													exceptionDeclCall.sym);
											JCExpression tc = M.at(vdo).TypeCast(vdo.type, exceptionId);
											JCVariableDecl vd = treeutils.makeVarDef(vdo.type, vdo.name, vdo.sym.owner,
													esc ? exceptionId : tc);
											vdtype = vd.type;
											addStat(vd);
											paramActuals_.put(vdo.sym, treeutils.makeIdent(vd.pos, vd.sym));
										}
										// FIXME - we should have a condition that the exception is an Exception (not a
										// Throwable)
										prevSource = log.useSource(clauseSource);
										conditionAssociatedClause = clause;
										JCExpression e = convertJML(ex, condition, false);
										log.useSource(prevSource);
										addAssume(that, Label.SIGNALS, e, clause, clauseSource);
										ex = treeutils.trueLit;
										if (vdo != null && !treeutils.isFalseLit(e) && exceptionDeclCall != null) {
											ex = M.at(clause)
													.TypeTest(treeutils.makeIdent(clause.pos, exceptionDeclCall.sym),
															treeutils.makeType(clause.pos, vdtype))
													.setType(syms.booleanType);
											paramActuals_.remove(vdo.sym);
										}
										JCBlock bl = popBlock(that, check8);
										JCStatement st = M.at(clause).If(newTempIfNeeded(ex), bl, null);

										addStat(wrapRuntimeException(clause,
												M.at(clause).Block(0, List.<JCStatement>of(st)),
												"JML undefined exceptional postcondition - exception thrown", null));
									} catch (JmlNotImplementedException e) {
										popBlock(that, check8);
										notImplemented(clause.keyword + " clause containing ", e, clause.source());
									} finally {
										if (prevSource != null)
											log.useSource(prevSource);
										conditionAssociatedClause = null;
									}
								} else if (ct == SignalsOnlyClauseExtension.signalsOnlyClauseKind) {
									if (print) System.out.println("APPLYHELPER-X4BA " + clause);
									if (exceptionDeclCall != null && exceptionSym != null) { // FIXME - why might
																								// exceptionSym be null?
																								// halndling field
																								// initializer?

										JCIdent exceptionId = treeutils.makeIdent(clause.pos, exceptionSym);
										JCExpression condd = treeutils.falseLit;
										for (JCExpression t : ((JmlMethodClauseSignalsOnly) clause).list) {
											JCExpression tc = M.at(t).TypeTest(exceptionId, t)
													.setType(syms.booleanType);
											condd = treeutils.makeOr(clause.pos, condd, tc);
										}
										JCExpression extype = treeutils.makeType(clause.pos, syms.exceptionType);
										JCExpression isExcType = M.at(clause.pos).TypeTest(exceptionId, extype)
												.setType(syms.booleanType);
										condd = treeutils.makeOr(clause.pos, treeutils.makeNot(clause.pos, isExcType),
												condd);
										if (print)
											System.out.println("APPLYHELPER-X4BP " + clause);
										addAssume(that, Label.SIGNALS_ONLY, condd, clause, clause.source(), null,
												!rac ? null
														: treeutils.makeUtilsMethodCall(clause.pos, "getClassName",
																exceptionId));
										if (print) System.out.println("APPLYHELPER-X4BQ " + clause);
									} else {
										// FIXME - I think this should never happen
										// FIXME - shouldn'tx we include runtimeException
										JCExpression exx = treeutils.makeDuplicateLiteral(clause.pos,
												treeutils.falseLit);
										addAssume(that, Label.SIGNALS_ONLY, exx, clause, clauseSource); // FIXME - which
																										// exception
									}
									if (print)
										System.out.println("APPLYHELPER-X4BZ " + clause);
								}
							} catch (NoModelMethod e) {
								// FIXME - need to catch to skip the clause
							} catch (JmlNotImplementedException e) {
								// FIXME - should not need this anymore
								notImplemented(clause.keyword + " clause containing ", e, clause.source());
							}
							if (print) System.out.println("APPLYHELPER-X4C " + clause);
						}
						if (print) System.out.println("APPLYHELPER-X5");

						if (!ensuresStats.isEmpty()) {
							JCBlock ensuresBlock = M.at(cs.pos + 1).Block(0, ensuresStats.toList());
							// The +1 is so that the position of this if statement
							// and hence the names of the BRANCHT and BRANCHE variables
							// is different from the if prior to the apply // FIXME - review if this is
							// still needed
							JCStatement st = (numCases == 1 && !rac) || treeutils.isTrueLit(pre) ? ensuresBlock
									: M.at(cs.pos + 1).If(pre, ensuresBlock, null);
							JCBlock bl = M.at(cs.pos + 1).Block(0, List.<JCStatement>of(st));
							ensuresStatsOuter.add(wrapRuntimeException(cs, bl,
									"JML undefined precondition while checking postconditions - exception thrown",
									null));
						}
						if (!exsuresStats.isEmpty()) {
							JCBlock exsuresBlock = M.at(cs.pos + 1).Block(0, exsuresStats.toList());
							// The +1 is so that the position of this if statement
							// and hence the names of the BRANCHT and BRANCHE variables
							// is different from the if prior to the apply // FIXME - review if this is
							// still needed
							// FIXME - don't think pre should be null
							JCStatement st = ((numCases == 1 && !rac) || pre == null || treeutils.isTrueLit(pre))
									? exsuresBlock
									: M.at(cs.pos + 1).If(pre, exsuresBlock, null);
							JCBlock bl = M.at(cs.pos + 1).Block(0, List.<JCStatement>of(st));
							exsuresStatsOuter.add(wrapRuntimeException(cs, bl,
									"JML undefined precondition while checking exceptional postconditions - exception thrown",
									null));
						}
						if (print) System.out.println("APPLYHELPER-X6");
					}
//					paramActuals = null;
					if (print) System.out.println("APPLYHELPER-X7");
				}
				if (print) System.out.println("APPLYHELPER-XA");

//                
//                if (!rac && newclass == null && !calleeMethodSym.isConstructor() && resultType.getTag() != TypeTag.VOID) {
//                    MethodSymbol calleeMethodSym1 = calleeMethodSym;
//                    JCExpression newThisExpr1 = newThisExpr;
//                    final VarSymbol resultSym1 = resultSym;
//                    List<JCStatement> stats = collectStats( () -> 
//                        {
//                            addStat(comment(that,"Add determinism function call",log.currentSourceFile()));
//                            JmlMethodDecl mdecl = specs.getSpecs(calleeMethodSym1).cases.decl;
//                            int p = (mdecl != null) ? mdecl.pos : 0;
//                            Name newMethodName = newNameForCallee(p, calleeMethodSym1, !calleeIsFunction);
//                            ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
//                            if (!utils.isJMLStatic(calleeMethodSym1)) newargs.add(newThisExpr1);
//                            newargs.addAll(trArgs);
//                            JCIdent id = M.at(p).Ident(newMethodName);
//                            id.sym = calleeMethodSym1;
//                            JCExpression newCall = M.at(p).Apply(List.<JCExpression>nil(),id,newargs.toList());
//                            newCall.setType(that.type);
//                            JCIdent resultId = M.at(p).Ident(resultSym1);
//                            addAssumeEqual(that, Label.METHOD_ASSUME, resultId, newCall);
//                        });
//                    JCBlock bl = M.at(that.pos).Block(0L,stats);
//                    if (!resultSym.type.isPrimitiveOrVoid() && !utils.isPrimitiveType(resultSym.type)) {
//                        JCExpression isNotFresh = treeutils.makeNot(that.pos,
//                                makeFreshExpression(that,resultExpr,oldLabel.name));
//                        JCStatement stat = M.at(that.pos).If(isNotFresh,bl,null);
//                        ensuresStatsOuter.add(stat);
//                    } else {
//                        ensuresStatsOuter.add(bl);
//                    }
//                }                
				typevarMapping = newTypeVarMapping;
			} catch (Exception eee) {
				utils.unexpectedException(eee, "APPLY-HELPER");
				eee.printStackTrace(System.out);
			}
			if (print) System.out.println("APPLYHELPER-XB " + calleeMethodSym + " ");
			// FIXME - the source must be handled properly

			calleePreconditions.clear();

			// Get rid of references - this may not really be needed, but it does not hurt
//			{
//				for (Symbol key : mapParamActuals.keySet()) {
//					mapParamActuals.get(key).clear();
//				}
//				mapParamActuals.clear();
//				mapParamActuals = null;
//			}

			currentStatements = saved;

			if (exceptionDeclCall != null) {
				exsuresStatsOuter.add(M.at(that).Throw(treeutils.makeIdent(that.pos, exceptionDeclCall.sym)));
			} else if (rac) {
				System.out.println("DID NOT EXPECT THIS"); // FIXME
			}

			if (print) System.out.println("APPLYHELPER-XC " + calleeMethodSym + " ");
			JCBlock ensuresBlock = M.at(that).Block(0, ensuresStatsOuter.toList());
			if (rac) {
				JCBlock exsuresBlock = M.at(that).Block(0, exsuresStatsOuter.toList());
				addStat(wrapException(that, ensuresBlock, exceptionDeclCall, exsuresBlock));
				addStat(popBlock(methodDecl, check1)); // Final outer block
			} else if (esc) {
				if (exceptionDeclCall != null && !translatingJML) { // FIXME - what is happening if exceptionDeclCall is null - is the
													// method pure?
					// declare the exception variable
					addStat(exceptionDeclCall);
					if (hasModelProgramBlocks) { // Generalized model program
						JCIdent eid = treeutils.makeIdent(that.pos, exceptionSym);
						JCIdent ecid = treeutils.makeIdent(that.pos, exceptionDeclCall.sym);
						JCExpression pre = treeutils.trueLit; // convertCopy(preExpressions.get(cs));
						JCStatement stat = treeutils.makeAssignStat(that.pos, ecid, eid);
						stat = M.at(that.pos).If(pre, stat, null);
						addStat(stat);
					}

					JCIdent nexceptionId = treeutils.makeIdent(that.getStartPosition(), exceptionDeclCall.sym);
					treeutils.copyEndPosition(nexceptionId, that);
					{
						JCStatement c = comment(that,
								"Exception thrown by " + (apply == null ? newclass.constructor
										: meth instanceof JCIdent ? ((JCIdent) meth).sym : ((JCFieldAccess) meth).sym),
								null);
						exsuresStatsOuter = exsuresStatsOuter.prepend(c);
						JCExpression nex = copy(nexceptionId);
						pathMap.put(nex, c);
						saveMapping(nex, nexceptionId);
//                        log.noticeWriter.println("POSs " + nexceptionId.getStartPosition()
//                                   + " " + nexceptionId.getEndPosition(log.currentSource().getEndPosTable())
//                                   + " " + nex.getStartPosition()
//                                   + " " + nex.getEndPosition(log.currentSource().getEndPosTable()));
					}
					JCBinary ch = treeutils.makeEqObject(that.pos, nexceptionId, treeutils.nullLit);
					JCBlock exsuresBlock = M.at(that).Block(0, exsuresStatsOuter.toList());
					JCStatement st = M.at(that.pos).If(newTempIfNeeded(ch), ensuresBlock, exsuresBlock);
					if (allCasesNormal && someCasesNormal && !rac) {
						addAssume(that, Label.IMPLICIT_ASSUME, ch);
						st = ensuresBlock;
					}
					addStat(st);
				} else {
					addStat(ensuresBlock);
				}
				addStat(popBlock(methodDecl, check1)); // Final outer block
				checkBlock(stack0);
			} else if (infer) {
				addStat(ensuresBlock);
				addStat(popBlock(methodDecl, check1));
			}
			if (print) System.out.println("APPLYHELPER-Z " + calleeMethodSym + " " + resultExpr);
			checkBlock(stack0);
			if (resultSym != null && resultExpr != null) {
				result = eresult = treeutils.makeIdent(resultExpr.pos, resultSym);
				transferInfo(resultExpr, eresult);
			} else {
				result = eresult = resultExpr;
			}
			checkBlock(stack0);
			if (print) System.out.println("APPLYHELPER-ZA " + calleeMethodSym.owner + " " + calleeMethodSym + " " + eresult);

		} catch (Error e) {
			log.error("jml.internal", e.toString()); // FIXME - improve error message
			Utils.conditionalPrintStack("JMLAA-Error", e);
			throw e;
		} catch (Exception e) {
			Utils.conditionalPrintStack("JMLAA-Exception", e);
			throw e;
		} finally {
			checkBlock(stack0);
			if (print) System.out.println("APPLYHELPER-ZZ "
						+ (calleeMethodSym == null ? "NULL" : (calleeMethodSym.owner + " " + calleeMethodSym)) + " " + eresult);
			this.freshnessReferenceCount = savedFreshnessReferenceCount;
			paramActuals_ = savedParamActuals;
			resultSym = savedResultSym;
			resultExpr = savedResultExpr;
			exceptionSym = savedExceptionSym;
			currentEnv.currentReceiver = savedThisExpr;
			oldStatements = savedOldStatements;
			condition = savedCondition;
			currentFresh = savedFresh;
			enclosingMethod = savedEnclosingMethod;
			enclosingClass = savedEnclosingClass;
			typevarMapping = savedTypeVarMapping;
			nestedCallLocation = savedNestedCallLocation;
			applyNesting--;
			this.calleePreconditions = savedPreexpressions;
			currentOldLabel = savedCurrentOldLabel;
			if (rac) {
				outerDeclarations.addAll(currentStatements);
				currentStatements = outerDeclarations;
			}
			JCBlock b = popBlock(that, check0);
			currentStatements.addAll(b.stats);
			methodsInlined.remove(calleeMethodSym);
			if (pushedMethod) {
				callStack.remove(0);
				callStackSym.remove(0);
			}
            if (print) System.out.println("APPLYHELPER-ZZZ " + eresult);
		}
	}
	
	public void makeMethodHavocAxiom(DiagnosticPosition pos, Type receiverType, MethodSymbol calleeMethodSym, Type returnType, Object havocs,
	                        java.util.List<StoreRefGroup> readItems, List<JCExpression> args) {
	    int hc = heapCount;
        //System.out.println("HAVOCAXIOM " + calleeMethodSym + " " + hc + " " + args);
	    try {
	        var heapInfo = currentEnv.heap;
	        //System.out.println(" CALLING FOR " + calleeMethodSym + " " + hc + " " + heapInfo.heapID + " " + heapInfo.previousHeaps);
	        if (heapInfo.previousHeaps.isEmpty()) return;
	        for (var oldHeapInfo: heapInfo.previousHeaps) {
	            //System.out.println("   OLDHC " + oldHeapInfo.heapID + " " + hc);
	            if (hc == oldHeapInfo.heapID) continue; // No need for axioms if it is the same heap
	            MethodSymbol newCalleeSym = getNewMethodSymbol(calleeMethodSym);
	            MethodSymbol oldMethodSym = getNewMethodSymbol(calleeMethodSym, oldHeapInfo.heapID);
                //System.out.println("   SYMS " + newCalleeSym + " " + oldMethodSym);
	            if (oldMethodSym == null) {
	                // No instance of the method in this old heap
	                // So there is nothing to compare against.
	                // FIXME - we could keep going back until we find a match -- probably need to do this eventually
	                continue;
	            }
	            //System.out.println("HEAPFUCNAXIOM " + calleeMethodSym + " " + hc + " " + newCalleeSym + " " + oldHeapInfo.heapID + " " + oldMethodSym);
	            ListBuffer<JCVariableDecl> quantDecls = new ListBuffer<>();
	            ListBuffer<JCExpression> argList1 = new ListBuffer<>();
	            ListBuffer<JCExpression> argList2 = new ListBuffer<>();
	            //System.out.println("CALLEE " + calleeMethodSym + " " + calleeMethodSym.getReceiverType() + " " + calleeMethodSym.getParameters() + " " + calleeMethodSym.getReturnType());
	            JCVariableDecl d;
	            if (newCalleeSym.getParameters() != null) for (var p: newCalleeSym.getParameters()) {
	                d = newTempDecl(pos, p.type);
	                quantDecls.add(d);
	                argList1.add(M.at(pos).Ident(d.sym));
	                argList2.add(M.at(pos).Ident(d.sym));
	            }
	            var e1 = M.at(pos).Apply(List.<JCExpression>nil(), M.Ident(newCalleeSym), argList1.toList());
	            var e2 = M.at(pos).Apply(List.<JCExpression>nil(), M.Ident(oldMethodSym), argList2.toList());
	            e1.type = e2.type = returnType;
	            JCExpression ee = treeutils.makeEquality(pos.getPreferredPosition(), e1,  e2);
	            ee = M.at(pos).JmlQuantifiedExpr(qforallKind, quantDecls.toList(), treeutils.trueLit, ee);
	            JCStatement noChangeAxiom = M.at(pos).JmlExpressionStatement("assume", StatementExprExtensions.assumeClause, Label.METHODAXIOM, ee);
	            JCExpression e3 = M.at(pos).Apply(List.<JCExpression>nil(), M.Ident(newCalleeSym), copy(args));
	            JCExpression e4 = M.at(pos).Apply(List.<JCExpression>nil(), M.Ident(oldMethodSym), copy(args));
	            e3.type = e4.type = returnType;
	            JCStatement noChangeInstantiation = M.at(pos).JmlExpressionStatement("assume", StatementExprExtensions.assumeClause, Label.METHODAXIOM, 
	                treeutils.makeEquality(pos.getPreferredPosition(), e3, e4));
	            //System.out.println("NOCHANGEINST " + newCalleeSym + " " + noChangeInstantiation);

	            SpecCaseIterable specCases = new SpecCaseIterable(calleeMethodSym, false);
	            for (var info: specCases) {
	                var parentMethodSym = info.parentMethodSymbol;
	                var scase = info.specCase();
	                //paramActuals = info.paramActuals();
	                JCExpression preid = calleePreconditions.get(scase);
	                currentEnv = currentEnv.pushEnvCopy();
	                // FIXME - no 'noChangeInstantiation' if receiver is fresh
	                for (var clause : scase.clauses) {
	                    if (!(clause instanceof JmlMethodClauseStoreRef sc)) continue;
	                    if (clause.clauseKind != accessibleClauseKind) continue;
	                    currentEnv.enclosingClauseKind = sc.clauseKind;
	                    //JCExpression locset = convertAssignableToLocsetExpression(clause, sc.list, (ClassSymbol)receiverType.tsym, null);
	                    // make sure sc.list and info.havocs are disjoint
	                    JCExpression disjoint = treeutils.trueLit;
	                    Object oldhavocs = heapInfo.havocs;
	                    //System.out.println("OLDHAVOCS " + oldHeapInfo.condition + " " + oldhavocs);
	                    if (oldhavocs == null || oldhavocs instanceof JCIf) {
	                        // skip
	                    } else if (oldhavocs instanceof JCNewClass nc) {
	                        if (isPure((MethodSymbol)nc.constructor) && currentEnv.currentReceiver != null) {
	                            var z = freshTest(nc, currentEnv.currentReceiver, labelPropertiesStore.get(oldHeapInfo.label).allocCounter);
	                            disjoint = treeutils.makeNot(z, z);
	                        } else {
	                            disjoint = treeutils.falseLit; // FIXME - overly conservative
	                        }
	                        //System.out.println("  ISPURE? " + isPure((MethodSymbol)nc.constructor) + " " + disjoint);
	                    } else if (oldhavocs instanceof List<?> writesList) {
	                        //System.out.println("Computing DISJOINT of " + readItems + " VS " + writesList);
                                @SuppressWarnings("unchecked")  // FIXME - do better on the type of havocs
	                        var hasIntersection = simplifyNonDisjoint(pos, readItems, (List<StoreRefGroup>)writesList);
                            disjoint = treeutils.makeNotSimp(pos, hasIntersection);
                            //System.out.println(" RESULT DISJOINT " + disjoint);
	                    } else {
	                        JCExpression hasIntersection = treeutils.falseLit;
	                        for (JCExpression srex: sc.list) { 
	                            JmlStoreRef jmlsr = makeJmlStoreRef(srex, srex, (ClassSymbol)calleeMethodSym.owner, false).head;
	                            if (jmlsr == null) continue; // srex is \nothing
	                            JmlStoreRef sr = null;
	                            /*if (oldhavocs instanceof JCFieldAccess fa) {
	                                sr = makeJmlStoreRef(fa, fa, (ClassSymbol)fa.sym.owner, false).head;
	                            } if (oldhavocs instanceof JCIdent id) {
	                                if (id.sym.owner instanceof ClassSymbol) {
	                                    sr = makeJmlStoreRef(id, id, (ClassSymbol)id.sym.owner, false).head;
	                                } // otherwise is a local assignment that does not affect the heap
	                            } else if (oldhavocs instanceof JCArrayAccess aa) {
	                                sr = makeJmlStoreRef(aa, aa, (ClassSymbol)calleeMethodSym.owner, false).head;
	                            } else */
	                            {
	                                // FIXME - watch out for fresh receivers
	                                System.out.println("UNSUPPORTED HAVOCS " + oldhavocs);
	                                System.out.println("  WITH READS " + Utils.join(" ", readItems));
	                            }
	                            if (sr != null) {
	                                TranslationEnv oldenv = labelPropertiesStore.get(heapInfo.label).labelEnv;
	                                JCExpression nondisjoint = simplifyNonDisjoint(jmlsr, sr, oldenv, false); // FIXME  - need an old environment here
	                                //System.out.println("NONDISJ " + jmlsr + " ^ " + sr + " = " + nondisjoint);
	                                //System.out.println("   Checking reads clause " + sc.list + "(receiver " + currentEnv.currentReceiver + ") is nondisjoint from " + sr + " == " + nondisjoint);
	                                hasIntersection = treeutils.makeOrSimp(srex, hasIntersection, nondisjoint);
	                            } else {
	                                hasIntersection = treeutils.trueLit;
	                            }
	                        }
	                        disjoint = treeutils.makeAndSimp(hasIntersection, disjoint, treeutils.makeNotSimp(hasIntersection, hasIntersection));
	                    }
	                    // If no clauses, default is \everything, which is presumed to not be disjoint with anything
	                    // If a state change had no havocs, this is overly conservative
	                    if (treeutils.isFalseLit(disjoint)) {
	                        addStat(comment(methodDecl, "   Reads clause " + sc.list + "(receiver " + currentEnv.currentReceiver + ") is never disjoint from " + oldhavocs , null));
	                    } else {
	                        var ex = treeutils.makeAndSimp(clause, copy(preid), disjoint);
	                        if (oldHeapInfo.condition != null) ex = treeutils.makeAndSimp(clause, oldHeapInfo.condition, ex);
	                        ex = newTempIfNeeded(ex);
	                        if (treeutils.isTrueLit(ex)) {
	                            addStat(comment(methodDecl, "   Checking reads clause " + sc.list + "(receiver " + currentEnv.currentReceiver + ") is disjoint from " + oldhavocs + "  Precondition: " + preid + " " + copy(preid), null));
	                            addStat(noChangeInstantiation);
	                        } else {
	                            addStat(comment(methodDecl, "   Checking reads clause " + sc.list + "(receiver " + currentEnv.currentReceiver + ") is disjoint from " + oldhavocs + "  Precondition: " + preid + " " + copy(preid), null));
	                            JCStatement v = M.at(clause).If(ex, noChangeInstantiation, null);
	                            addStat(v);
	                        }
	                    }
	                }
	                currentEnv = currentEnv.popEnv();
	            }
	        }

 //           info.methodAxiomsBlock.stats = info.methodAxiomsBlock.stats.append(s);
 //           System.out.println("  AXIOM " + ee);
	    } catch (Throwable e) {
	        System.out.println("CRASH IN makeMethodHavocAxiom for " + methodDecl.sym + " " + calleeMethodSym.owner + "." + calleeMethodSym + " " + currentEnv.heap.previousHeaps.iterator().next().heapID);
	        System.out.println("  ITEMS " + readItems + " " + havocs);
	        e.printStackTrace(System.out);
	    }

	}

	public JCExpression makeDeterminismCall(JCExpression that, MethodSymbol calleeMethodSym, JCExpression newThisExpr,
			List<JCExpression> extendedArgs) {

		MethodSymbol newCalleeSym = getNewMethodSymbol(calleeMethodSym);
		if (newCalleeSym == null) {
			utils.error(that, "jml.internal", "No logical function for method " + that + " " + calleeMethodSym);
			return null;
		}

		if (utils.isJMLStatic(calleeMethodSym) && extendedArgs.isEmpty()) {
			// Should be a constant- what if it has type arguments
            return treeutils.makeMethodInvocation(that, null, newCalleeSym, extendedArgs);
		} else {
			return treeutils.makeMethodInvocation(that, null, newCalleeSym, extendedArgs);
		}
	}

	public void addToCallStack(JCExpression that) {
		Symbol sym = (that instanceof JCMethodInvocation) ? treeutils.getSym(((JCMethodInvocation) that).meth)
				: ((JCNewClass) that).constructor;
		String s = utils.locationString(that.pos) + " " + utils.qualifiedName(sym);
		callStack.add(0, s);
		callStackSym.add(0, sym);
	}

	public boolean isRecursiveCall(MethodSymbol calleeMethodSym) {
		if (methodsInlined.contains(calleeMethodSym)) {
			// Recursive inlining
			return true;
		}
		{
			Iterator<Symbol> iter = callStackSym.iterator();
			while (iter.hasNext()) {
				if (iter.next() == calleeMethodSym) {
					return true;
				}
			}
		}
		return false;
	}

	public List<JCExpression> extendArguments(JCExpression that, MethodSymbol calleeMethodSym, JCExpression newThisExpr,
			List<JCExpression> trArgs) {
		List<JCExpression> ntrArgs = trArgs;
		if (!utils.isJMLStatic(calleeMethodSym)) {
			ntrArgs = ntrArgs.prepend(newThisExpr);
		}
		if (!isHeapIndependent(calleeMethodSym) && !useNamesForHeap) {
			JCExpression heap = treeutils.makeIdent(that.pos, heapSym);
			ntrArgs = ntrArgs.prepend(heap); // only if heap dependent
		}
		return ntrArgs;
	}


	public void addMethodAxiomsPlus(JCExpression that, MethodSymbol calleeMethodSym, JCExpression newThisExpr,
			List<JCExpression> convertedArgs, Type receiverType, java.util.List<Pair<MethodSymbol, Type>> overridden,
			boolean details) {
        //System.out.println("METHODAXIOMS-START " + calleeMethodSym + " " + that + " " + that.type);
	    try {
	        specs.getAttrSpecs(calleeMethodSym);
	        var returnType = that.type; // FIXME - in some cases (cf. test linked2) that.type does not have type parameters, as the symbol does
	        //if (calleeMethodSym.type instanceof Type.MethodType mt) returnType = mt.getReturnType();
	        //if (calleeMethodSym.type instanceof Type.ForAll mt) returnType = mt.getReturnType();
	        //System.out.println("METHODAXIOMS-TYPES " + calleeMethodSym + " " + that + " " + that.type + " " + returnType + " " + calleeMethodSym.type.getClass());

	        JCBlock bl = addMethodAxioms(that, calleeMethodSym, overridden, receiverType, returnType);
	        //System.out.println("makeMethodHavocAxiom " + calleeMethodSym + " " + getNewMethodSymbol(calleeMethodSym) + " "  + details + " " + bl);
	        if (details) { // FIXME - document this details check - if it is false, the axioms are dropped
	            // FIXME - actually should add these into whatever environment is operative

	            if (bl == null) {
	            } else if (currentEnv.stateLabel != null) {
	                addToOldList(currentEnv.stateLabel, bl);
	            } else if (nonignoredStatements != null) {
	                nonignoredStatements.add(bl);
	            } else if (axiomBlock != null) {
	                axiomBlock.stats = axiomBlock.stats.append(bl);
	            } else {
	                addStat(bl);
	            }
	        }
	    } catch (Throwable e) {
	        utils.warning(that,"jml.message","Unexpected exception in addMethodAxioms: " + calleeMethodSym + " " + that );
	        e.printStackTrace(System.out);
	    }
	}

	public void assertCalledMethodPrecondition(JCExpression that, MethodSymbol calleeMethodSym,
			List<JCExpression> convertedArgs) {
		WellDefined info = wellDefinedCheck.get(calleeMethodSym);
		if (info != null && !info.alltrue) { // FIXME - should not ever be null? perhaps anon types?
			MethodSymbol s = info.sym;
			if (s != null && localVariables.isEmpty() && !treeutils.isTrueLit(info.wellDefinedExpression)) {
				JCExpression e;
				if (!convertedArgs.isEmpty())
					e = treeutils.makeMethodInvocation(that, null, s, convertedArgs);
				else
					e = treeutils.makeIdent(that, s);
				if (currentEnv.stateLabel != null)
					e = makeOld(e.pos, e, currentEnv.stateLabel);
				e = condition == null ? e : conditionedAssertion(condition, e); // FIXME - why is the condition the
																				// location
				if (assumingPureMethod) {
					addAssume(that, Label.UNDEFINED_PRECONDITION, e, info.pos, info.source);
				} else {
					addAssert(that, Label.UNDEFINED_PRECONDITION, e, info.pos, info.source);
				}
			}
		}
	}
	
//	public boolean isBuiltinMethod(MethodSymbol msym) {
//	    if (!msym.owner.toString().contains("org.jmlspecs.lang")) return false;
//	    for (var p: msym.getParameters()) {
//	        if (!utils.isJavaOrJmlPrimitiveType(p.type)) return false;
//	    }
//	    return true;
//	}
	
	public void initialInvariantCheck(DiagnosticPosition that, boolean isSuperCall, boolean isThisCall,
			MethodSymbol calleeMethodSym, JCExpression callerThisExpr, JCExpression newThisExpr,
			List<JCExpression> trArgs, JCMethodInvocation apply) {

		ClassSymbol calleeClass = (ClassSymbol) calleeMethodSym.owner;

		// FIXME - the check on helper here is only if callee and caller have the same
		// receiver, or is it receivers with the same class?
		if (applyNesting <= 1 && !methodDecl.sym.isConstructor() 
		        && !(isHelper(calleeMethodSym) && apply != null && !isHeapIndependent(calleeMethodSym)
                && (utils.isJMLStatic(apply.meth instanceof JCIdent ? ((JCIdent) apply.meth).sym : ((JCFieldAccess) apply.meth).sym)
    				|| apply.meth instanceof JCIdent)
    			)) {
			addStat(comment(that,
					"Checking caller invariants of " + methodDecl.sym + " before calling method " + utils.qualifiedMethodSig(calleeMethodSym),
					null));
			if (!isSuperCall && !isThisCall) {
//                    if (meth instanceof JCFieldAccess) {
//                        addInvariants(that,savedEnclosingClass.type,
//                                savedEnclosingMethod == null || utils.isJMLStatic(savedEnclosingMethod)  ? null : savedThisExpr,
//                                currentStatements,
//                                true,savedEnclosingMethod != null && savedEnclosingMethod.isConstructor(),isSuperCall,isHelper(methodDecl.sym),false,false,Label.INVARIANT_EXIT_CALLER, "(Caller: " + utils.qualifiedMethodSig(methodDecl.sym) + ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");
//
				var invariantsNeededByCallee = invariantsNeeded(newThisExpr, calleeMethodSym);
				for (var r : invariantsNeededByCallee.first) {
					if (r != newThisExpr || !calleeMethodSym.isConstructor()) {
					    String msg = "(Caller: " + (methodDecl != null ? utils.qualifiedMethodSig(methodDecl.sym) : classDecl.sym )+ ", Callee: "
		                                        + utils.qualifiedMethodSig(calleeMethodSym) + ")";
						addInvariants(that, r.type, r, currentStatements, false, calleeMethodSym.isConstructor(),
								isSuperCall, isHelper(calleeMethodSym), false, false, Label.INVARIANT_EXIT_CALLER,
								msg);
                    }
				}
				for (var r : invariantsNeededByCallee.second) {
				    String msg = 
				        "(Caller: " + (methodDecl != null ? utils.qualifiedMethodSig(methodDecl.sym) : classDecl.sym) + ", Callee: "
                        + utils.qualifiedMethodSig(calleeMethodSym) + ")";
				        
					addInvariants(that, r.type, null, currentStatements, false, calleeMethodSym.isConstructor(),
							isSuperCall, isHelper(calleeMethodSym), false, false, Label.INVARIANT_EXIT_CALLER,
							msg);
				}
				// utils.qualifiedMethodSig(methodDecl.sym) + " " +
				// utils.qualifiedMethodSig(calleeMethodSym)); // FIXME - do we really do post
				// here and below
//                    }
			}
			clearInvariants();
			// Note that methodDecl.params will be null for initializer blocks
			if (methodDecl != null && methodDecl.params != null)
				for (JCVariableDecl v : methodDecl.params) {
					if (utils.isJavaOrJmlPrimitiveType(v.type))
						continue;
					// FIXME - it is an open question which invariants to check here - in principle
					// all invariants must hold - but which might not? - need the pack/unpack
					// capability
					// FIXME - for now we check the invariants of the parameters in the prestate
					// JCIdent d = preparams.get(v.sym);
					JCIdent id = treeutils.makeIdent(v.pos, v.sym);
					// FIXME - do we needs an \old here?
					addStat(comment(v, "Checking invariants for caller parameter " + v.sym + " before calling method "
							+ utils.qualifiedMethodSig(calleeMethodSym), null));
					addInvariants(v, v.type, id, currentStatements, false, false, false, isHelper(calleeMethodSym),
							false, false, Label.INVARIANT_EXIT_CALLER,
							"(Parameter: " + v.sym + ", Caller: " + utils.qualifiedMethodSig(methodDecl.sym)
									+ ", Callee: " + utils.qualifiedMethodSig(calleeMethodSym) + ")");
					clearInvariants();
				}
		}

		JCExpression collectedInvariants = treeutils.trueLit; // FIXME - do we need this - do we include this in the
																// 'condition' ?
		Label assertionLabel = Label.INVARIANT_ENTRANCE;
		// if (translatingJML) assertionLabel = Label.
		if (!isSuperCall && !isThisCall && !isHelper(calleeMethodSym)) { // Iterate through parent classes and
																			// interfaces, adding relevant invariants
			String owner = (methodDecl != null ? utils.qualifiedMethodSig(methodDecl.sym) : classDecl.sym.toString());
		    String msg = "(Caller: " + owner + ", Callee: "
					+ utils.qualifiedMethodSig(calleeMethodSym) + ")";
			addStat(comment(that, "Checking callee invariants by the caller " + owner
					+ " before calling method " + utils.qualifiedMethodSig(calleeMethodSym), null));
			// System.out.println("Checking callee invariants by the caller " +
			// utils.qualifiedMethodSig(methodDecl.sym) + " before calling method " +
			// utils.qualifiedMethodSig(calleeMethodSym) + " helper="+
			// isHelper(calleeMethodSym) + " " + calleeClass);
			addStat(comment(that, "RECEIVER = " + newThisExpr + " " + that, null));
			addInvariants(that, calleeClass.type, newThisExpr, currentStatements, false,
					calleeMethodSym.isConstructor(), false, isHelper(calleeMethodSym), false, false, assertionLabel,
					msg);
			// System.out.println("FINISHED Checking callee invariants by the caller " +
			// utils.qualifiedMethodSig(methodDecl.sym) + " before calling method " +
			// utils.qualifiedMethodSig(calleeMethodSym));
			addStat(comment(that,
					"END Checking callee invariants by the caller " + owner
							+ " before calling method " + utils.qualifiedMethodSig(calleeMethodSym),
					null));
			for (JCExpression arg : trArgs) {
				if (utils.isJavaOrJmlPrimitiveType(arg.type))
					continue;
				currentStatements
						.add(comment(arg, "Asserting invariants for callee parameter before calling the callee "
								+ utils.qualifiedMethodSig(calleeMethodSym), null));
				JCIdent id;
				if (arg instanceof JCIdent)
					id = (JCIdent) arg;
				else {
					continue; // FIXME - see testbigint
				}
				addInvariants(arg, arg.type, id, currentStatements, false, false, false, false, false, false,
						assertionLabel, msg);
			}
			clearInvariants(); // TODO - test this?
		}
	}

	public Pair<List<JCExpression>, List<TypeSymbol>> invariantsNeeded(/* @ nullable */JCExpression receiver,
			MethodSymbol calleeMethodSymbol) {
		var instances = new ListBuffer<JCExpression>();
		var statics = new ListBuffer<TypeSymbol>();
		if (!isHelper(calleeMethodSymbol)) {
			if (receiver != null)
				instances.add(receiver);
			else
				statics.add((TypeSymbol) calleeMethodSymbol.owner);
		}
		return new Pair<List<JCExpression>, List<TypeSymbol>>(instances.toList(), statics.toList());
	}

	public void applyLambda(JCExpression that, JCExpression convertedReceiver, List<JCExpression> untrArgs,
			List<JCExpression> trArgs, Type resultType) {
		if (convertedReceiver instanceof JCTree.JCLambda) {
			// Now need to apply the lambda to its arguments, by substitution
			JCTree bl = ((JCTree.JCLambda) convertedReceiver).body;
			JavaFileObject lambdaSource = ((JmlTree.JmlLambda) convertedReceiver).sourceLocation;
			JCBlock block = null;
			if (bl instanceof JCBlock) {
				block = (JCBlock) bl;
			} else if (bl instanceof JCStatement) {
				block = collectBlock(bl, () -> {
					addStat((JCStatement) bl);
				});
			} else if (bl instanceof JCExpression) {
				block = collectBlock(bl, () -> {
					addStat(M.at(bl).Exec((JCExpression) bl));
				});
			} else {
				String msg = "Unknown type of lambda expression body: " + bl.getClass();
				utils.error(convertedReceiver, "jml.internal", msg);
				throw new JmlInternalError(msg);
			}
			// If there are arguments or a return value, we need to do a substitution pass
			addStat(comment(that, "Inlining lambda " + convertedReceiver.toString(), log.currentSourceFile()));
			if (true || trArgs.size() != 0 || resultType.getTag() != TypeTag.VOID) {
				Map<Object, JCExpression> replacements = new HashMap<Object, JCExpression>();
				Iterator<JCExpression> iter = trArgs.iterator();
				for (JCVariableDecl d : ((JCTree.JCLambda) convertedReceiver).params) {
					replacements.put(d.sym, iter.next());
				}
				VarSymbol oldSymbol = resultSym;
				JCExpression saved = currentEnv.currentReceiver;
				currentEnv.currentReceiver = lambdaLiterals.get(((JmlLambda)convertedReceiver).literal.toString()).second;
				JavaFileObject prev = null;
				try {
					if (lambdaSource != null)
						log.useSource(lambdaSource);
					result = eresult = inlineConvertBlock(block, replacements, resultType);
				} finally {
					if (prev != null)
						log.useSource(prev); // FIXME - should this be protected with a try block
				}
				currentEnv.currentReceiver = saved;
				resultSym = oldSymbol;
			} else {
				addStat(block);
				result = eresult = null; // FIXME WHAT should this be?
			}

			// addStat(comment(that,"Translated body of lambda: " + that.toString(),
			// log.currentSourceFile()));
			// addStat(comment(that,"END body of lambda: " + that.toString(),
			// log.currentSourceFile()));

		} else if (convertedReceiver instanceof JCTree.JCMemberReference) {

			// Make a method invocation in which the method reference has the argument list
			JCTree.JCMemberReference mref = (JCTree.JCMemberReference) convertedReceiver;
			JCExpression mexpr = mref.expr;
			JCExpression receiver = null;
			if (treeutils.isATypeTree(mexpr)) {
				if (!mref.sym.isStatic()) {
					receiver = untrArgs.head;
					untrArgs = untrArgs.tail;
				}
			} else {
				receiver = mexpr;
			}

			// The receiver may not be null./ But that condition is checked when we convert
			// the Exec statement
			// created below.

			// FIXME - the receiver, the method name, and the arguments may all be from
			// different files.

			JCExpression e = treeutils.makeMethodInvocation(that, receiver, (MethodSymbol) mref.sym, untrArgs);
			// System.out.println("MEMREF " + that + " " + convertedReceiver + " " + e);
			if (((MethodSymbol) mref.sym).getReturnType().hasTag(TypeTag.VOID)) {
				// Statement - no return values
				JCStatement stat = M.at(that.pos).Exec(e); // FIXME - position location is likely in the wrong file
				convert(stat); // Since we are converting the entire inlined expression, we don't convert the
								// arguments before this point
				result = eresult = null;
			} else {
				// return value
				result = eresult = convertExpr(e);
			}
		} else {
			throw new RuntimeException("Unexpected alternative");
		}
		if (splitExpressions && eresult != null) {
			result = eresult = newTemp(eresult);
		}
	}

	public JCExpression insertAllModelProgramInlines(JCExpression that,
			Map<Symbol, Map<Object, JCExpression>> mapParamActuals,
			Map<JmlSpecificationCase, JCExpression> preExpressions, MethodSymbol calleeMethodSym,
			List<JCExpression> typeargs, JCExpression meth, boolean inliningCall,
			java.util.List<Pair<MethodSymbol, Type>> overridden) {
		JCIdent localResult = null;
		JCExpression savedResultExpr = resultExpr;
		try {
			for (Pair<MethodSymbol, Type> pair : overridden) {
				MethodSymbol mpsym = pair.first;
				Type classType = pair.second;
				addStat(comment(that,
						"... Checking for model programs " + calleeMethodSym + " in " + classType.toString(), null));

				// FIXME - from here down to loop is duplicated from above

				// FIXME - meth is null for constructors - fix that also; also generic types
				typevarMapping = typemapping(classType, calleeMethodSym, typeargs,
						meth == null ? null : meth.type instanceof Type.MethodType ? (Type.MethodType) meth.type : null,
						null);
				if (that instanceof JCMethodInvocation)
					typevarMapping = typemapping((JCMethodInvocation) that, typevarMapping);
				// This initial logic must match that below for postconditions

				JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(mpsym);
				if (calleeSpecs == null)
					continue; // FIXME - not sure about this - should get a default?

//				paramActuals = mapParamActuals.get(mpsym);

				LinkedList<ListBuffer<JCStatement>> temptt = markBlock();
				for (JmlSpecificationCase cs : calleeSpecs.cases) {
                    if (!doSpecificationCase(methodDecl, calleeMethodSym, mpsym, cs)) continue; 
//					if (!utils.jmlvisible(mpsym, classDecl.sym, mpsym.owner, cs.modifiers.flags, methodDecl.mods.flags))
//						continue;
//					if (translatingJML && cs.token == exceptionalBehaviorClause)
//						continue;
//					if (mpsym != calleeMethodSym && cs.code)
//						continue;

					if (cs.block != null && !localVariables.isEmpty()) {
						utils.warning(cs.block.pos, "jml.message",
								"Cannot use functions with model methods within quantified expressions");
						break;
					}
					if (cs.block != null) { // Note: inlining for RAC, also -- FIXME - need to check this
						JCExpression pre = preExpressions.get(cs);
						if (pre == null) {
							pre = treeutils.trueLit;
							for (JmlMethodClause clause : cs.clauses) {
								if (clause.clauseKind == accessibleClauseKind) {
									JmlTree.JmlMethodClauseExpr cl = (JmlTree.JmlMethodClauseExpr) clause;
									pre = treeutils.makeAndSimp(clause.pos, pre, copy(cl.expression));
								}
							}
						}
						if (localResult == null && that.type.getTag() != TypeTag.VOID) {
							localResult = newTemp(that, that.type);
						}
						resultSym = localResult == null ? null : (VarSymbol) localResult.sym;
						resultExpr = localResult;
						addStat(comment(cs.block, "Inlining model program ", cs.source())); // FIXME - source file for
																							// inlining?
						JavaFileObject prevv = log.useSource(cs.source());
						// We make a copy because the block being inlined might be inlined more than
						// once
						// and it might have modifications to it, such as if there are any inlined_loop
						// statements
						JCExpression cpre = copy(pre);
						inlineConvertBlock(that, cpre, copy(cs.block), "model program");
						log.useSource(prevv);
					}
				}
				checkBlock(temptt);

				if (inliningCall) { // Note: inlining for RAC, also -- FIXME - need to check this
					if (localResult == null) {
						localResult = newTemp(that, that.type);
					}
					resultSym = (VarSymbol) localResult.sym;
					resultExpr = localResult;
					addStat(comment(that, "Inlining method " + calleeMethodSym.toString(), log.currentSourceFile()));
					// Find definition of method to be inlined
					JmlSpecs.MethodSpecs m = JmlSpecs.instance(context).getAttrSpecs(calleeMethodSym);
					JmlMethodDecl mdecl = m.cases.decl;
					inlineConvertBlock(that, treeutils.trueLit, mdecl.body, "body of method " + calleeMethodSym);
				}
				checkBlock(temptt);
//				paramActuals = null;
			}
		} finally {
			resultExpr = savedResultExpr;
		}
		return localResult;
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
//        if (that.type.getTag() != TypeTag.VOID) eresult = newTemp(e);
//        else eresult = e;
//        // TODO Auto-generated method stub
//        //throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//    }

	/** Returns true iff the only statements on the list are comment statements */
	protected boolean onlyComments(Iterable<JCStatement> list) {
		for (JCStatement s : list) {
			if (!(s instanceof JmlStatementExpr && ((JmlStatementExpr) s).clauseType == commentClause))
				return false;
		}
		return true;
	}

	// assume that 'expr' is not allocated
	protected void newAllocation1(DiagnosticPosition pos, JCExpression expr) {
		int p = pos.getPreferredPosition();
		JCFieldAccess fa = treeutils.makeSelect(p, copy(expr), isAllocSym);
		addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeNot(p, fa));
	}

	// make an assignment that states that 'expr' is now allocated
	protected void newAllocation2(DiagnosticPosition pos, JCExpression resultExpr) {
		int p = pos.getPreferredPosition();
		JCFieldAccess fa = treeutils.makeSelect(p, copy(resultExpr), isAllocSym);
		JCStatement st = treeutils.makeAssignStat(p, fa, treeutils.makeBooleanLiteral(p, true));
		addStat(st);

	}


	// insert a state change that states that 'resultId" was not allocated but now
	// is
	protected void newAllocation(DiagnosticPosition pos, JCIdent resultId) {
		newAllocation1(pos, copy(resultId));
		newAllocation2(pos, copy(resultId));
	}

	// FIXME - review newClass

	@Override
	public void visitNewClass(JCNewClass that) {

		// FIXME - need to check definedness by testing preconditions when
		// translatingJML

//        JCExpression savedCondition = condition;
//        condition = treeutils.trueLit;

		// FIXME - need to call the constructor; need an assertion about the type of the
		// result; about allocation time
		boolean isUtils = that.type.toString().contains("org.jmlspecs.runtime.Utils"); // FIXME - must be a better way
		if (isUtils) {
			ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
			for (JCExpression arg : that.args) {
				args.add(convertExpr(arg));
			}
			JCNewClass expr = M.at(that).NewClass(that.encl, convert(that.typeargs), convert(that.clazz), args.toList(),
					convert(that.def));
			expr.constructor = that.constructor;
			expr.constructorType = that.constructorType;
			expr.varargsElement = that.varargsElement;
			expr.setType(that.type);
			result = eresult = expr;
//            condition = savedCondition;
			return;
		}
		Map<Symbol, Symbol> saved = pushMapSymbols();
		try {
			applyHelper(that);
		} finally {
			popMapSymbols(saved);
		}
	}

	Map<Symbol, WellDefined> wellDefinedCheck = new HashMap<Symbol, WellDefined>();

	/**
	 * Maps symbols of methods in Java or JML to the translated methods that
	 * represent them in translated programs, and will be carried further into the
	 * SMT translation. Such translations are only produced if the method's specs
	 * are not inlined. The methods are always static.
	 */
//    Map<Symbol,MethodSymbol> pureMethod = new HashMap<Symbol,MethodSymbol>();

	// Set<Symbol> axiomsAdded = new HashSet<Symbol>();
	Map<Integer, Set<Symbol>> axiomsAdded = new HashMap<>();
	Set<Symbol> methodsInlined = new HashSet<Symbol>();

	int heapCountForAxioms = -2;

	/** Returns true if the symbol was not already in the set for hc */
	protected boolean addAxioms(int hc, Symbol sym) {
		Set<Symbol> ss = axiomsAdded.get(hc);
		if (ss == null) {
			ss = new HashSet<Symbol>();
			axiomsAdded.put(hc, ss);
		}
		return ss.add(sym);
	}


	// FIXME - review newArray
	// OK
	@Override
	public void visitNewArray(JCNewArray that) {
		// Note that a JCNewArray can be the full new array expression: new Type[]{...}
		// But in a multi-dimensional initializer, each nested {...} is itself
		// a JCNewArray, though now with a null elemtype.

		ListBuffer<JCExpression> dims = new ListBuffer<JCExpression>();
		for (JCExpression dim : that.dims) {
			JCExpression ex = convertExpr(dim);
			// FIXME - is there a range check on BigInteger converting down to int
			ex = addImplicitConversion(ex.pos(), syms.intType, ex);
			dims.add(ex);
			neg: if (ex != null) {
				// TODO: Also bigint?
				Number n = treeutils.integralLiteral(ex);
				if (n != null && n.longValue() >= 0) {
					addStat(comment(ex, "Constant array size is non-negative: " + n.longValue(),
							log.currentSourceFile()));
					break neg;
				}

				JCExpression comp = treeutils.makeBinary(dim.pos, JCTree.Tag.LE, treeutils.intleSymbol, treeutils.zero,
						ex);
				addJavaCheck(dim, comp, Label.POSSIBLY_NEGATIVESIZE, Label.UNDEFINED_NEGATIVESIZE,
						"java.lang.NegativeArraySizeException");
			}
		}

		ListBuffer<JCExpression> elems = new ListBuffer<JCExpression>();
		if (that.elems != null) {
			for (JCExpression elem : that.elems) {
				elems.add(convertExpr(elem)); // FIXME - we need implicit conversions
			}
		} else {
			elems = null;
		}

		if (rac) {
			// This will create a fully-qualified version of the type name
			JCExpression elemtype = that.elemtype == null ? null
					: treeutils.makeType(that.elemtype.pos, that.elemtype.type);
			result = eresult = M.at(that).NewArray(elemtype, dims.toList(), elems == null ? null : elems.toList())
					.setType(that.type);
			result = eresult = newTemp(eresult);
		} else { // esc
			// FIXME - Creating a decl and initializing it outside the expression doe snot
			// work for translatigJML if there is a quantifier expression
			JCVariableDecl decl = treeutils.makeVarDef(that.type,
					names.fromString(Strings.newArrayVarString + that.pos + "_" + nextUnique()), null, that.pos);
			addStat(decl);
			JCIdent id = treeutils.makeIdent(that.pos, decl.sym);

			addArrayElementAssumptions(that, id, dims, elems);

			result = eresult = copy(id);

			// FIXME - need assertions about size of array and about any known array
			// elements; about allocation time
			// also about type of the array
		}
	}

	protected void addArrayElementAssumptions(DiagnosticPosition p, JCIdent array, ListBuffer<JCExpression> dims,
			ListBuffer<JCExpression> elems) {
		JCExpression size = null;
		int pos = p.getPreferredPosition();
		if (dims != null && dims.length() > 0) {
			size = dims.first();
		} else if (elems != null) {
			size = treeutils.makeIntLiteral(array.pos, elems.length());
		} else {
			// ERROR
		}
		// array != null
		addAssume(array, Label.NULL_CHECK, treeutils.makeNeqObject(array.pos, array, treeutils.nullLit));
		newAllocation(array, array);
		if (size != null) {
			// Set the size if it is known, either from the dimension or the array of
			// initializer elements
			// array.length == size
			addAssume(array, Label.IMPLICIT_ASSUME,
					treeutils.makeEquality(array.pos, treeutils.makeLength(array, copy(array)), convert(size)));
		}
		if (elems != null) {
			// There is an initializer; so initialize all the elements
			Type ctype = ((Type.ArrayType) array.type).getComponentType();
			int i = 0;
			for (JCExpression e : elems) {
				JCLiteral index = treeutils.makeIntLiteral(e.pos, i);
				e = addImplicitConversion(e, ctype, e);
				JmlBBArrayAccess aa = new JmlBBArrayAccess(null, array, index); // FIXME - switch to factory
				aa.pos = array.pos;
				aa.setType(ctype);
				aa.arraysId = null;

				JCBinary b = treeutils.makeEquality(e.pos, aa, e);
				addAssume(e.pos(), Label.IMPLICIT_ASSUME, b);
				++i;
			}
		}
		JCExpression e3 = treeutils.makeDynamicTypeEquality(p, array, array.type);

		addAssume(p, Label.IMPLICIT_ASSUME, e3);

		if (true) {
			JCExpression e = allocCounterEQ(p, copy(array), ++allocCounter);
			addAssume(p, Label.IMPLICIT_ASSUME, e);

//            if (dims.first() instanceof JCLiteral) {
//                e = createNullInitializedArray(array.type, dims.toList());
//                JCBinary b = treeutils.makeEquality(e.pos,array,e);
//                addAssume(array,Label.IMPLICIT_ASSUME,b);
//            } else 
			{
				// assume the proper lengths of all the sub arrays
				for (int n = 1; n < dims.length(); n++) {
					int i = 0;
					ListBuffer<JCVariableDecl> decls = new ListBuffer<JCVariableDecl>();
					JCExpression range = null;
					JCExpression expr = copy(array);
					Type ct = array.type;
					int k = n;
					Iterator<JCExpression> idims = dims.iterator();
					while (--k >= 0) {
						JCExpression ex = idims.next();
						if (ex == null)
							break;
						JCVariableDecl vd = treeutils.makeIntVarDef(names.fromString("i" + i), null, null);
						decls.add(vd);
						JCExpression ee = treeutils.makeBinary(pos, JCTree.Tag.LE, treeutils.intleSymbol,
								treeutils.makeIntLiteral(pos, 0), treeutils.makeIdent(pos, vd.sym));
						JCExpression eee = treeutils.makeBinary(pos, JCTree.Tag.LT, treeutils.intltSymbol,
								treeutils.makeIdent(pos, vd.sym), copy(ex));
						ee = treeutils.makeAnd(pos, ee, eee);
						range = range == null ? ee : treeutils.makeAnd(pos, range, ee);
						JmlBBArrayAccess aa = new JmlBBArrayAccess(null, expr, treeutils.makeIdent(pos, vd.sym)); // FIXME
																													// -
																													// switch
																													// to
																													// factory
						aa.setPos(p.getPreferredPosition());
						ct = ((Type.ArrayType) ct).getComponentType();
						aa.setType(ct);
						expr = aa;
						i++;
					}
					JCExpression dim = idims.next();
					if (dim != null) {
						JCExpression ex1 = treeutils.makeNotNull(array.pos, expr);
						JCExpression ex2 = treeutils.makeEquality(array.pos, treeutils.makeLength(array, expr), dim);
						JCExpression q = M.at(p).JmlQuantifiedExpr(qforallKind, decls.toList(), range,
								treeutils.makeBitAnd(pos, ex1, ex2));
						q.setType(treeutils.falseLit.type);
						addAssume(array, Label.IMPLICIT_ASSUME, q);
					}

				}
				for (int n = 1; n < dims.length(); n++) {
					int i = 0;
					ListBuffer<JCVariableDecl> decls = new ListBuffer<JCVariableDecl>();
					JCExpression range = null;
					JCExpression expr = copy(array);
					Type ct = array.type;
					int k = n;
					Iterator<JCExpression> idims = dims.iterator();
					JCExpression ex = null;
					while (--k >= 0) {
						ex = idims.next();
						if (ex == null)
							break;
						JCVariableDecl vd = treeutils.makeIntVarDef(names.fromString("i" + i), null, null);
						decls.add(vd);
						JCExpression ee = treeutils.makeBinary(pos, JCTree.Tag.LE, treeutils.intleSymbol,
								treeutils.makeIntLiteral(pos, 0), treeutils.makeIdent(pos, vd.sym));
						JCExpression eee = treeutils.makeBinary(pos, JCTree.Tag.LT, treeutils.intltSymbol,
								treeutils.makeIdent(pos, vd.sym), copy(ex));
						ee = treeutils.makeBitAnd(pos, ee, eee);
						range = range == null ? ee : treeutils.makeBitAnd(pos, range, ee);
						JmlBBArrayAccess aa = new JmlBBArrayAccess(null, expr, treeutils.makeIdent(pos, vd.sym)); // FIXME
																													// -
																													// switch
																													// to
																													// factory
						aa.setPos(p.getPreferredPosition());
						ct = ((Type.ArrayType) ct).getComponentType();
						aa.setType(ct);
						expr = aa;
						i++;
					}
					JCExpression dim = idims.next();
					if (dim != null) {
						JCExpression ex1 = treeutils.makeNotNull(array.pos, expr);
						JCExpression ex2 = treeutils.makeEquality(array.pos, treeutils.makeLength(array, expr), dim);
						JCExpression ex3 = allocCounterEQ(p, copy(expr), ++allocCounter);
						JCExpression q = M.at(p).JmlQuantifiedExpr(qforallKind, decls.toList(), range,
								treeutils.makeBitAnd(pos, ex1, ex2, ex3));
						q.setType(treeutils.falseLit.type);
						addAssume(array, Label.IMPLICIT_ASSUME, q);

						// anti-aliasing assumption, but FIXME: only for the first dimension
						JmlBBArrayAccess aex = (JmlBBArrayAccess) expr;
						JCVariableDecl vd = treeutils.makeIntVarDef(names.fromString("i" + i), null, null);
						decls.add(vd);
						JCExpression ee = treeutils.makeBinary(pos, JCTree.Tag.LE, treeutils.intleSymbol,
								treeutils.makeIntLiteral(pos, 0), treeutils.makeIdent(pos, vd.sym));
						JCExpression eee = treeutils.makeBinary(pos, JCTree.Tag.LT, treeutils.intltSymbol,
								treeutils.makeIdent(pos, vd.sym), copy(ex));
						ee = treeutils.makeBitAnd(pos, ee, eee);
						range = range == null ? ee : treeutils.makeBitAnd(pos, range, ee);
						JmlBBArrayAccess aa = new JmlBBArrayAccess(null, copy(aex.indexed),
								treeutils.makeIdent(pos, vd.sym)); // FIXME - switch to factory
						aa.setPos(p.getPreferredPosition());
						aa.setType(ct);
						ex1 = treeutils.makeNot(array.pos,
								treeutils.makeEquality(array.pos, copy(aex.index), copy(aa.index)));
						ex2 = treeutils.makeImplies(array.pos, ex1,
								treeutils.makeNot(array.pos, treeutils.makeEquality(array.pos, expr, aa)));
						q = M.at(p).JmlQuantifiedExpr(qforallKind, decls.toList(), range, ex2);
						q.setType(syms.booleanType);
						addAssume(array, Label.IMPLICIT_ASSUME, q);
					}

				}
				{ // initialize elements to zero-equivalent value
					int i = 0;
					ListBuffer<JCVariableDecl> decls = new ListBuffer<JCVariableDecl>();
					JCExpression range = null;
					JCExpression expr = copy(array);
					Type ct = array.type;
					for (JCExpression ex : dims) {
						JCVariableDecl vd = treeutils.makeIntVarDef(names.fromString("i" + i), null, null);
						decls.add(vd);
						JCExpression ee = treeutils.makeBinary(pos, JCTree.Tag.LE, treeutils.intleSymbol,
								treeutils.makeIntLiteral(pos, 0), treeutils.makeIdent(pos, vd.sym));
						JCExpression eee = treeutils.makeBinary(pos, JCTree.Tag.LT, treeutils.intltSymbol,
								treeutils.makeIdent(pos, vd.sym), copy(ex));
						ee = treeutils.makeAnd(pos, ee, eee);
						range = range == null ? ee : treeutils.makeAnd(pos, range, ee);
						JmlBBArrayAccess aa = new JmlBBArrayAccess(null, expr, treeutils.makeIdent(pos, vd.sym)); // FIXME
																													// -
																													// switch
																													// to
																													// factory
						aa.setPos(p.getPreferredPosition());
						ct = ((Type.ArrayType) ct).getComponentType();
						aa.setType(ct);
						expr = aa;
						i++;
					}
					if (decls.size() > 0) {
						JCExpression q = M.at(p).JmlQuantifiedExpr(qforallKind, decls.toList(), range,
								treeutils.makeEquality(pos, expr, treeutils.makeZeroEquivalentLit(pos, ct)));
						q.setType(treeutils.falseLit.type);
						addAssume(array, Label.IMPLICIT_ASSUME, q);
					}
				}
			}

		}
	}

	protected JCExpression createNullInitializedArray(Type type, List<JCExpression> dims) {
		DiagnosticPosition pos = methodDecl;
		int p = pos.getPreferredPosition();
		if (!(type instanceof Type.ArrayType)) {
			return treeutils.makeZeroEquivalentLit(p, type);
		} else if (dims.head instanceof JCLiteral) {
			Type ctype = ((Type.ArrayType) type).getComponentType();
			int sz = (Integer) ((JCLiteral) dims.head).value; // FIXME - long?
			JCVariableDecl decl = newTempDecl(methodDecl, type);
			addStat(decl);
			JCIdent id = treeutils.makeIdent(p, decl.sym);
			addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeNeqObject(p, id, treeutils.nullLit));
			newAllocation(pos, id);
			addAssume(id, Label.IMPLICIT_ASSUME,
					treeutils.makeEquality(p, treeutils.makeLength(pos, copy(id)), convertExpr(dims.head)));
			for (int i = 0; i < sz; ++i) {
				JCLiteral index = treeutils.makeIntLiteral(p, i);
				JmlBBArrayAccess aa = new JmlBBArrayAccess(null, id, index); // FIXME - switch to factory
				aa.pos = p;
				aa.setType(ctype);
				aa.arraysId = null;
				JCExpression e = createNullInitializedArray(ctype, dims.tail);
				JCBinary b = treeutils.makeEquality(p, aa, e);
				addAssume(pos, Label.IMPLICIT_ASSUME, b);
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
		result = eresult = isIdOrLit(arg) ? arg : M.at(that).Parens(arg).setType(arg.type);
		treeutils.copyEndPosition(eresult, that);
	}

	// FIXME - check endpos everywhere

	// FIXME - this needs work per the complicated Java conversion rules

	/**
	 * Adds any checks and conversions that Java implicitly applies to convert the
	 * given expression to the given type; the 'expr' argument is already converted.
	 */
	public JCExpression addImplicitConversion(DiagnosticPosition pos, Type annotatedNewtype, JCExpression expr) {
		// if (expr instanceof JCLambda) return expr; // We depend on seeing JCLambda
		// literals so we can't hide them behind a cast, but FIXME: does this cause
		// other problems, what about for MemberReferences?
		Type newtype = annotatedNewtype.stripMetadata();
		Type origtype = convertType(expr.type); // Substitutes type variables

		if (paramActuals_ != null && newtype instanceof Type.TypeVar) {
			JCExpression e = paramActuals_.get(newtype.toString());
			if (e != null) {
				newtype = e.type;
			}
		}

		if (utils.isExtensionValueType(annotatedNewtype)) {
			// converting to a value type
			if (types.isSameType(annotatedNewtype, utils.extensionValueType("string"))
					&& types.isSameType(expr.type, syms.stringType)) {
				// string.string(expr);
				Type.ClassType t = utils.extensionValueType("string");
				JCExpression ty = treeutils.makeType(pos.getPreferredPosition(), t);
				JCExpression e = treeutils.makeMethodInvocation(pos, ty, names.fromString("string"), expr);
				return eresult;
			}
			if (types.isSameType(expr.type, annotatedNewtype)) {
				return eresult;
			}
		}

		// FIXME - change to utils.isPrimitiveType
		boolean isPrim = origtype.isPrimitive() && origtype.getTag() != TypeTag.BOT;
		boolean newIsPrim = newtype.isPrimitive() && newtype.getTag() != TypeTag.BOT;

		// If we are converting from a non-primitive to primitive type (unboxing),
		// check that the expression is not null
		// But we don't unbox for rac for JML types because those are represented as a
		// non-primitive anyway
		if (methodEnv.javaChecks && newIsPrim && !isPrim && (esc || !jmltypes.isJmlType(newtype))) {
			JCExpression e = treeutils.makeNeqObject(pos.getPreferredPosition(), expr, treeutils.nullLit);
			addJavaCheck(pos, e, Label.POSSIBLY_NULL_UNBOX, Label.UNDEFINED_NULL_UNBOX,
					"java.lang.NullPointerException");
		}
		if (rac && origtype.tsym == jmltypes.repSym(jmltypes.BIGINT) && newIsPrim) {
			// For checking reductions of \bigint to regular int in MATH mode
			if (newtype == jmltypes.BIGINT) {
				// continue
			} else if (jmltypes.isIntegral(newtype)) {
				int p = pos.getPreferredPosition();
				JCExpression emax = treeutils.makeUtilsMethodCall(expr.pos, "bigint_le", expr,
						treeutils.makeUtilsMethodCall(expr.pos, "bigint_valueOf",
								treeutils.makeLongLiteral(p, maxValue(p, newtype.getTag()))));
				JCExpression emin = treeutils.makeUtilsMethodCall(expr.pos, "bigint_ge", expr,
						treeutils.makeUtilsMethodCall(expr.pos, "bigint_valueOf",
								treeutils.makeLongLiteral(p, minValue(p, newtype.getTag()))));
				addAssert(expr, Label.ARITHMETIC_CAST_RANGE, emax, newtype.toString() + " overflow");
				addAssert(expr, Label.ARITHMETIC_CAST_RANGE, emin, newtype.toString() + " underflow");
			}
		}
//        if (esc && !useBV && expr.type.getTag() == TypeTag.NONE && newtype.getTag() != TypeTag.NONE) {
//            // For checking reductions of \bigint to regular int in MATH mode
//            int p = pos.getPreferredPosition();
//            JCExpression emax = treeutils.makeBinary(p, JCTree.Tag.LE, expr, 
//                    treeutils.makeLit(p, syms.longType, Long.valueOf(maxValue(p,newtype.getTag()))));
//            JCExpression emin = treeutils.makeBinary(p, JCTree.Tag.LE,  
//                    treeutils.makeLit(p, syms.longType, Long.valueOf(minValue(p,newtype.getTag()))),
//                    expr);
//            addAssert(expr, Label.ARITHMETIC_CAST_RANGE, emax, newtype.toString() + " overflow");
//            addAssert(expr, Label.ARITHMETIC_CAST_RANGE, emin, newtype.toString() + " underflow");
//        }

		if (rac) {
			if ((jmltypes.isSameType(newtype, jmltypes.BIGINT) || newtype.tsym == jmltypes.repSym(jmltypes.BIGINT))
					&& isPrim && !jmltypes.isJmlType(expr.type)) {
				// primitive to BigInteger
				return treeutils.makeUtilsMethodCall(expr.pos, "bigint_valueOf", expr);
			} else if (jmltypes.isSameTypeOrRep(jmltypes.BIGINT, newtype) && !isPrim
					&& !jmltypes.isJmlType(expr.type)) {
				// boxed primitive to BigInteger
				if (jmltypes.isSameTypeOrRep(newtype, expr.type))
					return expr;
				return treeutils.makeUtilsMethodCall(expr.pos, "bigint_valueOfNumber", expr);
			} else if (jmltypes.isSameTypeOrRep(jmltypes.REAL, newtype) && isPrim && !jmltypes.isJmlType(expr.type)) {
				return treeutils.makeUtilsMethodCall(expr.pos, "real_valueOf", expr);
			} else if (expr.type.getKind() == TypeKind.NULL && newtype.getKind() != TypeKind.NULL) {
				expr = M.at(expr).TypeCast(newtype, expr);
				expr.type = newtype;
				return expr;
			} else if (newIsPrim && jmltypes.isSameTypeOrRep(jmltypes.BIGINT, expr.type)
					&& !jmltypes.isSameTypeOrRep(jmltypes.BIGINT, newtype) && !isPrim
					&& currentEnv.arithmeticMode.mode() == Arithmetic.Mode.MATH) {
				// In BIGINT mode, we can be required to cast a bigint value back to a primitive
				// for an assignment
				if (rac) {
					if (newtype.getTag() == TypeTag.LONG)
						expr = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "bigint_tolong", expr)
								.setType(syms.longType);
					else if (newtype.getTag() == TypeTag.FLOAT)
						expr = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "bigint_tofloat", expr)
								.setType(syms.floatType);
					else if (newtype.getTag() == TypeTag.DOUBLE)
						expr = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "bigint_todouble", expr)
								.setType(syms.doubleType);
					else if (newtype == jmltypes.REAL)
						expr = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "bigint_toreal", expr)
								.setType(jmltypes.REAL);
					else
						expr = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "bigint_toint", expr)
								.setType(syms.intType);
				} else if (!rac) { // FIXME - this never happens
					expr = M.at(expr).TypeCast(newtype, expr);
					expr.type = newtype;
				}
				return expr;
			} else if (newIsPrim && jmltypes.isSameTypeOrRep(jmltypes.REAL, expr.type) && !isPrim
					&& currentEnv.arithmeticMode.mode() == Arithmetic.Mode.MATH) {
				// In BIGINT mode, we can be required to cast a real value back to a primitive
				// for an assignment
				if (rac) {
					if (newtype.getTag() == TypeTag.FLOAT)
						expr = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "real_tofloat", expr)
								.setType(syms.floatType);
					else if (newtype.getTag() == TypeTag.DOUBLE)
						expr = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "real_todouble", expr)
								.setType(syms.doubleType);
				} else if (!rac) { // FIXME - this never happens
					expr = M.at(expr).TypeCast(newtype, expr);
					expr.type = newtype;
				}
				return expr;
//            } else if (expr.type.isPrimitive() && newtype.isPrimitive() && expr.type.getTag() > newtype.getTag()) {
//                // TODO: understand - it appears that RAC does not like unnecessary casts - e.g. short to int
//                expr = M.at(expr).TypeCast(newtype,expr);
//                expr.type = newtype;
//                expr = newTemp(expr);
//                return expr; // - need to do casts explicitly at least for op= operations
			} else {
				return expr;// RAC handles implicit conversions implicitly
			}
		}

		if (types.isSameType(newtype, expr.type.stripMetadata()))
			return expr;
		if (expr.type.getTag() == TypeTag.BOT || (expr instanceof JCLiteral && ((JCLiteral) expr).value == null))
			return expr;

//        Type unboxed = unboxedType(expr.type);
//        int tag = unboxed.getTag();
//        String methodName =
//                tag == TypeTag.INT ? "intValue" :
//                tag == TypeTag.SHORT ? "shortValue" :
//                tag == TypeTag.LONG ? "longValue" :
//                tag == TypeTag.BOOLEAN ? "booleanValue" :
//                tag == TypeTag.DOUBLE ? "doubleValue" :
//                tag == TypeTag.FLOAT ? "floatValue" :
//                tag == TypeTag.BYTE ? "byteValue" :
//                tag == TypeTag.CHAR ? "charValue" : "";
//                ;
//        JCIdent id = M.Ident(names.fromString(methodName));
		if (newIsPrim && !isPrim) {
			if (expr.type instanceof Type.TypeVar) {
				// FIXME: This is a hack - should really translate the typevar
				expr.type = boxedType(annotatedNewtype.stripMetadata());
			}
			JCExpression mth = createUnboxingExpr(expr);
			if (translatingJML || mth instanceof JCIdent) {
				eresult = mth;
			} else {
				eresult = newTemp(mth);
			}
			isPrim = true;
			expr = eresult;
			if (types.isSameType(newtype, eresult.type))
				return expr;
		}
		// Don't do casts to a base type
		if (!isPrim && !newIsPrim) {
			Type t = expr.type.stripMetadata();
			if (!(t instanceof Type.ForAll)) {
				if (types.isSubtype(t, newtype))
					return expr;
			} else {
				if (newtype == syms.objectType)
					return expr;
				// FIXME - should do a better job of detecting subtypes for parameterized types
			}
		}

		if (!newIsPrim && isPrim) {
			// boxing: Integer = int and the like

			JCExpression id = createBoxingStatsAndExpr(expr, newtype, true);
			eresult = id;

		} else {
			JCTypeCast t = M.at(pos).TypeCast(newtype, expr);
			t.clazz.type = newtype;
			t.type = newtype;
//            if (!jmltypes.isIntegral(newtype) && jmltypes.isIntegral(origtype)) {
//                JCExpression ee = M.Apply(null, fn, args)
//            }
			eresult = t;
			// FIXME - for integer promotions, add assumptions about range of value
		}
		return eresult;
	}

	/**
	 * If the argument is a reference type with an unboxed version (e.g. Integer ->
	 * int) then returns the unboxed type, otherwise returns the argument.
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
		boolean useMethod = false;
		ClassType origtype = (ClassType) convertType(expr.type);
		specs.getAttrSpecs((ClassSymbol) origtype.tsym); // To ensure that model fields are loaded
		Type unboxed = unboxedType(expr.type);
		TypeTag tag = unboxed.getTag();
		String origtypeString = origtype.tsym.getSimpleName().toString();
		if (rac || useMethod) {
			String methodName = unboxed.toString() + "Value";

			Name id = names.fromString(methodName);
			MethodSymbol msym = getMethod(expr.type, id);
			if (msym == null) {
				utils.error(expr, "jml.message", "Could not find method " + methodName);
				// ERROR - throw something
			}

			JCFieldAccess receiver = M.at(expr).Select(expr, id);
			receiver.type = msym.type;
			receiver.sym = msym;

			JCMethodInvocation call = M.at(expr).Apply(List.<JCExpression>nil(), receiver, List.<JCExpression>nil());
			call.setType(unboxed);
			boolean saved = alreadyConverted;
			alreadyConverted = true;
			try {
				// FIXME - explain what happens when alreadyCOnverted is set
				return convertExpr(call);
			} finally {
				alreadyConverted = saved;
			}
		} else { // use model field
			String fieldName = "the" + origtypeString;
			if (origtypeString.equals("BigInteger"))
				fieldName = "value";
			Name id = names.fromString(fieldName);
			Type t = expr.type;
			specs.getAttrSpecs((ClassSymbol) t.tsym);
			VarSymbol fsym = getField(t, id);
			if (fsym != null)
				specs.getAttrSpecs(fsym);

			if (fsym == null) {
				utils.error(expr, "jml.message", "Could not find model field " + fieldName + " in " + origtypeString);
				// ERROR - throw something
			}
			JCExpression fa = M.at(expr).Select(expr, fsym);
			fa.setType(unboxed);
			return fa;
		}
	}

	protected boolean alreadyConverted = false;

	// Presume exactly one element with thast name
	protected MethodSymbol getMethod(Type type, Name nm) {
		Iterator<Symbol> iter = type.tsym.members().getSymbolsByName(nm).iterator();
		if (iter.hasNext())
			return (MethodSymbol) iter.next();
		return null;
	}

	// Presume exactly one element with that name
	protected VarSymbol getField(Type type, Name nm) {
		Iterator<Symbol> iter = type.tsym.members().getSymbolsByName(nm).iterator();
		if (iter.hasNext())
			return (VarSymbol) iter.next();
		return null;
	}

	protected JCExpression createBoxingStatsAndExpr(JCExpression expr, Type newtype, boolean alreadyConverted) {
		TypeTag tag = expr.type.getTag();
		newtype = boxedType(expr.type);
//        String methodName =
//                tag == TypeTag.INT ? "intValue" :
//                tag == TypeTag.SHORT ? "shortValue" :
//                tag == TypeTag.LONG ? "longValue" :
//                tag == TypeTag.BOOLEAN ? "booleanValue" :
//                tag == TypeTag.DOUBLE ? "doubleValue" :
//                tag == TypeTag.FLOAT ? "floatValue" :
//                tag == TypeTag.BYTE ? "byteValue" :
//                tag == TypeTag.CHAR ? "charValue" : "";
//                ;
//        Name id = names.fromString(methodName);
//        MethodSymbol msym = getMethod(newtype,id);
		addStat(comment(expr, "Boxing an " + expr.type, log.currentSourceFile()));

		// Create a temporary that is the boxed value; assume it is non-null
		JCIdent tmp = newTemp(expr.pos(), newtype); // the result - uninitialized id of type 'newtype'
		addNullnessTypeConditionId(tmp, expr, tmp.sym, true, false);

//        JCFieldAccess receiver = M.at(expr).Select(tmp, id);
//        receiver.type = msym.type;
//        receiver.sym = msym;
//        JCMethodInvocation call = M.at(expr).Apply(List.<JCExpression>nil(), receiver, List.<JCExpression>nil());
//        call.setType(expr.type); // Note: no symbol set, OK since this is esc

		// Equate the unboxed value of tmp to 'expr'
		// 'createUnboxingExpr' might use a method call (e.g. intValue()) or a field
		// (e.g. theInteger)
		JCExpression unboxedExpr = createUnboxingExpr(tmp);
		JCExpression e = treeutils.makeEquality(expr.pos, unboxedExpr, expr);
		addAssume(expr, Label.IMPLICIT_ASSUME, alreadyConverted ? e : convertExpr(e));

		// assume the type conditions about the boxed value
		addAssume(expr, Label.IMPLICIT_ASSUME, treeutils.makeDynamicTypeEquality(expr,
				treeutils.makeIdent(expr.getPreferredPosition(), tmp.sym), newtype));
		return tmp;

	}

	// FIXME - document
	JCTree lastStat;

	protected void checkRW(IJmlClauseKind rw, Symbol sym, JCExpression th, DiagnosticPosition p) {
		if (!translatingJML && methodDecl != null) {
			if (sym instanceof VarSymbol && sym.owner instanceof TypeSymbol) {
				Label lab = rw == readableClause ? Label.READABLE : Label.WRITABLE;
				FieldSpecs fs = specs.getAttrSpecs((VarSymbol) sym);
				if (fs != null)
					for (JmlTypeClause clause : fs.list) {
						if (clause.clauseType == rw) {
							JCExpression ee = ((JmlTypeClauseConditional) clause).expression;
							JCExpression saved = currentEnv.currentReceiver;
							try {
								currentEnv.currentReceiver = th;
								ee = convertJML(ee);
							} finally {
								currentEnv.currentReceiver = saved;
							}
							ee = conditionedAssertion(ee, ee);
							ee = makeAssertionOptional(ee);
							addAssert(p, lab, ee, clause, clause.source(), utils.qualifiedName(sym));
						}
					}
			}
		}
	}

	protected boolean translatingLHS = false;

	// Havocs all containing model fields. FIXME - need to substitute 'this' by the
	// recevier of newfa.
	public void havocModelFields(JCFieldAccess fa) {
		havocModelFields(fa.pos, fa.selected, (VarSymbol) fa.sym);
	}

	public void havocModelFields(int pos, JCExpression recv, VarSymbol sym) {
		if (rac)
			return;
		ListBuffer<JCExpression> havocList = new ListBuffer<>();
		havocModelFields(recv, sym, havocList);
		addStat(comment(null, "Model fields for " + sym + ": " + havocList, null));
		addStat(M.at(pos).JmlHavocStatement(havocList.toList()));
	}

	private void havocModelFields(JCExpression recv, VarSymbol sym, ListBuffer<JCExpression> havocList) {
		FieldSpecs fspecs = specs.getAttrSpecs(sym);
		if (fspecs != null)
			for (JmlTypeClause tc : fspecs.list) {
				if (tc.clauseType == inClause) {
					JmlTypeClauseIn tcin = (JmlTypeClauseIn) tc;
					for (JmlGroupName g : tcin.list) {
						JCFieldAccess fa = treeutils.makeSelect(g.pos, recv, g.sym);
						if (!isDataGroup(fa.type))
							havocList.add(fa);
						havocModelFields(fa.selected, (VarSymbol) fa.sym, havocList);
					}
				}
			}
	}

	public JCExpression convertLHS(JCExpression lhs) {
		if (lhs instanceof JCIdent) {
			translatingLHS = true;
			JCExpression tlhs = convertExpr(lhs);
			translatingLHS = false;
			return tlhs;
		} else {
			utils.error(lhs, "jml.message", "Not implemented in convertLHS");
			return null;
		}
	}

	public void assignIdentHelper(DiagnosticPosition pos, JCIdent id, JCExpression origrhs, JCExpression lhs,
			JCExpression rhs) {

		Symbol.VarSymbol vsym = (Symbol.VarSymbol) id.sym;
//      specs.getSpecs(vsym).  // FIXME - need to call isNonNull with the declaration for id
		if (!infer && specs.isNonNull(vsym)) { // && !(rac &&
												// vsym.type.tsym.toString().equals("org.jmlspecs.runtime.IJMLTYPE"))) {
			if (rhs instanceof JCTree.JCMemberReference) {
				// Need to check that the spec of the reference is subsumed in the spec of the
				// type (that.type) inferred by type checking
				checkCompatibleSpecs((JCTree.JCMemberReference) rhs, rhs.type);
			} else if (rhs instanceof JCLambda) {
				// Need to check that the spec of the reference is subsumed in the spec of the
				// type (that.type) inferred by type checking
				checkCompatibleSpecs((JCLambda) rhs, rhs.type);
			} else if (!isKnownNonNull(origrhs)) {
				JCExpression e = treeutils.makeNeqObject(pos.getPreferredPosition(), rhs, treeutils.nullLit);
				// FIXME - location of nnonnull declaration?
				addAssert(pos, Label.POSSIBLY_NULL_ASSIGNMENT, e);
			}
		}
		// checkAccess(assignableClauseKind, pos, id, lhs, classDecl.type,
		// currentEnv.currentReceiver, currentEnv.currentReceiver);
		boolean constructorField = id.sym.owner instanceof TypeSymbol && methodDecl.sym.isConstructor()
				&& !id.sym.isStatic();
		if (!constructorField) checkAccess2(assignableClauseKind, pos, id, lhs, true, treeutils.trueLit, true, null, false);
		checkRW(writableClause, id.sym, currentEnv.currentReceiver, id);

		JCExpressionStatement st = treeutils.makeAssignStat(pos.getPreferredPosition(), lhs, rhs);
        JmlLabeledStatement stt = markUniqueLocation(st);
        addStat(stt);
		lastStat = st.expr;
		JCExpression r = lhs;

		if (splitExpressions && !(lhs instanceof JCIdent)) {
			r = newTemp(copy(lhs));
		}
		if (lhs instanceof JCFieldAccess)
			havocModelFields((JCFieldAccess) lhs);
		
		saveMappingOverride(id, eresult);
        // Don't change heap state if the assignment is just to a local variable or a
        // formal parameter
		Symbol owner = id.sym.owner;
		if (owner == null || owner instanceof Symbol.MethodSymbol) { // FIXME - clarify when the owner is null
		    ;
		} else {
		    changeState(pos, List.<StoreRefGroup>of(convertFrameConditionList(pos, treeutils.trueLit, List.<JCExpression>of(id))), stt.label);
		}
		result = eresult = r;
	}
	
	/** Checks the access of lhsUnconverted (with a 'this' which is currentTheExpr)
	 *  against the assignable or accessible clauses (per 'kind') of the current TanslationEnv (or the caller's env if 'targetEnv' is null)
	 *  That env holds the methodSym from which to get the specification and the receiver to use as 'this' for those specifications.
	 * @param kind
	 * @param pos
	 * @param lhsUnconverted
	 * @param lhs
	 * @param isConverted
	 * @param guard
	 * @param emitAsserts
	 * @param targetEnv
	 * @return
	 */
	public JCExpression checkAccess2(IJmlClauseKind kind, DiagnosticPosition pos, JCExpression lhsUnconverted, JCExpression lhs,
			boolean isConverted, JCExpression guard, boolean emitAsserts, TranslationEnv targetEnv, boolean comparingToCallee) {
		//System.out.println("CHECKACCESS@ " + lhsUnconverted + " " + lhs + " " + guard + " " + emitAsserts + " " + targetEnv);
		JCExpression okCondition = emitAsserts ? null : treeutils.makeBooleanLiteral(pos, true);
		if (rac) return okCondition;
		TranslationEnv callerEnv = currentEnv.pushEnvCopy();
		callerEnv.currentReceiver = explicitThisId;
		callerEnv.stateLabel = attr.preLabel;
		callerEnv.allocCount = 0;
		callerEnv.methodSym = methodDecl.sym;
		if (targetEnv == null) targetEnv = callerEnv;
		//System.out.println("ENV " + (targetEnv==callerEnv) + " " + targetEnv.receiver + " " + callerEnv.receiver + " " + currentEnv.currentReceiver);
        //System.out.println("THIS " + currentEnv.currentReceiver + " " + targetEnv.receiver);
		MethodSymbol methodSym = targetEnv.methodSym;
		JavaFileObject prev = log.currentSourceFile();
		try {
			//System.out.println("CA2 " + lhs + " " + lhs.getClass() + " " + methodSym + " " + methodSym.isConstructor() + " " + targetEnv.receiver + " " + methodSym.owner);
			if (lhs instanceof JCIdent id && id.sym.owner instanceof ClassSymbol && methodSym.isConstructor()) return okCondition;// OK to set a field of 'this' inside a constructor
			var srlist = lhs instanceof JmlStoreRef j ? List.<JmlStoreRef>of(j) : makeJmlStoreRef(pos, lhs, (ClassSymbol)methodSym.owner, false);
			var kindLabel = kind == assignableClauseKind ? Label.ASSIGNABLE
					: kind == accessibleClauseKind ? Label.ACCESSIBLE
							: kind == capturesClauseKind ? Label.CAPTURES : Label.UNKNOWN;
			//System.out.println("CA2-A " + lhs +  " " + srlist);
			for (var sr: srlist) {
				for (MethodSymbol parentMethodSym : utils.parents(methodSym,true)) {
					//System.out.println("CA2-B " + parentMethodSym);
					if (parentMethodSym.params == null) continue; // FIXME - we should do something better? or does this mean binary with no
					// specs?
					JmlMethodSpecs denestedSpecs = JmlSpecs.instance(context).getDenestedSpecs(parentMethodSym);
					// System.out.println("ADDPRE " + methodDecl.sym + " " + parentMethodSym.owner +
					// " " + parentMethodSym + " # " + denestedSpecs);
					if (denestedSpecs == null) continue;
					//System.out.println("CA2-C " + parentMethodSym);
					// denestedSpecs.decl.params.forEach(p -> System.out.println(" PARAM " + p.name
					// + " " + p.type + " " + p.sym.name + " " + p.sym.type));
					// denestedSpecs.decl.sym.params.forEach(p -> System.out.println(" PARAM-SYM " +
					// p + " " + p.hashCode() + " " + p.name + " " + p.type));

					// Set up the map from parameter symbol of the overridden method to
					// corresponding parameter of the target method.
					// We need this even if names have not changed, because the parameters
					// will have been attributed with different symbols.
					//paramActuals = specParamsToActuals(denestedSpecs, methodDecl, parentMethodSym);
					//System.out.println("PARAMACTUALS-BA " + paramActuals);
//					var oldMap = mapFormals(methodDecl, denestedSpecs.decl);
					//System.out.println("PARAMACTUALS-BB " + paramActuals);
					// heapCount = preheapcount;
					elseExpression = treeutils.falseLit;
					try {
						for (JmlSpecificationCase specCase : denestedSpecs.cases) {

							if (!doSpecificationCase(methodDecl, methodSym, parentMethodSym, specCase)) continue; // FIXME - something different for targetENv
							log.useSource(specCase.source());
							JCExpression precondition = !comparingToCallee ? preconditions.get(specCase): calleePreconditions.get(specCase); // FIXME - a hack
							//System.out.println("SPECCASE PRE " + precondition);
							if (precondition == null) {
								if (!parentMethodSym.owner.isAnonymous()) {
								    System.out.println("NULL PRECONDITION FOR " + methodDecl.sym.owner + "." + methodDecl.sym + " " + methodSym.owner + "." + methodSym + " " + (methodDecl.sym == methodSym) + " " + parentMethodSym.owner + "." + parentMethodSym + " " + (methodSym==parentMethodSym) + " " + specCase);
								}
								precondition = treeutils.trueLit; // Not correct, but just error recovery
								// FIXME - this can happen during assignable and accessible checking for a method called in a precondition
							}
							precondition = treeutils.makeAndSimp(precondition,  guard, precondition);
							for (var clause : specCase.clauses) {
								if (clause.clauseKind == kind) {
									if (emitAsserts) pushBlock();
									var lsexpr = convertAssignableToLocsetExpression(clause,
											((JmlMethodClauseStoreRef) clause).list, (ClassSymbol) methodSym.owner,
											targetEnv.currentReceiver);
									//System.out.println("CHECKING " + sr + " WITH " + currentEnv.currentReceiver + " VS " + clause + " IN " + parentMethodSym.owner + ":" + parentMethodSym + " " + kind + " " + lsexpr);
									JCExpression ss = treeutils.makeSubset(sr, sr, lsexpr);
									JCExpression convertedCondition = simplifySubset(ss, targetEnv, isConverted);
									if (!emitAsserts) {
										convertedCondition = treeutils.makeImplies(pos, precondition, convertedCondition);
										okCondition = treeutils.makeAndSimp(pos,  okCondition,  convertedCondition);
									} else {
										convertedCondition = conditionedAssertion(convertedCondition, convertedCondition); // FIXME - verify that we need this
										if (!treeutils.isTrueLit(convertedCondition)) {
											convertedCondition = makeAssertionOptional(convertedCondition);
											//System.out.println("Assertion checking if " + lhsUnconverted + " is in " + clause + " : " + convertedCondition);
											addStat(comment(pos, "Assertion checking if " + lhsUnconverted + " is in " + clause, clause.sourcefile));
											var sst = addAssert(pos, kindLabel, convertedCondition, clause, clause.sourcefile, lhsUnconverted);
											var bl = popBlock(clause);
											addStat(M.at(clause).If(precondition, bl, null));
                                        } else {
                                            var bl = popBlock(clause);
                                            addStat(comment(pos, "Assertion checking if " + lhsUnconverted + " is in " + clause + " <<< always true", clause.sourcefile));                                            
                                        }
									}
								}
							}
						}
					} finally {
//						paramActuals = oldMap;
						//System.out.println("PARAMACTUALS-C " + paramActuals);
					}
				}
			}
			return okCondition;
		} finally {
			callerEnv.popEnv();
			log.useSource(prev);
		}
	}

	// FIXME - review
	@Override
	public void visitAssign(JCAssign that) {
		//System.out.println("VISITASSIGN " + oldenv);
		if (that.lhs instanceof JmlTuple) {
			java.util.List<JCExpression> lhss = new ArrayList<>();
			for (JCExpression lhs : ((JmlTuple) that.lhs).values) {
				lhss.add(convertLHS(lhs));
			}
			if (that.rhs instanceof JmlTuple) {
				java.util.List<JCExpression> rhss = new ArrayList<>();
				int i = 0;
				for (JCExpression rhs : ((JmlTuple) that.rhs).values) {
					JCExpression convertedRhs = convertExpr(rhs);
					JCExpression convertedLhs = lhss.get(i++);
					convertedRhs = addImplicitConversion(convertedLhs, convertedLhs.type, convertedRhs);
					rhss.add(convertedRhs);
				}
				i = 0;
				for (JCExpression rhs : ((JmlTuple) that.rhs).values) {
					JCExpression convertedRhs = rhss.get(i);
					JCExpression convertedLhs = lhss.get(i++);
					JCIdent id = (JCIdent) convertedLhs;
					assignIdentHelper(that, id, rhs, convertedLhs, convertedRhs);
				}
			} else {
				java.util.List<JCExpression> rhss = new ArrayList<>();
				int i = 0;
				JCExpression convertedRhs = convertExpr(that.rhs);
				for (JCExpression lhs : ((JmlTuple) that.lhs).values) {
					JCExpression convertedLhs = lhss.get(i++);
					convertedRhs = addImplicitConversion(convertedLhs, convertedLhs.type, convertedRhs);
					rhss.add(convertedRhs);
				}
				i = 0;
				for (JCExpression lhs : ((JmlTuple) that.lhs).values) {
					convertedRhs = rhss.get(i);
					JCExpression convertedLhs = lhss.get(i++);
					JCIdent id = (JCIdent) convertedLhs;
					assignIdentHelper(that, id, that.rhs, convertedLhs, convertedRhs);
				}

			}
			return;
		}
		if (that.lhs instanceof JCIdent id) {
			translatingLHS = true;
			JCExpression convertedLhs = convertExpr(copy(that.lhs));
			translatingLHS = false;
			JCExpression convertedRhs = convertExpr(that.rhs);
			convertedRhs = addImplicitConversion(that, convertedLhs.type, convertedRhs);

			assignIdentHelper(that, id, that.rhs, convertedLhs, convertedRhs);
			saveMappingOverride(that, eresult);

		} else if (that.lhs instanceof JCFieldAccess fa) {
			JCFieldAccess newfa;
			if (!utils.isJMLStatic(fa.sym)) {
				//System.out.println("VISIT-ASSIGN_FA " + that + " " + oldenv);
				JCExpression obj = convertExpr(fa.selected);
				if (!utils.isExtensionValueType(fa.selected.type)) {
					JCExpression e = treeutils.makeNeqObject(obj.pos, obj, treeutils.nullLit);
					addJavaCheck(that.lhs, e, Label.POSSIBLY_NULL_DEREFERENCE, Label.UNDEFINED_NULL_DEREFERENCE,
							"java.lang.NullPointerException");
					if (!infer) {
						checkRW(writableClause, fa.sym, obj, fa);
					}
				}

				newfa = treeutils.makeSelect(that.pos, copy(obj), fa.sym);

				// Map<JCTree,Integer> table = log.currentSource().getEndPosTable();
				// log.noticeWriter.println("FA " + fa.getStartPosition() + " " +
				// fa.getEndPosition(table) + " " + newfa.getStartPosition() + " " +
				// newfa.getEndPosition(table));
			} else {
				// We must evaluate the fa.lhs if it is an expression and not a type,
				// even though the value is not used (and might even be null)
				if (!treeutils.isATypeTree(fa.selected)) {
					scan(fa.selected);
				}
				// If the field is static, substitute the type tree

				JCExpression obj = treeutils.makeType(fa.getStartPosition(), fa.sym.owner.type);
				if (!infer) {
					checkRW(writableClause, fa.sym, obj, fa);
				}
				newfa = treeutils.makeSelect(that.pos, obj, fa.sym);

			}
			JCExpression rhs = convertExpr(that.rhs);
			rhs = addImplicitConversion(that, that.lhs.type, rhs);
			if (rhs instanceof JCTree.JCMemberReference) {
				// Need to check that the spec of the reference is subsumed in the spec of the
				// type (that.type) inferred by type checking
				checkCompatibleSpecs((JCTree.JCMemberReference) rhs, rhs.type);
			} else if (rhs instanceof JCLambda) {
				// Need to check that the spec of the reference is subsumed in the spec of the
				// type (that.type) inferred by type checking
				checkCompatibleSpecs((JCLambda) rhs, rhs.type);
			} else {
				if (specs.isNonNull(fa.sym)) {
					JCExpression e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nullLit);
					// FIXME - location of nnonnull declaration?
					addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e);
				}
			}
			boolean constructorField = fa.sym.owner instanceof TypeSymbol && methodDecl.sym.isConstructor()
					&& !utils.isJMLStatic(fa.sym);
			if (!constructorField) checkAccess2(assignableClauseKind, that, fa, newfa, true, treeutils.trueLit, true, null, false);

			// FIXME _ use checkAssignable
			// checkAccess(assignableClauseKind, that, fa, newfa, methodDecl.sym.owner.type,
			// currentEnv.currentReceiver, currentEnv.currentReceiver); // FIXME - should the second argument be
			// newfa?

			JCExpressionStatement st = treeutils.makeAssignStat(that.pos, newfa, rhs);
			JmlLabeledStatement stt = markUniqueLocation(st);
			addStat(stt);
			lastStat = st.expr;
			saveMapping(that, st.expr);
			var saved = newTemp(newfa);
			havocModelFields(newfa);
			saveMapping(that.lhs, eresult);
	        if (!rac) changeState(that, List.<StoreRefGroup>of(convertFrameConditionList(that, treeutils.trueLit, List.<JCExpression>of(newfa))), stt.label);
	        result = eresult = saved;
	        
		} else if (that.lhs instanceof JCArrayAccess aa) {
			// that.lhs.getPreferredPosition() is the position of the [ in
			// the array access expression
			JCExpression array = convertExpr(aa.indexed);
			JCExpression e;
			if (!utils.isJavaOrJmlPrimitiveType(aa.indexed.type)) {
				e = treeutils.makeNeqObject(array.pos, array, treeutils.nullLit);
				addJavaCheck(aa, e, Label.POSSIBLY_NULL_DEREFERENCE, Label.UNDEFINED_NULL_DEREFERENCE,
						"java.lang.NullPointerException");
			}
			JCExpression index = convertExpr(aa.index);
			if (array.type instanceof Type.ArrayType) {
				index = addImplicitConversion(index, syms.intType, index);
				e = treeutils.makeBinary(index.pos, JCTree.Tag.GE, index, treeutils.zero);
				addJavaCheck(aa, e, Label.POSSIBLY_NEGATIVEINDEX, Label.UNDEFINED_NEGATIVEINDEX,
						"java.lang.ArrayIndexOutOfBoundsException");

				JCFieldAccess newfa = treeutils.makeLength(array, array);
				e = treeutils.makeBinary(index.pos, JCTree.Tag.GT, newfa, index);
				addJavaCheck(aa, e, Label.POSSIBLY_TOOLARGEINDEX, Label.UNDEFINED_TOOLARGEINDEX,
						"java.lang.ArrayIndexOutOfBoundsException");

				JCArrayAccess newfaa = M.at(that.pos).Indexed(array, index);
				newfaa.setType(that.type);

				// FIXME - test this
				if (!infer) {
					checkAccess2(assignableClauseKind, that, that.lhs, newfaa, true, treeutils.trueLit, true, null, false);
					// checkAccess(assignableClauseKind, that, aa, newfaa,
					// methodDecl.sym.owner.type, currentEnv.currentReceiver, currentEnv.currentReceiver);
				}
			} else if (jmltypes.isIntArray(array.type)) {
				index = addImplicitConversion(index, jmltypes.BIGINT, index);
			}

			JCExpression rhs = convertExpr(that.rhs);
			rhs = addImplicitConversion(rhs, that.lhs.type, rhs);
			if (array.type instanceof Type.ArrayType) {
				var atype = (Type.ArrayType) array.type;
				if (specs.isNonNull(atype.elemtype, (ClassSymbol)enclosingClass)) { // FIXME - need the enclosing class at the
																			// point of declaration
					e = treeutils.makeNeqObject(that.rhs.pos, rhs, treeutils.nullLit);
					addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e);
				}
			}

			if (methodEnv.javaChecks && jmltypes.isArray(array.type) && !jmltypes.elemtype(array.type).isPrimitive()) {
				if (esc) {
					JCExpression rhstype = treeutils.makeTypeof(rhs);
					JCExpression lhselemtype;
					if (array.type instanceof Type.ArrayType) {
						lhselemtype = treeutils.makeJmlMethodInvocation(array, elemtypeKind, jmltypes.TYPE,
								treeutils.makeTypeof(array));
					} else {
						lhselemtype = treeutils
								.makeTypelc(treeutils.makeType(array.pos, jmltypes.elemtype(array.type)));
					}
					JCExpression sta = treeutils.makeSubtype(array, rhstype, lhselemtype);
					JCExpression rhsnull = treeutils.makeEqNull(rhs.pos, rhs);
					addJavaCheck(that, treeutils.makeOr(sta.pos, rhsnull, sta), Label.POSSIBLY_BAD_ARRAY_ASSIGNMENT,
							Label.POSSIBLY_BAD_ARRAY_ASSIGNMENT, "java.lang.ArrayStoreException");
				} else if (rac) {
					// FIXME - I don't think this is checkable
//                    JCExpression rhstype = treeutils.makeTypeof(rhs);
//                    JCExpression lhselemtype = treeutils.makeJmlMethodInvocation(array,JmlToken.BSELEMTYPE,jmltypes.TYPE, 
//                            treeutils.makeTypeof(array));
//                    JCExpression sta = treeutils.makeJmlMethodInvocation(array,JmlToken.SUBTYPE_OF,syms.booleanType,rhstype,lhselemtype);
//                    JCExpression rhsnull = treeutils.makeEqNull(rhs.pos, rhs);
//                    addAssert(that, Label.POSSIBLY_BAD_ARRAY_ASSIGNMENT, treeutils.makeOr(sta.pos,rhsnull,sta));
				}
			}

			JCArrayAccess lhs = new JmlBBArrayAccess(null, array, index);
			lhs.pos = aa.pos;
			lhs.type = aa.type;
			JCExpressionStatement st = treeutils.makeAssignStat(that.pos, lhs, rhs);
            JmlLabeledStatement stt = markUniqueLocation(st);
			addStat(st);
			lastStat = st.expr;
			saveMapping(that, st.expr);
			var saved = newTemp(lhs);
			saveMapping(that.lhs, eresult);
            if (!rac) changeState(that, List.<StoreRefGroup>of(convertFrameConditionList(that, treeutils.trueLit, List.<JCExpression>of(lhs))), stt.label);
            result = eresult = saved;

		} else {
			error(that, "An unknown kind of assignment seen in JmlAssertionAdder: " + that.lhs.getClass());
		}
	}

	// OK
	@Override
	public void visitAssignop(JCAssignOp that) {
		visitAssignopHelper(that, false);
	}

	// OK
	protected void visitAssignopHelper(JCAssignOp that, boolean post) {
		JCExpression lhs = that.lhs;
		JCExpression rhs = that.rhs;
		JCTree.Tag op = that.getTag().noAssignOp();
		if (types.isSameType(that.type, syms.stringType)) {
			JCExpression rhs1 = copy(lhs);
			JCBinary bin = treeutils.makeBinary(that.pos, op, rhs1, rhs);
			bin.operator = that.operator;
			JCAssign e = treeutils.makeAssign(that.pos, lhs, bin);
			e.type = that.type;
			visitAssign(e);
			// TODO: Check mappings for trace and counterexample
			return;
		}
		boolean arith = op == JCTree.Tag.PLUS || op == JCTree.Tag.MINUS || op == JCTree.Tag.MUL || op == JCTree.Tag.DIV
				|| op == JCTree.Tag.MOD;
		boolean lhsscanned = false;
		if (lhs instanceof JCIdent) {
			// Note checkRW is called during the following convertExpr
			lhs = convertLHS(lhs); // This may no longer be a JCIdent (e.g. f may become this.f or T.f)
			lhsscanned = true;
		}
//        if (!lhs.type.isPrimitive() && rhs.type.isPrimitive()) {
//            // FIXME - this is still not quite right if either lhs or rhs needs implicit conversion to int or long
//            // FIXME - also this results in any computations in the lhs being performed twice
//            JCExpression lcast = M.at(lhs.pos).TypeCast(rhs.type, lhs).setType(rhs.type);
//            JCExpression newop = M.at(that.pos).Binary(op, lcast, rhs).setType(rhs.type);
//            JCExpression rcast = M.at(that.pos).TypeCast(lhs.type, newop).setType(lhs.type);
//            rcast = M.at(that.pos).Assign(lhs,rcast).setType(that.type);
//            result = eresult = convert(rcast);
//            return;
//        }
		Type maxJmlType = that.lhs.type;
		if (jmltypes.isJmlType(that.rhs.type))
			maxJmlType = that.rhs.type;
		Type optype = treeutils.opType(that.lhs.type, that.rhs.type);
		// FIXME - the following gives \bigint+\bigint instead of int+int for optype=int
		// -- why?
		// var newOperator =
		// JmlResolve.instance(context).resolveBinaryOperator(that,op,Enter.instance(context).getEnv((ClassSymbol)enclosingClass),optype,optype);
		var newOperator = JmlOperators.instance(context).resolveBinary(that, op, optype, optype);
//        System.out.println("OPTYPE " + op + " " + optype + " " + newOperator);
		if (lhs instanceof JCIdent) {
			// We start with: id = expr
			// We generate
			// ... statements for the subexpressions of lhs (if any)
			// ... statements for the subexpressions of expr
			// temp = lhs' op rhs'
			// lhs' = temp

			Type t = unboxedType(that.type);

			JCExpression lhsc = addImplicitConversion(lhs, optype, convertExpr(copy(that.lhs)));

			rhs = convertExpr(rhs);
			rhs = addImplicitConversion(rhs, optype, rhs); // or optype?

			addBinaryChecks(that, op, lhsc, rhs, maxJmlType); // includes implicit conversion

			rhs = makeBin(that, op, newOperator, lhsc, rhs, maxJmlType);
			treeutils.copyEndPosition(rhs, that);

			if (arith && rhs instanceof JCBinary) {
				// FIXME - this is going to call checkRW again, already called during
				// convertExpr(rhs) above
				rhs = currentEnv.arithmeticMode.rewriteBinary(this, (JCBinary) rhs, true);
			}

			checkAccess2(assignableClauseKind, that, lhs, lhs, false, treeutils.trueLit, true, null, false);
			// checkAccess(assignableClauseKind, that, lhs, lhs, methodDecl.sym.owner.type,
			// currentEnv.currentReceiver, currentEnv.currentReceiver);
			checkRW(writableClause, ((JCIdent) lhs).sym, currentEnv.currentReceiver, lhs);

			// Note that we need to introduce the temporary since the rhs contains
			// identifiers that may be captured by the lhs. - TODO - need an example?
			JCIdent id = newTemp(rhs);
			JCExpression newlhs = treeutils.makeIdent(lhs.pos, ((JCIdent) lhs).sym);
			JCExpression nid = addImplicitConversion(id, lhs.type, id);
			JCExpressionStatement st = treeutils.makeAssignStat(that.getStartPosition(), newlhs, nid);
            JmlLabeledStatement stt = markUniqueLocation(st);
            addStat(st);
			var savedResult = post ? newTemp(lhs) : newlhs;
			saveMapping(that.lhs, eresult);
			var sym = ((JCIdent) lhs).sym;
			if (sym.owner instanceof ClassSymbol) {
				havocModelFields(that.pos, currentEnv.currentReceiver, (VarSymbol) sym);
			}
			lastStat = st.expr;
	        // Don't change heap state if the assignment is just to a local variable
			if (!(that.lhs instanceof JCIdent && ((JCIdent) that.lhs).sym.owner instanceof Symbol.MethodSymbol)) {
			    changeState(that, List.<StoreRefGroup>of(convertFrameConditionList(that, treeutils.trueLit, List.<JCExpression>of(that.lhs))), stt.label);
			}
            result = eresult = savedResult;
			
		} else if (lhs instanceof JCFieldAccess fa) {
			JCFieldAccess newfa;
			if (utils.isJMLStatic(fa.sym)) {
				if (!lhsscanned && !treeutils.isATypeTree(fa.selected))
					convertExpr(fa.selected);
				JCExpression typetree = treeutils.makeType(fa.selected.pos, fa.sym.owner.type);
				//if (!(that.lhs instanceof JCIdent))
					checkRW(readableClause, fa.sym, typetree, fa);
				checkRW(writableClause, fa.sym, typetree, fa);
				newfa = treeutils.makeSelect(fa.selected.pos, typetree, fa.sym);
				newfa.name = fa.name;
				rhs = convertExpr(rhs);
				rhs = addImplicitConversion(rhs, optype, rhs);

			} else {
				JCExpression sel = lhsscanned ? fa.selected : convertExpr(fa.selected);

				newfa = M.at(lhs).Select(sel, fa.name);
				newfa.sym = fa.sym;
				newfa.type = fa.type;

				{
					JCExpression e = treeutils.makeNeqObject(lhs.pos, sel, treeutils.nullLit);
					addJavaCheck(that.lhs, e, Label.POSSIBLY_NULL_DEREFERENCE, Label.UNDEFINED_NULL_DEREFERENCE,
							"java.lang.NullPointerException");
				}
				//if (!(that.lhs instanceof JCIdent))
					checkRW(readableClause, fa.sym, sel, fa);
				checkRW(writableClause, fa.sym, sel, fa);

				rhs = convertExpr(rhs);
				rhs = addImplicitConversion(rhs, optype, rhs);
//                if (specs.isNonNull(fa.sym,methodDecl.sym.enclClass())) {
//                    JCExpression e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nullLit);
//                    // FIXME - location of nnonnull declaration?
//                    addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e);
//                }

			}
			addBinaryChecks(that, op, newfa, rhs, maxJmlType);
			checkAccess2(assignableClauseKind, that, lhs, newfa, false, treeutils.trueLit, true, null, false);
//			checkAccess(assignableClauseKind, that, that.lhs, newfa, methodDecl.sym.owner.type, currentEnv.currentReceiver,
//					currentEnv.currentReceiver);

			// We have to make a copy because otherwise the old and new JCFieldAccess share
			// a name field, when in fact they must be different
			JCFieldAccess newlhs = treeutils.makeSelect(newfa.pos, newfa.selected, newfa.sym);

			JCExpression newfac = addImplicitConversion(newfa, optype, newfa);
			// Note that we need to introduce the temporary since the rhs may contain
			// identifiers that will be captured by the lhs. (TODO - example?)
			rhs = makeBin(that, op, newOperator, newfa, rhs, maxJmlType);
			if (arith) {
				// FIXME - this is going to call checkRW again, already called during
				// convertExpr(rhs) above
				rhs = currentEnv.arithmeticMode.rewriteBinary(this, (JCBinary) rhs, true);
			}

			// rhs = treeutils.makeBinary(that.pos,op ,newfac,rhs);
			JCIdent id = newTemp(rhs);
			JCExpression idc = addImplicitConversion(id, newlhs.type, id);
			JCExpressionStatement st = treeutils.makeAssignStat(that.getStartPosition(), newlhs, idc);
            JmlLabeledStatement stt = markUniqueLocation(st);
            addStat(st);
			treeutils.copyEndPosition(st, that);
			var savedResult = post ? idc : newTemp(newlhs);
			saveMapping(that.lhs, eresult);
			var sym = ((JCFieldAccess) lhs).sym;
			if (sym.owner instanceof ClassSymbol) {
				havocModelFields(newfa);
			}
			lastStat = st.expr;
			changeState(that, List.<StoreRefGroup>of(convertFrameConditionList(that, treeutils.trueLit, List.<JCExpression>of(newfa))), stt.label);
			result = eresult = savedResult;
		} else if (lhs instanceof JCArrayAccess) {
			JCArrayAccess aa = (JCArrayAccess) lhs;
			JCExpression array = convertExpr(aa.indexed);
			if (!utils.isJavaOrJmlPrimitiveType(array.type)) {
				JCExpression e = treeutils.makeNeqObject(array.pos, array, treeutils.nullLit);
				// FIXME - location of nnonnull declaration?
				addJavaCheck(that.lhs, e, Label.POSSIBLY_NULL_DEREFERENCE, Label.UNDEFINED_NULL_DEREFERENCE,
						"java.lang.NullPointerException");
			}

			JCExpression index = convertExpr(aa.index);
			index = addImplicitConversion(index, syms.intType, index);
			if (methodEnv.javaChecks) {
				JCExpression e = treeutils.makeBinary(index.pos, JCTree.Tag.GE, index, treeutils.zero);
				addJavaCheck(that.lhs, e, Label.POSSIBLY_NEGATIVEINDEX, Label.UNDEFINED_NEGATIVEINDEX,
						"java.lang.ArrayIndexOutOfBoundsException");
			}

			JCFieldAccess newfa = treeutils.makeLength(array, array);
			if (methodEnv.javaChecks) {
				JCExpression e = treeutils.makeBinary(index.pos, JCTree.Tag.LT, index, newfa);
				addJavaCheck(that.lhs, e, Label.POSSIBLY_TOOLARGEINDEX, Label.UNDEFINED_TOOLARGEINDEX,
						"java.lang.ArrayIndexOutOfBoundsException");
			}

			checkAccess2(assignableClauseKind, that, lhs, newfa, false, treeutils.trueLit, true, null, false);

			rhs = convertExpr(rhs);
			rhs = addImplicitConversion(rhs, optype, rhs);

			JCExpression nlhs = new JmlBBArrayAccess(null, array, index); // FIXME - use factory
			nlhs.pos = aa.pos;
			nlhs.type = aa.type;
			nlhs = newTemp(nlhs);
			nlhs = addImplicitConversion(nlhs, optype, nlhs);

			addBinaryChecks(that, op, nlhs, rhs, optype);
			rhs = makeBin(that, op, newOperator, nlhs, rhs, maxJmlType);
			if (arith) {
				rhs = currentEnv.arithmeticMode.rewriteBinary(this, (JCBinary) rhs, true);
			}

			if (array.type instanceof Type.ArrayType) {
				var atype = (Type.ArrayType) array.type;
				if (specs.isNonNull(atype.elemtype, (ClassSymbol) null) && rhs.type.isReference()) { // FIXME - need the
																										// enclosing
																										// class at the
																										// point of
																										// declaration
					JCExpression e = treeutils.makeNeqObject(that.rhs.pos, rhs, treeutils.nullLit);
					addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e);
				}
			}

			// Note that we need to introduce the temporary since the rhs contains
			// identifiers that will be captured by the lhs. (TODO _ example?)
			// rhs = treeutils.makeBinary(that.pos,op,nlhs,rhs);
			JCIdent id = newTemp(rhs);
			JCExpression idc = addImplicitConversion(id, lhs.type, id);

			lhs = new JmlBBArrayAccess(null, array, index); // FIXME - use factory
			lhs.pos = aa.pos;
			lhs.type = aa.type;

			JCExpressionStatement st = addStat(treeutils.makeAssignStat(that.getStartPosition(), lhs, idc));
            JmlLabeledStatement stt = markUniqueLocation(st);
			treeutils.copyEndPosition(st, that);
			var savedResult = post ? idc : newTemp(lhs);
			saveMapping(that.lhs, eresult);
			lastStat = st.expr;
			changeState(that, List.<StoreRefGroup>of(convertFrameConditionList(that, treeutils.trueLit, List.<JCExpression>of(lhs))), stt.label);
            result = eresult = savedResult;
			// FIXME - what model fields should be havoced?

		} else {
			error(that, "Unexpected kind of AST in JmlAssertionAdder.visitAssignOp: " + that.getClass());
		}
	}

	// FIXME - check boxing conversions for ++ --?

	/** This translates Java unary operations: ++ -- ! ~ - + */
	@Override
	public void visitUnary(JCUnary that) {
		JCTree.Tag tag = that.getTag();
		if (tag == JCTree.Tag.PREDEC || tag == JCTree.Tag.PREINC) {
			JCAssignOp b = M.at(that.getStartPosition()).Assignop(
					tag == JCTree.Tag.PREDEC ? JCTree.Tag.MINUS_ASG : JCTree.Tag.PLUS_ASG, that.getExpression(),
					treeutils.one);
			treeutils.copyEndPosition(b, that);
			b.setType(that.type);
			Type t = that.type.getTag().ordinal() < TypeTag.INT.ordinal() ? syms.intType : unboxedType(that.type);
			b.operator = treeutils.findUnaryOpSymbol(tag == JCTree.Tag.PREDEC ? JCTree.Tag.MINUS : JCTree.Tag.PLUS, t);
			visitAssignopHelper(b, false);
		} else if (tag == JCTree.Tag.POSTDEC || tag == JCTree.Tag.POSTINC) {
			JCExpression arg = convertExpr(that.getExpression());
			JCIdent id = newTemp(arg);
			JCAssignOp b = M.at(that).Assignop(tag == JCTree.Tag.POSTDEC ? JCTree.Tag.MINUS_ASG : JCTree.Tag.PLUS_ASG,
					that.getExpression(), treeutils.one);
			treeutils.copyEndPosition(b, that);
			b.setType(that.type);
			TypeTag typetag = that.type.getTag();
			Type t = (typetag == TypeTag.INT || typetag == TypeTag.BYTE || typetag == TypeTag.SHORT
					|| typetag == TypeTag.CHAR) ? syms.intType : unboxedType(that.type);
			b.operator = treeutils.findUnaryOpSymbol(tag == JCTree.Tag.POSTDEC ? JCTree.Tag.MINUS : JCTree.Tag.PLUS, t);
			visitAssignopHelper(b, true);
			saveMapping(that.getExpression(), eresult);
			result = eresult = id;
		} else if (tag == JCTree.Tag.NEG) {
			if (jmltypes.isSameType(that.arg.type, syms.doubleType) && that.arg instanceof JCLiteral lit) {
				JCLiteral nlit = copy(lit);
				nlit.value = -((Double) lit.value);
				result = eresult = convertExpr(nlit);
			} else if (jmltypes.isSameType(that.arg.type, syms.floatType) && that.arg instanceof JCLiteral lit) {
				JCLiteral nlit = copy(lit);
				nlit.value = -((Float) lit.value);
				result = eresult = convertExpr(nlit);
			} else {
				result = eresult = currentEnv.arithmeticMode.rewriteUnary(this, that);
			}
			if (splitExpressions)
				result = eresult = newTemp(eresult);
		} else if (tag == JCTree.Tag.COMPL || tag == JCTree.Tag.POS) {
			result = eresult = currentEnv.arithmeticMode.rewriteUnary(this, that);
			if (splitExpressions)
				result = eresult = newTemp(eresult);
		} else {
			JCExpression arg = convertExpr(that.getExpression());
			if (tag == JCTree.Tag.NOT && arg instanceof JCLiteral) {
				result = eresult = treeutils.makeBooleanLiteral(arg.pos, !((Boolean) ((JCLiteral) arg).getValue()));
			} else {
				if (!rac)
					arg = addImplicitConversion(arg, syms.booleanType, arg);
				JCExpression e = treeutils.makeUnary(that.pos, tag, that.getOperator(), arg);
				if (splitExpressions)
					e = newTemp(e);
				result = eresult = e;
			}
		}
	}

	/** Add any assertions to check for problems with binary operations. */
	public void addBinaryChecks(JCExpression that, JCTree.Tag op, JCExpression lhs, JCExpression rhs, Type maxJmlType) {

		if (op == JCTree.Tag.DIV || op == JCTree.Tag.MOD) {
			/* @nullable */ JCExpression nonzero = nonZeroCheck(that, rhs);
			if (methodEnv.javaChecks && nonzero != null)
				addAssert(that, Label.POSSIBLY_DIV0, nonzero);
		}
		// NOTE: In Java, a shift by 0 is a no-op (aside from type promotion of the
		// lhs);
		// a shift by a positive or negative amount s is actually a shift by
		// the amount (s & 31) for int lhs or (s & 63) for long lhs.
		// So any rhs value is legal, but may be unexpected.

		if (op == JCTree.Tag.SL || op == JCTree.Tag.SR || op == JCTree.Tag.USR) {
			int mask = (lhs.type.getTag() == TypeTag.LONG) ? 63 : 31;
			JCTree.JCBinary bin = (JCBinary) that;
			if (bin.rhs instanceof JCLiteral) {
				long bits = ((Number) ((JCLiteral) bin.rhs).getValue()).longValue();
				if (currentEnv.arithmeticMode instanceof Arithmetic.Safe) {
					if (bits < 0 || bits > mask) {
						addAssert(that, Label.POSSIBLY_LARGESHIFT, treeutils.trueLit);
					}
				}
				if (!(currentEnv.arithmeticMode instanceof Arithmetic.Math))
					bits &= mask;
			} else {
				JCExpression expr = treeutils.makeBinary(that.pos, JCTree.Tag.BITAND,
						mask == 31 ? treeutils.intbitandSymbol : treeutils.longbitandSymbol, rhs,
						treeutils.makeIntLiteral(that.pos, mask));
				expr = treeutils.makeBinary(that.pos, JCTree.Tag.EQ, rhs, expr);
				addAssert(that, Label.POSSIBLY_LARGESHIFT, expr);
			}
			// FIXME - need to export the adjusted rhs
		}
		// FIXME - add a command-line switch to enable the above?
		// FIXME - add checks for numeric overflow

	}

	public void addToCondition(int pos, JCExpression arg) {
		JCExpression saved = eresult;
		condition = treeutils.makeAndSimp(pos, condition, wrapForOld(arg.pos, copy(arg)));
		result = eresult = saved;
	}

	public JCExpression wrapForOld(int pos, JCExpression arg) {
		if (currentEnv.stateLabel == null) return arg;
		return makeOld(pos, arg, currentEnv.stateLabel);
	}

	public JCExpression foldConstants(JCBinary that) {
		JCLiteral lhs = (JCLiteral) that.lhs;
		JCLiteral rhs = (JCLiteral) that.rhs;
		Object lhsv = lhs.getValue();
		Object rhsv = rhs.getValue();
		Object res = null;
		switch (that.getTag()) {
		case EQ:
			res = lhsv.equals(rhsv);
			break;
		case NE:
			res = !lhsv.equals(rhsv);
			break;
		case AND:
			res = (Boolean) lhsv && (Boolean) rhsv; // FIXME _ the value of the literal might be Integer
			break;
		case OR:
			res = (Boolean) lhsv || (Boolean) rhsv; // FIXME _ the value of the literal might be Integer
			break;
		case PLUS: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() + ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() + ((Number) rhsv).longValue();
			} else if (types.isSameType(that.type, syms.stringType)) {
				// FIXME - what about null arguments?
				res = lhs.toString() + rhsv.toString();
			} // bigint, real
			break;
		}
		case MINUS: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() - ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() - ((Number) rhsv).longValue();
			} // bigint, real
			break;
		}
		case MUL: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() * ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() * ((Number) rhsv).longValue();
			} // bigint, real
			break;
		}
		case DIV: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				int d = ((Number) rhsv).intValue();
				if (d == 0) {
					utils.warning(that.rhs, "jml.message", "Literal divide by zero");
					res = 0;
				} else {
					res = ((Number) lhsv).intValue() / d;
				}
			} else if (that.type.getTag() == TypeTag.LONG) {
				long d = ((Number) rhsv).longValue();
				if (d == 0) {
					utils.warning(that.rhs, "jml.message", "Literal divide by zero");
					res = 0;
				} else {
					res = ((Number) lhsv).longValue() / d;
				}
			}
			// bigint, real

			break;
		}
		case MOD: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				int d = ((Number) rhsv).intValue();
				if (d == 0) {
					utils.warning(that.rhs, "jml.message", "Literal mod by zero");
					res = 0;
				} else {
					res = ((Number) lhsv).intValue() % d;
				}
			} else if (that.type.getTag() == TypeTag.LONG) {
				long d = ((Number) rhsv).longValue();
				if (d == 0) {
					utils.warning(that.rhs, "jml.message", "Literal mod by zero");
					res = 0;
				} else {
					res = ((Number) lhsv).longValue() % d;
				}
			}
			// bigint, real

			break;
		}
		case BITAND: // FIXME - logical result?
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() & ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() & ((Number) rhsv).longValue();
			} else if (that.type.getTag() == TypeTag.BOOLEAN) {
				res = ((Boolean) lhsv).booleanValue() & ((Boolean) rhsv).booleanValue();
			} // bigint
			break;
		}
		case BITOR: // FIXME - logical result?
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() | ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() & ((Number) rhsv).longValue();
			} else if (that.type.getTag() == TypeTag.BOOLEAN) {
				res = ((Boolean) lhsv).booleanValue() | ((Boolean) rhsv).booleanValue();
			} // bigint
			break;
		}
		case BITXOR: // FIXME - logical result?
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() ^ ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() & ((Number) rhsv).longValue();
			} else if (that.type.getTag() == TypeTag.BOOLEAN) {
				res = ((Boolean) lhsv).booleanValue() != ((Boolean) rhsv).booleanValue();
			} // bigint
			break;
		}
		case GT: {
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() > ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() > ((Number) rhsv).longValue();
			} // bigint, real
			break;
		}
		case GE: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() >= ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() >= ((Number) rhsv).longValue();
			} // bigint, real
			break;
		}
		case LT: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() < ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() < ((Number) rhsv).longValue();
			} // bigint, real
			break;
		}
		case LE: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() <= ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() <= ((Number) rhsv).longValue();
			} // bigint, real
			break;
		}
		case SL: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() << ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() << ((Number) rhsv).longValue();
			} // bigint, real
			break;
		}
		case SR: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() >> ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() >> ((Number) rhsv).longValue();
			} // bigint, real
			break;
		}
		case USR: // FIXME - what about overflow checks and arithmetic mode
		{
			if (that.type.getTag() == TypeTag.INT) {
				res = ((Number) lhsv).intValue() >>> ((Number) rhsv).intValue();
			} else if (that.type.getTag() == TypeTag.LONG) {
				res = ((Number) lhsv).longValue() >>> ((Number) rhsv).longValue();
			} // bigint, real
			break;
		}
		}
		if (res == null) {
			utils.error(that, "jml.internal", "Constant folding here not implemented");
			return that;
		}
		return M.at(that).Literal(res);
	}

	public Type maxNumericType(Type maxType, Type rhst) {
		if (maxType == null)
			return null;
		if (rhst.isReference())
			rhst = types.unboxedType(rhst);
		boolean rhsIsPrim = rhst.isPrimitive() && rhst.getTag() != TypeTag.BOT;
		if (jmltypes.isJmlType(rhst) || jmltypes.isJmlRepType(rhst))
			maxType = rhst;
		// The following is only valid for numeric types
		if (rhsIsPrim)
			maxType = treeutils.maxType(maxType, rhst);
		return maxType;
	}

	// OK
	@Override
	public void visitBinary(JCBinary that) {
		// FIXME - check on numeric promotion, particularly shift operators
		JCTree.Tag optag = that.getTag();
		boolean equality = optag == JCTree.Tag.EQ || optag == JCTree.Tag.NE;
		boolean comp = equality || optag == JCTree.Tag.GE || optag == JCTree.Tag.LE || optag == JCTree.Tag.LT
				|| optag == JCTree.Tag.GT;
		boolean shift = optag == JCTree.Tag.SL || optag == JCTree.Tag.SR || optag == JCTree.Tag.USR;
		boolean arith = optag == JCTree.Tag.PLUS || optag == JCTree.Tag.MINUS || optag == JCTree.Tag.MUL
				|| optag == JCTree.Tag.DIV || optag == JCTree.Tag.MOD;
		boolean bit = optag == JCTree.Tag.BITAND || optag == JCTree.Tag.BITOR || optag == JCTree.Tag.BITXOR;

		//System.out.println("VISIT-BINARY " + that);
		//if (that.toString().contains("length != null")) Utils.dumpStack();
		if (optag == JCTree.Tag.PLUS && that.type.equals(syms.stringType)) {
			if ((infer || esc)) {
				Symbol s = utils.findStaticMember(syms.stringType.tsym, "concat");
				if (s == null) {
					utils.error(that, "jml.internal", "Could not find the concat method");
				} else {
					JCIdent id = M.Ident("String");
					id.sym = syms.stringType.tsym;
					id.type = syms.stringType;
					JCExpression lhs = that.getLeftOperand();
					JCExpression rhs = that.getRightOperand();
					if (lhs.type != syms.stringType) {
						Type t = lhs.type;
						if (!lhs.type.isPrimitive())
							t = syms.objectType;
						JCFieldAccess call = M.Select(id, names.fromString("valueOf"));
						call.sym = utils.findStaticMethod(syms.stringType.tsym, "valueOf", t);
						call.type = call.sym.type;
						lhs = M.at(that).Apply(null, call, List.<JCExpression>of(lhs)).setType(syms.stringType);
					}
					if (rhs.type != syms.stringType) {
						Type t = rhs.type;
						if (!rhs.type.isPrimitive())
							t = syms.objectType;
						JCFieldAccess call = M.Select(id, names.fromString("valueOf"));
						call.sym = utils.findStaticMethod(syms.stringType.tsym, "valueOf", t);
						call.type = call.sym.type;
						rhs = M.at(that).Apply(null, call, List.<JCExpression>of(rhs)).setType(syms.stringType);
					}
					JCFieldAccess call = M.Select(id, names.fromString("concat"));
					call.sym = s;
					call.type = s.type;
					JCMethodInvocation m = M.at(that).Apply(null, call, List.<JCExpression>of(lhs, rhs))
							.setType(that.type);
					result = eresult = convertExpr(m);
				}
				return;
			} else { // rac and anything else
				JCExpression lhs = convertExpr(that.getLeftOperand());
				JCExpression rhs = convertExpr(that.getRightOperand());
				result = eresult = treeutils.makeBinary(that.pos, optag, that.getOperator(), lhs, rhs);
				return;
			}
		} else if (optag == JCTree.Tag.AND || optag == JCTree.Tag.OR) {
			JCExpression prev = condition;
			try {
				Type maxJmlType = that.getLeftOperand().type;
				if (jmltypes.isJmlType(that.getRightOperand().type))
					maxJmlType = that.getRightOperand().type;

				// FIXME - check that all the checks in makeBinaryCHecks are here - or somehow
				// reuse that method here
				// same for unary checks
				if (optag == JCTree.Tag.AND) {
					if (splitExpressions) {
						JCConditional cond = M.at(that).Conditional(that.lhs, that.rhs, treeutils.falseLit);
						cond.setType(that.type);
						visitConditional(cond);
						return;
					} else {
						JCExpression lhs = convertExpr(that.getLeftOperand());
						JCExpression rhs = that.getRightOperand();
						lhs = addImplicitConversion(lhs, syms.booleanType, copy(lhs));
						if (translatingJML)
							condition = treeutils.makeAnd(that.lhs.pos, condition, wrapForOld(lhs.pos, lhs));
						if (!(lhs instanceof JCLiteral && ((JCLiteral) lhs).getValue().equals(Boolean.FALSE))) {
							rhs = convertExpr(rhs); // condition is used within scanExpr so this statement must follow
													// the previous one
							rhs = addImplicitConversion(rhs, syms.booleanType, rhs);
							if (translatingJML)
								adjustWellDefinedConditions(lhs);
							result = eresult = makeBin(that, optag, that.getOperator(), lhs, rhs, maxJmlType);
						} else {
							result = eresult = lhs;
						}
					}
				} else if (optag == JCTree.Tag.OR) {
					if (splitExpressions) {
						JCConditional cond = M.at(that).Conditional(that.lhs, treeutils.trueLit, that.rhs);
						cond.setType(that.type);
						visitConditional(cond);
						return;
					} else {
						JCExpression lhs = convertExpr(that.getLeftOperand());
						JCExpression rhs = that.getRightOperand();
						lhs = addImplicitConversion(lhs, syms.booleanType, lhs);
						if (translatingJML)
							condition = treeutils.makeAnd(that.lhs.pos, condition,
									treeutils.makeNot(that.lhs.pos, wrapForOld(lhs.pos, lhs)));
						if (!(lhs instanceof JCLiteral && ((JCLiteral) lhs).getValue().equals(Boolean.TRUE))) {
							rhs = convertExpr(rhs); // condition is used within scanExpr so this statement must follow
													// the previous one
							rhs = addImplicitConversion(rhs, syms.booleanType, rhs);
							if (translatingJML)
								adjustWellDefinedConditions(treeutils.makeNot(that.lhs.pos, lhs));
							result = eresult = makeBin(that, optag, that.getOperator(), lhs, rhs, maxJmlType);
						} else {
							result = eresult = lhs;
						}
					}
				}
				if (splitExpressions)
					result = eresult = newTemp(eresult);
				return;
			} finally {
				condition = prev;
			}
		} else if (bit && that.lhs.type.getTag() == TypeTag.BOOLEAN) {
			JCExpression lhs = convertExpr(that.getLeftOperand());
			JCExpression rhs = convertExpr(that.getRightOperand());
			result = eresult = makeBin(that, optag, that.getOperator(), lhs, rhs, lhs.type);
		} else if (arith) {
			result = eresult = currentEnv.arithmeticMode.rewriteBinary(this, that, false);
			if (splitExpressions)
				result = eresult = newTemp(eresult);
			return;

		} else if (translatingJML) {
//            boolean savedApplyingLambda = applyingLambda;
//            applyingLambda = false;
			JCExpression lhs = convertExpr(that.getLeftOperand());
			JCExpression rhs = convertExpr(that.getRightOperand());
//            applyingLambda = savedApplyingLambda;
			Number n = treeutils.integralLiteral(lhs);
			Number nn = treeutils.integralLiteral(rhs);
			if (n != null && nn != null) {
				Boolean b = null;
				if (optag == JCTree.Tag.EQ)
					b = n.longValue() == nn.longValue();
				else if (optag == JCTree.Tag.NE)
					b = n.longValue() != nn.longValue();
				else if (optag == JCTree.Tag.LT)
					b = n.longValue() < nn.longValue();
				else if (optag == JCTree.Tag.LE)
					b = n.longValue() <= nn.longValue();
				else if (optag == JCTree.Tag.GT)
					b = n.longValue() > nn.longValue();
				else if (optag == JCTree.Tag.GE)
					b = n.longValue() >= nn.longValue();
				if (b != null) {
					result = eresult = treeutils.makeBooleanLiteral(that, b);
					return;
				}
			}
			if (equality && ((lhs instanceof JCLambda && treeutils.isNullLit(rhs))
					|| (rhs instanceof JCLambda && treeutils.isNullLit(lhs)))) {
				result = eresult = treeutils.makeBooleanLiteral(that.pos, optag == JCTree.Tag.NE);
				return;
			}
			if (equality && ((treeutils.isNullLit(rhs) && treeutils.typeLiteral(lhs) != null)
					|| (treeutils.isNullLit(lhs) && treeutils.typeLiteral(rhs) != null))) {
				result = eresult = treeutils.makeBooleanLiteral(that.pos, optag == JCTree.Tag.NE);
				return;
			}
			Type maxJmlType = lhs.type;
			boolean lhsIsPrim = lhs.type.isPrimitive() && lhs.type.getTag() != TypeTag.BOT;
			boolean rhsIsPrim = rhs.type.isPrimitive() && rhs.type.getTag() != TypeTag.BOT;
			if (jmltypes.isJmlType(rhs.type) || jmltypes.isJmlRepType(rhs.type))
				maxJmlType = rhs.type;
			// The following is only valid for numeric types
			if (lhsIsPrim && rhsIsPrim)
				maxJmlType = treeutils.maxType(lhs.type, rhs.type);

			if (equality && jmltypes.isJmlTypeOrRep(maxJmlType, jmltypes.TYPE)) {
				if (rac)
					lhs = treeutils.makeUtilsMethodCall(that.pos, "isEqualTo", lhs, rhs);
				else
					lhs = treeutils.makeBinary(that.pos, JCTree.Tag.EQ, lhs, rhs);
				if (optag == JCTree.Tag.NE)
					lhs = treeutils.makeNot(that.pos, lhs);
				lhs.type = syms.booleanType; // FIXME - equality between JMLTypes needs improvement
				result = eresult = lhs;
				// Exit because we are replacing the == operator with a
				// function call
				eresult.pos = that.getStartPosition();
				if (!rac && splitExpressions)
					result = eresult = newTemp(eresult);
				treeutils.copyEndPosition(eresult, that);
				return;
			} else if (equality && (lhs instanceof JCLambda || rhs instanceof JCLambda
					|| lhs instanceof JCTree.JCMemberReference || rhs instanceof JCTree.JCMemberReference)) {
				Boolean b = null;
				if ((lhs instanceof JCLambda || lhs instanceof JCTree.JCMemberReference) && treeutils.isNullLit(rhs)) {
					b = optag == JCTree.Tag.NE;
				} else if ((rhs instanceof JCLambda || rhs instanceof JCTree.JCMemberReference)
						&& treeutils.isNullLit(lhs)) {
					b = optag == JCTree.Tag.NE;
				} else if (lhs instanceof JCTree.JCMemberReference && rhs instanceof JCTree.JCMemberReference) {
					b = (optag == JCTree.Tag.EQ) == (((JCTree.JCMemberReference) lhs).sym == ((JCTree.JCMemberReference) rhs).sym);
//                } else {
//                    log.error(that,"jml.unimplemented.lambda");
				}
				if (b != null) {
					result = eresult = treeutils.makeBooleanLiteral(that.pos, b);
					return;
				}
			} else if (equality && that.lhs.type.isNullOrReference() && that.rhs.type.isNullOrReference()) {
				// This is a pure object comparison - no unboxing
				if (optag == JCTree.Tag.EQ)
					result = eresult = treeutils.makeEqObject(that.pos, lhs, rhs);
				else
					result = eresult = treeutils.makeNeqObject(that.pos, lhs, rhs);
				if (splitExpressions)
					result = eresult = newTemp(eresult);
				return;

				// FIXME - check that all the checks in makeBinaryCHecks are here - or somehow
				// reuse that method here
				// same for unary checks
			} else if (equality && jmltypes.isJmlTypeOrRep(maxJmlType, jmltypes.BIGINT)) {
				lhs = addImplicitConversion(lhs, maxJmlType, lhs);
				rhs = addImplicitConversion(rhs, maxJmlType, rhs);
				if (rac) { // FIXME && !that.lhs.type.isPrimitive() && !that.rhs.type.isPrimitive()) {
					lhs = treeutils.makeUtilsMethodCall(that.pos, optag == JCTree.Tag.NE ? "bigint_ne" : "bigint_eq",
							lhs, rhs);
				} else {
					lhs = treeutils.makeBinary(that.pos, optag, lhs, rhs);
				}
				result = eresult = lhs;
				eresult.pos = that.getStartPosition();
				treeutils.copyEndPosition(eresult, that);
				if (!rac && splitExpressions)
					result = eresult = newTemp(eresult);
				return;
			} else if (equality && jmltypes.isJmlTypeOrRep(maxJmlType, jmltypes.REAL)) {
				lhs = addImplicitConversion(lhs, maxJmlType, lhs);
				rhs = addImplicitConversion(rhs, maxJmlType, rhs);
				if (rac)
					lhs = treeutils.makeUtilsMethodCall(that.pos, "real_eq", lhs, rhs);
				else
					lhs = treeutils.makeBinary(that.pos, JCTree.Tag.EQ, lhs, rhs);
				if (optag == JCTree.Tag.NE)
					lhs = treeutils.makeNot(that.pos, lhs);
				result = eresult = lhs;
				eresult.pos = that.getStartPosition();
				treeutils.copyEndPosition(eresult, that);
				if (!rac && splitExpressions)
					result = eresult = newTemp(eresult);
				return;
			} else if (equality && maxJmlType.toString().equals("org.jmlspecs.runtime.IJMLTYPE")) {
				lhs = addImplicitConversion(lhs, maxJmlType, lhs);
				rhs = addImplicitConversion(rhs, maxJmlType, rhs);
				if (rac) {
					eresult = treeutils.makeUtilsMethodCall(that.pos, "equalTYPE", lhs, rhs);
				} else {
					eresult = treeutils.makeBinary(that.pos, JCTree.Tag.EQ, lhs, rhs);
				}
				if (optag == JCTree.Tag.NE)
					eresult = treeutils.makeNot(that.pos, eresult);
				result = eresult;
				eresult.pos = that.getStartPosition();
				treeutils.copyEndPosition(eresult, that);
				if (!rac && splitExpressions)
					result = eresult = newTemp(eresult);
				return;
			} else {
				Type t = that.type;
				if (t.getTag() == TypeTag.BOOLEAN) {
					// Compute a max type - FIXME - need to do this for all types
					if (lhs instanceof JCLiteral && ((JCLiteral) lhs).typetag == TypeTag.BOT) {
						t = boxedType(rhs.type);
					} else if (rhs instanceof JCLiteral && ((JCLiteral) rhs).typetag == TypeTag.BOT) {
						t = boxedType(lhs.type);
					} else if (jmltypes.isJmlType(maxJmlType) || jmltypes.isJmlRepType(maxJmlType)) {
						t = maxJmlType;
					} else if (equality && !lhs.type.isPrimitive() && !rhs.type.isPrimitive()) {
						t = null;
					} else if (rac && currentEnv.arithmeticMode.mode() == Arithmetic.Mode.MATH && maxJmlType.isPrimitive()
							&& !comp) {
						if (jmltypes.isIntegral(maxJmlType))
							maxJmlType = jmltypes.BIGINT;
						else
							maxJmlType = jmltypes.REAL;
						t = maxJmlType;
					} else {
						Type tlhs = unboxedType(lhs.type);
						Type trhs = unboxedType(rhs.type);
						t = tlhs;
						if (tlhs.getTag() == TypeTag.BOT)
							t = trhs;
						else
							t = treeutils.maxType(tlhs, trhs);
					}
					t = convertType(t);
				}
				// FIXME - this is incorrect, but handles Jml primitive types at least
//                if (jmltypes.isJmlType(t)){ 
				if (equality && t == null) {
				} // OK
				else if (comp) {
					lhs = addImplicitConversion(lhs, t, lhs); // FIXME - what final type
				} else if (shift)
					lhs = addImplicitConversion(lhs, unboxedType(that.type), lhs); // FIXME - what final type
				else
					lhs = addImplicitConversion(lhs, that.type, lhs);

				if (equality && t == null) {
				} // OK
				else if (comp) {
					rhs = addImplicitConversion(rhs, t, rhs); // FIXME - what final type
				} else if (shift) {
					Type tt = unboxedType(that.rhs.type);
					if (!tt.equals(syms.longType))
						tt = syms.intType;
					rhs = addImplicitConversion(rhs, tt, rhs);
				} else
					rhs = addImplicitConversion(rhs, that.type, rhs);
			}
			// FIXME - add checks for numeric overflow - PLUS MINUS MUL
//            if (!translatingJML) addBinaryChecks(that,optag,lhs,rhs,null);
			result = eresult = makeBin(that, optag, that.getOperator(), lhs, rhs, maxJmlType);
			if (!rac && splitExpressions)
				result = eresult = newTemp(eresult);

		} else { // !translatingJML
			Symbol s = that.getOperator();
			Type maxJmlType = that.getLeftOperand().type;
			boolean lhsIsPrim = that.getLeftOperand().type.isPrimitive()
					&& that.getLeftOperand().type.getTag() != TypeTag.BOT;
			boolean rhsIsPrim = that.getRightOperand().type.isPrimitive()
					&& that.getRightOperand().type.getTag() != TypeTag.BOT;
			if (jmltypes.isJmlType(that.getRightOperand().type))
				maxJmlType = that.getRightOperand().type;
			if (lhsIsPrim && rhsIsPrim)
				maxJmlType = treeutils.maxType(that.getLeftOperand().type, that.getRightOperand().type);

			Type t = that.type;
			if (t.getTag() == TypeTag.BOOLEAN) {
				// Compute a max type - FIXME - need to do this for all types
				if (jmltypes.isJmlType(maxJmlType)) {
					t = maxJmlType;
				} else if (that.lhs.type.getTag() == TypeTag.BOT) {
					t = boxedType(that.rhs.type);
				} else if (that.rhs.type.getTag() == TypeTag.BOT) {
					t = boxedType(that.lhs.type);
				} else {
					Type tlhs = unboxedType(that.getLeftOperand().type);
					Type trhs = unboxedType(that.getRightOperand().type);
					t = tlhs;
					if (tlhs.getTag() == TypeTag.BOT)
						t = trhs;
					else
						t = treeutils.maxType(tlhs, trhs);
				}
			}
			JCExpression lhs = convertExpr(that.getLeftOperand());
			JCExpression rhs = convertExpr(that.getRightOperand());
			if (equality && ((treeutils.isNullLit(rhs) && treeutils.typeLiteral(lhs) != null)
					|| (treeutils.isNullLit(lhs) && treeutils.typeLiteral(rhs) != null))) {
				result = eresult = treeutils.makeBooleanLiteral(that.pos, optag == JCTree.Tag.NE);
				return;
			}
			{
				if (comp)
					lhs = addImplicitConversion(lhs, t, lhs);
				else if (shift)
					lhs = addImplicitConversion(lhs, unboxedType(that.type), lhs); // FIXME - what final type
				else
					lhs = addImplicitConversion(lhs, that.type, lhs);
			}

			{
				if (comp)
					rhs = addImplicitConversion(rhs, t, rhs);
				else if (shift) {
					Type tt = unboxedType(that.rhs.type);
					if (!tt.equals(syms.longType))
						tt = syms.intType;
					rhs = addImplicitConversion(rhs, tt, rhs); // FIXME - tt or int as above?
				} else
					rhs = addImplicitConversion(rhs, that.type, rhs);
			}
			if (equality && ((that.lhs instanceof JCLambda && treeutils.isNullLit(that.rhs))
					|| (that.rhs instanceof JCLambda && treeutils.isNullLit(that.lhs)))) {
				result = eresult = treeutils.makeBooleanLiteral(that.pos, optag == JCTree.Tag.NE);
				return;
			}

			addBinaryChecks(that, optag, lhs, rhs, null);
			JCBinary bin = treeutils.makeBinary(that.pos, optag, that.getOperator(), lhs, rhs);
			result = eresult = splitExpressions ? newTemp(bin) : bin;
		}
		if (splitExpressions)
			eresult.pos = that.getStartPosition(); // Need to make the start of the temporary Ident the same as the
													// start of the expression it represents
		treeutils.copyEndPosition(eresult, that);
	}

	public void visitJmlChained(JmlChained that) {
		JCExpression lhs = that.conjuncts.head.lhs;
		Type maxType = maxNumericType(syms.intType, lhs.type);
		for (JCBinary b : that.conjuncts) {
			maxType = maxNumericType(maxType, b.rhs.type);
		}

		lhs = convertExpr(that.conjuncts.head.lhs);
		lhs = addImplicitConversion(lhs, maxType, lhs);
		JCExpression ba = null;
		for (JCBinary b : that.conjuncts) {
			JCExpression rhs = convertExpr(b.rhs);
			rhs = addImplicitConversion(rhs, maxType, rhs);
			JCBinary bb = M.at(b.pos).Binary(b.getTag(), lhs, rhs);
			bb.operator = b.operator;
			bb.type = b.type;
			ba = ba == null ? bb : utils.esc ? treeutils.makeBitAnd(b.pos, ba, bb) : treeutils.makeAnd(b.pos, ba, bb);
			lhs = rhs;
		}
		result = eresult = splitExpressions ? newTemp(ba) : ba;
	}

	/** Returns the AST for (rhs != 0), for the appropriate type */
	public /* @nullable */ JCExpression nonZeroCheck(JCTree that, JCExpression rhs) {
		JCExpression nonzero;
		if (rhs instanceof JCLiteral) {
			Object value = ((JCLiteral) rhs).value;
			if (value instanceof Integer && ((Integer) value).intValue() != 0)
				return null;
		} else if (rhs instanceof JCTypeCast && ((JCTypeCast) rhs).expr instanceof JCLiteral) {
			Object value = ((JCLiteral) ((JCTypeCast) rhs).expr).value;
			if (value instanceof Integer && ((Integer) value).intValue() != 0)
				return null;
		}
		if (rac && rhs.type == jmltypes.BIGINT) {
			nonzero = treeutils.makeUtilsMethodCall(that.pos, "bigint_nonzero", rhs);
		} else if (rac && rhs.type == jmltypes.REAL) {
			nonzero = treeutils.makeUtilsMethodCall(that.pos, "real_nonzero", rhs);
		} else {
			nonzero = treeutils.makeBinary(that.pos, JCTree.Tag.NE, rhs,
					treeutils.makeZeroEquivalentLit(rhs.pos, rhs.type));
		}
		return nonzero;
	}

	public JCExpression makeBin(JCTree that, JCTree.Tag tag, OperatorSymbol opSym, JCExpression lhs, JCExpression rhs,
			Type maxJmlType) {
		if (rac && (jmltypes.isJmlType(maxJmlType) || jmltypes.isJmlRepType(maxJmlType))) {
			boolean bi = maxJmlType == jmltypes.BIGINT || maxJmlType.tsym == jmltypes.repSym(jmltypes.BIGINT);
			if (bi || maxJmlType == jmltypes.REAL || maxJmlType.tsym == jmltypes.repSym(jmltypes.REAL)) {
				String fcn;
				switch (tag) {
				case PLUS:
					fcn = "add";
					break;
				case MINUS:
					fcn = "sub";
					break;
				case MUL:
					fcn = "mul";
					break;
				case DIV:
					fcn = "div";
					break;
				case MOD:
					fcn = "remainder";
					break;
				case LT:
					fcn = "lt";
					break;
				case LE:
					fcn = "le";
					break;
				case GT:
					fcn = "gt";
					break;
				case GE:
					fcn = "ge";
					break;
				case EQ:
					fcn = "eq";
					break;
				case NE:
					fcn = "ne";
					break;
				// FIXME - need shift types
				default: {
					String msg = "Unexpected operation tag in JmlAssertionAdder.makeBin: " + tag + " "
							+ JmlPretty.write(that);
					log.error(that.pos, "jml.internal", msg);
					throw new JmlInternalError(msg);
				}
				}
				String pre = bi ? "bigint_" : "real_";
				if (lhs.type != maxJmlType)
					lhs = addImplicitConversion(lhs, maxJmlType, lhs);
				if (rhs.type != maxJmlType)
					rhs = addImplicitConversion(rhs, maxJmlType, rhs);
				return treeutils.makeUtilsMethodCall(that.pos, pre + fcn, lhs, rhs);
			} else {
				String msg = "Unexpected JML type in JmlAssertionAdder.makeBin: " + maxJmlType;
				log.error(that.pos, "jml.internal", msg);
				throw new JmlInternalError(msg);
			}
		} else {
			return treeutils.makeBinary(that.pos, tag, opSym, lhs, rhs);
		}

	}

	public long maxValue(int pos, TypeTag tag) {
		switch (tag) {
		case INT:
			return Integer.MAX_VALUE;
		case SHORT:
			return Short.MAX_VALUE;
		case LONG:
			return Long.MAX_VALUE;
		case BYTE:
			return Byte.MAX_VALUE;
		case CHAR:
			return Character.MAX_VALUE;
		default:
			log.error(pos, "jml.internal", "Unknown type tag " + tag);
			return 0;
		}
	}

	public long minValue(int pos, TypeTag tag) {
		switch (tag) {
		case INT:
			return Integer.MIN_VALUE;
		case SHORT:
			return Short.MIN_VALUE;
		case LONG:
			return Long.MIN_VALUE;
		case BYTE:
			return Byte.MIN_VALUE;
		case CHAR:
			return Character.MIN_VALUE;
		default:
			log.error(pos, "jml.internal", "Unknown type tag " + tag);
			return 0;
		}
	}

	public int comparePrecision(TypeTag a, TypeTag b) {
		switch (a) {
		case INT:
			switch (b) {
			case INT:
				return 0;
			case BYTE:
			case CHAR:
			case SHORT:
				return 1;
			case FLOAT:
			case DOUBLE:
			case LONG:
				return -1;
			}
			break;
		case BYTE:
			switch (b) {
			case BYTE:
				return 0;
			case INT:
			case CHAR:
			case SHORT:
			case FLOAT:
			case DOUBLE:
			case LONG:
				return -1;
			}
			break;
		case SHORT:
			switch (b) {
			case SHORT:
				return 0;
			case BYTE:
			case CHAR:
				return 1;
			case INT:
			case FLOAT:
			case DOUBLE:
			case LONG:
				return -1;
			}
			break;
		case LONG:
			switch (b) {
			case LONG:
				return 0;
			case BYTE:
			case CHAR:
			case INT:
			case SHORT:
				return 1;
			case FLOAT:
			case DOUBLE:
				return -1;
			}
			break;
		}
		return 0;
	}
	
    public boolean hasNonNull(Type type) {
        return type.getAnnotationMirrors().stream().anyMatch(a->a.type == attr.nonnullAnnotationSymbol.type);
    }

    public boolean hasNullable(Type type) {
        return type.getAnnotationMirrors().stream().anyMatch(a->a.type == attr.nullableAnnotationSymbol.type);
    }

	@Override
	public void visitTypeCast(JCTypeCast that) {
		// Note - casting a null produces a null value
		Type origType = that.getExpression().type;
		origType = convertType(origType);
		JCExpression arg = convertExpr(that.getExpression());
		Type argType = arg.type;
		JCTree newTypeTree = that.getType(); // the tree, not the Type
		JCTree clazz = convert(newTypeTree);
		if (types.isSameType(that.type, utils.extensionValueType("string"))) {
			addImplicitConversion(that, that.type, that.expr);
			return;
		}
		if (rac && that.type.isPrimitive() && jmltypes.isJmlTypeOrRepType(argType)) {

			if (jmltypes.isSameTypeOrRep(that.type, origType)) {
				result = eresult = arg; // No-op
				// FIXME - will need a cast from real to bigint
			} else {
				// FIXME - the null here should be an error
				String s = (jmltypes.isJmlTypeOrRep(argType, jmltypes.BIGINT) ? "bigint_to"
						: jmltypes.isJmlTypeOrRep(argType, jmltypes.REAL) ? "real_to" : null) + newTypeTree.toString();
				JCExpression e = treeutils.makeUtilsMethodCall(that.pos, s, arg);
				result = eresult = e;
			}
			return;
		}
		if (rac && that.type.isPrimitive() && jmltypes.isJmlType(that.type)) {
			if (origType.tsym == jmltypes.repSym((JmlType) that.type)) {
				result = eresult = arg; // No-op since the representation type is the same as the argument type
			} else if (that.type == jmltypes.BIGINT) {
				result = eresult = treeutils.makeUtilsMethodCall(that.pos, "bigint_valueOf", arg);
			} else if (that.type == jmltypes.REAL) {
				result = eresult = treeutils.makeUtilsMethodCall(that.pos, "real_valueOf", arg);
			}
			return;
		}
		JCTypeCast castexpr = M.at(that).TypeCast(clazz, arg);
		castexpr.setType(that.type); // may be superfluous
		treeutils.copyEndPosition(castexpr, that);
		JCExpression newexpr = castexpr;

		
        // Check whether expression is null
		JCExpression eqnull = treeutils.makeEqObject(that.pos, arg, treeutils.makeNullLiteral(that.pos));
        JCExpression notnull = treeutils.makeNot(that.pos, eqnull);

        boolean hasNonNull = hasNonNull(newTypeTree.type);
        if (hasNonNull && !origType.isPrimitive()) {
            addAssert(that, Label.NULL_CAST, notnull);
        }
        
		JCExpression emax = null, emin = null;
		int changePrecision = comparePrecision(origType.getTag(), that.type.getTag());
		if (types.isSameType(clazz.type, origType)) {
			// redundant - remove the cast in both rac and esc
			newexpr = arg;
		} else if (argType.getTag() == TypeTag.NONE && that.type.getTag() != TypeTag.NONE) {
			// cast of \bigint or \real to a primitive type
			// FIXME - for now presume the bigint fits into a long
			emax = treeutils.makeBinary(that.pos, JCTree.Tag.LE, arg,
					treeutils.makeLit(that.pos, syms.longType, Long.valueOf(maxValue(that.pos, that.type.getTag()))));
			emin = treeutils.makeBinary(that.pos, JCTree.Tag.LE,
					treeutils.makeLit(that.pos, syms.longType, Long.valueOf(minValue(that.pos, that.type.getTag()))),
					arg);
			addAssert(that, Label.ARITHMETIC_CAST_RANGE, emax);
			addAssert(that, Label.ARITHMETIC_CAST_RANGE, emin);

		} else if (clazz.type.isPrimitive()) {
			if (origType.isPrimitive()) {
				// Java primitive to Java primitive - must be a numeric cast
				// FIXME - should be able to check for overflow in BV modes -- also move all
				// this into th Arithmetic mode classes
				boolean check = !(currentEnv.arithmeticMode instanceof Arithmetic.Java);
				if (useBV) {
					// skip
				} else if (changePrecision == 1) {
					TypeTag ntag = that.type.getTag();
					// change precision == 1 means that a higher precision value is being cast to a
					// lower precision
					// so we check the range of the argument
					TypeTag otag = origType.getTag();
					switch (otag) {
					case LONG:
						emax = treeutils.makeBinary(that.pos, JCTree.Tag.LE, arg, treeutils.makeLit(that.pos, arg.type,
								Long.valueOf(maxValue(that.pos, that.type.getTag()))));
						emin = treeutils.makeBinary(that.pos, JCTree.Tag.LE, treeutils.makeLit(that.pos, arg.type,
								Long.valueOf(minValue(that.pos, that.type.getTag()))), arg);
						break;
					case INT:
					case SHORT:
					case CHAR:
					case BYTE:
						long mx = maxValue(that.pos, that.type.getTag());
						Integer min = Integer.valueOf((int) minValue(that.pos, that.type.getTag()));
						Integer max = Integer.valueOf((int) mx);
						if (argType.isPrimitive()) {
							emax = treeutils.makeBinary(that.pos, JCTree.Tag.LE, arg,
									treeutils.makeLit(that.pos, arg.type, max));
							emin = treeutils.makeBinary(that.pos, JCTree.Tag.LE,
									treeutils.makeLit(that.pos, arg.type, min), arg);
						} else if (rac) {
							emax = treeutils.makeUtilsMethodCall(that.pos, "bigint_le", arg,
									treeutils.makeUtilsMethodCall(that.pos, "bigint_valueOf",
											treeutils.makeLongLiteral(that.pos, max)));
							emin = treeutils.makeUtilsMethodCall(that.pos, "bigint_le", treeutils.makeUtilsMethodCall(
									that.pos, "bigint_valueOf", treeutils.makeLongLiteral(that.pos, min)), arg);
							newexpr = arg;
						}
						break;
					default:
						utils.error(that, "jml.internal", "Unimplemented case combination");
						break;
					case FLOAT: // FIXME - ignore for now
					case DOUBLE:
						emax = emin = treeutils.trueLit;
						break;
					// Must be numeric to numeric - do numeric range checks
					// FIXME - implement
					}
					// reducing precision - make assertions about range of input value
					if (check) {
						addAssert(that, Label.ARITHMETIC_CAST_RANGE, emax);
						addAssert(that, Label.ARITHMETIC_CAST_RANGE, emin);
					}
				} else if (changePrecision == -1) {
					// In this branch we are casting from a lower precision to a higher precision
					// So we can assume that the range of the value in the new type is the smaller
					// range appropriate to the original type

					// FIXME the type of the valueOf needs to match the output type
					switch (origType.getTag()) {
					case LONG:
					case INT:
					case SHORT:
					case CHAR:
					case BYTE:
						emax = treeutils.makeBinary(that.pos, JCTree.Tag.LE, arg, treeutils.makeLit(that.pos, arg.type,
								Integer.valueOf((int) maxValue(that.pos, origType.getTag())))); // FIXME - here and
																								// below, INT but we
																								// need LONGr
						emin = treeutils.makeBinary(that.pos, JCTree.Tag.LE, treeutils.makeLit(that.pos, arg.type,
								Integer.valueOf((int) minValue(that.pos, origType.getTag()))), arg);
						break;
					default:
						utils.error(that, "jml.internal", "Unimplemented case combination");
						break;
					case FLOAT: // FIXME - ignore for now
					case DOUBLE:
						emax = emin = treeutils.trueLit;
						break;
					// Must be numeric to numeric - do numeric range checks
					// FIXME - implement
					}
					// increasing precision - make assumptions about range of output value
					addAssume(that, Label.ARITHMETIC_CAST_RANGE, emax);
					addAssume(that, Label.ARITHMETIC_CAST_RANGE, emin);
				}

			} else if (jmltypes.isSameType(origType, jmltypes.BIGINT)) {
				// \bigint to primitive
				// FIXME - reducing precision - check range
				String s = "bigint_to" + that.type.toString();
				JCExpression e = treeutils.makeUtilsMethodCall(that.pos, s, arg);
				newexpr = e;
			} else if (jmltypes.isSameType(origType, jmltypes.REAL)) {
				// \real to primitive
				// FIXME - reducing precision - check range
				String s = "real_to" + that.type.toString();
				JCExpression e = treeutils.makeUtilsMethodCall(that.pos, s, arg);
				newexpr = e;

			} else {
				// unboxing = FIXME = check type combinations
				addJavaCheck(that.expr, notnull, Label.POSSIBLY_NULL_UNBOX, Label.UNDEFINED_NULL_UNBOX,
						"java.lang.NullPointerException");
				newexpr = rac ? castexpr : createUnboxingExpr(arg);
			}
		} else if (jmltypes.isSameType(clazz.type, jmltypes.BIGINT)) {
			if (origType.isPrimitive()) {
				// FIXME - need assumptions about range of output
				// Java primitive to JML \bigint - must be a numeric cast
				switch (origType.getTag()) {
				case LONG:
				case INT:
				case SHORT:
				case CHAR:
				case BYTE:
					String s = "bigint_valueOf";
					JCExpression e = treeutils.makeUtilsMethodCall(that.pos, s, arg);
					newexpr = e;
					break;
				case FLOAT:
				case DOUBLE:
					// FIXME float/double to bigint
					// continue using cast expression
					break;
				default:
					log.error(that.pos, "jml.internal",
							"Unexpected cast from " + origType + " via" + argType + " to " + that.type);
					// continue using cast expression
				}
			} else if (jmltypes.isSameType(origType, jmltypes.BIGINT)) {
				// this case should not happen
				newexpr = arg;
			} else if (jmltypes.isSameType(origType, jmltypes.REAL)) {
				// FIXME - reducing precision \real to \bigint
				String s = "real_to" + that.type.toString();
				JCExpression e = treeutils.makeUtilsMethodCall(that.pos, s, arg);
				newexpr = e;

			} else {
				// FIXME - unboxing numeric reference to \bigint
			}
		} else if (jmltypes.isSameType(clazz.type, jmltypes.REAL)) {
			if (origType.isPrimitive()) {
				// Java primitive to JML \real - must be a numeric cast
				// FIXME - need assumptions about range of output
				String s = "real_valueOf";
				JCExpression e = treeutils.makeUtilsMethodCall(that.pos, s, arg);
				newexpr = e;

			} else if (jmltypes.isSameType(origType, jmltypes.BIGINT)) {
				// convert \bigint to \real
				String s = "bigint_to" + that.type.toString();
				JCExpression e = treeutils.makeUtilsMethodCall(that.pos, s, arg);
				newexpr = e;

			} else if (jmltypes.isSameType(origType, jmltypes.REAL)) {
				// this case should not happen
				newexpr = arg;

			} else {
				// FIXME - unboxing numeric reference to \real
			}

		} else {
			if (origType.isPrimitive()) {
				// Must be primitive to object (boxing)
				// OK for Rac
				newexpr = rac ? castexpr : createBoxingStatsAndExpr(arg, clazz.type, false);
			} else if (jmltypes.isSameType(origType, jmltypes.BIGINT)) {
				// FIXME - box a \bigint to reference

			} else if (jmltypes.isSameType(origType, jmltypes.REAL)) {
				// FIXME - box a \real to reference

			} else if (esc && types.isSubtype(argType, clazz.type)) {
				// The cast is to a parent type and is statically allowed

				// No check needed
				newexpr = castexpr;

			} else {
				// object to object
				// For RAC, we check that the expression will not throw an exception
				// and then we calculate it
				// For ESC, we do the same check, but we don't do the cast

				JCTree erasure = clazz;
				if (clazz instanceof JCTypeApply)
					erasure = ((JCTypeApply) clazz).clazz;

				JCExpression typeok = M.at(that).TypeTest(arg, erasure);
				typeok.setType(syms.booleanType);
				// FIXME - end position?

				JCExpression cond = treeutils.makeOr(that.pos, eqnull, typeok);
				if (methodEnv.javaChecks && localVariables.isEmpty()) {
					cond = conditionedAssertion(that, cond);
					if (rac) {
						addAssert(that, translatingJML ? Label.UNDEFINED_BADCAST : Label.POSSIBLY_BADCAST, cond,
								arg.type, clazz.type);
					} else {
						addAssert(that, translatingJML ? Label.UNDEFINED_BADCAST : Label.POSSIBLY_BADCAST, cond,
								"a " + arg.type + " cannot be proved to be a " + clazz.type);
					}
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
		JCExpression e = M.at(that).TypeTest(lhs, clazz);
		e.setType(that.type);
        boolean hasNullable = type.type.getAnnotationMirrors().stream().anyMatch(a->a.type == attr.nullableAnnotationSymbol.type);
		if (hasNullable) {
	        JCExpression eqnull = treeutils.makeEqObject(that.pos, lhs, treeutils.makeNullLiteral(that.pos));
		    e = treeutils.makeOr(e,  eqnull, e);
		}
		treeutils.copyEndPosition(e, that);
		result = eresult = translatingJML ? e : newTemp(e);

	}

	public void addJavaCheck(DiagnosticPosition p, JCExpression cond, Label javaLabel, Label jmlLabel,
			String exception) {
		// FIXME - what if the dereference happens in a spec in a different file -
		// ,that,log.currentSourceFile());
		// FIXME- what should we do if !split, in particular what if this comes from
		// convertAssignable
		if (methodEnv.javaChecks && splitExpressions && localVariables.isEmpty()) {
			ClassSymbol csym = attr.createClass(exception);
			if (translatingJML) { // allow, forbid, ignore do not apply to JML
				cond = conditionedAssertion(p, cond);
				addAssert(p, jmlLabel, cond);
			} else {
				long line = JCDiagnostic.Factory.instance(context).error(null, log.currentSource(), p, "jml.message")
						.getLineNumber();
				boolean allow = findExplicitLineAnnotation(classDecl.lineAnnotations,
						LineAnnotationClauses.allowClauseKind, line, exception);
				boolean forbid = findExplicitLineAnnotation(classDecl.lineAnnotations,
						LineAnnotationClauses.forbidClauseKind, line, exception);
				boolean ignore = findExplicitLineAnnotation(classDecl.lineAnnotations,
						LineAnnotationClauses.ignoreClauseKind, line, exception);
				boolean useException = false;
				if (allow && forbid || allow && ignore || forbid && ignore) {
					utils.warning(p, "jml.message",
							"It is not permitted to have more than one of allow, forbid, ignore for one line");
				}
				if (allow) {
					useException = true;
				} else if (forbid) {
					useException = false;
				}
				if (!allow && !forbid && !ignore) {
					Type ex = csym.type;
					for (Type t : activeExceptions) {
						if (types.isSubtype(ex, t)) {
							useException = true;
							break;
						}
					}
				}
				if (ignore) {
					if (!rac)
						addAssume(p, javaLabel, cond);
				} else if (useException) {
					if (!rac)
						conditionalException(p, cond, csym); // For rac, Java throws the exception
				} else {
					addAssert(p, javaLabel, cond);
				}
			}
		}
	}

	public boolean findExplicitLineAnnotation(java.util.List<ExceptionLineAnnotation> list, IJmlClauseKind kind,
			long line, String exType) {
		if (list == null)
			return false;
		for (ExceptionLineAnnotation a : list) {
			if (a.line == line && a.clauseKind() == kind) {
				for (JCExpression e : a.exprs()) {
					if (e.type != null) {
						if (e.type.toString().equals(exType))
							return true; // FIXME - should compare by subtyping
						if (e.type == syms.runtimeExceptionType)
							return true; // FIXME - only true if exType is a subtype
					} else {
						// Backstop for bad exceptions
						if (e.toString().equals(exType))
							return true;
					}
				}
			}
		}
		return false;
	}

	public void conditionalException(DiagnosticPosition p, JCExpression cond, ClassSymbol csym) {
		Type ex = csym.type;
		JCExpression ty = M.at(p).Type(ex).setType(ex);
		JCNewClass ap = M.at(p).NewClass(null, null, ty, List.<JCExpression>nil(), null);
		ap.setType(ex);
		for (Symbol c : csym.getEnclosedElements()) {
			if (c.isConstructor() && ((MethodSymbol) c).getParameters().size() == 0) {
				ap.constructor = c;
				ap.constructorType = c.type;
				break;
			}
		}
		JCStatement th = M.at(p).Throw(ap);
		JCStatement iff = M.at(p).If(treeutils.makeNot(p, cond), th, null);
		iff.accept(this);
	}


	// OK
	@Override
	public void visitIndexed(JCArrayAccess that) {

		JCExpression indexed = convertExpr(that.indexed);

		// FIXME - resolve the use of splitExpressions 

		// FIXME - for now we don't check undefinedness inside quantified expressions
		JCExpression ind = that.indexed;
		Symbol sym = null;
		if (ind instanceof JCFieldAccess)
			sym = ((JCFieldAccess) ind).sym;
		if (ind instanceof JCIdent)
			sym = ((JCIdent) ind).sym;

		// FIXME _ readable?
//        checkAccess(JmlTokenKind.ACCESSIBLE, that.indexed, that.indexed, indexed, currentThisId, currentThisId);

		JCExpression index = null;
		// FIXME - better test for array type
		if (that.indexed.type instanceof Type.ArrayType) { // FIXME should be instancesof
															// org.jmlspecs.lang.IJmlIntArrayLike
			// This is a regular Java array index expression, with either an integral index
			// that must be in range
			// or a range value

			boolean checkNull = true;
			if (sym instanceof VarSymbol) {
				VarSymbol vsym = (VarSymbol) sym;
				checkNull = !(attr.isNonNull(vsym) && isModel(vsym));
			}
			if (checkNull) {
				if (ind instanceof JCArrayAccess aind && aind.index instanceof JmlRange) {
					// FIXME - should ensure that all elements in range are non-null
				} else {
					JCExpression nonnull = treeutils.makeNeqObject(that.indexed.pos, indexed, treeutils
							.makeNullLiteral(that.indexed.getEndPosition(log.currentSource().getEndPosTable())));
					addJavaCheck(that, nonnull, Label.POSSIBLY_NULL_DEREFERENCE, Label.UNDEFINED_NULL_DEREFERENCE,
							"java.lang.NullPointerException");
				}
			}

			if (!jmltypes.isAnyIntegral(that.index.type)) {
				// A range value
				var rt = rangeTypeKind.getType(context);
				var ta = indexed;
				if (that.index instanceof JmlRange) {
					var range = (JmlRange) that.index;
					if (range.lo == range.hi && range.lo != null) {
						JCExpression tl = convertExpr(range.lo);
						JmlBBArrayAccess aa = new JmlBBArrayAccess(null, ta, tl);
						aa.pos = that.pos;
						aa.type = that.type;
						result = eresult = aa;
					} else {
						JCExpression tl = convertExpr(range.lo);
						result = eresult = M.at(that)
								.Indexed(ta, M.at(that)
										.JmlRange(tl, (range.lo == range.hi) ? tl : convertExpr(range.hi)).setType(rt))
								.setType(that.type);
					}
				} else {
					// Should not happen, at least not yet
				}
				return;

			} else if (that.indexed.type instanceof Type.ArrayType) { // Don't do these tests for JML types
				index = convertExpr(that.index);
				if (that.indexed.type instanceof Type.ArrayType)
					index = addImplicitConversion(index, syms.intType, index);
				Number n = treeutils.integralLiteral(index);
				if (n != null && n.longValue() >= 0) {
					addStat(comment(index, "Constant index is non-negative: " + n.longValue(),
							log.currentSourceFile()));
				} else {
					JCExpression compare = treeutils.makeBinary(that.index.pos, JCTree.Tag.LE, treeutils.intleSymbol,
							treeutils.makeIntLiteral(that.index.pos, 0), index);
					addJavaCheck(that, compare, Label.POSSIBLY_NEGATIVEINDEX, Label.UNDEFINED_NEGATIVEINDEX,
							"java.lang.ArrayIndexOutOfBoundsException");
				}
				JCExpression length = treeutils.makeLength(that.indexed, indexed);
				JCExpression compare = treeutils.makeBinary(that.pos, JCTree.Tag.GT, treeutils.intgtSymbol, length,
						index); // We use GT to preserve the textual order of the subexpressions
				addJavaCheck(that, compare, Label.POSSIBLY_TOOLARGEINDEX, Label.UNDEFINED_TOOLARGEINDEX,
						"java.lang.ArrayIndexOutOfBoundsException");
			}
		} else {
			// In this case, the 'array' is a value type (a JML extension), so no checks for
			// nullity or range.
			// In fact the index might be any type
			// So nothing to do here except convert the index
			index = convertExpr(that.index);
		}

		{
			JmlBBArrayAccess aa = new JmlBBArrayAccess(null, indexed, index); // FIXME - switch to factory // is the
																				// null correct?
			aa.pos = that.pos;
			aa.setType(that.type);
			aa.arraysId = that instanceof JmlBBArrayAccess ? ((JmlBBArrayAccess) that).arraysId : null;
			JCExpression save = (translatingJML || convertingAssignable) ? aa : newTemp(aa);

			if (utils.isExtensionValueType(that.indexed.type)) {
				// continue
			} else if (esc && localVariables.isEmpty()) {
				if (utils.isJavaOrJmlPrimitiveType(that.type)) {
					if (that.type == syms.byteType) {
						JCExpression e1 = treeutils.makeBinary(that.pos, JCTree.Tag.LE, treeutils.intleSymbol,
								treeutils.makeIntLiteral(save, -128), save);
						JCExpression e2 = treeutils.makeBinary(that.pos, JCTree.Tag.LE, treeutils.intleSymbol, save,
								treeutils.makeIntLiteral(save, 127));
						addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeAnd(that, e1, e2));
					} // FIXME - other types, share this code with elsewhere?
				} else { // FIXME - we perhaps need quantified sstatements if we are within a qunatified
							// scope
					// assume \typeof(eresult) <: \elemtype(\typeof(indexed));
					JCExpression e1 = treeutils.makeTypeof(save);
					JCExpression e2 = treeutils.makeElemtype(treeutils.makeTypeof(indexed));
					e1 = treeutils.makeSubtype(e1, e1, e2);
					addAssume(that, Label.IMPLICIT_ASSUME, e1);
				}
			}
			if (!translatingJML) {
				checkAccess2(accessibleClauseKind, that, that, aa, true, treeutils.trueLit, true, null, false);
				// checkAccess(accessibleClauseKind, that, that, aa, classDecl.type,
				// currentEnv.currentReceiver, currentEnv.currentReceiver);
			}
			result = eresult = save;
		}

		treeutils.copyEndPosition(result, that);
	}

	public JCExpression conditionedAssertion(DiagnosticPosition pos, JCExpression expr) {
		int p = pos.getPreferredPosition();
		if (expr instanceof JCLiteral) {
		} // no need to wrap in an old
		else if (currentEnv.stateLabel != null) {
			expr = makeOld(p, expr, currentEnv.stateLabel);
		}
		if (condition != null) expr = treeutils.makeImpliesSimp(p, condition, expr);
		return expr;
	}

	// OK
	@Override
	public void visitSelect(JCFieldAccess that) {
	    boolean print = false; // that.toString().endsWith(".balance");
        if (print) System.out.println("VISITSELECT-A " + that );
		JCExpression selected;
		Symbol s = convertSymbol(that.sym);
		JCExpression trexpr = that.getExpression();

		//System.out.println("VISIT-SELECT " + that + " " + that.sym + " " + s + " " + trexpr);
		if (!(s instanceof Symbol.TypeSymbol)) trexpr = convertExpr(trexpr);
        if (print) System.out.println("VISITSELECT " + that + " " + trexpr);
		JCFieldAccess newfa = null;
		Symbol sym = s;
		JCExpression eee = null;
		if (sym != null && sym.owner instanceof ClassSymbol) {
			if (utils.isJMLStatic(sym))
				newfa = treeutils.makeSelect(that.pos, treeutils.makeType(that.pos, sym.owner.type), sym);
			else
				newfa = treeutils.makeSelect(that.pos, trexpr, sym);
		}
		if (!rac && s != null && s.name != names._class && alreadyDiscoveredFields.add(s)) { // true if s was NOT in the
																								// set already
			if (utils.isJMLStatic(s) && (s.flags_field & Flags.FINAL) != 0) {
				addFinalStaticField(newfa);
			} else {
				utils.note(true, "No invariants created for " + that);
			}
		}
		if (esc && sym == syms.lengthVar && jmltypes.isArray(trexpr.type)) {
	        if (print) System.out.println("VISITSELECT-ARRAYLIKE " + that + " " + trexpr);
			JCExpression ntrExpr = copy(trexpr);
			JCExpression newfaa = treeutils.makeSelect(that.pos, ntrExpr, sym);
			JCExpression bina = treeutils.makeBinary(that, JCTree.Tag.LE, treeutils.intleSymbol,
					treeutils.makeIntLiteral(that, 0), newfaa);
			JCExpression binb = treeutils.makeBinary(that, JCTree.Tag.LE, treeutils.intleSymbol, copy(newfaa),
					treeutils.makeIntLiteral(that, Integer.MAX_VALUE));
			addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeAnd(that, bina, binb));
		}
		if (that.sym != null && that.sym.name != names._class) {
		    checkRW(readableClause, that.sym, trexpr, that);
		}
		if (!convertingAssignable && checkAccessEnabled) {
			checkAccess2(accessibleClauseKind, that, that, newfa, true, treeutils.trueLit, true, null, false); // FIXME - condition?
		}
        if (print) System.out.println("VISITSELECT-B " + that + " " + trexpr + " " + newfa);
		if (localVariables.containsKey(s)) {
			eee = newfa;
		} else if ((infer || esc) && s != null && s.name == names._class) {
			eee = treeutils.makeJavaTypelc(that.selected);
//		} else if (that.sym == allocSym) {
//			eee = M.at(that.pos).Select(trexpr, that.sym);
//		} else if (translatingJML && s == null) {
//			// This can happen while scanning a store-ref x.*
//			JCExpression sel = trexpr; // FIXME - what if static; what if not a variable
//			JCFieldAccess fa = M.Select(sel, (Name) null);
//			fa.pos = that.pos;
//			fa.sym = null;
//			eee = fa;
		} else if (translatingJML && (s == null || (s instanceof VarSymbol && (utils.isModel(s) || utils.isJML(s.owner.flags()))
				&& !convertingAssignable))) {
			selected = copy(trexpr);

			// FIXME - why must selected be a JCIdent here and below
			if (s==null || (!utils.isJMLStatic(s) && (!(that.selected instanceof JCIdent)
					|| !localVariables.containsKey(((JCIdent) that.selected).sym)))) {
				if (convertingAssignable && currentFresh != null && selected instanceof JCIdent
						&& ((JCIdent) selected).sym == currentFresh.sym) {
					// continue
				} else if (!utils.isJavaOrJmlPrimitiveType(that.selected.type)) {
					JCExpression nonnull = treeutils.trueLit;
					if (!utils.isJavaOrJmlPrimitiveType(selected.type))
						nonnull = treeutils.makeNotNull(that.pos, selected);
					if (selected.toString().contains(Strings.newObjectVarString))
						nonnull = treeutils.trueLit;

					addJavaCheck(that, nonnull, Label.POSSIBLY_NULL_DEREFERENCE, Label.UNDEFINED_NULL_DEREFERENCE,
							"java.lang.NullPointerException");
					// FIXME - what if the dereference happens in a spec in a different file -
					// ,that,log.currentSourceFile());
				}
			}

			Type type = that.selected.type;
			if (type instanceof Type.TypeVar)
				type = ((Type.TypeVar) type).getUpperBound();
			// result = eresult = treeutils.makeSelect(that.pos, selected, s);
			// The following method sets result and eresult
			if (s != null && !reps.contains(s)) {
			    // copying the untranslated that.selected here because it is converted in addRepresentsAxioms and
			    // that.selected may be wrapped in \old wrappers -- really?
			    addRepresentsAxioms((ClassSymbol) type.tsym, s, that, selected);
			}
			// The tsym can be a TypeVar
            if (print) System.out.println("VISITSELECT-M " + that + " " + trexpr + " " + eresult);
            
            if (rac && utils.isModel(s)) {
                JCFieldAccess recv = M.at(that.pos).Select(trexpr, names.fromString(Strings.modelFieldMethodPrefix + that.name.toString()));
                recv.sym = JmlMemberEnter.instance(context).modelMethods.get(s).sym;
                recv.type = recv.sym.type;
                result = eresult = M.at(that.pos).Apply(null,recv, List.<JCExpression>nil());
                eresult.type = that.type;
                //System.out.println("MODEL " + that + " " + eresult + " " + recv.sym + " " + recv.type);
            } else {
                if (currentEnv.stateLabel != null) {
                    result = eresult = makeOld(newfa.pos, newfa, currentEnv.stateLabel);
                } else {
                    result = eresult = newfa;
                }
                if (print) System.out.println("VISITSELECT-HERE " + eresult);
            }
            
			return; // TODO REVIEW - why this return here - why not do the remainder of visitSelect
		} else if (s instanceof Symbol.TypeSymbol) {
			// This is a type name, so the tree should be copied, but without inserting
			// temporary assignments
			// makeType creates a fully-qualified name
			eee = treeutils.makeType(that.pos, that.type);
		} else if (translatingJML && (infer || esc) && !localVariables.isEmpty()) {
		    if (print) System.out.println("VISITSELECT-Q " + that + " " + trexpr);
			selected = trexpr;
			JCFieldAccess fa = treeutils.makeSelect(that.pos, selected, s);
			eee = fa;
			if (currentEnv.stateLabel != null) {
				eee = makeOld(that.pos, eee, currentEnv.stateLabel);
			}
//        } else if (translatingJML) {
//            selected = convertExpr(that.selected);
//            boolean var = false;
//            JCFieldAccess fa = treeutils.makeSelect(that.pos,selected,that.sym);
//            result = eresult = fa;
//            if (oldenv != null) {
//                result = eresult = treeutils.makeOld(that.pos,eresult,oldenv);
//            }
		} else if (s instanceof MethodSymbol && s.name.toString().equals("erasure")
				&& utils.qualifiedName((MethodSymbol) s).equals(Strings.jmlSpecsPackage + ".JML.erasure")) {
			JCMethodInvocation m = treeutils.makeUtilsMethodCall(that.pos, "erasure");
			eee = m.meth;
		} else {
			selected = copy(trexpr);
			boolean var = false;
			if (treeutils.isATypeTree(selected) && s.name == names._this) {
				if (rac) {
					result = eresult = that;
					return;
				} else {
		            if (print) System.out.println("VISITSELECT-R " + that + " " + trexpr);
					VarSymbol vsym = makeEnclosingSymbol(classDecl.sym, currentEnv.currentReceiver);
					selected = currentEnv.currentReceiver;
					s = vsym;
					eee = treeutils.makeSelect(that.pos, currentEnv.currentReceiver, vsym);
					addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeNotNull(that.pos, eee));
				}
			} else if (!utils.isJMLStatic(s) && (!(that.selected instanceof JCIdent)
					|| !localVariables.containsKey(((JCIdent) that.selected).sym))) {
				JCIdent id = that.selected instanceof JCIdent ? (JCIdent) that.selected : null;
				if (convertingAssignable && currentFresh != null && selected instanceof JCIdent
						&& ((JCIdent) selected).sym == currentFresh.sym) {
					// continue
				} else if (id != null && id.sym.isEnum() && id.sym.isStatic()
						&& ((id.sym.flags() & Flags.FINAL) != 0)) {
					// Optimization: Enum constants are always non-null
					// addStat(comment(that.selected,"Skipping non-null check of " +
					// that.selected.toString(), log.currentSourceFile()));
				} else {
					JCExpression nonnull = treeutils.trueLit;
					if (!utils.isJavaOrJmlPrimitiveType(selected.type))
						nonnull = treeutils.makeNotNull(that.pos, selected);
					if (selected.toString().contains(Strings.newObjectVarString))
						nonnull = treeutils.trueLit;

					addJavaCheck(that, nonnull, Label.POSSIBLY_NULL_DEREFERENCE, Label.UNDEFINED_NULL_DEREFERENCE,
							"java.lang.NullPointerException");
//                    if (translatingJML) nonnull = conditionedAssertion(that, nonnull);
//                    if (methodEnv.javaChecks && localVariables.isEmpty()) {
//                        if (splitExpressions) { // FIXME- what should we do if !split, in particular what if this comes from convertAssignable
//                            addAssert(that,
//                                translatingJML? Label.UNDEFINED_NULL_DEREFERENCE : Label.POSSIBLY_NULL_DEREFERENCE,
//                                        nonnull); // FIXME - what if the dereference happens in a spec in a different file - ,that,log.currentSourceFile());

//                        } else if (!treeutils.isTrueLit(nonnull)){
//                            condition = treeutils.makeImpliesSimp(that.pos, condition, nonnull);
//                        }
//                    }
				}
				var = true;
			}
			if (s.owner instanceof ClassSymbol) {
				if (specs.isNonNull(s) && s instanceof VarSymbol && !localVariables.containsKey(s)) {
					if (convertingAssignable && currentFresh != null && selected instanceof JCIdent
							&& ((JCIdent) selected).sym == currentFresh.sym) {
						// continue
					} else if (!utils.isJavaOrJmlPrimitiveType(s.type)) {
						// Check that the field is not null, if it is declared non_null
						JCFieldAccess e = M.at(that).Select(selected, that.name);
						e.sym = s;
						e.type = that.type;
						JCExpression ee = e;
						if (currentEnv.stateLabel != null && !rac) {
							ee = makeOld(e.pos, e, currentEnv.stateLabel);
						}
						JCExpression nl = treeutils.makeNullLiteral(that.pos);
						treeutils.copyEndPosition(nl, ee);
						JCExpression nonnull = treeutils.makeNeqObject(that.pos, ee, nl);
						if (methodDecl.sym.isConstructor() && !utils.isJMLStatic(that.sym)
								&& (s.owner == methodDecl.sym.owner) && currentEnv.currentReceiver != null && !inInvariantFor) { // FIXME
																														// -
																														// needs
																														// review
							// If the method being translated is a constructor and the field in question is
							// not static
							// and the object being dereferenced is indeed the object being constructed,
							// then the
							// field is allowed to be null, because the construction is in progress
							JCExpression ne = treeutils.makeNeqObject(that.pos, currentEnv.currentReceiver, selected);
							nonnull = treeutils.makeImplies(nonnull.pos, ne, nonnull);
						}
						addAssume(nonnull, Label.NULL_FIELD, nonnull);
					}
				}
			}
			// if (!translatingJML && that.sym != syms.lengthVar)
			// checkAccess(JmlToken.ACCESSIBLE, that, that, (VarSymbol)currentThisId.sym,
			// (VarSymbol)currentThisId.sym);
			JCFieldAccess fa = treeutils.makeSelect(that.pos, selected, s);
            if (print) System.out.println("VISITSELECT-X " + that + " " + fa + " " + trexpr);
			fa.type = that.type; // in rac the type can be changed to a representation type
//	        if (!translatingJML && (sym.flags() & Flags.VOLATILE) != 0 && sym.owner instanceof ClassSymbol) {
//	            boolean constructorField = fa.sym.owner instanceof TypeSymbol && methodDecl.sym.isConstructor()
//	                                    && !utils.isJMLStatic(fa.sym);
//	            if (!constructorField) checkAccess2(assignableClauseKind, that, that, fa, true, treeutils.trueLit, true, null, false);
//	            addStat(M.at(that).JmlHavocStatement(List.<JCExpression>of(fa)));
//	        }
			eee = fa;
			if (currentEnv.stateLabel != null && !translatingLHS) {
				eee = makeOld(that.pos, eee, currentEnv.stateLabel); // FIXME - will make overly nested \old expressions
			}
			eee = (!var || convertingAssignable || !splitExpressions || rac) ? eee : newTemp(eee);
		}
		treeutils.copyEndPosition(result, that);
		if (!utils.isJavaOrJmlPrimitiveType(that.selected.type)) {
//			System.out.println("VISIT-SELECT-Y " + that.selected.type + " " + !utils.isJavaOrJmlPrimitiveType(that.selected.type) + " " + translatingJML + " " + s + " " + specs.isNonNull(s));
			if (translatingJML && s instanceof VarSymbol && specs.isNonNull(s)) {
				JCExpression nn = treeutils.makeNeqObject(that.pos, eee, treeutils.nullLit);
				addToCondition(that.pos, nn);
			} else if (esc && splitExpressions && s != null && s.name == names._class) {
				JCExpression nn = treeutils.makeNeqObject(that.pos, eee, treeutils.nullLit);
				addAssume(that, Label.IMPLICIT_ASSUME, nn);
			}
		}
		result = eresult = eee;
		if (print) System.out.println("VISITSELECT-Z " + that + " " + eresult);
	}

	protected Symbol classSuffix = null;

	public static class NoModelMethod extends RuntimeException {
		private static final long serialVersionUID = 1L;

		public NoModelMethod() {
			super();
		}

		public NoModelMethod(String msg) {
			super(msg);
		}
	}

	// FIXME - check use of condition everywhere

	java.util.List<Symbol> reps = new LinkedList<>();

	// OK
	@Override
	public void visitIdent(JCIdent that) {
		if (that.sym == null) {
			utils.error(that, "jml.message", "NULL SYMBOL " + that);
		}
		if (translatingLambda && that.sym.name == names._this) {
			copy(currentEnv.currentReceiver);
			return;
		}
		
//		if (that.name.toString().contains("result") || that.name.toString().contains("rep") || that.name.toString().contains("value")) {
//		    System.out.println("VISIT IDENT " + that + " " + paramActuals_);
//		}

		//		System.out.println("VISIT-IDENT " + that + " " + oldenv); 
		if (utils.rac && currentEnv.stateLabel != null && utils.isExprLocal(that.sym.flags()) && !that.toString().equals("this")) {
			// FIXME - thiz should be allopwed if the whole qukantifier expression is in the
			// same old context
			String message = "quantifier variable inside a \\old or \\pre expression: " + that.toString();
			throw new JmlNotImplementedException.Quantifier(that, message);
		}
		//System.out.println("VISITIDENT " + that + " " + oldenv + " " + translatingJML);
		Symbol sym = convertSymbol(that.sym);

		// FIXME - what about super when esc? or when we have a different
		// currentEnv.currentReceiver?
		if (sym.name == names._super && rac
				&& (currentEnv.currentReceiver.toString().equals("this") || currentEnv.currentReceiver.toString().equals(Strings.THIS))) {
			// super is special in that it precludes dynamic dispatch
			// reaming super to a new ident would just end up calling the child method again
			result = eresult = that;
			return;
		}
		JCFieldAccess newfa = null;
		if (sym != null && sym.owner instanceof ClassSymbol) {
			if (currentEnv.currentReceiver != null && sym instanceof VarSymbol && sym.owner != currentEnv.currentReceiver.type.tsym
					&& (currentEnv.currentReceiver.type.tsym instanceof ClassSymbol)) {
				ClassSymbol base = (ClassSymbol) currentEnv.currentReceiver.type.tsym;
				ClassSymbol fieldOwner = (ClassSymbol) sym.owner;
				JCExpression baseExpr = currentEnv.currentReceiver;
				while (true) {
					if (base.isSubClass(fieldOwner, types)) { // true if the same class or directly or indirectly the
																// subclass
						if (utils.isJMLStatic(sym))
							newfa = treeutils.makeSelect(that.pos, treeutils.makeType(that.pos, fieldOwner.type), sym);
						else
							newfa = treeutils.makeSelect(that.pos, baseExpr, sym);
						break;
					}
					VarSymbol enclFieldSym = enclosingClassFieldSymbols.get(base);
					if (enclFieldSym == null)
						break;
					Symbol bsym = base.owner;
					if (!(bsym instanceof ClassSymbol))
						break;
					base = (ClassSymbol) bsym;
					baseExpr = treeutils.makeSelect(that.pos, baseExpr, enclFieldSym); // FIXME - does not work for more
																						// than one level
				}
				if (newfa == null) {
					if (utils.isJMLStatic(sym))
						newfa = treeutils.makeSelect(that.pos, treeutils.makeType(that.pos, sym.owner.type), sym);
					else
						newfa = treeutils.makeSelect(that.pos, currentEnv.currentReceiver, sym);
				}
			} else {
				if (utils.isJMLStatic(sym)) {
					newfa = treeutils.makeSelect(that.pos, treeutils.makeType(that.pos, sym.owner.type), sym);
					newfa.type = that.type;
				} else {
					newfa = treeutils.makeSelect(that.pos, currentEnv.currentReceiver, sym);
					newfa.type = that.type;
				}
			}
		}
		if (!rac && sym != null && alreadyDiscoveredFields.add(sym)) { // true if s was NOT in the set already
			if (utils.isJMLStatic(sym) && isFinal(sym)) {
				if (newfa != null)
					addFinalStaticField(newfa);
			} else if (sym.kind == Kinds.Kind.VAR && sym.owner != null && sym.owner.kind == Kinds.Kind.MTH
					&& splitExpressions && !localVariables.containsKey(sym)
					&& !isFormal(sym, (MethodSymbol) sym.owner)) {
				addLocalVar(that);
			} else {
				utils.note(true, "No invariants created for " + that);
			}
		}

        if (!translatingLHS)
            checkRW(readableClause, that.sym, currentEnv.currentReceiver, that);
//        System.out.println("VISITIDENT-D " + that + " " + oldenv + " " + eresult + " " + translatingJML);

//		if (!translatingJML && (sym.flags() & Flags.VOLATILE) != 0 && sym.owner instanceof ClassSymbol) {
//	        boolean constructorField = that.sym.owner instanceof TypeSymbol && methodDecl.sym.isConstructor()
//	                                && !that.sym.isStatic();
//	        if (!constructorField) checkAccess2(assignableClauseKind, that, that, newfa, true, treeutils.trueLit, true, null, false);
//		    addStat(M.at(that).JmlHavocStatement(List.<JCExpression>of(newfa)));
//		}
		try {
			// If we are translating the postcondition then parameters
			// must be mapped to the values at the beginning of the method,
			// not the current values
			if (translatingJML) {
			    boolean print = false;//(that.toString().equals("s1") || that.toString().equals("s2")) && sym.owner.toString().contains("equals");
				if (print) System.out.println("VISITIDENT-E " + that + " " + isPostcondition + " "
						+ sym + " " + sym.owner + " " + sym.owner.getClass() + " " + isFormal(sym, methodDecl.sym) + " " + paramActuals_);
				if (print) Utils.dumpStack();
				if (!isPostcondition) {
					JCExpression actual = paramActuals_ == null ? null : paramActuals_.get(sym);
					//if (sym.toString().equals("dxyz")) System.out.println("VISIT-IDENT-DD " + sym + " " + sym.hashCode() + " " + actual + " " + System.identityHashCode(actual) + " " + paramActuals_);
					if (actual != null) {
						// Replicate the AST so we are not sharing ASTs across multiple
						// instances of the original ID.
						// System.out.println("MAPPED " + sym + " " + sym.hashCode() + " TO " + actual);
						result = eresult = copy(actual);
						eresult.pos = that.pos; // FIXME - this might be better if the actual were converted to a
												// temporary Ident
						treeutils.copyEndPosition(eresult, that);
						return;
					}
				}
				//System.out.println("VISITIDENT-F " + that + " " + oldenv + " " + isPostcondition);
				if (esc && (that.name == names._this || that.name == names._super)) {
					result = eresult = currentEnv.currentReceiver != null ? copy(currentEnv.currentReceiver) : copy(that);
					return;
				}
				if (esc && isPostcondition && isFormal(sym, methodDecl.sym)) {
					// Variables are owned by methods if they are locals or formals
					// Locals can't be in postcondition, so this must be a formal
					// Formals are evaluated in the pre-state
					// It can also be an old id from the specification
					// Name nm = utils.isJMLTop(sym.flags()) ? names.fromString("Precondition") :
					// preLabel.name;
					JCExpression actual = paramActuals_ == null ? null : paramActuals_.get(sym);
					//if (sym.toString().equals("dxyz")) System.out.println("VISIT-IDENT-DX " + sym + " " + sym.hashCode() + " " + actual + " " + System.identityHashCode(actual) + " " + paramActuals_);

                    if (actual == null) actual = treeutils.makeIdent(that.pos, sym); // FIXME - if it is a formal there shuld always be
																		// a mapping
					result = eresult = treeutils.makeOld(that, actual, labelPropertiesStore.get(currentOldLabel));
					treeutils.copyEndPosition(eresult, that);
					return;
				}
				if (rac && isPostcondition && isFormal(sym, methodDecl.sym)) {
					//System.out.println("VISITIDENT-RAC-POST " + that + " " + currentEnv.label + " " + isPostcondition + " " + eresult);
					JCExpression e = treeutils.makeOld(that, treeutils.makeIdent(that.pos, sym), labelPropertiesStore.get(currentOldLabel));
					isPostcondition = false;
					result = eresult = convertExpr(e);
					isPostcondition = true;
					treeutils.copyEndPosition(eresult, that);
					return;
				}
			}

			// Check if the id is a model field, and if so:
			// if rac, then map it to a call of
			// the corrresponding model method. We have to use model methods
			// instead of just inlining the represents clause expression because
			// the model field/method may be overridden in derived classes.
			// FIXME - this is needed for ESC as well, not sure why
			if (utils.isModel(sym) && sym instanceof VarSymbol && !convertingAssignable && !reps.contains(sym)) {
				translateModelField(currentEnv.currentReceiver, that, sym, newfa);
//	            System.out.println("VISITIDENT-F " + that + " " + eresult);
				// FIXME - if this is translated, then the tranlation below is not needed
				// FIXME - if this is not trznslated, then why the return
				return;
			}

//            System.out.println("VISITIDENT-G " + that + " " + oldenv);
			// FIXME - are we expecting fully-qualified arguments?
			if (checkAccessEnabled) {
				var trlhs = convertAssignable(that, currentEnv.currentReceiver, true, log.currentSourceFile());
				// We don't care about type names -- the name of the type in new T() comes here
				if (that.sym instanceof VarSymbol)
					checkAccess2(accessibleClauseKind, that, that, that, false, treeutils.trueLit, true, null, false);
				// checkAccess(accessibleClauseKind, that, that, trlhs, classDecl.type,
				// currentEnv.currentReceiver, currentEnv.currentReceiver);
//	            System.out.println("VISITIDENT-H " + that + " " + eresult);
			}
//            System.out.println("VISITIDENT-H " + that + " " + oldenv);
			// Lookup if there is some other translation of the id. For example,
			// this could be a translation of the formal from the specification
			// in a parent class mapped to the formal in the target class. It
			// can also be the mapping from a formal to actual argument.
			boolean local = false;
			JCExpression actual = paramActuals_ == null ? null : paramActuals_.get(sym);
			if (actual != null) {
				// Replicate the AST so we are not sharing ASTs across multiple
				// instances of the original ID.
				result = eresult = copy(actual);
                //System.out.println("VISITIDENT-K " + that + " " + eresult);
				eresult.pos = that.pos;
				treeutils.copyEndPosition(eresult, that);

//            } else if (sym.type instanceof Type.TypeVar) {
//                Type t = typevarMapping.get(sym.type.tsym);
//                result = eresult = treeutils.makeType(that.pos,t);

			} else if (localVariables.containsKey(sym)) {
				// just copy - bound in a quantification
				Symbol sy = localVariables.get(sym);
				result = eresult = treeutils.makeIdent(that.pos, sy);
				local = true;

			} else if (!(sym.owner instanceof Symbol.TypeSymbol)) {
				// local variable or formal parameter - just leave it as
				// an ident (the owner is null or the method)
				// System.out.println("LOCAL " + that);
				eresult = null;
				if (sym.owner != methodDecl.sym) {
					Name nm = that.name;
					for (JCTree t : classDecl.defs) {
						if (!(t instanceof JmlVariableDecl)) continue;
						JmlVariableDecl vd = (JmlVariableDecl) t;
						if (vd.name != nm) continue;
						if (!attr.isCaptured(vd)) continue;
						result = eresult = M.at(vd.pos).Select(currentEnv.currentReceiver, vd.sym);
						eresult.type = vd.type;
//			            System.out.println("VISITIDENT-K " + that + " " + eresult);
						break;
					}
				}
				if (sym.owner == methodDecl.sym || eresult == null) {
					JCExpression id = treeutils.makeIdent(that.pos, sym);
					result = eresult = id;
					local = true;
				}

			} else if (currentEnv.currentReceiver instanceof JCIdent id && sym == id.sym) {
				// 'this' - leave it as it is
				result = eresult = copy(currentEnv.currentReceiver);
//	            System.out.println("VISITIDENT-L " + that + " " + eresult);

			} else if (that.name == names._this) {
				result = eresult = currentEnv.currentReceiver != null ? copy(currentEnv.currentReceiver) : copy(that);

			} else if (that.name == names._super) {
				result = eresult = currentEnv.currentReceiver != null ? copy(currentEnv.currentReceiver) : copy(that);
				
			} else if (that.name.equals(heapVarName)) {
				result = eresult = copy(that);

			} else if (rac && utils.isModel(sym) && sym instanceof VarSymbol && !convertingAssignable) {
			    JCExpression recv = currentEnv.currentReceiver != null ? copy(currentEnv.currentReceiver) : copy(that);
                JCFieldAccess fcn = M.at(that.pos).Select(recv, names.fromString(Strings.modelFieldMethodPrefix + that.name.toString()));
                fcn.sym = JmlMemberEnter.instance(context).modelMethods.get(sym).sym;
                fcn.type = fcn.sym.type;
                result = eresult = M.at(that.pos).Apply(null, fcn, List.<JCExpression>nil());
                eresult.type = that.type;
			    
			} else if (sym instanceof Symbol.TypeSymbol) {
				Type t = typevarValue(that.type, typevarMapping);
				// The input id is a type, so we expand it to a FQ name
				// If the input id is a type variable (that.type instanceof Type.TypeVar)
				// then makeType creates a new JCIdent, as is appropriate.
				result = eresult = treeutils.makeType(that.pos, t);
//	            System.out.println("VISITIDENT-N " + that + " " + eresult);

//            } else if (sym instanceof Symbol.MethodSymbol) {
//                {
//                    Map<Symbol,MethodSymbol> pm;
//                    Name nm = oldenv == null ? null : oldenv.name;
//                    pm = oldHeapMethods.get(nm);
//                    MethodSymbol msym = (MethodSymbol)sym;
////                    if (pm == null)) {
////                        newNameForCallee(that.sym)
////                    }
//                    if (pm != null) msym = pm.get(sym);
//                    if (msym != null) {
//                        result = eresult = treeutils.makeIdent(that.pos, msym);
//                    } else {
//                        result = eresult = treeutils.makeIdent(that.pos, sym);
//                    }
//                }
			} else if (!utils.isJMLStatic(sym)) {
				// It is a non-static class field, so we prepend the receiver

//                System.out.println("VISITIDENT-P " + that + " " + oldenv);
				// FIXME - if currentEnv.currentReceiver is null, when not static, it should be the object
				// being constructed
				if (esc && currentEnv.currentReceiver != null && sym.owner != currentEnv.currentReceiver.type.tsym
						&& currentEnv.currentReceiver.type.tsym instanceof ClassSymbol) {
					ClassSymbol base = (ClassSymbol) currentEnv.currentReceiver.type.tsym;
					ClassSymbol fieldOwner = (ClassSymbol) sym.owner;
					JCExpression baseExpr = currentEnv.currentReceiver;
					while (true) {
						if (base.isSubClass(fieldOwner, types)) { // true if the same class or directly or indirectly
																	// the subclass
							if (utils.isJMLStatic(sym))
								newfa = treeutils.makeSelect(that.pos, treeutils.makeType(that.pos, fieldOwner.type),
										sym);
							else
								newfa = treeutils.makeSelect(that.pos, baseExpr, sym);
							break;
						}
						VarSymbol enclFieldSym = enclosingClassFieldSymbols.get(base);
						if (enclFieldSym == null)
							break;
						Symbol bsym = base.owner;
						if (!(bsym instanceof ClassSymbol))
							break;
						base = (ClassSymbol) bsym;
						baseExpr = treeutils.makeSelect(that.pos, baseExpr, enclFieldSym); // FIXME - does not work for
																							// more than one level
					}
					if (newfa == null) {
						// FIXME - already tested for static
						if (utils.isJMLStatic(sym))
							newfa = treeutils.makeSelect(that.pos, treeutils.makeType(that.pos, sym.owner.type), sym);
						else
							newfa = treeutils.makeSelect(that.pos, currentEnv.currentReceiver, sym);
					}
				} else {
					// FIXME - already tested for static
					if (utils.isJMLStatic(sym))
						newfa = treeutils.makeSelect(that.pos, treeutils.makeType(that.pos, sym.owner.type), sym);
					else
						newfa = treeutils.makeSelect(that.pos, currentEnv.currentReceiver, sym);
				}
				JCExpression cp = copy(newfa.getExpression());
				if (cp != null && cp.toString().equals(Strings.THIS))
					((JCIdent) cp).pos = that.pos;
				JCExpression fa = treeutils.makeSelect(that.pos, cp, that.sym);
				fa.type = convertType(fa.type);
//                if (sym instanceof VarSymbol && sym.owner instanceof ClassSymbol && specs.isNonNull(sym, classDecl.sym) && !localVariables.isEmpty()) {
//                    JCExpression e = treeutils.makeNotNull(that.pos, fa);
//                    addAssume(that,Label.NULL_FIELD,e);
//                }
				result = eresult = fa;
//	            System.out.println("VISITIDENT-PP " + that + " " + eresult);

			} else {
//               System.out.println("VISITIDENT-Q " + that + " " + oldenv);
				// static class field - add the qualified name
				JCExpression typetree = treeutils.makeType(that.pos, sym.owner.type);
				JCFieldAccess fa = treeutils.makeSelect(that.pos, typetree, sym);
				if (!translatingJML && that.sym instanceof VarSymbol && that.sym.owner instanceof ClassSymbol
						&& specs.isNonNull(sym)) {
					JCExpression e = treeutils.trueLit;
					if (!utils.isJavaOrJmlPrimitiveType(fa.type))
						e = treeutils.makeNotNull(that.pos, fa);
					addAssume(that, Label.NULL_FIELD, e);
				}
				result = eresult = fa;
//	            System.out.println("VISITIDENT-QQ " + that + " " + eresult);
			}
//            System.out.println("VISITIDENT-T " + that + " " + oldenv);
			treeutils.copyEndPosition(eresult, that);
			if (currentEnv.stateLabel != null && !rac) {
//            	System.out.println("IDENT_OLDENV-A " + that + " " + eresult);
				// FIXME - the old may imappropriately encapsulate the receiver
				result = eresult = makeOld(that.pos, eresult, currentEnv.stateLabel);
//            	System.out.println("IDENT_OLDENV-Z " + that + " " + eresult);
				treeutils.copyEndPosition(eresult, that);
			}
			// Need to capture the result in a temporary, because the value of the JCIdent might change, e.g. even within the same expression,
			// but not if we are within JML
			if (esc && splitExpressions && sym instanceof VarSymbol && !translatingJML
					&& !(eresult instanceof JCLambda) && !(eresult instanceof JCMemberReference)) {
			    JCIdent nm = newTemp(eresult);
				saveMapping(that, nm);
				// Can't set eresult = nm generally because this ident might be an LHS.
				if (!translatingLHS || eresult instanceof JmlMethodInvocation)
					result = eresult = nm;
				else
					result = eresult = copy(eresult);
			}
//            System.out.println("VISITIDENT-W " + that + " " + eresult);

		} finally {
			// Note that since 'this' is a ClassSymbol, not a VarSymbol, no check for
			// non-null is made here, which is just fine.
			// Also lambda expressions as actual arguments are automatically non-null
			if (translatingJML && !utils.isJavaOrJmlPrimitiveType(that.type) && sym instanceof VarSymbol
					&& specs.isNonNull(sym) && eresult != null && !(eresult instanceof JCLambda)
					&& !(eresult instanceof JCMemberReference)) {
//				System.out.println("VISIT-IDENT-Z " + that + " " + eresult);
				JCExpression nn = treeutils.makeNotNull(that.pos, eresult);
				addToCondition(that.pos, nn);
			}
//            System.out.println("VISITIDENT-Z " + that + " " + oldenv);

		}
	}

	protected void translateModelField(JCExpression translatedReceiver, JCIdent that, Symbol sym, JCFieldAccess newfa) {
		// translatedReceiver is null if the symbol is static
		TypeSymbol tsym = translatedReceiver != null ? translatedReceiver.type.tsym : (TypeSymbol) sym.owner; // FIXME -
																												// perhaps
																												// can
																												// always
																												// be
																												// sym.owner
		addRepresentsAxioms(tsym, sym, that, translatedReceiver);
		// if (checkAccessEnabled) checkAccess(JmlTokenKind.ACCESSIBLE, that, that,
		// (VarSymbol)currentThisId.sym, (VarSymbol)currentThisId.sym);
		// FIXME - should we check accessibility for model fields
		JCExpression e = newfa;
		if (currentEnv.stateLabel != null && !translatingLHS)
			e = makeOld(that.pos, newfa, currentEnv.stateLabel);
		if (!rac) {
			result = eresult = e;
		}
	}

	boolean encapsulated = false;

	// OK
	@Override
	public void visitLiteral(JCLiteral that) {
		result = eresult = that;
		if (rac)
			return; // FIXME - something goes wrong with duplicated literals in rac
		boolean traceInfo = esc;
		if (that.type == null) System.out.println("NULLTYPE " + that.pos + " " + that);
		boolean stringType = esc && types.isSameType(that.type, syms.stringType);
		boolean makeCopy = !splitExpressions && (traceInfo || fullTranslation || stringType);
		makeCopy = makeCopy || stringType; // FIXM - really shjould make variables in the prologue for all string values

		JCExpression etype = null;
		if (!encapsulated) {
			if (types.isSameType(that.type, syms.doubleType)) {
				etype = M.Ident(names.fromString("Double")); // FIXME - should use fully qualified type
			} else if (types.isSameType(that.type, syms.floatType)) {
				etype = M.Ident(names.fromString("Float")); // FIXME - should use fully qualified type
			}
			if (etype != null && splitExpressions) { // FIXME - still need the assumption even if !splitExpressions
				JCFieldAccess fa = M.Select(etype, names.fromString("isFinite")); // FIXME _ what in the world is this for
				JCMethodInvocation app = M.Apply(null, fa, List.<JCExpression>of(that));
				encapsulated = true;
				attr.attribExpr(app, Enter.instance(context).getTopLevelEnv(classDecl.toplevel)); // FIXME - just topLevelEnv I think
				addAssume(that, Label.IMPLICIT_ASSUME, convertExpr(app));
				encapsulated = false;
			}
		}

		JCIdent id = null;
		if (makeCopy) {
			JCLiteral init = treeutils.makeDuplicateLiteral(that.pos, that);
			treeutils.copyEndPosition(init, that);
			id = newTemp(init);
		} else {
			result = eresult = that;
			return;
		}
		if (traceInfo) {
			// This block is only needed for tracing
			saveMappingOverride(that, id); // The override is to help i nthe case where a calleee spec is reused but is
											// not a full solution
		}
		if (stringType) {

			addNullnessAllocationTypeCondition(that, id.sym, true, false, false, null);

			if (esc) {
				String str = (String) that.getValue();
				int len = str.length();
				ClassSymbol chseq = ClassReader.instance(context)
						.enterClass(names.fromString("java.lang.CharSequence"));
				Symbol chs = chseq == null ? null : utils.findFieldMember(chseq, "charArray");
				// chs is null if we don't have specs for CharSequence,
				// or if the charArray model field has been renamed
				if (chs != null) {
					JCExpression fa = M.at(id).Select(id, chs);
					JCExpression e = treeutils.makeNotNull(fa.pos, fa);
					fa = treeutils.makeLength(id, fa);
					JCExpression ee = treeutils.makeEquality(id.pos, fa, treeutils.makeIntLiteral(id, len));
					addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeAnd(id.pos, e, ee));
				}

				// These assumptions are necessary so that String literals are
				// known to satisfy the invariants about Strings
				addInvariants(id, id.type, id, currentStatements, false, false, false, false, false, true,
						Label.INVARIANT_ENTRANCE, utils.qualifiedMethodSig(methodDecl.sym));

				if (chs != null) {
					for (int k = 0; k < len; k++) {
						JCFieldAccess arr = treeutils.makeSelect(that.pos, id, chs);
						JCExpression z = treeutils.makeIntLiteral(that.pos, k);
						JCExpression mm = treeutils.makeArrayElement(that.pos, arr, z);
						mm.type = syms.charType;
						JCExpression c = treeutils.makeCharLiteral(that.pos, str.charAt(k));
						JCExpression m = treeutils.makeEquality(that.pos, mm, c);
						JCStatement st = treeutils.makeAssume(that, Label.IMPLICIT_ASSUME, m);
						st.accept(this);
					}
				}

			}

			// Use the literal instead of the temp in order to make optimizations
			// and constant folding, for some types. Keep the temp above for tracing.
			if (that.type.baseType() == syms.booleanType || that.type.isNumeric()) {
				result = eresult = that; // FIXME - what about bigint, real, null
			} else {
				result = eresult = id;
			}
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
		// This is a type literal which is the application of a generic type to its
		// parameters
		result = eresult = !fullTranslation ? that
				: M.at(that).TypeApply(convertExpr(that.clazz), convertExprList(that.arguments)).setType(that.type);
	}

	// OK
	@Override
	public void visitTypeParameter(JCTypeParameter that) {
		// This is a formal class type parameter, possibly including bounds
		result = !fullTranslation ? that
				: M.at(that).TypeParameter(that.name, convertExprList(that.bounds)).setType(that.type);
	}

	// OK
	@Override
	public void visitWildcard(JCWildcard that) {
		// This is a wildcard (?) type
		result = eresult = !fullTranslation ? that
				: M.at(that).Wildcard(convert(that.kind), convert(that.inner)).setType(that.type);
	}

	// OK
	@Override
	public void visitTypeBoundKind(TypeBoundKind that) {
		result = !fullTranslation ? that : M.at(that).TypeBoundKind(that.kind).setType(that.type);
	}

	// OK
	@Override
	public void visitAnnotation(JCAnnotation that) {
		// Only needed for a full tree copy
		// A JCAnnotation is a kind of JCExpression
		if (fullTranslation) {
			JCTree aType = copy(that.annotationType);
			List<JCExpression> args = copy(that.args);
			JCAnnotation a = M.at(that).Annotation(aType, args);
			a.setType(that.type);
			treeutils.copyEndPosition(a, that);
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
			for (JCAnnotation a : that.annotations) {
				annotations.add(copy(a));
			}
			JCModifiers mods = M.at(that).Modifiers(that.flags, annotations.toList());
			result = mods;
			((JmlModifiers)result).jmlmods = ((JmlModifiers)that).jmlmods; // FIXME - should we copy the tokens?
		} else {
			result = that;
		}
	}

	// OK
	@Override
	public void visitErroneous(JCErroneous that) {
		List<? extends JCTree> errs = fullTranslation ? copy(that.errs) : that.errs;
		result = eresult = M.at(that).Erroneous(errs).setType(that.type);
	}

	// OK
	@Override
	public void visitLetExpr(LetExpr that) {
		if (splitExpressions) {
			JmlVariableDecl dec = newTempDecl(that, that.type); // Adds a declaration
			addStat(dec);
			ListBuffer<JCStatement> check = pushBlock();
			for (JCStatement st : that.defs) {
				if (st instanceof JCVariableDecl) {
					localVariables.put(((JCVariableDecl) st).sym, ((JCVariableDecl) st).sym);
				}
			}
			try {
				for (JCStatement d : that.defs) {
                    if (d instanceof JmlVariableDecl vd && isNonNullLocal(vd.vartype.type)) {
                        addAssert(vd.init, Label.UNDEFINED_NULL_INITIALIZATION, treeutils.makeNotNull(vd.init, convertJML(vd.init)));
                    }
					convert(d);
				}
				JCExpression e = convertExpr(that.expr);
                addStat(treeutils.makeAssignStat(that.pos, treeutils.makeIdent(that.pos, dec.sym), e));
			} finally {
				for (JCStatement st : that.defs) {
					if (st instanceof JCVariableDecl) {
						localVariables.remove(((JCVariableDecl) st).sym);
					}
				}
				addStat(popBlock(that, check));
				result = eresult = treeutils.makeIdent(dec.pos, dec.sym);
			}
		} else {
		    // FIXME - needs welldefinedness check
			for (JCStatement st : that.defs) {
				if (st instanceof JCVariableDecl) {
					var d = (JCVariableDecl) st;
					d.init = convert(d.init);
				}
			}
			for (JCStatement st : that.defs) {
				if (st instanceof JCVariableDecl) {
					localVariables.put(((JCVariableDecl) st).sym, ((JCVariableDecl) st).sym);
				}
			}
			try {
				JCExpression e = convertExpr(that.expr);
				result = eresult = M.at(that).JmlLetExpr(that.defs, e, ((JmlLetExpr) that).explicit).setType(that.type);
			} finally {
				for (JCStatement st : that.defs) {
					if (st instanceof JCVariableDecl) {
						localVariables.remove(((JCVariableDecl) st).sym);
					}
				}
			}
		}
	}

	// OK
	@Override
	public void visitJmlBinary(JmlBinary that) {
		JCExpression saved = condition;
		eresult = treeutils.trueLit;
		try {
			JCExpression lhs = convertExpr(that.lhs);
			if (that.op != subtypeofKind && that.op != jsubtypeofKind && that.op != subtypeofeqKind
					&& that.op != jsubtypeofeqKind) {
				lhs = addImplicitConversion(that.lhs, syms.booleanType, lhs);
			}
			JCExpression rhs, t;
			switch (that.op.keyword()) {
			case impliesID: {// P ==> Q is !P || Q
				if (translatingJML)
					addToCondition(that.pos, lhs);
				Boolean b = treeutils.booleanLiteral(lhs);
				if (b != null && !b) {
					eresult = treeutils.makeBooleanLiteral(lhs.pos, true);
				} else if (rac) { // temp = true; if (P) { temp = Q; }
					if (translatingJML)
						addToCondition(that.pos, lhs);
					JCIdent id = newTemp(treeutils.trueLit);
					id.pos = that.pos;
					JCBlock thenBlock = collectBlock(that, () -> {
						JCExpression rhse = convertExpr(that.rhs);
						rhse = addImplicitConversion(that.rhs, that.type, rhse);
						addStat(treeutils.makeAssignStat(that.rhs.pos, treeutils.makeIdent(rhse.pos, id.sym), rhse));
					});
					addStat(M.If(lhs, thenBlock, null));
					eresult = copy(id);
				} else if (splitExpressions) { // if (P) { temp = Q; } else temp = true;
					if (treeutils.isFalseLit(lhs)) {
						eresult = treeutils.makeBooleanLiteral(that, true);
					} else {
						if (translatingJML)
							addToCondition(that.pos, lhs);
						JCIdent id = newTemp(that, that.type);
						JCBlock thenBlock = collectBlock(that, () -> {
							JCExpression rhse = convertExpr(that.rhs);
							rhse = addImplicitConversion(that.rhs, that.type, rhse);
							addStat(treeutils.makeAssignStat(that.rhs.pos, treeutils.makeIdent(rhse.pos, id.sym),
									rhse));
						});
						if (treeutils.isTrueLit(lhs)) {
							addStat(thenBlock);
						} else {
							JCBlock elseBlock = collectBlock(that, () -> {
								addStat(treeutils.makeAssignStat(that.pos, copy(id), treeutils.trueLit));
							});
							addStat(M.If(lhs, thenBlock, elseBlock));
						}
						eresult = copy(id);
					}
				} else { // !P || Q
					if (translatingJML)
						addToCondition(that.pos, lhs);
					rhs = convertExpr(that.rhs);
					rhs = addImplicitConversion(that.rhs, that.type, rhs);
					t = treeutils.makeNotSimp(lhs.pos, lhs);
					t = treeutils.makeOrSimp(that.pos, t, rhs);
					eresult = t;
				}
				if (translatingJML)
					adjustWellDefinedConditions(lhs);
				break;
			}
			case reverseimpliesID: {// P <== Q is P || !Q
				t = treeutils.makeNot(lhs.pos, lhs);
				if (translatingJML)
					addToCondition(that.pos, t);
				if (lhs instanceof JCLiteral && ((JCLiteral) lhs).getValue().equals(Boolean.TRUE)) {
					eresult = treeutils.makeBooleanLiteral(lhs.pos, true);
				} else if (rac) { // temp = true; if (!P) temp = !Q
					JCIdent id = newTemp(treeutils.trueLit);
					id.pos = that.pos;
					JCBlock bl = collectBlock(that, () -> {
						JCExpression rhse = convertExpr(that.rhs);
						rhse = addImplicitConversion(that.rhs, that.type, rhse);
						addStat(treeutils.makeAssignStat(that.rhs.pos, treeutils.makeIdent(rhse.pos, id.sym),
								treeutils.makeNot(rhse.pos, rhse)));
					});

					addStat(M.If(treeutils.makeNot(lhs.pos, lhs), bl, null));
					eresult = copy(id);
				} else if (splitExpressions) { // if (P) { temp = true; } else { temp = (not Q); }
					{
						JCIdent id = newTemp(treeutils.trueLit);
						id.pos = that.pos;
						JCBlock thenBlock = collectBlock(that, () -> {
							addStat(treeutils.makeAssignStat(that.pos, copy(id), treeutils.trueLit));
						});
						JCBlock elseBlock = collectBlock(that, () -> {
							JCExpression rhse = convertExpr(that.rhs);
							rhse = addImplicitConversion(that.rhs, that.type, rhse);
							addStat(treeutils.makeAssignStat(that.rhs.pos, copy(id),
									treeutils.makeNot(rhse.pos, rhse)));
						});
						addStat(M.If(lhs, thenBlock, elseBlock));
						eresult = copy(id);
					}
				} else {
					rhs = convertExpr(that.rhs);
					rhs = addImplicitConversion(that.rhs, that.type, rhs);
					rhs = treeutils.makeNotSimp(that.rhs.pos, rhs);
					t = treeutils.makeOrSimp(that.pos, lhs, rhs);
					eresult = t;
				}
				if (translatingJML)
					adjustWellDefinedConditions(t);
				break;
			}
			case equivalenceID: {
				rhs = convertExpr(that.rhs);
				rhs = addImplicitConversion(that.rhs, that.type, rhs);
				Boolean b = treeutils.booleanLiteral(lhs);
				Boolean bb = treeutils.booleanLiteral(rhs);
				if (b != null) {
					result = eresult = (b ? rhs
							: bb != null ? treeutils.makeBooleanLiteral(that, !bb) : treeutils.makeNot(that, rhs));
					return;
				}
				if (bb != null) {
					result = eresult = (bb ? lhs : treeutils.makeNot(that, lhs));
					return;
				}
				t = treeutils.makeBinary(that.pos, JCTree.Tag.EQ, treeutils.booleqSymbol, lhs, rhs);
				eresult = splitExpressions ? newTemp(t) : t;
				break;
			}
			case inequivalenceID: {
				rhs = convertExpr(that.rhs);
				rhs = addImplicitConversion(that.rhs, that.type, rhs);
				Boolean b = treeutils.booleanLiteral(lhs);
				Boolean bb = treeutils.booleanLiteral(rhs);
				if (b != null) {
					result = eresult = (!b ? rhs
							: bb != null ? treeutils.makeBooleanLiteral(that, !bb) : treeutils.makeNot(that, rhs));
					return;
				}
				if (bb != null) {
					result = eresult = (!bb ? lhs : treeutils.makeNot(that, lhs));
					return;
				}
				t = treeutils.makeBinary(that.pos, JCTree.Tag.NE, treeutils.boolneSymbol, lhs, rhs);
				eresult = splitExpressions ? newTemp(t) : t;
				break;
			}
			case wfltID:
			case wfleID:
				// TODO: Not yet implemented
				eresult = treeutils.trueLit;
				break;

			case subtypeofID: // JML subtype
			case subtypeofeqID: {// JML subtype
				rhs = convertExpr(that.rhs);
				Type lt = treeutils.typeLiteral(lhs);
				Type rt = treeutils.typeLiteral(rhs);
				if (lt != null && rt != null) {
					boolean b = types.isSubtype(lt, rt);
					eresult = treeutils.makeBooleanLiteral(that, b);
				} else {
					// \TYPE <: \TYPE
					if (rac) {
						JCExpression c = methodCallUtilsExpression(that, "isSubTypeOf", lhs, rhs);
						eresult = splitExpressions ? newTemp(c) : c;
					} else {
						JmlMethodInvocation c = treeutils.makeJmlMethodInvocation(that, JmlTokenKind.SUBTYPE_OF,
								that.type, lhs, rhs);
						eresult = splitExpressions ? newTemp(c) : c;
					}
				}
				break;
			}
			case jsubtypeofID: // Java subtype
			case jsubtypeofeqID: {// Java subtype
				rhs = convertExpr(that.rhs);
				Type lt = treeutils.typeLiteral(lhs);
				Type rt = treeutils.typeLiteral(rhs);
				if (lt != null && rt != null) {
					boolean b = types.isSubtype(lt, rt);
					eresult = treeutils.makeBooleanLiteral(that, b);
				} else {
					// Class <: Class - in case type checking allows it

					// TODO - move to a utility method
					// FIXME - do we intend that <: is always false among pairs of primitive types
					// (even the same)
					if (rac) {
						Name n = names.fromString("isAssignableFrom");
						Iterator<Symbol> e = rhs.type.tsym.members().getSymbolsByName(n).iterator();
						Symbol ms = e.next();
						JCFieldAccess m = M.at(that).Select(rhs, n);
						m.sym = ms;
						m.type = m.sym.type;

						JCExpression c = M.at(that).Apply(null, m, List.<JCExpression>of(lhs));
						c.setType(syms.booleanType);
						eresult = splitExpressions ? newTemp(c) : c;
					} else {
						JmlMethodInvocation c = treeutils.makeJmlMethodInvocation(that, JmlTokenKind.JSUBTYPE_OF,
								that.type, lhs, rhs);
						eresult = splitExpressions ? newTemp(c) : c;
					}
				}
				break;
			}
			case lockltID:
			case lockleID:
				notImplemented(that, "Lock ordering operations");
				throw new JmlNotImplementedException(that, "Lock ordering operations");
			// FIXME - need <# <#= operators

			default:
				error(that, "Unexpected token in JmlAssertionAdder.visitJmlBinary: " + that.op);

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
		result = M.at(that).JmlChoose(that.keyword, that.clauseType, convert(that.orBlocks), convert(that.elseBlock))
				.setType(that.type);
	}

	// FIXME - review this
	public JCIdent makeThisId(int pos, Symbol sym) {
		VarSymbol THISSym = treeutils.makeVarSymbol(Flags.STATIC, names.fromString(Strings.THIS), sym.type,
				Position.NOPOS);
		THISSym.owner = infer || esc ? null : sym;
		// In esc, the owner is null (instead of sym) to indicate
		// that this new symbol is a synthetic variable that will not ever
		// be assigned to.
		JCIdent id = treeutils.makeIdent(pos, THISSym);
//        this.thisIds.put(sym, id);
		saveMapping(id, id);
		return id;
	}

	/** Makes an \old expression */
	public JmlMethodInvocation makeOld(int pos, JCExpression arg, Name label) {
		return makeOld(pos, arg, label, labelPropertiesStore.get(label));
	}

	public JmlMethodInvocation makeOld(int pos, JCExpression arg, Name label, LabelProperties labelProperties) {
		JmlMethodInvocation m;
		if (label == null || label == names.empty) { // TODO: Actually should never be empty
			m = M.at(pos).JmlMethodInvocation(oldKind, List.<JCExpression>of(arg));
		} else {
			JCIdent id = M.at(pos).Ident(label);
			id.type = null; // Should never refer to the label's type
			id.sym = null; // Should never refer to the label's symbol
			m = M.at(pos).JmlMethodInvocation(oldKind, List.<JCExpression>of(arg, id));
		}
		m.labelProperties = labelProperties;
		m.type = arg.type;
		return m;
	}

	Map<ClassSymbol, VarSymbol> enclosingClassFieldSymbols = new HashMap<>();
	JCExpression enclosingExpr = null;

	public VarSymbol makeEnclosingSymbol(ClassSymbol sym, JCExpression enclosingThisExpr) {
		VarSymbol result = enclosingClassFieldSymbols.get(sym);
		if (result != null)
			return result;
		Symbol owner = sym.owner;
		while (owner instanceof MethodSymbol) {
			owner = owner.owner;
		}
		if (esc && owner instanceof ClassSymbol && !sym.isStatic()) {
			// FIXME - this modeling of the enclosing this is not complete and likely not
			// right.
			// FIXME - enclosingThisExpr does not work as an initializer
			String s = "this$encl";
			Type enclType = owner.type;
			Name nm = names.fromString(s);
			JCVariableDecl decl = treeutils.makeVarDef(enclType, nm, owner, enclosingThisExpr.pos);
			if (currentStatements != null)
				addStat(decl);
			else
				this.classDefs.add(decl);
			enclosingClassFieldSymbols.put(sym, decl.sym);
			result = decl.sym;
		}
		return result;
	}

	// OK
	@Override
	public void visitJmlClassDecl(JmlClassDecl that) {

		JmlOptions.instance(context).pushOptions(that.mods);

		JmlMethodDecl savedMethodDecl = this.methodDecl;
		JmlClassDecl savedClassDecl = this.classDecl;
		ListBuffer<JCTree> savedClassDefs = this.classDefs;
		ListBuffer<JCStatement> savedCurrentStatements = this.currentStatements;
		Symbol savedAllocSym = this.allocSym;
		Symbol savedIsAllocSym = this.isAllocSym;
		this.currentEnv = this.currentEnv.pushEnvCopy();
//		JCExpression savedThisExpr = this.currentEnv.currentReceiver;
//		IArithmeticMode savedMode = this.currentEnv.arithmeticMode;

		try {
			enclosingExpr = this.currentEnv.currentReceiver;
			this.classDecl = that;
			this.methodDecl = null;
			this.currentEnv.arithmeticMode = Arithmetic.Math.instance(context).defaultArithmeticMode(classDecl.sym, false);
			if (esc || infer) {
				this.currentEnv.currentReceiver = makeThisId(classDecl.pos, classDecl.sym);
			} else { // rac
				this.currentEnv.currentReceiver = treeutils.makeIdent(classDecl.pos, that.thisSymbol);
			}

			this.classDefs = new ListBuffer<JCTree>();
			this.currentStatements = null;

			if (esc || infer) {
				JCVariableDecl d = treeutils.makeStaticVarDef(syms.intType, heapVarName, classDecl.sym,
						treeutils.makeIntLiteral(0, 0));
				heapSym = d.sym;
				// initialStatements.add(d);
				this.classDefs.add(d);
			}
			if (esc && that.sym.owner instanceof ClassSymbol && !that.sym.isStatic()) {
				makeEnclosingSymbol(that.sym, enclosingExpr);
			}
			{
				JCVariableDecl d = treeutils.makeVarDef(syms.intType, names.fromString(Strings.allocName),
				    syms.objectType.tsym, treeutils.makeNullLiteral(classDecl.pos));
				allocSym = d.sym;
				d = treeutils.makeVarDef(syms.booleanType, names.fromString(Strings.isAllocName), syms.objectType.tsym,
						treeutils.makeNullLiteral(classDecl.pos));
				isAllocSym = d.sym;
			}

			enclosingClass = that.sym;

			if (rac) {
				// For RAC, we need to be sure there are no missing model field methods
				// because of a represents clause representing a super class field.
				JmlSpecs.TypeSpecs tyspecs = that.typeSpecs;
				if (tyspecs != null) {
					for (JmlTypeClause t : tyspecs.clauses) {
						if (t.clauseType == representsClause) {
							boolean pv = checkAccessEnabled;
							checkAccessEnabled = false; // Do not check access in JML clauses
							try {
								scan(t);
							} finally {
								checkAccessEnabled = pv;
							}
						}
					}
				}
			}

			// THis will recursively check nested classes and for each class, checks the
			// constructors, methods, and static initialization.
			// For esc, field initializations are part of constructors and would not be
			// needed to be scanned here.
			// However, for rac, we potentially modify each declaration, in order, so all
			// declarations are scanned here.
			for (JCTree t : that.defs) {
				if (t instanceof JmlClassDecl 
				        || t instanceof JmlMethodDecl
				        || (rac && (t instanceof JmlVariableDecl || t instanceof JmlBlock))
				        ) {
//                    if (org.jmlspecs.openjml.Utils.debug()) {
//                    	System.out.println("JAA-visitJmlClassDecl-C " + that.sym + " " + t);
//                    	if (t instanceof JmlMethodDecl) {
//                    		var msym = ((JmlMethodDecl)t).sym;
//                        	System.out.println("JAA-visitJmlClassDecl-CC " + specs.status(msym) + " " + specs.get(msym));
//                    	}
//                    }
					// try { // FIXME - not working reliably yet -- need to completely skip not
					// implemented clauses
					scan(t);
//                    } catch (JmlNotImplementedException e) {
//                    	if (t instanceof JmlTypeClause) {
//                    		notImplemented(((JmlTypeClause)t).keyword + " clause containing ",e, ((JmlTypeClause)t).source());
//                    	}
//                    }
				}
			}

			// FIXME - need to fixup RAC and ESC check of static initialization
			if (discoveredFields == null) {
				pushBlock();
				discoveredFields = popBlock(that);
			}
			JCBlock bl = checkStaticInitialization();
			if (bl != null) this.classDefs.add(bl);

			JmlSpecs.TypeSpecs tyspecs = that.typeSpecs;
			if (!rac)
				if (tyspecs != null) {
					for (JmlTypeClause t : tyspecs.clauses) {
						if (t.clauseType == representsClause) {
							boolean pv = checkAccessEnabled;
							checkAccessEnabled = false; // Do not check access in JML clauses
							try {
								scan(t);
							} finally {
								checkAccessEnabled = pv;
							}
						}
					}
				}

			List<JCTree> defs = this.classDefs.toList();
			// if (print) System.out.println("JAA-visitJmlClassDecl-K " + defs);

			for (JCTree def : defs) {
				if (def instanceof JmlMethodDecl jdef) {
					String nm = jdef.name.toString();
					if (utils.isSynthetic(jdef.mods) && attr.isModel(jdef.mods) && nm.startsWith(Strings.modelFieldMethodPrefix)) {
						if ((jdef.mods.flags & Utils.JMLADDED) != 0) {
							// We are presuming that all represents clauses are processed
							// (as part of scanning the specs defs in visitJmlClassDecl)
							// before we handle all the model field methods.
							utils.warning(jdef.source(), jdef.pos, "jml.no.model.method.implementation",
									nm.substring(Strings.modelFieldMethodPrefix.length())); // FIXME - extract name of
																							// model field
						}
					}
				}
			}

			// FIXME - replicate all the other AST nodes
			List<JCTypeParameter> typarams = that.typarams;
			if (fullTranslation)
				typarams = convert(typarams);
			JmlClassDecl n = M.at(that).ClassDef(convert(that.mods), that.name, typarams, convertExpr(that.extending),
					convertExprList(that.implementing), defs);
			n.sym = that.sym;
			n.setType(that.type);
			n.superSymbol = that.superSymbol;
			n.thisSymbol = that.thisSymbol;
			n.toplevel = that.toplevel; // FIXME - translate to new top level
			n.docComment = that.docComment;
			n.env = that.env; // FIXME - translate?
			n.specsDecl = that.specsDecl; // FIXME - these may be self-references - and I think there are now only one
			n.typeSpecs = null; // that.typeSpecs; // not copied - FIXME? here and elsewhere
			if (savedClassDefs != null && n.sym.owner instanceof ClassSymbol) {
				savedClassDefs.add(n);
			} else if (currentStatements != null) {
				addStat(n);
			}
			result = n;
			classBiMap.put(that, n);
		} finally {
			this.classDecl = savedClassDecl;
			this.methodDecl = savedMethodDecl;
			this.classDefs = savedClassDefs;
			this.currentStatements = savedCurrentStatements;
			this.allocSym = savedAllocSym;
			this.isAllocSym = savedIsAllocSym;
			this.currentEnv = this.currentEnv.popEnv();
			this.enclosingExpr = null;
			JmlOptions.instance(context).popOptions();
		}
	}

	// FIXME - review
	protected JCBlock checkStaticInitialization() {
		JmlMethodDecl md = methodSymForInitBlock(classDecl, Flags.STATIC, classDecl);

		ListBuffer<JCStatement> check = pushBlock();
		if (esc) {
			JCVariableDecl d = treeutils.makeVarDef(syms.intType, names.fromString(Strings.feasCheckVar), methodDecl.sym, Position.NOPOS); // NOPOS so the
																											// name is
																											// not
																											// mangled
			feasCheckSym = d.sym;
			d.sym.owner = null;
			currentStatements.add(d);
		}
		for (Symbol s : classDecl.sym.getEnclosedElements()) {
			if (utils.isJMLStatic(s) && s instanceof VarSymbol && !utils.isJavaOrJmlPrimitiveType(s.type)) {
				VarSymbol v = (VarSymbol) s;
				if (specs.isNonNull(v)) {
					JCIdent id = treeutils.makeIdent(v.pos, v);
					JCExpression e = treeutils.makeNeqObject(v.pos, id, treeutils.nullLit);
					// e = convertJML(e);
					JCStatement st = addAssert(new JCDiagnostic.SimpleDiagnosticPosition(v.pos), Label.STATIC_INIT, e,
							"non-null static field has null value: " + v.name);
					if (st instanceof JCAssert) {
						e = ((JCAssert) st).cond;
					} else if (st instanceof JCIf) {
						e = ((JCIf) st).cond;
						if (e instanceof JCUnary)
							e = ((JCUnary) e).arg;
					} else {
						e = null;
					}
					if (e instanceof JCIdent) {
						((JCIdent) e).sym.owner = md.sym;
					}

				}
			}
		}
		// FIXME - what are the rules about accessibility for static initializers
		boolean pv = checkAccessEnabled;
		checkAccessEnabled = false;
		try {
			addInvariants(classDecl, classDecl.sym.type, null, currentStatements, true, false, false, false, true,
					false, Label.STATIC_INIT, "invariant is false");
			clearInvariants();
		} finally {
			checkAccessEnabled = pv;
		}
		JCBlock bl = popBlock(Flags.STATIC, classDecl, check);
		if (onlyComments(bl.stats))
			bl = null;
		return bl;
	}

//    // OK
//    @Override
//    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
//        if (translatingJML) {
//            error(that,"Unexpected call of JmlAssertionAdder.visitJmlCompilationUnit while translating JML: " + that.getClass());
//            return;
//        }
//
//        List<JCTree> defs = convert(that.defs);
//        JmlCompilationUnit n = M.at(that).TopLevel(defs);
//        n.docComments = that.docComments; // FIXME: need to translate map
//        n.endPositions = that.endPositions; // FIXME: need to convert map?
////        n.flags = that.flags;
//        n.mode = that.mode;
//        n.lineMap = that.lineMap;
//        n.namedImportScope = that.namedImportScope;
//        n.packge = that.packge;
//        n.setType(that.type);
////        n.parsedTopLevelModelTypes = that.parsedTopLevelModelTypes; // FIXME: need to convert
//        n.sourcefile = that.sourcefile;
//        n.starImportScope = that.starImportScope;
//        n.specsCompilationUnit = that.specsCompilationUnit; // FIXME: need to convert
////        n.specsTopLevelModelTypes = convert(that.specsTopLevelModelTypes);
//        result = n;
//    }

	// OK
	@Override
	public void visitJmlMethodSig(JmlMethodSig that) {
		result = M.at(that).JmlConstraintMethodSig(convertExpr(that.expression), convertExprList(that.argtypes));
		result.setType(that.type);
	}

	// OK
	@Override
	public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {

		/*
		 * loop_invariant INV loop_variant VAR label: do { BODY } while (COND); becomes
		 * { ... declare index assert INV label: do { havoc assume INV TEMP = VAR assert
		 * 0 <= TEMP loop_bodyN: { ... statements from BODY ... continue --> break
		 * loop_bodyN; ... break --> break; } ... statements from COND // put before INV
		 * for side-effects assert INV TEMP2 = VAR assert TEMP2 < TEMP if (!COND') {
		 * assert INV; break; } } while (true); }
		 * 
		 */

		// FIXME - need label for loop if any and the target mapping

		// Outer block to restrict scopes of temporaries
		pushBlock();

		JCVariableDecl indexDecl = loopHelperDeclareIndex(that);

		java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

		// Create this early so it is available as a target
		JmlWhileLoop loop = M.at(that).WhileLoop(treeutils.trueLit, null);
		treeMap.put(that, loop);

		// Test that invariants hold before entering loop
		loopHelperInitialInvariant(that.loopSpecs);

		// New loop body
		pushBlock();

		// Havoc all items that might be changed in the loop
		if (esc) {
			boolean b = loopHelperHavoc(that.loopSpecs, that.body, indexDecl, null, null, that.body, that.cond);
//			if (!b) {
//			    changeStateForLoop(that, that.loopSpecs);
//			}
		}

		loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that, null);

		// Now in the loop, so check that the variants are non-negative
		loopHelperCheckNegative(decreasesIDs, that);

		// Then translate the original loop body

		loopHelperMakeBody(that.body);

		// Now compute any side-effects of the loop condition
		addTraceableComment(that.cond, that.cond, "Loop test");
		JCExpression cond = convertExpr(that.cond);

		// increment the index
		loopHelperIncrementIndex(indexDecl);

		// In a do-while loop we test the condition before the invariants

		// Construct the loop test and the exit block.
		Boolean splitInfo = loopHelperMakeBreak(that.loopSpecs, cond, loop, that);

		// After the loop, check the invariants and check that the variants have
		// decreased
		loopHelperAssertInvariants(that.loopSpecs, decreasesIDs);

		// Finish up the new loop body
		// Finish up the output block
		loopHelperFinish(loop, that);
		addStat(popBlock(that));
	}
	
    public boolean isNonNullLocal(Type t) {
        return !utils.isJavaOrJmlPrimitiveType(t) && ( hasNonNull(t) || (!hasNullable(t) && attr.isNonNull(enclosingMethod,null) ));
    }

    public boolean isNullableLocal(Type t) {
        return !utils.isJavaOrJmlPrimitiveType(t) && ( hasNullable(t) || (!hasNonNull(t) && !attr.isNonNull(enclosingMethod,null) ));
    }

	// OK
	@Override
	public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {

		/*
		 * loop_invariant INV loop_variant VAR label: for (T v: ARRAY) BODY becomes {
		 * ... statements from ARRAY ... declare INDEX = 0 ... compute LENGTH assert INV
		 * label: while (true) { havoc assume INV TEMP = VAR if (INDEX >= LENGTH) {
		 * assert INV; break; } assert 0 <= TEMP declare v = ARRAY[INDEX] loop_bodyN: {
		 * ... statements from BODY ... continue --> break loop_bodyN; ... break -->
		 * break; } INDEX = INDEX + 1 assert INV TEMP2 = VAR assert TEMP2 < TEMP } //
		 * FIXME - if break exits still have to satisfy invariant, put the check here }
		 * 
		 */
		/*
		 * loop_invariant INV loop_variant VAR label: for (T v: ITERABLE) BODY becomes {
		 * ... statements from ITERABLE ... declare INDEX = 0 ... declare ITERATOR =
		 * ITERABLE.iterator() assert INV label: while (true) { havoc assume INV TEMP =
		 * VAR if (ITERATOR.hasNext()) { assert INV; break; } declare v =
		 * ITERATOR.next() assert 0 <= TEMP loop_bodyN: { ... statements from BODY ) ...
		 * continue --> break loop_bodyN; ... break --> break; } INDEX = INDEX + 1
		 * assert INV TEMP2 = VAR assert TEMP2 < TEMP } // FIXME - if break exits still
		 * have to satisfy invariant, put the check here }
		 * 
		 */

		// FIXME - need label for loop if any and the target mapping

		// Outer block to restrict scopes of temporaries
		pushBlock();

//        JCExpression originalIterable = null;
//        Type iterableSuperType = null;
//        if (!rac && types.isSubtype(types.erasure(that.expr.type), types.erasure(syms.iterableType))) {
//            iterableSuperType = types.asSuper(that.expr.type, syms.iterableType.tsym);
//            System.out.println("ITERABLE " + that.expr.type + " " + iterableSuperType + " " + iterableSuperType.getTypeArguments().head + " " + paramActuals);
////            java.util.Optional<Symbol> sym = java.util.Optional.<Symbol>empty();
////            for (Symbol ss: t.tsym.getEnclosedElements()) {
////                if (ss.name.toString().equals("values")) {
////                    sym = java.util.Optional.of(ss);
////                }
////            }
////            java.util.Optional<Symbol> sym = iterableSuperType.tsym.getEnclosedElements().stream().filter(s->s.name.toString().equals("values")).findFirst();
////            if (sym.isPresent()) {
////                originalIterable = (that.expr);
////                JCExpression fa = M.at(that.expr).Select(that.expr,sym.get());
////                fa.type = sym.get().type;
////                JCExpression bin = treeutils.makeNotNull(that.expr.pos, fa);
////                bin = convertExpr(bin);
////                addAssume(that.expr,Label.IMPLICIT_ASSUME,bin);
////                that.expr = fa;
////            } else {
////                utils.error(that.expr,"jml.message","No values field found for type " + that.expr.type);
////            }
//            
//        }
		JCExpression array = null;

		JCVariableDecl indexDecl = loopHelperDeclareIndex(that);

		java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

		// Create this early so it is available as a target
		JmlWhileLoop loop = M.at(that).WhileLoop(treeutils.trueLit, null);
		treeMap.put(that, loop);

		int savedHeapCount = -1;
		Boolean splitInfo = null;
		boolean doRemainderOfLoop = true;
		boolean isArray = that.expr.type.getTag() == TypeTag.ARRAY;
		if (isArray || !rac) {

			JCExpression lengthExpr = null;
			if (isArray) {
				array = convertExpr(that.expr);
				lengthExpr = treeutils.makeLength(array, array);
				lengthExpr = newTemp(lengthExpr); // FIXME - could give it a recognizable name
				Type elemType = ((Type.ArrayType)that.expr.type).getComponentType();
                //System.out.println("NN " + that.var.sym + " " + attr.isNonNull(that.var.sym) + " " + hasNonNull(elemType)+ " " + hasNullable(elemType));
				if (isNonNullLocal(that.var.type) && isNullableLocal(elemType)) {
//				    utils.warning(that.var, "jml.message", that.var.name + " is non_null but the type of " + that.expr + " allows null array elements");
                    JCExpression e4 = treeutils.makeJmlMethodInvocation(that.expr, nonnullelementsKind, syms.booleanType, array);
                    addAssert(that.expr, Label.NULL_ELEMENT, e4);
				}
			} else {
				JCExpression e = that.expr;
				Name niter = names.fromString("values");
				JCFieldAccess fa = M.at(that.expr).Select(e, niter);
				fa.sym = syms.iterableType.tsym.members().findFirst(niter);
				fa.type = typevarValue(fa.sym.type, typevarMapping);
				// System.out.println("CALLED TYPEVARVALUE-A " + fa.sym.type + " " + fa.type + "
				// " + typevarMapping);
				var lensym = fa.type.tsym.members().findFirst(names.length);
				fa = M.at(that.expr).Select(fa, names.length);
				fa.sym = lensym;
				fa.type = jmltypes.BIGINT;
				lengthExpr = convertJML(fa);
			}

			// Test that invariants hold before entering loop
			loopHelperInitialInvariant(that.loopSpecs);

			// New loop body
			pushBlock();

			// Havoc all items that might be changed in the loop
			if (esc) {
				boolean b = loopHelperHavoc(that.loopSpecs, that.body, indexDecl, null, null, that.body, that.expr);
//				if (!b) {
//	                changeStateForLoop(that, that.loopSpecs);
//				}
			}

			// Assume the invariants
			// Compute and remember the variants
			loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that, lengthExpr);

			// Compute the condition, recording any side-effects
			if (isArray) {
				JmlSingleton index = M.at(that.pos).JmlSingleton(countKind);
				index.kind = countKind;
				index.type = syms.intType;
				JCExpression ocond = treeutils.makeBinary(that.pos, JCTree.Tag.LT, index, lengthExpr);
				JCExpression cond = convertJML(ocond);
				addTraceableComment(ocond, ocond, "Loop test");

				// The exit block tests the condition; if exiting, it tests the
				// invariant and breaks.
				savedHeapCount = heapCount;
				splitInfo = loopHelperMakeBreak(that.loopSpecs, cond, loop, that);
			} else {
				JmlSingleton index = M.at(that.pos).JmlSingleton(countKind);
				index.kind = countKind;
				index.type = jmltypes.BIGINT;
				JCExpression ocond = treeutils.makeBinary(that.pos, JCTree.Tag.LT, index, lengthExpr);
				JCExpression cond = convertJML(ocond);
				addTraceableComment(ocond, ocond, "Loop test");

				// The exit block tests the condition; if exiting, it tests the
				// invariant and breaks.
				savedHeapCount = heapCount;
				splitInfo = loopHelperMakeBreak(that.loopSpecs, cond, loop, that);
			}
	        currentEnv = currentEnv.pushEnvCopy();

			doRemainderOfLoop = splitInfo == null || splitInfo;

			// Now in the loop, so check that the variants are non-negative
			if (doRemainderOfLoop)
				loopHelperCheckNegative(decreasesIDs, that);

			if (isArray) {
				JCExpression aa = new JmlBBArrayAccess(null, array, treeutils.makeIdent(that.pos, indexDecl.sym));
				aa.pos = array.pos;
				aa.setType(typevarValue(((Type.ArrayType) array.type).elemtype, typevarMapping));
				aa = addImplicitConversion(array, that.var.type, aa);
				JCVariableDecl loopVarDecl = treeutils.makeVarDef(that.var.type, that.var.name, methodDecl.sym, aa);
				loopVarDecl.sym = that.var.sym; // We share syms; if we don't we have to add
				// a mapping to paramActuals
				addStat(loopVarDecl);
//            	if (that.var.type.isReference()) { // Not null
//            		// If we originally had an Iterable, check the value of 'containsNull'
//            		if (iterableSuperType != null) {
//            			java.util.Optional<Symbol> sym = iterableSuperType.tsym.getEnclosedElements().stream().filter(s->s.name.toString().equals("containsNull")).findFirst();
//            			if (sym.isPresent()) {
//            				JCExpression fa = M.at(that.expr).Select(originalIterable,sym.get());
//            				fa.type = syms.booleanType;
//            				fa = convertExpr(fa);
//            				JCExpression b = treeutils.makeNot(that.pos, fa);
//            				JCExpression e = treeutils.makeNotNull(that.pos, treeutils.makeIdent(that.pos, that.var.sym));
//            				b = treeutils.makeImplies(that.pos, b, e);
//            				addAssume(that,Label.IMPLICIT_ASSUME,b);
//            			}
//            		}
//            		JCIdent id = M.at(that.var).Ident(that.var.sym);
//            		JCExpression e = treeutils.makeNotNull(id.pos, id);
//            		JCExpression ee = treeutils.makeInstanceOf(that.var.pos, id, that.var.type);
//            		addAssume(that.var,Label.IMPLICIT_ASSUME,treeutils.makeImplies(that.var.pos, e, ee));
//            	}
			} else {
				JCExpression e = that.expr;
				Name niter = names.fromString("values");
				JCFieldAccess fa = M.at(that.expr).Select(e, niter);
				fa.sym = syms.iterableType.tsym.members().findFirst(niter);
				fa.type = typevarValue(fa.sym.type, typevarMapping);
				// System.out.println("CALLED TYPEVARVALUE-B " + fa.sym.type + " " + fa.type + "
				// " + typevarMapping);

				var typeargs = that.expr.type.getTypeArguments();
				var typearg = syms.objectType;
				if (typeargs.size() > 0)
					typearg = typeargs.head;

				JmlSingleton index = M.at(that.var).JmlSingleton(countKind);
				index.kind = countKind;
				index.type = jmltypes.BIGINT;
				e = M.at(that.var).Indexed(fa, index);
				e.type = typearg;

				boolean nn = specs.isNonNull(typearg, (ClassSymbol) enclosingClass);
				e = convertJML(e);
				if (nn)
					addAssume(that.var, Label.IMPLICIT_ASSUME, treeutils.makeNotNull(that.var, e));

				// FIXME - the above is not a general solution to calculating argtype
				// FIXME - should also check the nullity of the declared variable and see if an
				// assert is needed

				Type vtype = typevarValue(that.var.type, typevarMapping);
				JCVariableDecl loopVarDecl = treeutils.makeVarDef(vtype, that.var.name, methodDecl.sym,
						addImplicitConversion(that.expr, vtype, e));
				loopVarDecl.sym = that.var.sym;
				// assign the foreach loop variable
				addStat(loopVarDecl);
				if (specs.isNonNull(vtype)) { // Only checks for explicit NonNull -- FIXME - is that correct
					addAssume(that, Label.NULL_CHECK,
							treeutils.makeNotNull(that, treeutils.makeIdent(that, loopVarDecl.sym)));
				}
			}

		} else { // rac && !isArray
			// Have an iterable instead of an array, with RAC

			array = convertExpr(that.expr);
			Name iteratorName = names.fromString("_JML_iterator_" + nextUnique());
			JCExpression iter = methodCallUtilsExpression(array, "iterator", array);
			Type restype;
			restype = iter.type;
			JCVariableDecl decl = treeutils.makeVarDef(restype, iteratorName, methodDecl.sym, iter);
			addStat(decl);

			// Test that invariants hold before entering loop
			loopHelperInitialInvariant(that.loopSpecs);

			// New loop body
			pushBlock();

			// Havoc all items that might be changed in the loop
			if (esc) {
				boolean b = loopHelperHavoc(that.loopSpecs, that.body, indexDecl, null, null, that.expr, that.body);
//				if (!b) {
//	                changeStateForLoop(that, that.loopSpecs);
//				}
			}

			// Assume the invariants
			// Compute and remember the variants
			loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that, null);

			// Compute the condition, recording any side-effects
			{

				// iterator.hasNext()
				JCExpression ocond = methodCallUtilsExpression(iter, "hasNext",
						treeutils.makeIdent(array.pos, decl.sym));
				JCExpression cond = copy(ocond);

				addTraceableComment(ocond, ocond, "Loop test");

				// The exit block tests the condition; if exiting, it tests the
				// invariant and breaks.
				savedHeapCount = heapCount;
	            currentEnv = currentEnv.pushEnvCopy();
				splitInfo = loopHelperMakeBreak(that.loopSpecs, cond, loop, that);
				doRemainderOfLoop = splitInfo == null || splitInfo;
			}

			// Now in the loop, so check that the variants are non-negative
			if (doRemainderOfLoop)
				loopHelperCheckNegative(decreasesIDs, that);

			// T v = ITERATOR.next()
			JCExpression value = methodCallUtilsExpression(iter, "next", treeutils.makeIdent(array.pos, decl.sym));
			value.type = typevarValue(value.type, typevarMapping);
			JCIdent iterId = newTemp(value); // We only want next called once, so we cache its value
			if (!rac)
				addNullnessTypeConditionId(iterId, that.var, iterId.sym, attr.isNonNull(that.var.sym, that.var.mods),
						false);
			JCExpression iterEx = addImplicitConversion(value, that.var.type, iterId);
			// This is the case in which the loop variable is typed with a generic type
			JCVariableDecl vd = treeutils.makeVarDef(iterEx.type, that.var.name, methodDecl.sym, iterEx);
			addStat(vd);
			if (!jmltypes.isSameType(that.var.type, iterEx.type)) {
				JCIdent id = treeutils.makeIdent(that.var.pos, vd.sym);
				if (paramActuals_ != null) paramActuals_.put(that.var.sym, id);
				that.var = vd;
			} else {
				vd.sym = that.var.sym; // We share syms; if we don't we have to add
				// a mapping to paramActuals
			}

		}

		// Then translate the original loop body
		// Have to do some footwork to get the Block object before constructing its
		// contents
		if (doRemainderOfLoop)
			loopHelperMakeBody(that.body);

		// increment the index
		if (doRemainderOfLoop)
			loopHelperIncrementIndex(indexDecl);

		// After the loop, check the invariants and check that the variants have
		// decreased
		if (doRemainderOfLoop)
			loopHelperAssertInvariants(that.loopSpecs, decreasesIDs);

		// Finish up the new loop body
		// Finish up the output block
		heapCount = savedHeapCount; // FIXME - only if no break statements targeted the end of the loop
        currentEnv = currentEnv.popEnv();
		loopHelperFinish(loop, that); // Does two popBlock operations
		JCBlock bl = popBlock(that);
		addStat(bl);
		if (splitInfo != null && splitInfo)
			continuation = Continuation.HALT;
	}

	/**
	 * Declares the synthetic index variable for the loop, adding the declaration to
	 * the current statement list.
	 */
	// OK
	protected JCVariableDecl loopHelperDeclareIndex(DiagnosticPosition pos) {
		int p = pos.getPreferredPosition();
		if (p < 0) p = 0;
		Name indexName = names.fromString("index_" + p + "_" + nextUnique());
		JCVariableDecl indexDecl = treeutils.makeVarDef(syms.intType, indexName, methodDecl.sym, treeutils.zero);
		indexDecl.sym.pos = pos.getPreferredPosition();
		indexDecl.pos = pos.getPreferredPosition();
		addStat(indexDecl);
		indexStack.add(0, indexDecl);
		return indexDecl;
	}

	/** Finds variables assigned in the loop body and adds a havoc statement */
	// OK
	// FIXME - needs checking that we are getting all of needed variables
	protected boolean loopHelperHavoc(List<JmlStatementLoop> loopSpecs, DiagnosticPosition pos,
			JCVariableDecl indexDecl, List<? extends JCTree> initlist, List<? extends JCTree> list, JCTree... trees) {
		ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
		boolean useDefaultModifies = true;
		if (loopSpecs != null)
			for (JmlStatementLoop spec : loopSpecs) {
				if (spec instanceof JmlStatementLoopModifies) {
					for (JCExpression stref : ((JmlStatementLoopModifies) spec).storerefs) {
						newlist.add(spec.translated ? copy(stref) : convertNoSplit(stref));
					}
					if (initlist != null)
						for (JCTree t : initlist) {
							// FIXME - might be already present; if the loop_modifies was added by an
							// inlining sepc it certainly would not be
							if (t instanceof JmlVariableDecl) {
								newlist.add(convertNoSplit(((JmlVariableDecl) t).ident));
							}
						}
					useDefaultModifies = false;
				}
			}
		{
			JCIdent id = treeutils.makeIdent(pos.getPreferredPosition(), indexStack.get(0).sym); // FIXME _ use
																									// indexDecl here?
			newlist.add(convertNoSplit(id));
		}
		if (useDefaultModifies) {
			ListBuffer<JCExpression> targets = new ListBuffer<JCExpression>();
			if (list != null)
				for (JCTree t : list) {
					TargetFinder.findVars(t, targets, context);
				}
			for (JCTree t : trees) {
				TargetFinder.findVars(t, targets, context);
			}
			targets.add(treeutils.makeIdent(pos.getPreferredPosition(), indexStack.get(0).sym));
			// synthesize a modifies list
			for (JCExpression target : targets.toList()) {
				JCExpression newtarget = null;
				if (target instanceof JCArrayAccess) {
					JCArrayAccess aa = (JCArrayAccess) target;
					if (aa.index instanceof JCIdent) {
						JCIdent id = (JCIdent) aa.index;
						if (initlist != null && initlist.length() == 1) {
							JCTree t = initlist.head;
							if (t instanceof JCVariableDecl) {
								JCVariableDecl vd = (JCVariableDecl) t;
								if (id.sym == vd.sym) {
//                                   newtarget = aa;
								}
							}
						}
					}
					// FIXME - we convert array accesses to the entire array.
					// This is partly because the array index may depend on the loop variable, which
					// is also havoced.
					// But the test for whether the index is in range occurs before the invariants
					// are assumed,
					// which would put the index back in range.
					if (newtarget == null) {
						var rt = rangeTypeKind.getType(context);
						JCExpression range = M.at(target.pos).JmlRange(null, null).setType(rt);
						newtarget = M.at(target.pos).Indexed(aa.indexed, range).setType(target.type);
					}
				} else {
					newtarget = target;
				}
				newlist.add(convertJML(newtarget));
			}
		}
		List<JCExpression> newlistx = expandStoreRefList(newlist.toList(), methodDecl.sym, true);
		int p = pos.getPreferredPosition();
		JmlStatementHavoc st = M.at(p).JmlHavocStatement(newlistx);
		for (JCExpression hv : newlistx) {
			if (hv instanceof JCFieldAccess) {
				var fa = (JCFieldAccess) hv;
				havocModelFields(fa);
			}
		}
		allocCounter++;
		// FIXME - this ought to work to preserve initialized values at the beginning of
		// th e0th iteration, but makes loops infeasbile
//        JCExpression id = treeutils.makeIdent(indexDecl.pos, indexDecl.sym);
//        JCExpression e = treeutils.makeBinary(p, JCTree.Tag.GT, id, treeutils.zero);
//        addStat(M.at(p).If(e, st, null));
		addStat(st);
		boolean allLocal = true;
		{
			for (JCExpression item : st.storerefs) {
				if (item instanceof JCIdent) {
					addNullnessTypeCondition(item, ((JCIdent) item).sym, false);
				} else if (item instanceof JCFieldAccess) {
					JCFieldAccess fa = (JCFieldAccess) item;
					if (fa.name != null) {
						JCExpression saved = currentEnv.currentReceiver;
						currentEnv.currentReceiver = fa.selected;
						addNullnessTypeCondition(item, fa.sym, false);
						currentEnv.currentReceiver = saved;
					}
				}
				if (!allLocal)
					continue;
				if (item instanceof JmlStoreRefKeyword) {
					if (((JmlStoreRefKeyword) item).kind != nothingKind)
						allLocal = false;
					;
					continue;
				}
				if (item instanceof JCIdent && item.type.isPrimitive()
						&& ((JCIdent) item).sym.owner instanceof MethodSymbol)
					continue;
				allLocal = false;
				if (item.type.isReference()) {
					if (item instanceof JCArrayAccess aa && aa.index instanceof JmlRange r
							&& !(r.lo == r.hi && r.lo != null)) {
						// Need to iterate over elements of the range
						addStat(comment(item,
								"TODO: Skipping assuming invariants of all the havoced array elements: " + item,
								log.currentSourceFile()));
					} else {
						JCExpression e = getInvariantAll(item, item.type, item, true); // FIXME - is item.type the resolved
																					// type?
						if (e != null)
							addAssume(item, Label.IMPLICIT_ASSUME, e); // if e is null, there is no invariant expression
					}
				}
				// FIXME - zadd more types? becareful not to include wildcards
			}
		}
        if (!allLocal) {
            List<JmlStatementLoop> justLoopModifies = null;
            JmlStatementLoop loopModifiesClause = null;
            if (loopSpecs != null) {
                loopModifiesClause = loopSpecs.stream().filter(c->(c.clauseType == StatementLocationsExtension.loopwritesStatement)).findFirst().orElse(null);
            }
            if (loopModifiesClause == null) {
                loopModifiesClause = M.at(pos.getPreferredPosition()).JmlStatementLoopModifies(StatementLocationsExtension.loopwritesStatement, newlistx);
            }
            changeStateForLoop(pos, List.<JmlStatementLoop>of(loopModifiesClause)); // FIXME _ but only if something is havoced? and it is not a local variable?
        }

		return allLocal;
	}

	// FIXME: implement loop_modifies?

//	/** Finds variables assigned in the loop body and adds a havoc statement */
//	// OK
//	// FIXME - needs checking that we are getting all of needed variables
//	protected boolean loopHelperHavoc(List<JmlStatementLoop> loopSpecs, DiagnosticPosition pos,
//			JCVariableDecl indexDecl, /* @ nullable */ List<? extends JCTree> initlist, JCTree... trees) {
//		return loopHelperHavoc(loopSpecs, pos, indexDecl, initlist, null, trees);
//	}

	/** Adds a statement to increment the index variable */
	protected void loopHelperIncrementIndex(JCVariableDecl var) {
		JCIdent oldid = treeutils.makeIdent(var.pos, var.sym);
		JCIdent newid = treeutils.makeIdent(var.pos, var.sym);
		addStat(treeutils.makeAssignStat(var.pos, newid,
				treeutils.makeBinary(var.pos, JCTree.Tag.PLUS, treeutils.intplusSymbol, oldid, treeutils.one)));
	}

	/** Creates initial assert statements for any loop invariants */
	protected void loopHelperInitialInvariant(List<JmlStatementLoop> loopSpecs) {
		if (loopSpecs != null) {
			for (JmlStatementLoop loop : loopSpecs) {
				if (loop.clauseType == loopinvariantClause) {
					JmlStatementLoopExpr inv = (JmlStatementLoopExpr) loop;
					try {
						JCExpression copy = copy(inv.expression); // Might throw NoModelMethod
						addTraceableComment(inv, copy, inv.toString());
						JCExpression e = inv.translated ? copy : convertJML(copy);
						addAssert(inv, Label.LOOP_INVARIANT_PRELOOP, e);
					} catch (NoModelMethod e) {
						// continue - skip the assertion
					}
				}
			}
		}
	}

	/** Create the if statement that is the loop exit */
	protected Boolean loopHelperMakeBreak(List<JmlStatementLoop> loopSpecs, JCExpression cond, JCTree loop,
			DiagnosticPosition pos) {
		Boolean res = null;
		boolean split = ((IJmlLoop) pos).isSplit();
		ListBuffer<JCStatement> check = pushBlock();
        addFeasibilityCheck(loop, currentStatements, Strings.feas_loopexit, "at loop exit");
		JCBreak br = M.at(pos).Break(null);
		br.target = loop;
		addStat(br);
		JCBlock bl = popBlock(pos, check);
		if (split && currentSplit != null) {
			boolean conditionTrue = true;
			if (currentSplit.isEmpty()) {
				adjustSplit(2);
				res = true;
			} else {
				conditionTrue = currentSplit.charAt(0) == 'A';
				currentSplit = currentSplit.substring(1);
				res = conditionTrue;
			}
			JCExpression ccond = newTempIfNeeded(cond);
			if (conditionTrue) {
				addAssume(pos, Label.IMPLICIT_ASSUME, ccond);
				// Will skip all the material after the loop
			} else {
				addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeNot(pos, ccond));
				JCExpression ncond = treeutils.makeNot(pos.getPreferredPosition(), cond);
				addStat(M.at(pos).If(ncond, bl, null)); // FIXME - does this need newTempIfNeeded?
				// Will skip the rest of the loop
			}
		} else {
			JCExpression ncond = treeutils.makeNot(pos.getPreferredPosition(), cond);
			addStat(M.at(pos).If(ncond, bl, null)); // FIXME - does this need newTempIfNeeded?
		}
		//System.out.println("LOOP " + loop.getClass() + " " + ((IJmlLoop)loop).body() + " " + loop);
		// FIXME - use ((IJmlLoop)loop).body() but it is unexpectedly null
        addFeasibilityCheck(loop, currentStatements, Strings.feas_loopcondition, "at beginning of loop body");
		return res;
	}

	/** Convert the loop body */
	protected void loopHelperMakeBody(JCStatement body) {
		addTraceableComment(body, null, "Begin loop body");
		JCBlock bodyBlock = M.at(body).Block(0, null);
		Name label = names.fromString("loopBody_" + body.pos + "_" + nextUnique());
		JCLabeledStatement lab = M.at(body).JmlLabeledStatement(label, null, bodyBlock);
		continueStack.push(lab);
		addStat(lab);

		try {
			JCBlock bl = convertIntoBlock(body, body);
			bodyBlock.stats = bl.stats;
		} finally {
			continueStack.pop();
		}
	}

	/**
	 * Inserts the invariants as assumptions; also computes initial values of the
	 * variants. (at the beginning of a loop body)
	 */
	protected void loopHelperAssumeInvariants(List<JmlStatementLoop> loopSpecs, java.util.List<JCIdent> decreasesIDs,
			JCTree that, JCExpression lengthExpr) {
		addTraceableComment(that, null, "Begin loop check");
		DiagnosticPosition pos = that;

		{
			JCVariableDecl indexDecl = indexStack.get(0);
			{
				JCIdent id = treeutils.makeIdent(pos.getPreferredPosition(), indexDecl.sym);
				JCBinary bin = treeutils.makeBinary(pos.getPreferredPosition(), JCTree.Tag.LE, treeutils.intleSymbol,
						treeutils.zero, id);
				addAssume(pos, Label.IMPLICIT_ASSUME, bin);
			}

			if (lengthExpr != null) {
				JCIdent id = treeutils.makeIdent(pos.getPreferredPosition(), indexDecl.sym);
				JCBinary bin = treeutils.makeBinary(pos.getPreferredPosition(), JCTree.Tag.LE, treeutils.intleSymbol,
						id, lengthExpr);
				addAssume(pos, Label.IMPLICIT_ASSUME, bin);
			}
		}

		// Assume the invariants
		if (loopSpecs != null) {
			for (JmlStatementLoop loop : loopSpecs) {
				if (loop.clauseType == loopinvariantClause) {
					JmlStatementLoopExpr inv = (JmlStatementLoopExpr) loop;
					try {
						JCExpression copy = copy(inv.expression);
						addTraceableComment(inv, copy, inv.toString());
						JCExpression e = inv.translated ? copy : convertJML(copy);
						addAssume(inv, Label.LOOP_INVARIANT_ASSUMPTION, e);
					} catch (NoModelMethod e) {
						// continue - no assertions added
					}
				}
			}
		}

		// Compute and remember the variants
		if (loopSpecs != null) {
			for (JmlStatementLoop loop : loopSpecs) {
				if (loop.clauseType == loopdecreasesClause) {
					JmlStatementLoopExpr inv = (JmlStatementLoopExpr) loop;
					try {
						JCExpression copy = copy(inv.expression);
						addTraceableComment(inv, copy, inv.toString(), "Initial value of Loop Decreases expression");
						JCExpression e = convertJML(copy);
						JCIdent id = newTemp(e);
						id.pos = inv.pos;
						decreasesIDs.add(id);
					} catch (NoModelMethod e) {
						// continue
					}

				}
			}
		}
	}

	/** Check that the variants are non-negative */
	protected void loopHelperCheckNegative(java.util.List<JCIdent> decreasesIDs, DiagnosticPosition pos) {
		for (JCIdent id : decreasesIDs) {
			TypeTag tag = id.type.getTag();
			JCExpression z = addImplicitConversion(pos, id.type, treeutils.zero);
			if (id.type.tsym == jmltypes.BIGINT.repSym) {
				JCExpression compare = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "bigint_le", z, id);
				addAssert(id, Label.LOOP_DECREASES_NEGATIVE, compare);
			} else {
				JCBinary compare = treeutils.makeBinary(pos.getPreferredPosition(), JCTree.Tag.LE, z, id);
				addAssert(id, Label.LOOP_DECREASES_NEGATIVE, compare);
			}
		}
	}

	/** Asserts the invariants and that the variants are decreasing */
	protected void loopHelperAssertInvariants(List<JmlStatementLoop> loopSpecs, java.util.List<JCIdent> decreasesIDs) {
		if (loopSpecs != null) {
			for (JmlStatementLoop loop : loopSpecs) {
				if (loop.clauseType == loopinvariantClause) {
					JmlStatementLoopExpr inv = (JmlStatementLoopExpr) loop;
					try {
						JCExpression copy = copy(inv.expression);
						addTraceableComment(inv, copy, inv.toString());
						JCExpression e = inv.translated ? copy : convertJML(copy);
						addAssert(inv, Label.LOOP_INVARIANT, e);
					} catch (NoModelMethod e) {
						// continue
					}
				}
			}

			Iterator<JCIdent> iter = decreasesIDs.iterator();
			for (JmlStatementLoop loop : loopSpecs) {
				if (loop.clauseType == loopdecreasesClause) {
					JmlStatementLoopExpr inv = (JmlStatementLoopExpr) loop;
					try {
						JCExpression copy = copy(inv.expression);
						addTraceableComment(inv, copy, inv.toString());
						JCExpression e = inv.translated ? copy : convertJML(copy);
						JCIdent id = newTemp(e);

						if (id.type.tsym == jmltypes.BIGINT.repSym) {
							JCExpression compare = treeutils.makeUtilsMethodCall(inv.pos, "bigint_lt", id, iter.next());
							addAssert(id, Label.LOOP_DECREASES, compare);
						} else {
							JCBinary bin = treeutils.makeBinary(inv.pos, JCTree.Tag.LT, id, iter.next());
							addAssert(inv, Label.LOOP_DECREASES, bin);
						}

					} catch (NoModelMethod e) {
						// continue
					}
				}
			}
		}

	}

	/** Completes the loop */
	protected void loopHelperFinish(JmlWhileLoop loop, JCTree that) {
		JCBlock bl = popBlock(that);
		loop.body = bl;
		loop.setType(that.type);
		addStat(loop);
		treeMap.remove(that);
		indexStack.remove(0);
	}

	// OK
	@Override
	public void visitJmlForLoop(JmlForLoop that) {

		addTraceableComment(that, "for ...");

		/*
		 * loop_invariant INV loop_variant VAR label: for (INIT; COND; STEP) BODY
		 * becomes { ... statements from INIT assert INV label: while (true) { havoc
		 * assume INV TEMP = VAR ... statements from COND if (!COND') { assert INV;
		 * break; } assert 0 <= TEMP loop_bodyN: { ... statements from BODY ... continue
		 * --> break loop_bodyN; ... break --> break; } ... statements from STEP assert
		 * INV TEMP2 = VAR assert TEMP2 < TEMP } // FIXME - if break exits still have to
		 * satisfy invariant, put the check here }
		 * 
		 */

		// FIXME - need label for loop if any and the target mapping

		// Outer block to restrict scopes of temporaries
		pushBlock();

		if (that.init != null)
			scan(that.init);

		JCVariableDecl indexDecl = loopHelperDeclareIndex(that);

		Name loopLabelInit = names.fromString("LoopInit");
		JmlLabeledStatement istat = M.at(that.body.pos).JmlLabeledStatement(loopLabelInit, null, null);
		recordLabel(loopLabelInit, istat);
		addStat(istat);

		if (mostRecentInlinedLoop != null) {
			for (JmlStatementLoop stat : mostRecentInlinedLoop.translatedSpecs) {
				if (stat instanceof JmlStatementLoopExpr) {
//                    if (mostRecentInlinedLoop.countIds.isEmpty()) {
//                        
//                    } else {
					JmlStatementLoopExpr loopEx = (JmlStatementLoopExpr) stat;
					JCExpression e = loopEx.expression;
//                        JCIdent id = mostRecentInlinedLoop.countIds.get(0);
//                        JCVariableDecl decl = treeutils.makeVariableDecl((VarSymbol)id.sym, treeutils.makeIdent(stat,indexDecl.sym));
//                        decl.pos = stat.pos;
//                        loopEx.expression = M.at(loopEx.pos).LetExpr(decl, e);
					JCIdent newid = treeutils.makeIdent(stat, indexDecl.sym);
					Map<Object, JCExpression> replacements = new HashMap<>();
					replacements.put(countID, newid);
					loopEx.expression = JmlTreeSubstitute.substitute(M, e, replacements);
//                    }
				}
			}
//            for (JCIdent id: mostRecentInlinedLoop.countIds) {
//                id.name = indexDecl.name;
//                id.sym = indexDecl.sym;
//                id.type = indexDecl.type; // TODO Presumably the type does not change?
//            }
			that.loopSpecs = that.loopSpecs.appendList(mostRecentInlinedLoop.translatedSpecs);
			mostRecentInlinedLoop = null;
		}

		java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

		// Create this early so it is available as a target
		JmlWhileLoop loop = M.at(that).WhileLoop(treeutils.trueLit, null);
		treeMap.put(that, loop);

		// Test that invariants hold before entering loop
		loopHelperInitialInvariant(that.loopSpecs);

		// New loop body
		pushBlock();

		// Havoc all items that might be changed in the loop
		if (esc) {
			boolean b = loopHelperHavoc(that.loopSpecs, that.body, indexDecl, that.init, that.step, that.body,
					that.cond);
//			if (!b) {
//	              changeStateForLoop(that, that.loopSpecs); // FIXME _ but only if something is havoced? and it is not a local variable?
//			}
		}

		JmlLabeledStatement lstat = M.at(that.body.pos).JmlLabeledStatement(loopbodyLabelName, null, null);
		recordLabel(loopbodyLabelName, lstat);
		addStat(lstat);

		loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that, null);

		// Compute the condition, recording any side-effects
		int savedHeapCount = -1;
		Boolean splitInfo = null;
		if (that.cond != null) {

			addTraceableComment(that.cond, that.cond, "Loop test");
			JCExpression cond = convertExpr(that.cond);

			// The exit block tests the condition; if exiting, it breaks out of the loop
			splitInfo = loopHelperMakeBreak(that.loopSpecs, cond, loop, that);
			savedHeapCount = heapCount;
	        currentEnv = currentEnv.pushEnvCopy();
		}
		boolean doRemainderOfLoop = splitInfo == null || splitInfo;

		// Now in the loop, so check that the variants are non-negative
		if (doRemainderOfLoop)
			loopHelperCheckNegative(decreasesIDs, that);

		// Then translate the original loop body
		// Have to do some footwork to get the Block object before constructing its
		// contents

		if (doRemainderOfLoop)
			loopHelperMakeBody(that.body);

		if (that.step != null && doRemainderOfLoop)
			scan(that.step);

		// increment the index
		if (doRemainderOfLoop)
			loopHelperIncrementIndex(indexDecl);

		// After the loop, check the invariants and check that the variants have
		// decreased
		if (doRemainderOfLoop)
			loopHelperAssertInvariants(that.loopSpecs, decreasesIDs);

		// Finish up the new loop body
		// Finish up the output block
		heapCount = savedHeapCount; // FIXME - only if no break statements targeted the end of the loop
        if (savedHeapCount != -1) currentEnv = currentEnv.popEnv();

		loopHelperFinish(loop, that);
		JCBlock bl = popBlock(that);
		addStat(bl);
		if (splitInfo != null && splitInfo)
			continuation = Continuation.HALT;
		labelPropertiesStore.pop(loopbodyLabelName);
		labelPropertiesStore.pop(loopLabelInit);
	}

	@Override
	public void visitJmlGroupName(JmlGroupName that) {
		JmlGroupName g = M.at(that).JmlGroupName(copy(that.selection)); // FIXME - not sure about the kind of
																				// copying
		g.setType(that.type);
		g.sym = that.sym;
		result = g;
	}


	int lblUnique = 0;

	// OK
	@Override
	public void visitJmlLblExpression(JmlLblExpression that) {
	    //System.out.println("LBL EXPRT " + that);
		JCExpression expr = convertExpr(that.expression);
        //System.out.println("LBL EXPR RES " + expr);

		if (depth > 0) {
			result = eresult = expr;
			return;
		}
		// The format of this string is important in interpreting it in JmlEsc
		String nm;
		if (that.label.toString().contains("CPRE")) {
			nm = that.label.toString();
			preconditionDetailClauses.put(nm, log.currentSourceFile());
		} else {
			nm = Strings.labelVarString + that.kind.keyword().substring(1) + "_" + that.label + "_" + (++lblUnique);
		}
		JCIdent id = newTemp(that.getLabelPosition(), nm, expr);
		id.pos = that.pos;
		result = eresult = id;
		if (expr instanceof JCLiteral || expr instanceof JCIdent) {
			result = eresult = expr;
		}
        //System.out.println("LBL EXPRZ " + eresult);

		if (rac) {
			JCExpression lit = treeutils.makeLit(that.getPreferredPosition(), syms.stringType, that.label.toString());
			// In rac math mode, eresult might have been converted to BigInteger or Real
			// Normally this is reported out through rportObject, with no ill effects,
			// except that we like to report Character values as characters
			if (expr.type != that.type && that.type.getTag() == TypeTag.CHAR) {
				expr = addImplicitConversion(that, syms.intType, expr);
				expr = treeutils.makeTypeCast(that, that.type, expr);
				result = eresult = id = newTemp(that.getLabelPosition(), nm, expr);
			}
			String name = null;
			Type t = eresult.type;
			TypeTag tag = t.getTag();
			if (!t.isPrimitive()) {
				name = "reportObject";
			} else if (tag == TypeTag.INT) {
				name = "reportInt";
			} else if (tag == TypeTag.BOOLEAN) {
				name = "reportBoolean";
			} else if (tag == TypeTag.LONG) {
				name = "reportLong";
			} else if (tag == TypeTag.CHAR) {
				name = "reportChar";
			} else if (tag == TypeTag.SHORT) {
				name = "reportShort";
			} else if (tag == TypeTag.FLOAT) {
				name = "reportFloat";
			} else if (tag == TypeTag.DOUBLE) {
				name = "reportDouble";
			} else if (tag == TypeTag.BYTE) {
				name = "reportByte";
			} else if (tag == TypeTag.BOT) {
				name = "reportObject";
			} else if (t instanceof JmlType) {
				name = "reportObject";
			} else {
				// this is a type error - should never get here
				error(that, "Unknown type in a \\lbl expression: " + t);
			}
			if (name != null) {
				JCFieldAccess m = findUtilsMethod(that, name);
				JCMethodInvocation c = M.at(that).Apply(null, m,
						List.<JCExpression>of(lit, treeutils.makeIdent(id.pos, id.sym)));
				c.type = id.type;
				JCStatement st = M.at(that).Exec(c);
				if (that.kind == lblposKind) {
					// Only report if the expression is true
					// It is a type error if it is not boolean
					st = M.at(that).If(treeutils.makeIdent(id.pos, id.sym), st, null);
				} else if (that.kind == lblnegKind) {
					// Only report if the expression is false
					// It is a type error if it is not boolean
					st = M.at(that).If(treeutils.makeNot(that.pos, treeutils.makeIdent(id.pos, id.sym)), st, null);
				}
				addStat(st);
			}
		}
	}

	// OK
	@Override
	public void visitJmlMatchExpression(JmlMatchExpression that) {
		// FIXME - not yet implemented
		result = treeutils.makeZeroEquivalentLit(that.pos, that.type);
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
		JmlMethodClauseConditional mc = M.at(that).JmlMethodClauseConditional(that.keyword, that.clauseKind,
				convertExpr(that.expression), convertExpr(that.predicate));
		mc.setType(that.type);
		mc.sourcefile = that.sourcefile;
		result = mc;
	}

	// OK
	@Override
	public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
		JmlMethodClauseDecl mc = M.at(that).JmlMethodClauseDecl(that.keyword, that.clauseKind, convert(that.decls));
		mc.setType(that.type);
		mc.sourcefile = that.sourcefile;
		result = mc;
	}

	// OK
	@Override
	public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
		JmlMethodClauseExpr mc = M.at(that).JmlMethodClauseExpr(that.keyword, that.clauseKind,
				convertExpr(that.expression));
		mc.setType(that.type);
		mc.sourcefile = that.sourcefile;
		result = mc;
	}

	// OK
	@Override
	public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
		JmlMethodClauseGroup mc = M.at(that).JmlMethodClauseGroup(convert(that.cases));
		mc.setType(that.type);
		mc.sourcefile = that.sourcefile;
		result = mc;
	}

	// OK
	@Override
	public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
		JmlMethodClauseSignals mc = M.at(that).JmlMethodClauseSignals(that.keyword, that.clauseKind,
				convert(that.vardef), convertExpr(that.expression));
		mc.setType(that.type);
		mc.sourcefile = that.sourcefile;
		result = mc;
	}

	// OK
	@Override
	public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
		JmlMethodClauseSignalsOnly mc = M.at(that).JmlMethodClauseSignalsOnly(that.keyword, that.clauseKind, convertExprList(that.list));
		mc.setType(that.type);
		mc.defaultClause = that.defaultClause;
		mc.sourcefile = that.sourcefile;
		result = mc;
	}

	// OK
	@Override
	public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
		JmlMethodClauseStoreRef mc = M.at(that).JmlMethodClauseStoreRef(that.clauseKind.keyword(), that.clauseKind,
				convertExprList(that.list));
		mc.setType(that.type);
		mc.sourcefile = that.sourcefile;
		result = mc;
	}

	// OK
	@Override
	public void visitJmlMethodDecl(JmlMethodDecl that) {
		// Checks whether there is a Skip annotation
		if (esc && JmlEsc.instance(context).skip(that))
			return;
		if (esc && !utils.filter(that, false))
			return;
		if (rac && (JmlEsc.instance(context).skipRac(that) || that.body == null)) {
			if (that.body == null && that.sym.owner.isInterface() && (that.mods.flags & Flags.DEFAULT) != 0) {
				// A default was put on a method with no body, presumably because it was a model
				// method in an interface
				// SO remove the default and add Abstract
				that.mods.flags &= ~Flags.DEFAULT;
				that.mods.flags |= Flags.ABSTRACT;
				that.sym.flags_field &= ~Flags.DEFAULT;
				that.sym.flags_field |= Flags.ABSTRACT;
			}
			if (classDefs != null)
				classDefs.add(that); // FIXME - should make a fresh copy of the declaration
			return;
		}
		if (org.jmlspecs.openjml.Utils.debug("trans"))
			System.out.println("JAA-visitJmlMethodDecl-A " + that.sym.owner + that.sym + " " + System
					.identityHashCode(ClassReader.instance(context).enterClass(names.fromString("java.lang.Object"))));

		Translations saved_t = translations;
		String saved_original = originalSplit;
		String saved_current = currentSplit;
		// Simple name of method
		String nm = that.name.toString();

		// If we visit this method by visiting its containing class, classDecl will be
		// set
		// but if we call this visit method directly, e.g., from the api,
		// it will not be, and we need to find the class
		if (classDecl == null)
			classDecl = utils.getOwner(that);

		log.useSource(that.source());
		boolean saved = translatingJML;
		JmlMethodDecl savedMD = methodDecl;
		methodDecl = that;
		Translations t = new Translations(context);
		methodBiMap.put(that, t);
		try {
			// FIXME - implemente constructors - need super calls.
			// if (that.restype == null) { classDefs.add(that); return; } // FIXME -
			// implement constructors
			while (true) {
				String splitkey = t.nextToDo();
				if (splitkey == null) break;
				// Save - in case of recursive calls
				setSplits(t, splitkey);
				JCBlock body = null;
				body = convertMethodBodyNoInit(that, classDecl);

				List<JCTypeParameter> typarams = that.typarams;
                List<JCVariableDecl> params = that.params;
                JCExpression restype = that.restype;
				if (fullTranslation) {
				    typarams = copy(typarams); // FIXME - is there anything to be translated
				    params = copy(params); // Just a copy - the parameters are just modifiers, types, and names
				    restype = convertExpr(restype);
				}
				JCModifiers mods = convert(that.mods);
				if (rac && attr.isSpecPublic(that.sym)) {
					long newflags = (mods.flags & ~Flags.AccessFlags) | Flags.PUBLIC;
					mods.flags = newflags;
					that.sym.flags_field = newflags;
				}
				if (rac && attr.isSpecProtected(that.sym)) {
					long newflags = (mods.flags & ~Flags.AccessFlags) | Flags.PROTECTED;
					mods.flags = newflags;
					that.sym.flags_field = newflags;
				}
				JmlMethodDecl m = M.MethodDef(mods, that.name, restype, typarams, null, params,
						convertExprList(that.thrown), body, convertExpr(that.defaultValue));
				m.pos = that.pos;
				m.sym = that.sym;
				m.setType(that.type);
				m._this = that._this;
				m.sourcefile = that.sourcefile;
				// m.owner = that.owner; // FIXME - new class decl?
				m.docComment = that.docComment;
				m.cases = copy(that.cases);
				m.methodSpecsCombined = that.methodSpecsCombined; // FIXME - copy?
				m.specsDecl = that.specsDecl; // FIXME - needs new reference
				if (classDefs != null)
					classDefs.add(m); // classDefs can be null if JmlEsc.check is called directly on a JCMethodDecl

				// FIXME - not working yet
				// if (rac && that.sym.isStatic() && that.name.toString().equals("main")) { //
				// FIXME - check the arguments?
				// Name n = names.fromString("_JML_racE");
				// ClassSymbol sym = attr.createClass("java.lang.NoClassDefFoundError");
				// JCVariableDecl decl = treeutils.makeVarDef(sym.type, n, that.sym, that.pos);
				// // decl.type =
				// JCExpression msg = treeutils.makeStringLiteral(that.pos, "Executable is
				// compiled with RAC, but the classpath is missing the jmlruntime.jar");
				// JCExpression ty = M.at(that).Type(syms.runtimeExceptionType);
				// JCExpression newex = M.at(that).NewClass(null, List.<JCExpression>nil(), ty,
				// List.<JCExpression>of(msg), null);
				// JCThrow th = M.at(that).Throw(newex);
				// JCBlock bl = M.at(that).Block(0L, List.<JCStatement>of(th));
				// JCCatch catcher = M.at(that).Catch(decl,bl);
				// JCTry tr = M.at(that).Try(m.body, List.<JCCatch>of(catcher), null);
				// m.body = M.at(that).Block(0L, List.<JCStatement>of(tr));
				// }

				result = m;
				t.addTranslation(originalSplit, m);
			}
//            String splits = "";
//            for (String s: translations.keys()) splits += (s + " " );
//            log.note(that.pos,"jml.message","Splits: " + splits);
		} catch (JmlNotImplementedException e) {
			// FIXME _ if it is actually the synthetic method for a model field we used to
			// use this
			// notImplemented("represents clause containing ", ee, that.source());
			if (that.name.toString().startsWith(Strings.modelFieldMethodPrefix)) {
				notImplemented("represents clause containing ", e);
			} else {
				notImplemented("method (or represents clause) containing ", e);
			}
			utils.error(e.pos, "jml.unrecoverable",
					"Unimplemented construct in a method or model method or represents clause");
		} catch (PropagatedException e) {
			throw e;
		} catch (Exception | AssertionError e) {
			utils.note(that, "jml.message", "Exception while translating method: " + that);
			throw e;
		} finally {
			methodDecl = savedMD;
			translatingJML = saved;
			// Restore
			translations = saved_t;
			originalSplit = saved_original;
			currentSplit = saved_current;
			if (org.jmlspecs.openjml.Utils.debug("trans"))
				System.out.println(
						"JAA-visitJmlMethodDecl-Z " + that.sym.owner + that.sym + " " + System.identityHashCode(
								ClassReader.instance(context).enterClass(names.fromString("java.lang.Object"))));
		}

	}

	//// FIXME - Document - should this be used where generic typeargs exist?
	protected JCExpression translateTypeArg(JCExpression targ) {
		// Argument is a type, not an expression, so we
		// replace it with a type literal
		if (targ instanceof JCTree.JCTypeApply) {
			JCTree.JCTypeApply ta = (JCTree.JCTypeApply) targ;
			JCTree.JCFieldAccess f = M.Select(ta.clazz, names._class);
			f.type = syms.classType;
			f.sym = f.type.tsym;
			int size = ta.arguments.size();
			ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
			for (JCExpression ttarg : ta.arguments) {
				args.add(translateTypeArg(ttarg));
			}
			Type elemtype = args.first().type;
			JCNewArray argsarray = M.NewArray(M.Type(elemtype),
					List.<JCExpression>of(treeutils.makeIntLiteral(Position.NOPOS, size)), args.toList());
			argsarray.type = new Type.ArrayType(elemtype, syms.arrayClass);
			return methodCallUtilsExpression(targ, "makeTYPE", f, argsarray);
		} else if (targ instanceof JCTree.JCWildcard) {
			return methodCallUtilsExpression(targ, "makeTYPEQ");
			// FIXME - need to handle more subtypes differently, I'm sure
		} else if (targ instanceof JCArrayTypeTree) {
			// FIXME - this not handled
			JCTree.JCFieldAccess f = M.Select(targ, names._class);
			f.type = syms.classType;
			f.sym = f.type.tsym;
			return methodCallUtilsExpression(targ, "makeTYPE0", f);
		} else { // JCPrimitiveTypeTree, JCFieldAccess, JCIdent, JCArrayTypeTree
			JCTree.JCFieldAccess f = M.Select(targ, names._class);
			f.type = syms.classType;
			f.sym = f.type.tsym;
			return methodCallUtilsExpression(targ, "makeTYPE0", f);
		}
	}

	// OK
	/** Creates a type-checked expression for (expr).getClass() - for RAC */
	protected JCExpression methodCallgetClass(JCExpression expr) {
		Name n = names.fromString("getClass");
		Iterable<Symbol> e = syms.objectType.tsym.members().getSymbolsByName(n);
		Symbol ms = e.iterator().next();
		JCFieldAccess m = M.Select(expr, n);
		m.sym = ms;
		m.type = m.sym.type;

		JCExpression c = M.Apply(null, m, List.<JCExpression>nil());
		c.setType(syms.classType);
		return c;
	}

	// FIXME - what about generic types
	// FIXME - what about arrays of arrays
	/** Translates \typeof(arg) */
	protected void translateTypeOf(JCMethodInvocation tree) {
		JCExpression arg = tree.args.get(0);
		TypeTag tag = arg.type.getTag();
		switch (tag) {
		case ARRAY:
		case CLASS:
			eresult = methodCallgetClass(convertExpr(arg));
			break;
		case BOOLEAN:
			eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Boolean");
			break;
		case INT:
			eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Integer");
			break;
		case LONG:
			eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Long");
			break;
		case SHORT:
			eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Short");
			break;
		case BYTE:
			eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Byte");
			break;
		case FLOAT:
			eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Float");
			break;
		case DOUBLE:
			eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Double");
			break;
		case CHAR:
			eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Character");
			break;
		default:
			log.error(arg.pos, "jml.unknown.construct", "typeof for " + arg.type, "JmlRac.translateTypeOf");
			// We give it an arbitrary value // FIXME - or do we call it undefined
			eresult = treeutils.makePrimitiveClassLiteralExpression("java.lang.Boolean");
			break;
		}
		// Make a \TYPE from a Java class literal
		result = eresult = methodCallUtilsExpression(tree, "makeTYPE0", eresult);
	}

	// TODO: Review
	/** Translates \type(arg) */
	protected JCExpression translateType(JCExpression arg) {
		if (arg.type instanceof Type.TypeVar) {
			Type tt = typevarMapping.get(arg.type.tsym);
			if (tt == null) {
				// FIXME - at least for generic functions, the wrong symbol is being looked up
				for (TypeSymbol ts : typevarMapping.keySet()) {
					if (ts.toString().equals(arg.toString())) {
						tt = typevarMapping.get(ts);
						break;
					}
				}
			}
			if (tt == null)
				tt = arg.type;
			JCExpression t = treeutils.makeType(arg.pos, tt);
			if (t != null)
				arg = t;
			return arg;
		}
		boolean pv = checkAccessEnabled;
		checkAccessEnabled = false;
		try {
			return convertExpr(arg);
		} finally {
			checkAccessEnabled = pv;
		}
	}

	/** Helper method to translate \elemtype expressions for RAC */
	protected void translateElemtype(JCMethodInvocation tree) {
		// OK for Java types, but not complete for JML types - FIXME
		JCExpression arg = tree.args.head;
		arg = convertExpr(arg);
		JCExpression c;
		if (arg.type.tsym.toString().equals("java.lang.Class")) { // FIXME - do this better?
			c = methodCallUtilsExpression(tree, "getJavaComponentType", arg);
		} else {
			c = methodCallUtilsExpression(tree, "getJMLComponentType", arg);
		}
		result = eresult = c;
	}

	protected Utils.DoubleMap<Name, Symbol, JCVariableDecl> oldarrays = new Utils.DoubleMap<Name, Symbol, JCVariableDecl>();

	protected void addToOldList(Name label, JCStatement stat) {
		labelPropertiesStore.get(label).labeledStatement.extraStatements.add(stat);
	}

	protected boolean inInvariantFor = false;

	// OK
	// These are special JML fcn-like calls (e.g. \old, \nonnullelements, ...)
	@Override
	public void visitJmlMethodInvocation(JmlMethodInvocation that) {
		IJmlClauseKind k = that.kind;

		if (k != null)
			switch (k.keyword()) {
			case oldID:
			case preID:
			case pastID: {
				if (currentEnv.stateLabel == null) {
					JmlLabeledStatement stat = M.at(that).JmlLabeledStatement(hereLabelName, null, null);
					recordLabel(hereLabelName, stat);
				}
				currentEnv = currentEnv.pushEnvCopy();
				//var savedEnv = evalStateLabel;
				// FIXME _ this implementation is not adequate for checking postconditions with
				// \old from callers
				// FIXME - also it does not work for rac at labelled locations
				int savedHeap = heapCount;
				try {
					var labelArg = that.args.size()>1?that.args.get(1):null;
					Name evalStateLabel = normalizeLabel(labelArg, k == StateExpressions.preKind ? attr.preLabel : attr.oldLabel, that );
					currentEnv.stateLabel = evalStateLabel;
					LabelProperties lp = labelPropertiesStore.get(evalStateLabel);
					that.labelProperties = lp;

					JCExpression arg = that.args.get(0);
                    //System.out.println("OLDEXPR " + evalStateLabel + " " + arg);
					if (evalStateLabel == null) {
						eresult = convertExpr(arg);
					} else if (rac) {
						pushBlock();
						//var saved = evalStateLabel;
						try {
							currentEnv.stateLabel = evalStateLabel = null;
							currentStatements = lp.extraStats();
							heapCount = lp.heapCount;
							if (!convertingAssignable && arg instanceof JCArrayAccess
									&& (((JCArrayAccess) arg).indexed instanceof JCIdent
											|| ((JCArrayAccess) arg).indexed instanceof JCFieldAccess)) {
								JCArrayAccess aa = (JCArrayAccess) arg;
								Symbol sym = treeutils.getSym(aa.indexed);
								JCExpression ad = convertExpr(aa.indexed);
								JCExpression a = treeutils.copyArray(that.pos, ad);
								JCVariableDecl d = newTempDecl(arg, a.type);
								d.init = a;
								oldarrays.put(evalStateLabel, sym, d);
								currentStatements.add(d); // This decl is used in postconditions - cannot currently be
															// put into Pre extra material

								JCIdent id = treeutils.makeIdent(arg.pos, d.sym);
								JCArrayAccess newaa = M.at(aa.pos).Indexed(id, aa.index);
								newaa.type = aa.type;
								visitIndexed(newaa); // may add material into label's extra statements
								// The above call sets result and eresult

							} else {
								arg = convertExpr(arg); // into label extra statements
								String s = "_JML___old_" + nextUnique(); // FIXME - Put string in Strings
								Name nm = names.fromString(s);
								JCVariableDecl d = treeutils.makeVarDef(arg.type, nm, methodDecl.sym,
										treeutils.makeZeroEquivalentLit(arg.pos, arg.type));
								// v.mods.flags |= Flags.FINAL; // If we use this, the sym has to be set FINAL
								// as well.
								ListBuffer<JCStatement> check7 = pushBlock();
								addStat(treeutils.makeAssignStat(arg.pos, treeutils.makeIdent(arg.pos, d.sym), arg));
								JCBlock bl = popBlock(arg, check7);
								JCTry st = makeRACTry(bl, "_JML__old_ex", arg);
								addStat(d); // into label extra statements
								addStat(st); // into label extra statements
								JCIdent id = treeutils.makeIdent(arg.pos, d.sym);
								eresult = id;
							}
						} finally {
							popBlock();
						}
					} else { // esc
						arg = convertExpr(that.args.get(0)); // convert is affected by evalStateLabel
						// We have to wrap this in an old (even though it sometimes wraps twice)
						// in order to get arrays properly resolved  // TODO: Is this still true?
						JmlMethodInvocation a = makeOld(that.pos, arg, evalStateLabel);
						a.labelProperties = that.labelProperties;
						eresult = a;
					}
				} finally {
					currentEnv = currentEnv.popEnv();
					if (currentEnv.stateLabel == null) {
						labelPropertiesStore.pop(hereLabelName);
					}
					heapCount = savedHeap;
				}
				break;
			}
			case nonnullelementsID: {
				int n = that.args.size();
				if (n == 0) {
					result = eresult = treeutils.trueLit;
				} else {
					JCExpression conj = null;
					for (JCExpression arg : that.args) {
						JCExpression e = convertExpr(arg);
						e = wrapTranslatedNonnullelements(arg,e);
						conj = conj == null ? e : treeutils.makeAnd(arg.pos, conj, e);
					}
					result = eresult = conj;
				}
				break;
			}
			case typeofID: {
				if (rac) {
					translateTypeOf(that);
				}
				if (esc || infer) {
					JCExpression arg = convertExpr(that.args.get(0));
					JmlMethodInvocation meth = M.at(that).JmlMethodInvocation(that.kind, arg);
					meth.startpos = that.startpos;
					meth.varargsElement = that.varargsElement;
					meth.meth = that.meth;
					meth.type = that.type;
					meth.labelProperties = that.labelProperties;
					meth.typeargs = that.typeargs; // FIXME - do these need translating?
					result = eresult = meth;
				}
				break;
			}
			case typelcID: {
				if (rac) {
					JCExpression arg = that.args.get(0);
					if (that.javaType) {
						JCTree.JCFieldAccess f = M.Select(arg, names._class);
						f.type = syms.classType;
						f.sym = f.type.tsym;
						result = eresult = f;
					} else {
						result = eresult = translateTypeArg(arg);
					}
					// FIXME - used to be something like result = eresult =
					// treeutils.trType(that.pos, type); ???
				}
				if (esc || infer) {
					JCExpression t = translateType(that.args.get(0));
					JmlMethodInvocation e = treeutils.makeJmlMethodInvocation(that, that.kind, that.type, t);
					e.javaType = that.javaType;
					result = eresult = e;
				}
				break;
			}
			case elemtypeID: {
				if (rac)
					translateElemtype(that);
				if (esc || infer) {
					JCExpression arg = that.args.get(0);
					if (arg.type == jmltypes.TYPE) {
						JCExpression t = translateType(that.args.get(0));
						result = eresult = treeutils.makeJmlMethodInvocation(that, elemtypeKind, that.type, t);
					} else {
						result = eresult = treeutils.makeJmlMethodInvocation(that, typeofKind, that.type,
								convertJML(arg));
						result = eresult = treeutils.makeJmlMethodInvocation(that, elemtypeKind, that.type, eresult);
					}
				}
				break;
			}
			case distinctID: {
				// Any type error should have been reported in JmlAttr
				boolean anyPrimitive = false;
				Type maxPrimitiveType = null;
				for (JCExpression arg : that.args) {
					Type tt = arg.type;
					if (tt.isErroneous())
						continue;
					if (tt.isPrimitive()) {
						anyPrimitive = true;
					}
				}
				if (anyPrimitive)
					for (JCExpression arg : that.args) {
						Type tt = arg.type;
						if (arg.type.isErroneous())
							continue;
						if (!tt.isPrimitive())
							tt = types.unboxedType(tt);
						if (arg.type.getTag() == TypeTag.VOID) {
							// FIXME -error
						} else if (maxPrimitiveType == null) {
							maxPrimitiveType = arg.type;
						} else if (types.isConvertible(tt, maxPrimitiveType)) {
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
					if (anyPrimitive)
						ex = addImplicitConversion(arg, maxPrimitiveType, ex);
					newargs.add(ex);
				}
				result = eresult = M.at(that.pos).JmlMethodInvocation(distinctKind, newargs.toList());
				eresult.type = syms.booleanType;
				that.kind = distinctKind;
				break;
			}
			
			case invariantForID:
			case staticInvariantForID:
			{
				boolean saved = inInvariantFor;
				inInvariantFor = true;
				result = eresult = that.kind.assertionConversion(this, that);
				inInvariantFor = saved;
				break;
			}
			case bigintMathID:
			case javaMathID:
			case safeMathID: { // Exactly one argument
				currentEnv = currentEnv.pushEnvCopy();
				try {
					if (k == bigintMathKind)
						currentEnv.arithmeticMode = Arithmetic.Math.instance(context);
					if (k == safeMathKind)
						currentEnv.arithmeticMode = Arithmetic.Safe.instance(context);
					if (k == javaMathKind)
						currentEnv.arithmeticMode = Arithmetic.Java.instance(context);
					JCExpression arg = that.args.get(0);
					JCExpression ex = convertExpr(arg);
					result = eresult = ex;
				} finally {
					currentEnv = currentEnv.popEnv();
				}
				break;
			}
			case notModifiedID: {
				JCExpression and = null;
				for (JCExpression arg : that.args) {
					// FIXME - use past instead of old?
					// FIXME - what prestate should we refer to - e.g. refining statements and loops
					// will have a different one
					Name earlierState = attr.preLabel;
					JCBinary bin;
					if (arg instanceof JCIdent) {
						JCExpression copy = copy(arg);
						JCExpression old = makeOld(arg.pos, copy, earlierState);
//						if (rac)
//							old = convertJML(old);
						bin = treeutils.makeEquality(arg.pos, arg, old);
					} else if (arg instanceof JCFieldAccess && ((JCFieldAccess) arg).name != null) {
						JCExpression copy = copy(arg);
						JCExpression old = makeOld(arg.pos, copy, earlierState);
						bin = treeutils.makeEquality(arg.pos, arg, old);
					} else if (arg instanceof JCArrayAccess) {
						JCArrayAccess ar = (JCArrayAccess) arg;
						JCExpression copy = copy(ar);
						JCExpression old = makeOld(arg.pos, copy, earlierState);
//						if (rac)
//							old = convertJML(old);
						bin = treeutils.makeEquality(arg.pos, ar, old);
					} else if (arg instanceof JmlStoreRefArrayRange) { // Apparently even single indexes are parsed into
																		// ranges
						JmlStoreRefArrayRange ar = (JmlStoreRefArrayRange) arg;
						if (ar.lo == ar.hi) {
							JCExpression expr = M.at(arg.pos).Indexed(ar.expression, ar.lo);
							expr.type = arg.type;
							JCExpression copy = copy(expr);
							JCExpression old = makeOld(arg.pos, copy, earlierState);
//							if (rac)
//								old = convertJML(old);
							bin = treeutils.makeEquality(arg.pos, expr, old);
						} else {
							throw new JmlNotImplementedException(that, that.token.internedName());
						}
					} else {
						// could be a.*, a[*], a[i..j]
						throw new JmlNotImplementedException(that, that.token.internedName());
					}
					and = and == null ? bin : treeutils.makeBitAnd(that.pos, and, bin);
				}
				result = eresult = convertExpr(and);
				break;
			}
			case freshID: {
				if (currentOldLabel == null) {
					// Likely a model method in a method spec clause that has a fresh expression -- which is dubious
				}
				Name label = normalizeLabel(that.args.size() > 1 ? that.args.get(1) : null, attr.oldLabel, that);
				if (rac) {
					throw new JmlNotImplementedException(that, that.kind.keyword());
				} else {
					result = eresult = makeFreshExpression(that, convertExpr(that.args.get(0)), label);
				}
				break;
			}
			case allocID: {
				Name label = normalizeLabel(that.args.size() > 1 ? that.args.get(1) : null, attr.oldLabel, that);
				if (rac) {
					throw new JmlNotImplementedException(that, that.kind.keyword());
				} else {
					result = eresult = makeAllocExpression(that, convertExpr(that.args.get(0)), label);
				}
				break;
			}
			case erasureID: {
				JCExpression arg = that.args.get(0);
				if (arg.type == syms.classType) {
					// no-op
					result = eresult = convertExpr(arg);
				} else if (rac) {
					arg = convertJML(arg);
					result = eresult = treeutils.makeUtilsMethodCall(that.pos, "erasure", arg);
				} else if (esc) {
					JCExpression t = translateType(arg);
					result = eresult = treeutils.makeJmlMethodInvocation(that, that.kind, that.type, t);
					t = treeutils.makeNeqObject(eresult.pos, eresult, treeutils.nullLit);
					addAssume(t, Label.IMPLICIT_ASSUME, t);
				}
				break;
			}

			case Functional.bsrequiresID:
			case Functional.bsensuresID:
			case Functional.bsreadsID:
			case Functional.bsassignsID: {
				ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
				for (JCExpression arg : that.args) {
					JCExpression ex = convertExpr(arg);
					newargs.add(ex);
				}
				result = eresult = M.at(that.pos).JmlMethodInvocation(that.token, newargs.toList());
				eresult.type = syms.booleanType;
				if (splitExpressions)
					result = eresult = newTemp(eresult);
				eresult.type = syms.booleanType;
				break;
			}

			case bsmaxID:
			case reachID:
			case spaceID:
			case workingspaceID:
			case durationID:
			case isInitializedID:
			case bsnowarnID:
			case nowarnopID:
			case warnID:
			case warnopID:
			case notAssignedID:
			case onlyAssignedID:
			case onlyCapturedID:
				// FIXME - not implemented
				throw new JmlNotImplementedException(that, that.kind.keyword());

			case LocsetExtensions.unionID:
			{
			    //System.out.println("UNCONVERTED-UNION " + that);
                ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
                that.args.stream().forEach(a -> newargs.add(convertExpr(a)));
                result = eresult = M.at(that.pos).JmlMethodInvocation(that.kind, newargs.toList());
                //System.out.println("CONVERTED-UNION " + eresult);
                eresult.type = that.type;
                break;
			}
            case LocsetExtensions.subsetID:
            {
                //System.out.println("UNCONVERTED " + that);
                ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
                that.args.stream().forEach(a -> newargs.add(convertExpr(a)));
                //System.out.println("CONVERTED " + newargs);
                try {
                result = eresult = simplifySubset(newargs.first(), newargs.toList().get(1), currentEnv, true);
                } catch (Exception e) {
                    e.printStackTrace(System.out);
                }
                //System.out.println("SIMPLIFIED " + eresult);
                break;
            }
           case LocsetExtensions.disjointID:
           {
               //System.out.println("UNCONVERTED-DISJOINT " + that);
               ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
               that.args.stream().forEach(a -> newargs.add(convertExpr(a)));
               //System.out.println("CONVERTED-DISJOINT " + newargs + " " + newargs.toList().get(1).getClass());
               try {
               eresult = simplifyNonDisjoint(newargs.first(), newargs.toList().get(1), currentEnv, true);
               result = eresult = treeutils.makeNotSimp(eresult, eresult);
               } catch (Exception e) {
                   e.printStackTrace(System.out);
               }
               //System.out.println("SIMPLIFIED-DISJOINT " + eresult);
               break;
           }

			case keyID:
				// Should never get here
				throw new JmlNotImplementedException(that, that.kind.keyword());
			}
		else {
			switch (that.token) {

			case SUBTYPE_OF:
			case SUBTYPE_OF_EQ:
			case JSUBTYPE_OF:
			case JSUBTYPE_OF_EQ: {
				ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
				for (JCExpression arg : that.args) {
					JCExpression ex = convertExpr(arg);
					newargs.add(ex);
				}
				result = eresult = M.at(that.pos).JmlMethodInvocation(that.token, newargs.toList());
				eresult.type = syms.booleanType;
				break;
			}

			// case BSMAX :
			// case BSREACH :
			// case BSSPACE :
			// case BSWORKINGSPACE :
			// case BSDURATION :
			// case BSISINITIALIZED :
			// case BSNOWARN:
			// case BSNOWARNOP:
			// case BSWARN:
			// case BSWARNOP:
			// case BSNOTASSIGNED:
			// case BSONLYASSIGNED:
			// case BSONLYCAPTURED:
			// FIXME - not implemented
			// throw new JmlNotImplementedException(that,that.kind.name());

			default:
				Log.instance(context).error("esc.internal.error",
						"Unknown token in JmlAssertionAdder: " + that.token.internedName());
				throw new JmlNotImplementedException(that, that.token.internedName());
			}
		}
		result = eresult;
	}


    private JCExpression wrapTranslatedNonnullelements(JCExpression arg, JCExpression convertedArg) {
        if (rac) {
        	convertedArg = methodCallUtilsExpression(arg, "nonnullElementCheck", convertedArg);
        } else {

        	if (false) {
        		// We leave this as \nonnullelements because the SMTTranslator
        		// translates this into an appropriate quantified expression directly
        		convertedArg = treeutils.makeAnd(arg.pos, treeutils.makeNeqObject(arg.pos, convertedArg, treeutils.nullLit),
        				treeutils.makeJmlMethodInvocation(arg, nonnullelementsKind, arg.type, convertedArg));
        	} else {
        		// Having the SMT solver implement a definition for \nonnullelementes causes it
        		// at least Z3 to timeout. So we insert the definition directly.
        		int p = arg.pos;
        		// replace \nonnullelements(arg) with (\let temp0 = arg; temp0 != null &&
        		// (\forall int temp; 0 <= temp && temp < temp0.length; temp0[temp] != null);
        		Name nm0 = names.fromString("__JMLtemp" + nextUnique());
        		JCExpression id0;
        		if (splitExpressions) {
        			JCVariableDecl vd0 = treeutils.makeVariableDecl(nm0, arg.type, convertedArg, p);
        			addStat(vd0);
        			id0 = treeutils.makeIdent(p, vd0.sym);
        		} else {
        			// FIXME - this is probably wrong - no conversion of arg
        			JCVariableDecl vd0 = treeutils.makeVariableDecl(nm0, arg.type, convertedArg, p);
        			id0 = treeutils.makeIdent(p, vd0.sym);
        		}

        		// FIXME _ for now don't use a let: there are problems translating it
        		// id0 = arg;

        		Name nm = names.fromString("__JMLtemp" + nextUnique());
        		JCVariableDecl vd = treeutils.makeVariableDecl(nm, syms.intType, null, p);
        		JCExpression z = treeutils.makeIntLiteral(p, 0);
        		JCExpression id1 = treeutils.makeIdent(p, vd.sym);
        		JCExpression id2 = treeutils.makeIdent(p, vd.sym);
        		JCExpression al = treeutils.makeArrayLength(p, id0);
        		JCExpression a = treeutils.makeBinary(p, JCTree.Tag.LE, treeutils.intleSymbol, z, id1);
        		JCExpression b = treeutils.makeBinary(p, JCTree.Tag.LT, treeutils.intltSymbol, id2, al);
        		JCExpression element = treeutils.makeArrayElement(p, id0,
        				treeutils.makeIdent(p, vd.sym));
        		JCExpression nnull = treeutils.makeNotNull(p, element);
        		JCExpression ex = M.JmlQuantifiedExpr(qforallKind, List.<JCVariableDecl>of(vd),
        				treeutils.makeAnd(p, a, b), nnull);
        		ex.pos = p;
        		ex.type = syms.booleanType;
        		ex = treeutils.makeAnd(p, treeutils.makeNotNull(p, copy(convertedArg)), convertExpr(ex));
//                                JCExpression let = M.LetExpr(vd0, ex);
//                                let.pos = p;
//                                let.type  = ex.type;
//                                ex = let;
        		convertedArg = ex;
        	}
        }
        return convertedArg;
    }
	
	public Name normalizeLabel(JCExpression arg, Name defaultLabel, DiagnosticPosition altpos) {
		Name label;
		if (arg != null) {
			label = ((JCIdent)arg).name;
		} else {
			label = defaultLabel;
		}
		if (label == attr.oldLabel) label = currentOldLabel;
		if (labelPropertiesStore.get(label) == null) {
			String s = label.toString();
			if (Arrays.stream(attr.predefinedLabels).anyMatch(ss->ss.equals(s))) {
				label = names.fromString("\\"+s);
			} else {
				// This problem should have been found in JmlAttr
				utils.error(arg!=null?arg:altpos, "jml.message", "Label " + label + " is not in scope here");
				result = eresult = treeutils.trueLit;
				return null;
			}
			if (label == attr.oldLabel) label = currentOldLabel;
		}
		if (label == attr.hereLabel) label = null;
		return label;
	}

	JCExpression makeFreshExpression(DiagnosticPosition pos, JCExpression trarg, /* @ nullable */ Name label) {
//        int ac;
//        LabelProperties lp = null;
//        if (trarg.type.tsym.isEnum()) {
//            // Enums are not fresh
//            // FIXME - what about enums classes declared as statement declarations.
//            return treeutils.falseLit;
//        }
//        if (label == null) ac = allocCounter;
//        else {
//            lp = labelPropertiesStore.get(label);
//            if (lp != null) {
//                ac = lp.allocCounter;
//            } else if (label.toString().isEmpty()) {
//                // ERROR _ FIXME - forgot to insert a LabelProperties for Pre
//                ac = 0;
//            } else if (label.toString().equals("LoopBodyBegin")) {
//                // Happens when a fresh expression referencing this label is in a loop_invariant
//                // The checking of the loop invariant before the loop begins occurs before the label
//                ac = allocCounter;
//            } else {
//                // ERROR - FIXME
//                ac = 0;
//            }
//        }
//        int p = pos.getPreferredPosition();
		JCExpression arg = trarg;
//        if (localVariables.isEmpty()) arg = newTemp(arg); // We make a temp variable so that the (converted) argument is not captured by the \old, except in a quantified expression
//        // FIXME _ I don't think this works properly if no temp is allocated
//        
//        // obj.isAlloc && !\old(obj.isalloc,label);
//        JCFieldAccess fa = isAllocated(pos,arg);
//        JCExpression n = makeOld(p,fa,treeutils.makeIdent(p,label,null));
//        JCExpression prev = treeutils.makeNot(p, n);
//        fa = isAllocated(pos,convertCopy(arg));
//        JCExpression ee = treeutils.makeAnd(p, prev, fa);
//        JCExpression e = treeutils.makeNeqObject(p, arg, treeutils.nullLit);
//        ee = e; //treeutils.makeAnd(that.pos, e, ee);
//        
//        JCExpression exprCopy = convertCopy(arg);
////        if (assumingPostConditions) {
////            // allocCounter is already bumped up earlier when it was declared that the result was allocated
////            e = allocCounterGT(pos, exprCopy, allocCounter-1);
////        } else {
//            // FIXME - explain why this is different than the above - this would be the postcondition for the method
//            e = allocCounterGT(pos, exprCopy, ac);
////        }
		Name current = currentEnv.stateLabel == null ? hereLabelName : currentEnv.stateLabel;
		return treeutils.makeAnd(pos, makeAllocExpression(pos, arg, current),
				treeutils.makeNot(pos, makeAllocExpression(pos, arg, label)));
	}

	JCExpression makeAllocExpression(DiagnosticPosition pos, JCExpression trarg, /* @ nullable */ Name label) {
		int ac;
		LabelProperties lp = null;
		if (trarg.type.tsym.isEnum()) {
			// Enums are always allocated
			// FIXME - what about enums classes declared as statement declarations.
			return treeutils.trueLit;
		}
		if (label == null || label == hereLabelName)
			ac = allocCounter; // CUrrent allocation state
		else {
			lp = labelPropertiesStore.get(label);
			if (lp != null) {
				ac = lp.allocCounter;
			} else if (label == names.empty) {
				ac = 0;
				utils.error(trarg,  "jml.internal", "Obsolete empty label string");
			} else if (label.toString().equals("LoopBodyBegin")) {
				// Happens when a fresh expression referencing this label is in a loop_invariant
				// The checking of the loop invariant before the loop begins occurs before the
				// label
				ac = allocCounter;
			} else {
				utils.error(trarg,  "jml.internal", "No label properties structure found for label " + label);
				Utils.dumpStack();
				ac = 0;
			}
		}
		int p = pos.getPreferredPosition();
		JCExpression arg = trarg;
//        if (localVariables.isEmpty()) arg = newTemp(arg); // We make a temp variable so that the (converted) argument is not captured by the \old, except in a quantified expression
		// FIXME _ I don't think this works properly if no temp is allocated
//        JCFieldAccess fa = isAllocated(pos,arg);
//        JCExpression ee = makeOld(p,fa,treeutils.makeIdent(p,label,null));
//        JCExpression e = treeutils.makeNeqObject(p, arg, treeutils.nullLit);
//        ee = e; //treeutils.makeAnd(that.pos, e, ee);

//        JCExpression exprCopy = convertCopy(arg);
//        if (assumingPostConditions) {
//            // allocCounter is already bumped up earlier when it was declared that the result was allocated
//            e = allocCounterGT(pos, exprCopy, allocCounter-1);
//        } else {
		// FIXME - explain why this is different than the above - this would be the
		// postcondition for the method
		JCExpression e = allocCounterLE(pos, arg, ac);
//        }
		return treeutils.makeAnd(p, treeutils.makeNotNull(p, arg), e);
	}

	// Get the conjunction of invariants of the type t and all its supertypes, with receiver obj. If obj == null, only static invaraints are conjoined.
	// If visibility is considered, invariants are included if visible from type baseType.
	/* @nullable */ public JCExpression getInvariantAll(DiagnosticPosition pos, Type baseType, JCExpression obj, boolean considerVisibility) {
		JCExpression res = null;
		for (Type ty : parents(baseType, true)) {
			JCExpression e = getInvariant(pos, baseType, ty, obj, considerVisibility);
			res = e == null ? res : res == null ? e : treeutils.makeAnd(pos, res, e);
		}
		return res;
	}

	// Get the conjunction of invariants of the type t, with receiver obj. If obj == null, only static invaraints are conjoined.
	// If visibility is considered, invariants are included if visible from type baseType.
	/* @nullable */ public JCExpression getInvariant(/* @non_null */ DiagnosticPosition pos, /* @non_null */ Type base,
			/* @non_null */ Type t, /* @nullable */ JCExpression obj, boolean considerVisibility) {
		if (!(t.tsym instanceof ClassSymbol))
			return null;
		TypeSpecs tspecs = specs.getAttrSpecs((ClassSymbol) t.tsym);
		JCExpression saved = currentEnv.currentReceiver;
		currentEnv.currentReceiver = convertJML(obj);
		JCExpression result = null;
		try {
			for (JmlTypeClause clause : tspecs.clauses) {
				if (clause.clauseType != invariantClause)
					continue;
				if (considerVisibility && !utils.jmlvisible(base.tsym, t.tsym, clause.modifiers.flags))
					continue;
				if (obj == null && !hasStatic(clause.modifiers))
					continue;
				JavaFileObject prevSource = log.useSource(clause.source);
				try {
					JCExpression e = convertJML(((JmlTypeClauseExpr) clause).expression);
					result = result == null ? e : treeutils.makeAnd(pos, result, e);
				} finally {
					log.useSource(prevSource);
				}
			}
		} finally {
			currentEnv.currentReceiver = saved;
		}
		return result;
	}

	protected JCTry makeRACTry(JCBlock bl, String name, JCExpression arg) {
		pushBlock();
		JCBlock cbl = popBlock(arg);
		JCVariableDecl ex = treeutils.makeVarDef(syms.exceptionType, names.fromString(name), methodDecl.sym, arg.pos);
		DiagnosticPosition pos = arg;
		boolean quiet = utils.jmlverbose == 0;
		JCCatch catcher1;
		JCVariableDecl vd = treeutils.makeVarDef(utils.createClassSymbol("java.lang.NoSuchMethodError").type,
				names.fromString("noSuchMethodError"), methodDecl.sym, arg.pos);
		if (quiet) {
			catcher1 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>nil()));
		} else {
			JCExpression id = treeutils.makeIdent(pos.getPreferredPosition(), vd.sym);
			JCExpression location = treeutils.makeStringLiteral(pos.getPreferredPosition(),
					utils.locationString(pos, log.currentSourceFile()));
			location = treeutils.makeNullLiteral(pos.getPreferredPosition()); // FIXME - really need to propagate the
																				// location of the call
			JCMethodInvocation m = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "reportNoSuchMethod", id,
					location);
			catcher1 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>of(M.at(pos.getPreferredPosition()).Exec(m))));
		}
		JCCatch catcher2;
		vd = treeutils.makeVarDef(utils.createClassSymbol("java.lang.NoSuchFieldError").type,
				names.fromString("noSuchFieldError"), methodDecl.sym, arg.pos);
		if (quiet) {
			catcher2 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>nil()));
		} else {
			JCExpression id = treeutils.makeIdent(pos.getPreferredPosition(), vd.sym);
			JCExpression location = treeutils.makeStringLiteral(pos.getPreferredPosition(),
					utils.locationString(pos, log.currentSourceFile()));
			if (Utils.testingMode)
				location = treeutils.makeNullLiteral(pos.getPreferredPosition());
			JCMethodInvocation m = treeutils.makeUtilsMethodCall(pos.getPreferredPosition(), "reportNoSuchField", id,
					location);
			catcher2 = M.at(pos).Catch(vd, M.Block(0L, List.<JCStatement>of(M.at(pos.getPreferredPosition()).Exec(m))));
		}
		JCTry st = M.at(arg.pos).Try(bl, List.<JCCatch>of(M.at(arg.pos).Catch(ex, cbl), catcher1, catcher2), null);
		// FIXME - don't add try if isOnlyComment(bl) is true
		return st;
	}

	@Override
	public void visitJmlMethodSpecs(JmlMethodSpecs that) {
		error(that, "Unexpected call of JmlAssertionAdder.visitJmlMethodSpecs: " + that.getClass());
		return;
//
//		List<JmlSpecificationCase> cases = convertCopy(that.cases);
//		JmlMethodSpecs ms = M.at(that).JmlMethodSpecs(cases);
//		ms.setType(that.type);
//		ms.decl = that.decl; // FIXME - copy - needs remapping
//		ms.deSugared = that.deSugared; // FIXME - copy
//		ms.forExampleCases = that.forExampleCases; // FIXME - copy
//		ms.impliesThatCases = that.impliesThatCases; // FIXME - copy
//		ms.feasible = that.feasible; // FIXME - copy
//		result = ms;
	}

	// OK
	@Override
	public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
		result = M.at(that).JmlModelProgramStatement(convert(that.item)).setType(that.type);
	}

	// OK
	@Override
	public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
		result = eresult = M.at(that).JmlPrimitiveTypeTree(that.token, that.typeName).setType(that.type);
	}

	/**
	 * Maps symbols declared in quantified and let statements to new symbols -
	 * needed because quantified symbols can be used in multiple places
	 */
	protected java.util.Map<Symbol, Symbol> localVariables = new java.util.HashMap<Symbol, Symbol>();

	protected ListBuffer<JCStatement> nonignoredStatements = null;

//    @Override
//    public void visitJmlLambda(JmlLambda that) {
//        visitLambda(that);
//    }
	// OK
	@Override
	public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {

		for (JCVariableDecl d : that.decls) {
			localVariables.put(d.sym, d.sym);
		}
		result = eresult = treeutils.makeZeroEquivalentLit(that.pos, that.type);
		// FIXME - should really turn splitExpressions off for these expressions.
		try {
		    var key = that.kind.keyword();
			if (!rac) {
				ListBuffer<JCStatement> prev = nonignoredStatements;
				try {
					if (translatingJML) {
						nonignoredStatements = new ListBuffer<JCStatement>();
						pushBlock(); // A // FIXME - we have not implemented guarding conditions for expressions
										// inside quantifiers
					}
					List<JCVariableDecl> dd = copy(that.decls);
					JCExpression range = convertNoSplit(that.range);
					if (range != null)
						range = addImplicitConversion(range, syms.booleanType, range);
					JCExpression value = convertNoSplit(that.value);
					Type targetType = that.kind == qforallKind ? syms.booleanType
							: that.kind == qexistsKind ? syms.booleanType
									: that.kind == qnumofKind ? syms.booleanType : that.value.type; // FIXME - not sure
																									// about this
																									// default
					value = addImplicitConversion(value, targetType, value);
					JmlQuantifiedExpr q = M.at(that).JmlQuantifiedExpr(that.kind, dd, // convertCopy(that.decls),
							range, value);
					{
						boolean saved = splitExpressions;
						try {
							splitExpressions = false;
							q.triggers = convertExprList(that.triggers);
						} finally {
							splitExpressions = saved;
						}
					}
					q.setType(that.type);
					result = eresult = q;
				} finally {
					if (translatingJML) {
						popBlock(); // A
						if (prev == null) {
							currentStatements.addAll(nonignoredStatements);
							nonignoredStatements = prev;
						} else {
							prev.addAll(nonignoredStatements);
							nonignoredStatements = prev;
						}
					}
				}
				if (splitExpressions) {
					// Normally the temporaries used to track subexpression values are introdcued
					// as an initialized expression, which becomes a define-fun in SMT, i.e.
					result = eresult = newTemp(eresult);
					// However, SMT ( at least Z3) does a direct substitution, so that when a
					// get-value
					// query is made with the id, the expression is queried instead, which provokes
					// an error
					// if the expression is a quantified expression. Hence we declare a variable and
					// then
					// add an assumption about its value.
//                    JCIdent id = newTemp(that,syms.booleanType);
//                    addAssumeEqual(that, Label.IMPLICIT_ASSUME, id, eresult);
//                    result = eresult = id;
				}
			} else {
				java.util.List<Bound> bounds = new java.util.LinkedList<Bound>();
				JCExpression innerexpr = determineRacBounds(that.decls, that.range != null ? that.range : that.value, bounds);
				if (innerexpr == null && rac) {
					utils.note(that, "rac.not.implemented.quantified");
					return;
				}
				// The accumulator variable
				Type t = that.type;
                if (utils.rac && that.type instanceof JmlType  && key != qchooseID)
					t = syms.longType; // FIXME - stopgap until RAC is working properly on quantifiers
				Name n = names.fromString("_JML$val$$" + nextUnique());
				// methodDecl is null if we are in a type specification clause (e.g. invariant)
				var ownersym = methodDecl!= null  ? methodDecl.sym : classDecl.sym;
				JCVariableDecl decl = treeutils.makeVarDef(t, n, ownersym, that.pos);
				decl.init = treeutils.makeZeroEquivalentLit(that.pos, types.unboxedTypeOrType(t));
				if (utils.rac && key == qchooseID) decl.init = treeutils.makeZeroEquivalentLit(that.pos, t);
				addStat(decl);
				JCBlock failureBlock = null;
				
				// Label for the loop, so we can break out of it
				Name label = names.fromString(Strings.genPrefix + "while_" + nextUnique());
				ListBuffer<JCStatement> check = pushBlock(); // B // enclosing block, except for declaration of
																// accumulator
				try {
					for (Bound bound : bounds) {

						JCVariableDecl indexdef = treeutils.makeVarDef(bound.decl.type, bound.decl.name, ownersym,
								bound.decl.pos);
						localVariables.put(bound.decl.sym, indexdef.sym);
						JCIdent id = treeutils.makeIdent(that.pos, decl.sym); // accumulator
                        JCIdent idd = treeutils.makeIdent(that.pos, decl.sym); // another id for the accumulator
						JCStatement st;
						JCBreak brStat = null;
						JCBlock bl;
						ListBuffer<JCStatement> checkA = pushBlock(); // C // Start of loop block
						try {
							JCExpression guard = convertNoSplit(innerexpr);
							ListBuffer<JCStatement> checkB = pushBlock(); // Start of guarded block
							try {
								JCExpression val = convertNoSplit(that.value);
								switch (key) {
								case qforallID:
									// if (guard) { val = convert(value); if (!val) { accumulator = false; break
									// <label>; }}
									decl.init = treeutils.trueLit;

									var check8 = pushBlock(); // E
									addStat(treeutils.makeAssignStat(that.pos, id, treeutils.falseLit));
									addStat(brStat = M.Break(label));
									bl = popBlock(that, check8); // E
									st = M.If(treeutils.makeNot(that.pos, val), bl, null);
									break;

                                case qexistsID:
                                    // if (guard) { val = convert(value); if (!val) { accumulator = true; break
                                    // <label>; }}

                                    var check9 = pushBlock();
                                    addStat(treeutils.makeAssignStat(that.pos, id, treeutils.trueLit));
                                    addStat(brStat = M.Break(label));
                                    bl = popBlock(that, check9);
                                    st = M.If(val, bl, null);
                                    break;

                                case qchooseID:
                                    // if (guard) { val = convert(value); if (!val) { accumulator = true; break <label>; }}
                                    // if the range was empty, the value was used as the range

                                    JCIdent index = treeutils.makeIdent(that.decls.head.pos, indexdef.sym);
                                    var check9a = pushBlock();
                                    addStat(treeutils.makeAssignStat(that.pos, idd, index));
                                    addStat(st = treeutils.makeAssignStat(that.pos, 
                                            treeutils.makeIdent(that.pos, that.founddef.sym), treeutils.trueLit));
                                    addStat(brStat = M.Break(label));
                                    bl = popBlock(that, check9a);
                                    if (that.range != null) {
                                        st = M.If(val, bl, null);
                                    } else {
                                        st = bl;
                                    }
                                    var checkF = pushBlock();
                                    addAssert(that, Label.CHOOSE, 
                                            M.at(that.pos).Ident(that.founddef.sym));
                                    failureBlock = popBlock(that,checkF);
                                    break;

								case qsumID:
									// if (guard) { val = convert(value); accumulator = accumulator + val; }
									st = treeutils.makeAssignStat(that.pos, id,
											treeutils.makeBinary(that.pos, JCTree.Tag.PLUS, idd, val));
									break;

								case qproductID:
									// if (guard) { val = convert(value); accumulator = accumulator * val; }
									switch (that.type.getTag()) {
									case INT:
									case SHORT:
									case BYTE:
										decl.init = treeutils.makeIntLiteral(that.pos, Integer.valueOf(1));
										break;
									case LONG:
										decl.init = treeutils.makeLit(that.pos, that.type, Long.valueOf(1));
										break;
									case DOUBLE:
										decl.init = treeutils.makeLit(that.pos, that.type, Double.valueOf(1));
										break;
									case FLOAT:
										decl.init = treeutils.makeLit(that.pos, that.type, Float.valueOf(1));
										break;
									// Skipping CHAR - multiplying chars does not make sense.
									default:
										utils.note(that, "rac.not.implemented.quantified");
										throw new JmlNotImplementedException(that,
												"RAC not implemented for this type: " + that.type);

									}
									st = treeutils.makeAssignStat(that.pos, id,
											treeutils.makeBinary(that.pos, JCTree.Tag.MUL, idd, val));
									break;

								case qnumofID:
									// if (guard) { val = convert(value); if (val) accumulator = accumulator + 1;
									st = treeutils.makeAssignStat(that.pos, id, treeutils.makeBinary(that.pos,
											JCTree.Tag.PLUS, idd,
											idd.type.getTag() == TypeTag.LONG ? treeutils.longone : treeutils.one)); // FIXME
																														// -
																														// what
																														// about
																														// bigint?
									st = M.at(that).If(val, st, null);
									break;

								case qmaxID:
								case qminID:
									// if (guard) { val = convert(value); if ( accumulator </> val) accumulator =
									// val;
									boolean isMax = that.kind != qminKind;
									switch (that.type.getTag()) {
									case INT:
										decl.init = treeutils.makeIntLiteral(that.pos,
												isMax ? Integer.MIN_VALUE : Integer.MAX_VALUE);
										break;
									case LONG:
										decl.init = treeutils.makeLit(that.pos, that.type,
												(isMax ? Long.MIN_VALUE : Long.MAX_VALUE));
										break;
									case SHORT:
										decl.init = treeutils.makeLit(that.pos, that.type,
												(int) (isMax ? Short.MIN_VALUE : Short.MAX_VALUE));
										break;
									case BYTE:
										decl.init = treeutils.makeLit(that.pos, that.type,
												(int) (isMax ? Byte.MIN_VALUE : Byte.MAX_VALUE));
										break;
									case CHAR:
										decl.init = treeutils.makeLit(that.pos, syms.intType,
												(int) (isMax ? Character.MIN_VALUE : Character.MAX_VALUE));
										break;
									case DOUBLE:
										decl.init = treeutils.makeLit(that.pos, that.type,
												(isMax ? Double.MIN_VALUE : Double.MAX_VALUE));
										break;
									case FLOAT:
										decl.init = treeutils.makeLit(that.pos, that.type,
												(isMax ? Float.MIN_VALUE : Float.MAX_VALUE));
										break;
									default:
										utils.note(that, "rac.not.implemented.quantified");
										throw new JmlNotImplementedException(that,
												"RAC not implemented for this type: " + that.type);

									}
									// FIXME - what about \bigint? should \min and \max be undefined if the range is
									// empty?
									JCExpression tmp = !splitExpressions ? newTemp(val) : val; // Make an ID if not
																								// already
									st = treeutils.makeAssignStat(that.pos, id, tmp);
									st = M.at(that.pos)
											.If(treeutils.makeBinary(that.pos,
													that.kind != qminKind ? JCTree.Tag.LT : JCTree.Tag.GT, idd, tmp),
													st, null);
									break;

								default:
									// popBlock(that); // ignore
									// popBlock(that); // ignore
									String msg = "Unknown quantified expression operation: " + that.kind.keyword();
									utils.error(that, "jml.internal", msg);
									throw new JmlNotImplementedException(that, msg);
								}
								addStat(st);
							} finally {
								bl = popBlock(that, checkB); // D // end of guarded block
							}
							st = M.If(guard, bl, null);
							addStat(st);

						} finally {
							if (bound.decl.type.getTag() == TypeTag.BOOLEAN) {
								// index = false; do { <innercomputation>; index = !index } while (index);
								st = treeutils.makeAssignStat(that.pos, treeutils.makeIdent(that.pos, indexdef.sym),
										treeutils.makeNot(that.pos, treeutils.makeIdent(that.pos, indexdef.sym)));
								addStat(st);

								bl = popBlock(that, checkA); // C // loop block

								indexdef.init = treeutils.falseLit;
								JCExpression comp = treeutils.makeIdent(that.pos, indexdef.sym);
								addStat(indexdef);
								st = M.at(that.pos).DoLoop(bl, comp);
								if (brStat != null)
									brStat.target = st;
								st = M.at(that.pos).JmlLabeledStatement(label, null, st);
								addStat(st);

							} else if (bound.iterable != null) {
								// for (T o: container) { <innercomputation>; }

								bl = popBlock(that, checkA); // C // loop block

								st = M.at(that.pos).ForeachLoop(indexdef, convertExpr(bound.iterable), bl);
								if (brStat != null)
									brStat.target = st;
								st = M.at(that.pos).JmlLabeledStatement(label, null, st);
								addStat(st);

							} else {
								// T index = lo; while (index </<= hi) { <inner computation>; index = index + 1
								// }
								JCExpression init = convertExpr(treeutils.makeBinary(that.pos, JCTree.Tag.PLUS,
										treeutils.makeIdent(that.pos, indexdef.sym), treeutils.one));
								st = treeutils.makeAssignStat(that.pos, treeutils.makeIdent(that.pos, indexdef.sym),
										castType(indexdef.type, init));

								// FIXME - one above might have to be long or bigint
								addStat(st);

								bl = popBlock(that, checkA); // C // loop block

								indexdef.init = castType(indexdef.type, convertExpr(copy(bound.lo)));
								addStat(indexdef);
								if (that.founddef != null) {
								    addStat(that.founddef);
								}

								JCExpression hi = bound.hi;
								JCExpression comp;
//                                if (jmltypes.isJmlTypeOrRepType(hi.type) && rac) {
//                                    JCExpression lhs = addImplicitConversion(that.pos(),hi.type,treeutils.makeIdent(that.pos, indexdef.sym));
//                                    JCTree.Tag op = bound.hi_equal ? JCTree.Tag.LE : JCTree.Tag.LT;
//                                    String opname = treeutils.opname(lhs.type,op);
//                                    if (opname == null) {
//                                        log.error("jml.internal","No jmltype operator implemented for type " + hi.type + " and tag " + op);
//                                    }
//                                    comp = treeutils.makeUtilsMethodCall(that.pos, opname, lhs, hi);
//                                    
//                                } else {
								Type maxtype = treeutils.maxType(indexdef.type, hi.type);
								JCTree.Tag op = bound.hi_equal ? JCTree.Tag.LE : JCTree.Tag.LT;

								comp = treeutils.makeBinary(that.pos, op, treeutils.makeIdent(that.pos, indexdef.sym),
										hi);
//                                }
								boolean saved1 = splitExpressions;
								splitExpressions = false;
								try {
									comp = convertJML(comp);
								} finally {
									splitExpressions = saved1;
								}
								st = M.at(that.pos).WhileLoop(comp, bl);
								if (brStat != null)
									brStat.target = st;
								st = M.at(that.pos).JmlLabeledStatement(label, null, st);
								addStat(st);
								if (failureBlock != null) {
								    addStat(failureBlock);
								}
							}
						}

					}
				} finally {
					addStat(popBlock(that, check)); // B // pops enclosing block
				}
				result = eresult = treeutils.makeIdent(that.pos, decl.sym);
			}
		} finally {
			for (JCVariableDecl d : that.decls) {
				localVariables.remove(d.sym);
			}
		}
		return;
	}

	// FIXME - duplicate with what is in JmlAttr?

	protected static class Bound {
		public JCExpression iterable;
		public JCVariableDecl decl;
		public JCExpression lo;
		public JCExpression hi;
		boolean lo_equal;
		boolean hi_equal;
		JCVariableDecl indexdef;
		/* @nullable */ JCVariableDecl lodef;
		/* @nullable */ JCVariableDecl hidef;
		public String toString() {
		    return "Bound[" + lo + (lo_equal?" <=":" <") + (hi_equal?" <= ":" < ") + hi + "]";
		}
	}
	
	protected static record Comp(JCExpression lo, JCTree.Tag tag, JCExpression hi) {}

	/**
	 * If appropriate bounds can be determined for all defined variables, the method
	 * returns the remaining expression and fills in the Bound list (first element
	 * is innermost loop); if appropriate bounds cannot be determined, the method
	 * returns null.
	 */
	public JCExpression determineRacBounds(List<JCVariableDecl> decls, JCExpression range,
			java.util.List<Bound> bounds) {
		// Some current assumptions
		if (decls.length() != 1)
			return null; // FIXME - does only one declaration!!!!!!
		if (decls.head.type.getTag() == TypeTag.DOUBLE)
			return null;
		if (decls.head.type.getTag() == TypeTag.FLOAT)
			return null;

		if (decls.head.type.getTag() == TypeTag.BOOLEAN) {
			Bound b = new Bound();
			b.decl = decls.head;
			b.lo = null;
			b.hi = null;
			bounds.add(0, b);
			return range;
		}
		Type declType = decls.head.type;

		xx: {
			JCExpression check = range instanceof JCBinary ? ((JCBinary) range).lhs : range;
			if (!(check instanceof JCMethodInvocation))
				break xx;
			JCMethodInvocation mi = (JCMethodInvocation) check;
			if (!(mi.meth instanceof JCFieldAccess))
				break xx;
			JCFieldAccess fa = (JCFieldAccess) mi.meth;
			if (!fa.name.toString().equals("contains") && !fa.name.toString().equals("has"))
				break xx;
			if (!types.isAssignable(types.erasure(fa.selected.type), syms.iterableType))
				break xx;
			if (rac && declType == jmltypes.BIGINT)
				return null; // FIXME - IMPLEMENT THESE SOMEDAY
			if (rac && declType == jmltypes.REAL)
				return null;
			Bound b = new Bound();
			b.decl = decls.head;
			b.iterable = fa.selected;
			b.lo = null;
			b.hi = null;
			bounds.add(0, b);
			return check == range ? check : // FIXME - could be set to true
					((JCBinary) range).rhs;
		}

		if (!jmltypes.unboxedTypeOrType(decls.head.type).isNumeric())
			return null;

		try {
		    java.util.List<Comp> comps = new LinkedList<>();
		    collectComparisons(comps, range, false);
		    sortComparisons(decls, comps, bounds);
		} catch (Exception e) {
			return null;
		}
		return range;
	}
	
	public void collectComparisons(java.util.List<Comp> comps, JCExpression expr, boolean negated) {
	    if (expr instanceof JCBinary bin) {
	        switch (bin.getTag()) {
            case AND:
            case BITAND:
                if (negated) break;
                collectComparisons(comps, bin.lhs, negated);
                collectComparisons(comps, bin.rhs, negated);
                break;
            case OR:
            case BITOR:
                if (!negated) break;
                collectComparisons(comps, bin.lhs, negated);
                collectComparisons(comps, bin.rhs, negated);
                break;
            case GE:
                if (negated) comps.add(new Comp(bin.lhs, JCTree.Tag.LT, bin.rhs));
                else comps.add(new Comp(bin.rhs, JCTree.Tag.LE, bin.lhs));
                break;
            case GT:
                if (negated) comps.add(new Comp(bin.lhs, JCTree.Tag.LE, bin.rhs));
                else comps.add(new Comp(bin.rhs, JCTree.Tag.LT, bin.lhs));
                break;
            case LT:
                if (negated) comps.add(new Comp(bin.rhs, JCTree.Tag.LE, bin.lhs));
                else comps.add(new Comp(bin.lhs, JCTree.Tag.LT, bin.rhs));
                break;
            case LE:
                if (negated) comps.add(new Comp(bin.rhs, JCTree.Tag.LT, bin.lhs));
                else comps.add(new Comp(bin.lhs, JCTree.Tag.LE, bin.rhs));
                break;
            case EQ:
                if (negated) break;
                comps.add(new Comp(bin.lhs, JCTree.Tag.LE, bin.rhs));
                comps.add(new Comp(bin.rhs, JCTree.Tag.LE, bin.lhs));
                break;
            case NE:
                if (!negated) break;
                comps.add(new Comp(bin.lhs, JCTree.Tag.LE, bin.rhs));
                comps.add(new Comp(bin.rhs, JCTree.Tag.LE, bin.lhs));
                break;
	        default:    
	        }
        } else if (expr instanceof JmlChained ch) {
            if (!negated) {
                for (var c: ch.conjuncts) collectComparisons(comps, c, negated);
            }
	    } else if (expr instanceof JCUnary unary) {
	        if (unary.getTag() == JCTree.Tag.NOT) {
                collectComparisons(comps, unary.arg, !negated);
	        }
	    } else if (expr instanceof JmlBinary jb) {
	        if (negated && jb.op.keyword() == impliesID) {
                collectComparisons(comps, jb.lhs, false);
                collectComparisons(comps, jb.rhs, true);
	        }
	    } else if (expr instanceof JCParens p) {
	        collectComparisons(comps, p.expr, negated);
	    }
	    return;
	}

    // FIXME - there is no check that there is no premature use of declara
    public void sortComparisons(List<JCVariableDecl> decls, java.util.List<Comp> comps, java.util.List<Bound> bounds) {
        //System.out.println("COMPS"); comps.forEach(c->{System.out.println(c);});
        for (var decl: decls) {
            JCExpression lo = null, hi = null;
            JCTree.Tag lotag = JCTree.Tag.EQ, hitag = JCTree.Tag.EQ; // Arbitrary value to satisfy initialization
            for (var comp: comps) {
                if (comp.hi instanceof JCIdent id && id.sym == decl.sym) {
                    lo = comp.lo;
                    lotag = comp.tag;
                    break;
                }
            }
            for (var comp: comps) {
                if (comp.lo instanceof JCIdent id && id.sym == decl.sym) {
                    hi = comp.hi;
                    hitag = comp.tag;
                    break;
                }
            }
            if (lo == null || hi == null) throw new RuntimeException(); // No usable bounds
            Bound b = new Bound();
            b.decl = decl;
            b.lo = lo;
            b.lo_equal = lotag == JCTree.Tag.LE;
            b.hi = hi;
            b.hi_equal = hitag == JCTree.Tag.LE;
            bounds.add(b);
        }
        //System.out.println("BOUNDS"); bounds.forEach(b->{System.out.println(b);});
	}


	public JCExpression castType(Type target, JCExpression arg) {
		if (jmltypes.isSameType(arg.type, target))
			return arg;
		if (!rac)
			return treeutils.makeTypeCast(arg, target, arg);
		boolean isPrim = arg.type.isPrimitive() && !(rac && jmltypes.isJmlType(arg.type));
		boolean isNewPrim = target.isPrimitive() && !(rac && jmltypes.isJmlType(target));
		if (isPrim && target.isPrimitive()) {
			return treeutils.makeTypeCast(arg, target, arg);
		} else if (jmltypes.isJmlTypeOrRep(arg.type, jmltypes.BIGINT)) {
			if (target == jmltypes.BIGINT)
				return arg;
			else if (isNewPrim) {
				return treeutils.makeUtilsMethodCall(arg.pos, "bigint_to" + target.toString(), arg);
			} else {
				Type t = types.unboxedType(target);
				JCExpression e = treeutils.makeUtilsMethodCall(arg.pos, "bigint_to" + t.toString(), arg);
				return treeutils.makeTypeCast(arg, target, e);
			}
		} else if (jmltypes.isJmlTypeOrRep(target, jmltypes.BIGINT)) {
			if (arg.type == jmltypes.BIGINT)
				return arg;
			if (isPrim) {
				return treeutils.makeUtilsMethodCall(arg.pos, "bigint_valueof", arg);
			} else {
				log.error(arg.pos, "jml.internal",
						"No implementation to convert " + arg.type.toString() + " to " + target.toString());
				return null;

			}
		} else if (isPrim || isNewPrim) {
			return treeutils.makeTypeCast(arg, target, arg);
		} else {
			log.error(arg.pos, "jml.internal",
					"No implementation to convert " + arg.type.toString() + " to " + target.toString());
			return null;
		}
	}

	// OK
	@Override
	public void visitJmlSetComprehension(JmlSetComprehension that) {
		if (esc || infer) {
			result = eresult = M.at(that)
					.JmlSetComprehension(convert(that.newtype), convert(that.variable), convertExpr(that.predicate))
					.setType(that.type);
			return;
		}
		// FIXME - implement
		throw new JmlNotImplementedException(that, "set comprehension expression");
		// return;
	}

	@Override
	public void visitJmlRange(JmlRange that) {
		result = eresult = M.at(that.pos).JmlRange(convert(that.lo), convert(that.hi)).setType(that.type);
	}

	// OK
	@Override
	public void visitJmlSingleton(JmlSingleton that) {
		if (!translatingJML) {
			error(that, "Unexpected call of JmlAssertionAdder.visitJmlSingleton: " + that.getClass());
			return;
		}
		IJmlClauseKind k = that.kind;
		if (k == resultKind) {
			if (resultExpr != null) {
				eresult = copy(resultExpr);
				eresult.pos = that.pos;
			} else {
				// This should be caught in type checking
				error(that, "It appears that \\result is used where no return value is defined");
			}
		} else if (k == informalCommentKind) {
			eresult = treeutils.makeBooleanLiteral(that.pos, true);

		} else if (k == exceptionKind) {
			if (exceptionSym == null) {
				error(that, "It appears that \\exception is used where no exception value is defined");
			} else {
				// This should be caught in type checking
				eresult = treeutils.makeIdent(that.pos, exceptionSym);
			}

		} else if (k == indexKind || k == countKind) {
			if (!indexStack.isEmpty()) {
				// Get the index of the inner most loop
				JCVariableDecl vd = indexStack.get(0);
				JCIdent id = treeutils.makeIdent(that.pos, vd.sym);
				eresult = id;
			} else if (inlinedLoop != null) {
//                    JCIdent id = treeutils.makeIdent(that.pos,"index_???",that.type);
//                    eresult = id;
//                    inlinedLoop.countIds.add(id);
				eresult = that;
			} else {
				error(that, "jml.misplaced.count", that.kind.keyword());
			}

		} else if (k == elseKind) {
			if (elseExpression == null) {
				error(that, "jml.message", "An \\else token not permitted here");
				eresult = treeutils.falseLit;
			} else {
				eresult = treeutils.makeNot(that, elseExpression);
			}

			// FIXME - implement these
		} else if (k == valuesKind) {
			if (that.info == null) {
				log.error(that.pos, "esc.internal.error", "No loop index found for this use of " + valuesKind.keyword);
				result = null;
			} else {
				result = M.at(that.pos).Ident((VarSymbol) that.info);
			}

//            case BSLOCKSET:
//            case BSSAME:

		} else if (k == nothingKind || k == everythingKind) {
			eresult = that;
			if (fullTranslation) {
				JmlSingleton e = M.at(that).JmlSingleton(that.kind);
				e.info = that.info;
				// e.symbol = that.symbol;
				e.setType(that.type);
				eresult = e;
			}

		} else {
			Log.instance(context).error(that.pos, "jml.unknown.construct", that.kind.keyword(),
					"JmlAssertionAdder.visitJmlSingleton");
			eresult = treeutils.makeZeroEquivalentLit(that.pos, that.type); // Not sure continuation will be successful
																			// in any way
		}
		result = eresult;
	}

	@Override
	public void visitJmlSpecificationCase(JmlSpecificationCase that) {
		error(that, "Unexpected call of JmlAssertionAdder.visitJmlSpecificationCase: " + that.getClass());
		return;
//
//		JmlSpecificationCase sc = M.at(that).JmlSpecificationCase(convert(that.modifiers), that.code, that.token,
//				that.also, that.clauses, convertBlock(that.block));
//		sc.sourcefile = that.sourcefile;
//		sc.setType(that.type);
//		result = sc;
	}

	@Override
	public void visitJmlStatement(JmlStatement that) {
		result = null;
		if (that.clauseType == SetStatement.setClause) {
			boolean saved = translatingJML;
			translatingJML = true;
			condition = treeutils.trueLit;
			try {
				addTraceableComment(that); // after the check on the key
				JCStatement st = that.statement;
				st.accept(this);
			} catch (NoModelMethod e) {
				// Ignore - don't add a statement
			} catch (JmlNotImplementedException e) {
				notImplemented(that.clauseType.keyword() + " statement containing ", e);
				result = null;
			} finally {
				translatingJML = saved;
				condition = null;
			}
		} else if (that.clauseType == Refining.endClause) {
			// do nothing -- this should be part of a JmlStatementSpec
		} else {
			String msg = "Unknown token in JmlAssertionAdder.visitJmlStatement: " + that.keyword;
			error(that, msg);
		}
	}

	JmlInlinedLoop mostRecentInlinedLoop = null;
	JmlInlinedLoop inlinedLoop = null;

	@Override
	public void visitJmlInlinedLoop(JmlInlinedLoop that) {
		if (that.translatedSpecs == null) {
			boolean saved = translatingJML;
			JmlInlinedLoop savedL = inlinedLoop;
			boolean savedSplit = splitExpressions;
			translatingJML = true;
			inlinedLoop = that;
			splitExpressions = false;
			try {
				ListBuffer<JmlStatementLoop> trspecs = new ListBuffer<>();
				for (JmlStatementLoop spec : that.loopSpecs) {
					condition = treeutils.trueLit;
					pushBlock();
					spec.accept(this);
					popBlock(); // FIXME - for now ignore well definedness conditions - which means method calls
								// are not handled - needs to be repaired
					trspecs.add((JmlStatementLoop) result);
					((JmlStatementLoop) result).translated = true;
				}
				that.translatedSpecs = trspecs.toList();
			} finally {
				translatingJML = saved;
				inlinedLoop = savedL;
				splitExpressions = savedSplit;
			}
		}
		if (!that.consumed) {
			mostRecentInlinedLoop = that;
			that.consumed = true;
		}
		result = null;
	}

	protected int jmlShowUnique = 0;

	@Override
	public void visitJmlStatementShow(JmlStatementShow that) {
		result = null;
		boolean saved = translatingJML;
		boolean savedP = isPostcondition;

		if (that.clauseType == showClause) {
		    currentEnv = currentEnv.pushEnvCopy();
			currentEnv.arithmeticMode = Arithmetic.Math.instance(context)
					.defaultArithmeticMode(methodDecl != null ? methodDecl.sym : classDecl.sym, true);
			try {
				translatingJML = true;
				//isPostcondition = false;
				addTraceableComment(that);
				for (JCExpression expr : that.expressions) {
					Name n = names.fromString("JMLSHOW_" + (++jmlShowUnique));
					// Add the equivalent of \lbl for each expressions
					JmlLblExpression e = M.at(expr.getStartPosition()).JmlLblExpression(expr.getStartPosition(),
							lblanyKind, n, expr);
					e.type = expr.type;
					condition = treeutils.trueLit;
					visitJmlLblExpression(e);
					showExpressions.put(n.toString(), expr);
				}
			} catch (NoModelMethod e) {
				// Ignore - don't add a statement
			} catch (JmlNotImplementedException e) {
				notImplemented(that.clauseType.keyword() + " statement containing ", e);
				result = null;
			} finally {
				translatingJML = saved;
				isPostcondition = savedP;
				currentEnv = currentEnv.popEnv();
			}

		} else {
			String msg = "Unknown token in JmlAssertionAdder.visitJmlStatement: " + that.clauseType.keyword();
			error(that, msg);
		}
	}

	public Map<String, JCExpression> showExpressions = new HashMap<String, JCExpression>();

	// jmlrewriter? FIXME; also explain what this is
	@Override
	public void visitJmlStatementDecls(JmlStatementDecls that) {
		if (translatingJML) {
			error(that, "Unexpected call of JmlAssertionAdder.visitJmlStatementDecls while translating JML: "
					+ that.getClass());
			return;
		}
		for (JCStatement stat : that.list) {
			stat.accept(this);
		}
		// FIXME - result = ?
	}

	// OK
	@Override
	public void visitJmlStatementExpr(JmlStatementExpr that) {
		boolean pv = checkAccessEnabled; // Don't check access during JML statements
		checkAccessEnabled = false;

		boolean saved = assumingPostConditions;
		assumingPostConditions = false;
		try {
			if (that.clauseType == assertClause || that.clauseType == checkClause) {
				addTraceableComment(that);
				JCExpression e = convertJML(that.expression);
				e = addImplicitConversion(that, syms.booleanType, e);
				addFeasibilityCheck(that, currentStatements, Strings.feas_assert, Strings.beforeAssertFeasCheckDescription);
				JCExpression opt = that.optionalExpression;
				if (opt != null) {
					if (!(opt instanceof JCLiteral))
						opt = convertJML(opt);
					if (rac) {
						JCExpression o = treeutils.convertToString(opt);
						if (o != null)
							opt = o;
					}
				}
				if (that.clauseType == checkClause) { // FIXME - use addCheck?
					JCIdent id = newTemp(e, syms.booleanType);
					e = treeutils.makeOr(e, id, e);
				}
				Label label = that.label;
				if (label == null)
					label = Label.EXPLICIT_ASSERT;
				JmlStatementExpr s = addAssert(false, that, label, e, null, null, opt);
				if (that.clauseType == checkClause && !rac) {
					s.clauseType = checkClause;
				}
				result = s;

			} else if (that.clauseType == assumeClause) {

				addTraceableComment(that);
				JCExpression ee = convertJML(that.expression);
				ee = addImplicitConversion(that, syms.booleanType, ee);
				JCExpression opt = that.optionalExpression;
				if (!(opt instanceof JCLiteral)) {
					opt = convertJML(opt);
				}
				result = addAssume(that, that.label, ee, null, null, opt);
				if (!treeutils.isFalseLit(ee)) {
				    if (that.label == Label.EXPLICIT_ASSUME) {
	                    addFeasibilityCheck(that, currentStatements, Strings.feas_assume, Strings.afterAssumeFeasCheckDescription);

				    } else {
	                    addFeasibilityCheck(that, currentStatements, Strings.feas_debug, Strings.afterImplicitAssumeFeasCheckDescription);
				    }
				}

			} else if (that.clauseType == commentClause) {
			    // Do not translate, because we want to keep the string literal intact
				JCExpression expr = that.expression;
				{
					JmlStatementExpr st = M.at(that).JmlExpressionStatement(that.keyword, that.clauseType, that.label,
							expr);
					st.setType(that.type);
					st.associatedSource = that.associatedSource;
					st.associatedPos = that.associatedPos;
					st.optionalExpression = fullTranslation ? convertExpr(that.optionalExpression)
							: that.optionalExpression;
					st.source = that.source;
					result = addStat(st);
				}

			} else if (that.clauseType == StatementExprExtensions.splitClause) {

				if (currentSplit == null || rac || infer) {
					// ignore;
				} else {
					boolean doPos = true;
					if (currentSplit.isEmpty()) {
						adjustSplit(2);
					} else {
						doPos = currentSplit.charAt(0) == 'A';
						currentSplit = currentSplit.substring(1);
					}
					JCExpression cond = convertJML(that.expression);
					if (!doPos)
						cond = treeutils.makeNot(that, cond);
					addAssume(that, Label.IMPLICIT_ASSUME, cond);
				}

			} else if (that.clauseType == ReachableStatement.haltClause) {

	            addFeasibilityCheck(that, currentStatements, Strings.feas_halt, "at halt statement");
				addStat(that);
				continuation = Continuation.HALT;

			} else if (that.clauseType == ReachableStatement.unreachableClause) {

				addTraceableComment(that);
				result = addAssert(that, Label.UNREACHABLE, that.expression == null ? treeutils.falseLit
						: treeutils.makeNot(that.pos, convertJML(that.expression)));

			} else if (that.clauseType == ReachableStatement.reachableClause) {

				if (feasibilityContains(Strings.feas_reachable)) {
	                addTraceableComment(that);
				    addFeasibilityCheck(that, currentStatements, Strings.atReachableStatementFeasCheckDescription);
				}

			} else if (that.clauseType == useClause) {

				// skip it - it has been handled previously
				result = null;

			} else {

				error(that, "Unknown token type in JmlAssertionAdder.visitJmlStatementExpr: " + that.keyword);

			}
		} catch (JmlNotImplementedException e) {
			notImplemented(that.clauseType.keyword() + " statement containing ", e);
		} catch (Exception e) {
			utils.unexpectedException(e, "JmlAssertionAdder:visitJmlStatementExpr: " + that + " " + that.hashCode()
					+ " " + that.expression.hashCode() + " " + that.expression.type);
		} finally {
			checkAccessEnabled = pv;
			assumingPostConditions = saved;
		}
	}

	public void adjustSplit(int num) {
		translations.addSplit(originalSplit, num);
		java.util.List<JmlStatementExpr> list = getFeasibilityChecks(methodDecl, originalSplit);
		feasibilityChecks.remove(assumeKey(methodDecl, originalSplit));
		originalSplit += "A";
		feasibilityChecks.put(assumeKey(methodDecl, originalSplit), list);
	}

	public static String assumeKey(JmlMethodDecl m, String split) {
		if (m == null)
			return null;
		return String.valueOf(m.sym.hashCode()) + "#" + split;
	}

	public java.util.List<JmlStatementExpr> getFeasibilityChecks(JmlMethodDecl m, String skey) {
		String key = assumeKey(m, skey);
		java.util.List<JmlStatementExpr> list = feasibilityChecks.get(key);
		if (list == null)
			feasibilityChecks.put(key, list = new LinkedList<JmlStatementExpr>());
		return list;
	}

    // OK
    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) {
        if (translatingJML) {
            error(that, "Unexpected call of JmlAssertionAdder.visitJmlStatementHavoc while translating JML: "
                    + that.getClass());
            return;
        }
        try {
            var saved = convertingAssignable;
            convertingAssignable = true;
            var stat = M.at(that).JmlHavocStatement(convertJML(that.storerefs)).setType(that.type);
            convertingAssignable = saved;
            JmlLabeledStatement sttt = markUniqueLocation(stat);
            addStat(sttt);
            changeState(that, List.<StoreRefGroup>of(convertFrameConditionList(that, treeutils.trueLit, that.storerefs)), sttt.label);
            for (var sr: that.storerefs) {
                addTypeAssumption(sr);
            }
            result = stat; // I don't think this matters
        } catch (JmlNotImplementedException e) {
            notImplemented("havoc statement containing ", e);
        }
    }
    
    public void addTypeAssumption(JCExpression sr) {
        // FIXME - won't work for anything with wild-cards; also not all types here, nor explicit invariants liek nullity
        if (types.isSameType(sr.type, syms.intType)) {
            var pred = treeutils.makeAnd(sr, 
                    treeutils.makeBinarySimp(sr, Tag.LE,
                            treeutils.makeIntLiteral(sr,  Integer.MIN_VALUE), 
                            sr),
                    treeutils.makeBinarySimp(sr, Tag.LE,
                            sr,
                            treeutils.makeIntLiteral(sr,  Integer.MAX_VALUE)));
            addAssume(sr, Label.IMPLICIT_ASSUME, pred);
        } else if (types.isSameType(sr.type, syms.shortType)) {
            var pred = treeutils.makeAnd(sr, 
                    treeutils.makeBinarySimp(sr, Tag.LE,
                            treeutils.makeIntLiteral(sr,  Short.MIN_VALUE), 
                            sr),
                    treeutils.makeBinarySimp(sr, Tag.LE,
                            sr,
                            treeutils.makeIntLiteral(sr,  Short.MAX_VALUE)));
            addAssume(sr, Label.IMPLICIT_ASSUME, pred);
        }
        if (types.isSameType(sr.type, syms.longType)) {
            var pred = treeutils.makeAnd(sr, 
                    treeutils.makeBinarySimp(sr, Tag.LE,
                            treeutils.makeLongLiteral(sr,  Long.MIN_VALUE), 
                            sr),
                    treeutils.makeBinarySimp(sr, Tag.LE,
                            sr,
                            treeutils.makeLongLiteral(sr,  Long.MAX_VALUE)));
            addAssume(sr, Label.IMPLICIT_ASSUME, pred);
        }
        if (types.isSameType(sr.type, syms.byteType)) {
            var pred = treeutils.makeAnd(sr, 
                    treeutils.makeBinarySimp(sr, Tag.LE,
                            treeutils.makeIntLiteral(sr,  Byte.MIN_VALUE), 
                            sr),
                    treeutils.makeBinarySimp(sr, Tag.LE,
                            sr,
                            treeutils.makeIntLiteral(sr,  Byte.MAX_VALUE)));
            addAssume(sr, Label.IMPLICIT_ASSUME, pred);
        }
        
    }

	// OK
	@Override
	public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) {
		boolean saved = assumingPostConditions;
		assumingPostConditions = false;
		JmlStatementLoopExpr st = M.at(that).JmlStatementLoopExpr(that.clauseType, convertExpr(that.expression));
		st.setType(that.type);
		// st.sym = that.sym;
		result = st;
		assumingPostConditions = saved;
	}

	@Override
	public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) {
		boolean saved = assumingPostConditions;
		assumingPostConditions = false;
		JmlStatementLoopModifies st = M.at(that).JmlStatementLoopModifies(that.clauseType, (that.storerefs));
		st.setType(that.type);
		// st.sym = that.sym;
		result = st;
		assumingPostConditions = saved;
	}
	
	/** Keeps track of the innermost statement spec */
	JmlStatementSpec innerStatementSpec = null;

	// OK
	@Override
	public void visitJmlStatementSpec(JmlStatementSpec that) {
		JmlStatementSpec savedInner = innerStatementSpec;
		innerStatementSpec = that;
		var savedCurrentOldLabel = currentOldLabel;
		currentOldLabel = that.label;
		JCStatement lst = M.at(that.pos).Labelled(that.label, M.at(that.pos).Skip());
		convert(lst);

		if (rac || infer || currentSplit == null) {
			// Ignore
			convert(that.statements);
			result = null;
			innerStatementSpec = savedInner;
			return;
		}

		boolean doSummary = true;
		if (currentSplit.isEmpty()) {
			adjustSplit(2);
		} else {
			doSummary = currentSplit.charAt(0) == 'A';
			currentSplit = currentSplit.substring(1);
		}

		if (that.newStatements == null) {
			ListBuffer<JCVariableDecl> newdecls = new ListBuffer<>();
			ListBuffer<JCStatement> newstats = new ListBuffer<>();
			for (JCStatement st : that.statements) {
				if (st instanceof JmlVariableDecl) {
					JmlVariableDecl decl = (JmlVariableDecl) st;
					for (JCIdent id : that.exports) {
						if (decl.name == id.name) {
							JmlVariableDecl ndecl = M.at(st.pos).VarDef(decl.sym, null);
							ndecl.fieldSpecs = decl.fieldSpecs;
							ndecl.ident = decl.ident;
							ndecl.jmltype = decl.jmltype;
							ndecl.mods = decl.mods;
							ndecl.originalType = decl.originalType;
							ndecl.originalVartype = decl.originalVartype;
							ndecl.specsDecl = decl.specsDecl;
							newdecls.add(ndecl);
							if (decl.init != null) {
								JCAssign assign = M.at(st.pos).Assign(M.at(st.pos).Ident(decl.sym), decl.init);
								st = M.at(st.pos).Exec(assign);
							} else {
								st = null;
							}
						}
						break;
					}
				}
				if (st != null)
					newstats.add(st);
			}
			that.decls = newdecls.toList();
			that.newStatements = newstats.toList();
		}
		for (JCVariableDecl decl : that.decls)
			addStat(decl);
		JmlMethodSpecs sspecs = that.statementSpecs;
		JmlSpecificationCase cs = sspecs.cases.get(0);
		if (doSummary) {
			// Make summary branch -- use the spec instead of the code
			addStat(comment(that, "Summary branch", log.currentSourceFile()));
			allocCounter++;
			{
				ListBuffer<JCExpression> newlist = new ListBuffer<>();
				for (JCIdent id : that.exports) {
					newlist.add(convertAssignable(id, currentEnv.currentReceiver, true));
				}
				JmlStatementHavoc hv = M.at(that).JmlHavocStatement(newlist.toList());
				addStat(hv);
			}
			for (JmlMethodClause clause : cs.clauses) {
				if (clause.clauseKind != assignableClauseKind)
					continue;
				JmlMethodClauseStoreRef a = (JmlMethodClauseStoreRef) clause;
				ListBuffer<JCExpression> newlist = new ListBuffer<>();
				for (JCExpression sf : a.list) {
					newlist.add(convertAssignable(sf, currentEnv.currentReceiver, true));
				}
				JmlStatementHavoc hv = M.at(a).JmlHavocStatement(newlist.toList());
				addStat(hv);
			}
			for (JmlMethodClause clause : cs.clauses) {
				if (clause.clauseKind != MethodExprClauseExtensions.ensuresClauseKind)
					continue;
				JmlMethodClauseExpr a = (JmlMethodClauseExpr) clause;
				addAssume(clause, Label.IMPLICIT_ASSUME, convertJML(a.expression));
			}
            addFeasibilityCheck(that, currentStatements, Strings.feas_summary, Strings.atSummaryFeasCheckDescription);

		} else {

			// Make non-summary branch
			addStat(comment(that, "Non-summary branch", log.currentSourceFile()));
			convert(that.newStatements);
			// FIXME - change the name on this and the defaults
			// FIXME _ fix position
			for (JmlMethodClause clause : cs.clauses) {
				if (clause.clauseKind != MethodExprClauseExtensions.ensuresClauseKind)
					continue;
				JmlMethodClauseExpr a = (JmlMethodClauseExpr) clause;
				addAssert(clause, Label.POSTCONDITION, convertJML(a.expression));
			}
			isRefiningBranch = true;
            addFeasibilityCheck(that, currentStatements, Strings.feas_summary, Strings.atNonSummaryFeasCheckDescription);
			addStat(M.at(that).JmlExpressionStatement(ReachableStatement.haltID, ReachableStatement.haltClause, null,
					null));
			continuation = Continuation.HALT;
		}
		innerStatementSpec = savedInner;
		currentOldLabel = savedCurrentOldLabel;
		result = null;
	}

	// OK
	@Override
	public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
		log.error(that.pos, "jml.message", "Should not be visiting a JmlStoreRefArrayRange: " + that);
	}

	// OK
	@Override
	public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
		log.error(that.pos, "jml.message", "Should not be visiting a JmlStoreRefKeyword: " + that);
	}

	// OK
	@Override
	public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
		switch (that.token) {

		default:
			result = eresult = M.at(that).JmlStoreRefListExpression(that.token, convert(that.list)).setType(that.type);

		}
	}

	// OK
	@Override
	public void visitJmlStoreRef(JmlStoreRef that) {
		if (that.isEverything) {
			// do nothing
		} else if (that.expression != null) {
			// These are always non-null \locset expressions
			convertExpr(that.expression);
		} else {
			//System.out.println("JSR " + that + " " + that.receiver + " " + that.field );
			if (that.receiver != null) {
			    var rcv = convertExpr(that.receiver);
				JCExpression exx = treeutils.makeNotNull(that.receiver, rcv);
				var prevv = log.useSource(that.source);
				addAssert(that, Label.UNDEFINED_NULL_DEREFERENCE, exx);
				log.useSource(prevv);
				that.receiver = rcv;
			}
			if (that.range != null) {
				if (that.range.lo != null
						&& !(that.range.lo instanceof JCLiteral lit && ((Number) lit.value).longValue() >= 0)) {
					var lhs = treeutils.makeLit(that.pos, syms.intType, 0); // FIXME - should this be bigint?
					var rhs = that.range.lo;
					JCExpression ex = treeutils.makeBinary(that.pos, JCTree.Tag.LE, lhs, rhs);
					ex = convertExpr(ex);
					var prev = log.useSource(that.source);
					addAssert(that.range.lo, Label.UNDEFINED_NEGATIVEINDEX, ex);
					log.useSource(prev);
				}
				if (that.range.hi != null) {
					var lhs = that.range.hi;
					var rhs = treeutils.makeLength(that.range.hi.pos(), that.receiver);
					JCExpression ex = treeutils.makeBinary(that.range.pos(), JCTree.Tag.LT, lhs, rhs);
					ex = convertExpr(ex);
					var prev = log.useSource(that.source);
					addAssert(that.range.hi, Label.UNDEFINED_TOOLARGEINDEX, ex);
					log.useSource(prev);
				}
			}
		}
		result = eresult = that;
	}

	// OK - readable and writable clauses
	@Override
	public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
		// FIXME _ error
		System.out.println("UNEXPECTED " + that + " : " + that.identifier + " " + that.identifier.sym); Utils.dumpStack();
		result = null;
	}

    // OK
    @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        // FIXME - not sure that this should ever be called.
        try {
            if (currentStatements == null) pushBlock();
            JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
            JCExpression expr = convertExpr(that.expression);
            JmlTypeClauseConstraint cl = M.at(that).JmlTypeClauseConstraint(mods, expr, convert(that.sigs));
            cl.setType(that.type);
            cl.source = that.source;
            cl.clauseType = that.clauseType;
            cl.notlist = that.notlist;
            classDefs.add(cl);
            result = cl;
        } catch (JmlNotImplementedException e) {
            notImplemented(that.keyword + " clause containing ", e, that.source());
            result = null;
        } finally {
            if (currentStatements == null) {
                popBlock();
            }
        }
    }

	// OK - e.g. ghost or model declaration
	@Override
	public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
		scan(that.decl);
	}

	// OK - e.g. invariant
	@Override
	public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
		try {
			if (currentStatements == null) pushBlock();
			JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
			JCExpression expr = convertJML(that.expression);
			JmlTypeClauseExpr cl = M.at(that).JmlTypeClauseExpr(mods, that.keyword, that.clauseType, expr);
			cl.setType(that.type);
			cl.source = that.source;
			// if (!rac) classDefs.add(cl);// FIXME - should we have this at all?
			result = cl;
		} catch (JmlNotImplementedException e) {
			notImplemented(that.clauseType + " clause containing ", e, that.source());
			result = null;
		} finally {
			if (currentStatements == null) {
				popBlock();
			}
		}
	}

	// OK
	@Override
	public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
		JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
		JmlTypeClauseIn cl = M.at(that).JmlTypeClauseIn(convert(that.list));
		cl.modifiers = mods;
		cl.setType(that.type);
		cl.source = that.source;
		cl.clauseType = that.clauseType;
		cl.parentVar = that.parentVar; // FIXME - need to map declaration
		classDefs.add(cl);
		result = cl;
	}

	// OK
	@Override
	public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
		JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
		JmlTypeClauseInitializer cl = M.at(that).JmlTypeClauseInitializer(that.clauseType, mods);
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
		ListBuffer<JCExpression> exprs = new ListBuffer<>();
		that.expressions.forEach( e->
		    {
		        JCExpression expr;
		        if (e instanceof JCFieldAccess fa) {
		            expr = convertExpr(fa.selected);
		            expr = M.at(fa).Select(expr, fa.sym);
		        } else if (e instanceof JCArrayAccess aa) {
		            expr = convertExpr(e);
		        } else {
		            expr = convertExpr(e);
		        }
		        exprs.add(e);
		    });
		JmlTypeClauseMaps cl = M.at(that).JmlTypeClauseMaps(exprs.toList(), convert(that.list));
		cl.modifiers = mods;
		cl.setType(that.type);
		cl.source = that.source;
		cl.clauseType = that.clauseType;
		classDefs.add(cl);
		result = cl;
	}

	// OK
	@Override
	public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
		JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
		JCIdent id = treeutils.makeIdent(that.identifier.pos, that.identifier.sym);
		JmlTypeClauseMonitorsFor cl = M.at(that).JmlTypeClauseMonitorsFor(mods, id, convert(that.list));
		cl.setType(that.type);
		cl.source = that.source;
		cl.clauseType = that.clauseType;
		classDefs.add(cl);
		result = cl;
	}

	// FIXME - needs review
	@Override
	public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
		// FIXME - implement for esc

		JCExpression e = that.ident;
		Symbol sym = null;
		if (e instanceof JCIdent)
			sym = ((JCIdent) e).sym;
		else if (e instanceof JCFieldAccess)
			sym = ((JCFieldAccess) e).sym;
		else {
			// FIXME - this should really be in JmlAttr
			utils.warning(that, "jml.internal.notsobad",
					"The lhs of a represents clause is expected to be an identifier or field access (found "
							+ e.getClass() + ")");
			return;
		}

		if (rac && that.suchThat) {
			//System.out.println("REP " + that.pos + " " + that.getStartPosition() + " " + utils.locationString(that, that.source()) + " " + that);
			notImplemented(that, "relational represents clauses (\\such_that)", that.source());
			return;
		}

		// The class we are in has a represents clause.
		// It may not have a corresponding model field; that field might be in a super
		// class.
		// If so, we need to construct the synthetic model metehod to hold it.
		JmlSpecs.TypeSpecs typeSpecs = specs.getAttrSpecs(classDecl.sym);
		if (sym != null && rac) {
			String str = Strings.modelFieldMethodPrefix + sym.name.toString();
			Name name = names.fromString(str);
			JmlMethodDecl mdecl = null;
			// Find the method for this model field. It will have been created in
			// JmlMemberEnter
			for (JmlTypeClauseDecl m : typeSpecs.modelFieldMethods) {
				JmlMethodDecl md = (JmlMethodDecl) m.decl;
				if (!md.name.toString().equals(str))
					continue;
//                try {
//                    JCStatement firststat = md.body.stats.head;
//                    if (firststat instanceof JCThrow) {
//                        // No (non-such_that) represents clause
//                        // But still keep the model field's method
//                        classDefs.add(md);
//                    } else if (firststat instanceof JCReturn && ((JCReturn)firststat).expr == that.expression) {
//                        pushBlock();
//                        boolean save = splitExpressions;
//                        splitExpressions = false;
//                        try {
//                            JCReturn st = M.at(that).Return(convertExpr(that.expression)); // FIXME - what do we do about undefined expressions?
//                            addStat(st);
//                            md.body.stats = popBlock(that.expression).stats;
//                            md.mods.flags &= ~Flags.DEFAULT;
//                        } finally {
//                            classDefs.add(md);
//                            splitExpressions = save;
//                        }
//                    } else {
//                        log.warning(that.pos,"jml.duplicate.represents");
//                    }
//
//                } catch (JmlNotImplementedException ee) {
//                    // Can't implement this represents clause because
//                    // of some non-translatable expression within it
//                    notImplemented(that.token.internedName() + " clause containing ", ee, that.source());
//                }
				mdecl = md;
				break;
			}
			if (mdecl == null) {
				// We can get here
				// when a subclass has a represents clause for a super class's
				// model field.

				long flags = Flags.PUBLIC | Flags.SYNTHETIC;
				flags |= (that.modifiers.flags & Flags.STATIC);
				JCModifiers mods = M.Modifiers(flags);
				JCMethodDecl msdecl = treeutils.makeMethodDefNoArg(mods, name, that.ident.type, classDecl.sym);
				msdecl.pos = that.pos;
				ListBuffer<JCStatement> check = pushBlock();
				try {
					currentStatements.addAll(msdecl.body.stats);
					// Note: we do not call convertJML on that expression because the body is
					// converted
					// later on - for rac, in visitClassDecl we are handling represents clauses
					// before we process
					// all the definitions in the class.
					// If we did call convertJML we would need to set the methodDecl so that newly
					// created
					// variables are owned by the method and not by the class (which would causes
					// NoSuchFieldError
					// when executed)
					JCReturn st = M.Return(that.expression);
					currentStatements.add(st);
				} catch (JmlNotImplementedException ee) {
					// Can't implement this represents clause because
					// of some non-translatable expression within it
					notImplemented(that.clauseType.keyword() + " clause containing ", ee, that.source());
				} finally {
					msdecl.body.stats = popBlock(msdecl.body, check).stats;
				}
				classDefs.add(msdecl);
				JmlTypeClauseDecl tcd = M.JmlTypeClauseDecl(msdecl);
				tcd.modifiers = msdecl.mods;
				tcd.pos = msdecl.pos;
				tcd.source = that.source();
				tcd.modifiers = msdecl.mods; // FIXME - is this necesssary
				typeSpecs.modelFieldMethods.append(tcd);
//                typeSpecs.decls.append(tcd);
			}
		}
		result = null;
	}

	public Type mathType(Type type) {
		TypeTag tag = type.getTag();
		if (tag == TypeTag.FLOAT || tag == TypeTag.DOUBLE) return jmltypes.REAL;
		if (tag == TypeTag.INT || tag == TypeTag.LONG || tag == TypeTag.SHORT || tag == TypeTag.BYTE || tag == TypeTag.CHAR) return jmltypes.BIGINT;
		return type;
	}

	// FIXME - needs review
	@Override
	public void visitJmlVariableDecl(JmlVariableDecl that) {
		specs.getAttrSpecs(that.sym);
		if (!specs.statusOK(that.sym))
			return; // FIXME - abort
		JavaFileObject prevSource = log.useSource(that.source());

		try {

			JCIdent newident = null;
			if (esc || infer) {
				that.ident = treeutils.makeIdent(that.pos, that.sym);
				// We don't use convertExpr, because that might chang the JCIdent to a
				// JCFieldAccess
				newident = treeutils.makeIdent(that.pos, that.sym);
				saveMapping(that.ident, newident);
				if (currentEnv.arithmeticMode instanceof Arithmetic.Math) {
					Symbol sym = that.sym;
					Type t = mathType(sym.type);
					if (t != sym.type) {
						Symbol newsym = sym.clone(sym.owner);
						newsym.type = t;
						newident.type = t;
						newident.sym = newsym;
						putSymbol(sym, newsym);
					}
				}
			} else if (rac) {
				// FIXME - should alo be copyint the symbol
				if (that.type instanceof JmlType) {// FIXME - should really be copying the AST
					that.vartype = ((JmlPrimitiveTypeTree) that.vartype).repType;
					that.type = jmltypes.repSym((JmlType) that.type).type;
					that.sym.type = that.type;
				}
				if (specs.fieldSpecHasModifier(that.sym, Modifiers.SPEC_PUBLIC)) {
					that.mods.flags &= ~Flags.AccessFlags;
					that.mods.flags |= Flags.PUBLIC;
					that.sym.flags_field &= ~Flags.AccessFlags;
					that.sym.flags_field |= Flags.PUBLIC;
				}
				if (specs.fieldSpecHasModifier(that.sym, Modifiers.SPEC_PROTECTED)) {
					that.mods.flags &= ~Flags.AccessFlags;
					that.mods.flags |= Flags.PROTECTED;
					that.sym.flags_field &= ~Flags.AccessFlags;
					that.sym.flags_field |= Flags.PROTECTED;
				}
			}

			if (!inClassDecl()) {
				addTraceableComment(that, that, that.toString(), null);
			}

			if ((that.type.tsym.flags_field & Flags.ENUM) != 0 && that.sym.owner instanceof ClassSymbol) { // FIXME -
																											// should
																											// check the
																											// initializer
																											// expressions
																											// of enums
				JmlVariableDecl stat = M.at(that).VarDef(that.sym, that.init);
				stat.ident = newident;

				if (inClassDecl())
					classDefs.add(stat);
				else
					addStat(stat);

				result = stat;
				return;
			}

			boolean inClassDecl = inClassDecl();
			if (localVariables.containsKey(that.sym)) {
				JmlVariableDecl stat = M.at(that).VarDef(that.sym, null);
				JCExpression init = convertExpr(that.init);
				stat.init = init;
				stat.ident = newident;
				if (inClassDecl)
					classDefs.add(stat);
				else
					addStat(stat);
				result = stat;
				return;
			}
			// Called during translation of model methods
			if (JmlAttr.instance(context).isGhost(that.mods)) {
				try {
					JCExpression init = null;

					// If we are in a class, there is nowhere to push statements
					// so we make a block and later turn it into an initializer block
					ListBuffer<JCStatement> check = null;
					if (inClassDecl) {
						check = pushBlock();
					}
					JmlVariableDecl stat = null;
					boolean pv = checkAccessEnabled;
					checkAccessEnabled = false;
					try {
					    //System.out.println("CONVERTING " + that.init + " " + that.init.getClass());
						init = convertJML(that.init);
						if (init != null)
							init = addImplicitConversion(init, that.type, init);

						stat = M.at(that).VarDef(that.sym, init);
						stat.ident = newident;
						JCExpression nn = null;
						if (init != null && !utils.isJavaOrJmlPrimitiveType(init.type) && !isKnownNonNull(that.init)
								&& !isKnownNonNull(init) && specs.isNonNull(that.sym)) {

							nn = treeutils.makeNeqObject(init.pos, init, treeutils.nullLit);
							if (init instanceof JCLiteral) {
								// FIXME - potential optimizations, but they need testing, particularly the
								// second one
								if (init.type.getTag() == TypeTag.BOT)
									nn = treeutils.falseLit;
								else if (init.type.getTag() == TypeTag.CLASS)
									nn = treeutils.trueLit;
							}
							// FIXME - should have an associated position in assert
						}
						if (inClassDecl)
							methodDecl = (JmlMethodDecl) M.MethodDef(attr.makeInitializerMethodSymbol(that.mods.flags,
									JmlEnter.instance(context).getEnv(classDecl.sym)), null);
						if (nn != null)
							addAssert(that, Label.POSSIBLY_NULL_INITIALIZATION, nn, that.name);
						if (esc && !utils.isJavaOrJmlPrimitiveType(that.type)) {
							addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeDynamicTypeInEquality(that,
									treeutils.makeIdent(that.pos, that.sym), that.type));
						}
					} finally {
						if (inClassDecl) {
							JCBlock bl = popBlock(that.mods.flags & Flags.STATIC, that, check);
							if (stat != null)
								classDefs.add(stat);
							classDefs.add(bl);
							methodDecl = null;
						} else {
							if (stat != null)
								addStat(stat);
						}
						if (stat != null && esc && !(that.type instanceof Type.ArrayType)
								&& jmltypes.isArray(that.type)) {
							JCExpression inv = getInvariantAll(that, that.type,
									treeutils.makeIdent(that.pos, that.sym), true);
							if (inv != null)
								inv.type = syms.booleanType;
							else
								inv = treeutils.trueLit;
							JCExpression nn = utils.isJavaOrJmlPrimitiveType(that.type) ? treeutils.trueLit
									: treeutils.makeNotNull(that.pos, treeutils.makeIdent(that.pos, that.sym));
							addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeAndSimp(that.pos, nn, inv));
						}
						checkAccessEnabled = pv;
					}
					result = stat;
				} catch (JmlNotImplementedException e) {
					notImplemented("ghost declaration containing ", e);
				}
			} else if (that.init == null) {
				JmlVariableDecl stat = M.at(that).VarDef(that.sym, that.init);
				stat.ident = newident;
				// type, vartype, sym, name, mods, init are filled in
				stat.mods = that.mods;
				stat.sourcefile = that.sourcefile;
				stat.docComment = that.docComment;
				stat.fieldSpecs = that.fieldSpecs; // TOOD: copy?
				stat.specsDecl = that.specsDecl; // TODO: copy? translate reference?
				if (currentStatements == null)
					classDefs.add(stat);
				else
					addStat(stat);
				if (esc && !that.type.isPrimitive()) {
					addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeDynamicTypeInEquality(that,
							treeutils.makeIdent(that.pos, that.sym), that.type));
				}

				result = stat;
			} else {
				// FIXME - are these regular Java declarations? what about model decls?

				// FIXME - need to make a unique symbol; what if the decl is final?
				JmlVariableDecl stat = M.at(that).VarDef(that.sym, null);
				stat.ident = newident;
				// type, vartype, sym, name, mods, init are filled in
				stat.mods = that.mods;
				stat.sourcefile = that.sourcefile;
				stat.docComment = that.docComment;
				stat.fieldSpecs = that.fieldSpecs;
				stat.specsDecl = that.specsDecl;

				ListBuffer<JCStatement> check = pushBlock();
				JCExpression init = null;
				JCExpression nn = null;
				try {
					if (statementStack.get(0) == null && methodDecl == null) {
						long flags = that.mods.flags & Flags.STATIC;
						// We are in an initializer block
						// We need a method symbol to be the owner of declarations
						// (otherwise they will have the class as owner and be thought to
						// be fields)
						MethodSymbol msym = new MethodSymbol(flags, classDecl.name, null, classDecl.sym);
						methodDecl = // M.MethodDef(msym, null,n)ull);
								new JmlMethodDecl(
										M.Modifiers(flags,
												M.Annotations(List.<com.sun.tools.javac.code.Attribute.Compound>nil())),
										classDecl.name, null, null, null, null, null, null, // body,
										null, msym);
						methodDecl.isInitializer = true;
					}

					// boolean pv = checkAccessEnabled;
					// checkAccessEnabled = enclosingMethod != null; // FIXME - decide how to handle
					// initialization of class fields
					// try {
					init = convertExpr(that.init);
					// } finally {
					// checkAccessEnabled = pv;
					// }
					if (init != null)
						init = addImplicitConversion(init, that.type, init);

					if (init != null && !utils.isJavaOrJmlPrimitiveType(that.type) && specs.isNonNull(that.sym, that)) { // isNonNull
																													// returns
																													// false
																													// if
																													// that.type
																													// is
																													// primitive
						nn = treeutils.makeNeqObject(init.pos, init, treeutils.nullLit);
						if (init instanceof JCLiteral) {
							// FIXME - potential optimizations, but they need testing, particularly the
							// second one
							if (init.type.getTag() == TypeTag.BOT)
								nn = treeutils.falseLit;
							else if (init.type.getTag() == TypeTag.CLASS)
								nn = treeutils.trueLit;
						}
						// FIXME - should have an associated position
					}
				} catch (PropagatedException e) {
					throw e;
				} catch (Exception e) {
					System.out.println("EXCEPTION " + e);
					e.printStackTrace(System.out);
				} finally {
					if (statementStack.get(0) == null) {
						// Class definition
						if (currentStatements.isEmpty() && nn == null) {
							// Just a simple initialization since there is no nonnull check
							// and the init expression did not create any new statements
							popBlock(null, check); // Nothing present - just ignore the empty block
							stat.init = init;
							this.classDefs.add(stat);
							if (esc && !utils.isJavaOrJmlPrimitiveType(that.type)) {
								addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeDynamicTypeInEquality(that,
										treeutils.makeIdent(that.pos, that.sym), that.type));
							}
						} else {
							long flags = that.mods.flags & Flags.STATIC;

							// Create a initializer block
							if (nn != null)
								addAssert(that, Label.POSSIBLY_NULL_INITIALIZATION, nn, that.name);
							addStat(treeutils.makeAssignStat(that.pos, treeutils.makeIdent(that.pos, stat.sym), init));
							if (esc && !utils.isJavaOrJmlPrimitiveType(that.type)) {
								addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeDynamicTypeInEquality(that,
										treeutils.makeIdent(that.pos, that.sym), that.type));
							}
							JCBlock bl = popBlock(flags, that, check);
							this.classDefs.add(stat);
							this.classDefs.add(bl);
						}
						methodDecl = null;
					} else {
						// Regular method body
						if (init == null || isKnownNonNull(that.init) || isKnownNonNull(init))
							nn = null;
						JCBlock bl = popBlock(that, check);
						currentStatements.addAll(bl.stats);
						if (nn != null)
							addAssert(that, Label.POSSIBLY_NULL_INITIALIZATION, nn, that.name);
						stat.init = init;
						// if (splitExpressions) {
						addStat(stat);
						if (esc && !utils.isJavaOrJmlPrimitiveType(that.type)) {
							addAssume(that, Label.IMPLICIT_ASSUME, treeutils.makeDynamicTypeInEquality(that,
									treeutils.makeIdent(that.pos, that.sym), that.type));
						}
						// }
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
		// return methodDecl == null;
	}

	// OK
	@Override
	public void visitJmlWhileLoop(JmlWhileLoop that) {

		/*
		 * loop_invariant INV loop_variant VAR label: while (COND) { BODY } becomes {
		 * assert INV label: while (true) { havoc assume INV TEMP = VAR ... statements
		 * from COND if (!COND') { assert INV; break; } assert 0 <= TEMP loop_bodyN: {
		 * ... statements from BODY ... continue --> break loop_bodyN; ... break -->
		 * break; } assert INV TEMP2 = VAR assert TEMP2 < TEMP } // FIXME - if break
		 * exits still have to satisfy invariant, put the check here }
		 * 
		 */

		// FIXME - need label for loop if any and the target mapping

		// Outer block to restrict scopes of temporaries
		pushBlock();

		JCVariableDecl indexDecl = loopHelperDeclareIndex(that);

		java.util.List<JCIdent> decreasesIDs = new java.util.LinkedList<JCIdent>();

		// Create this early so it is available as a target
		JmlWhileLoop loop = M.at(that).WhileLoop(treeutils.trueLit, null);
		treeMap.put(that, loop);

		// Test that invariants hold before entering loop
		loopHelperInitialInvariant(that.loopSpecs);

		// New loop body
		pushBlock();

		// Havoc all items that might be changed in the loop and change the state
		if (esc) {
			boolean b = loopHelperHavoc(that.loopSpecs, that.body, indexDecl, null, null, that.body, that.cond);
//			if (!b) {// FIXME - but only if somethings non-local is havoced?
//			    changeStateForLoop(that, that.loopSpecs);
//			}
		}

		loopHelperAssumeInvariants(that.loopSpecs, decreasesIDs, that, null);

		// Compute the condition, recording any side-effects

		addTraceableComment(that.cond, that.cond, "Loop test");
		JCExpression cond = convertExpr(that.cond);

		// The exit block tests the condition; if exiting, it tests the
		// invariant and breaks.
		int savedHeapCount = heapCount;
		currentEnv = currentEnv.pushEnvCopy();
		Boolean splitInfo = loopHelperMakeBreak(that.loopSpecs, cond, loop, that);
		boolean doRemainderOfLoop = splitInfo == null || splitInfo;

		// Now in the loop, so check that the variants are non-negative
		if (doRemainderOfLoop)
			loopHelperCheckNegative(decreasesIDs, that);

		// Then translate the original loop body
		// Have to do some footwork to get the Block object before constructing its
		// contents
		if (doRemainderOfLoop)
			loopHelperMakeBody(that.body);

		// increment the index
		if (doRemainderOfLoop)
			loopHelperIncrementIndex(indexDecl);

		// After the loop, check the invariants and check that the variants have
		// decreased
		if (doRemainderOfLoop)
			loopHelperAssertInvariants(that.loopSpecs, decreasesIDs);

		// Finish up the new loop body
		// Finish up the output block
		loopHelperFinish(loop, that);
		JCBlock bl = popBlock(that);
		addStat(bl);
		if (splitInfo != null && splitInfo)
			continuation = Continuation.HALT;

        currentEnv = currentEnv.popEnv();
		heapCount = savedHeapCount;
	}
	
    public JmlLabeledStatement markUniqueLocation(JCStatement statToMark) {
        Name label = names.fromString("`_label`" + nextUnique());
        JmlLabeledStatement mark = M.JmlLabeledStatement(label, null, statToMark  == null ? M.Skip() : statToMark);
        recordLabel(label, mark);
        markLocation(label, null, mark);
        return mark;
    }

    public JmlLabeledStatement markUniqueLocation() {
        return markUniqueLocation(M.Skip());
    }

	protected void markLocation(Name label, ListBuffer<JCStatement> list, JmlLabeledStatement marker) {
		Location loc = new Location(list, marker);
		locations.put(label, loc);
		LabelProperties lp = labelPropertiesStore.get(label);
		lp.labeledStatement = marker;
		lp.heapCount = this.heapCount;

		// FIXME - this requires all labels to be unique
	}

	protected void insertAtLocation(Name label, JCStatement... statements) {
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
					if (t == loc.marker) {
						tail.add(t);
						break head;
					}
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

	protected Map<Name, Location> locations = new HashMap<Name, Location>();

	public class Location {
		public ListBuffer<JCStatement> list;
		public JCStatement marker;

		public Location(ListBuffer<JCStatement> list, JCStatement marker) {
			this.list = list;
			this.marker = marker;
		}
	}

//	public class ParentItem {
//		public ClassSymbol classSym;
//		public Map<Type.TypeVar, Type> vars = new HashMap<Type.TypeVar, Type>();
//
//		public ParentItem(ClassSymbol cs, Map<Type.TypeVar, Type> vm) {
//			classSym = cs;
//			vars = vm;
//		}
//	}

	/**
	 * Returns a list of super classes and interfaces, as types; the order is that
	 * Object comes first, then interfaces, and then classes, with super classes/interfaces 
     * coming before derived ones, with the argument type last. If enclosing types are 
     * included, the outer type is listed before the inner type. JML Primitive types
     * have no inheritance and just return a singleton list of itself. The list may
     * include type variables.
	 */
	public java.util.List<Type> parents(Type targetClassWithMetadata, boolean includeEnclosing) { // FIXME - not implemented for
																				// includeEnclosing = true // FIXME -
																				// unify this with the methods in Utils.

		java.util.List<Type> classes = new LinkedList<Type>();
		Type targetClass = targetClassWithMetadata.stripMetadata();
		if (utils.isExtensionValueType(targetClass)) {
			classes.add(targetClass);
			return classes;
		}
		if (targetClass.getTag() == TypeTag.BOT) {
		    // For a 'null' type
	        // FIXME - is it OK that that occurs?
		    // Return an empty list
            return classes;
		}
		Type cc = targetClass; // Loop variable - class being considered
		// Prepend super classes into the 'classes' list, and optionally the enclosing classes
		while (cc.getTag() != TypeTag.NONE) { // NONE happens for the supertype of Object
			classes.add(0, cc);
			if (cc instanceof Type.ClassType cct) {
				if (includeEnclosing) { // FIXME - only if static?
					Type t = cc.getEnclosingType();
					if (t != null && t.getTag() != TypeTag.NONE) {
						int n = 0;
						for (Type tt : parents(t, includeEnclosing)) {
							if (!tt.isInterface()) {
							    var iter = classes.iterator();
							    while (iter.hasNext()) { 
							        var ttt = iter.next(); 
							        if (types.isSameType(ttt,tt)) { 
							            classes.remove(ttt); 
							            break; 
							        }
							    }
                                classes.add(n++, tt);
							}
						}
					}
				}
//                if (!types.isSameType(cct, cct.tsym.type)) System.out.println("NOT SAME TYPE " + cct + " " + cct.tsym + " " + cct.tsym.type);
				if (cct.tsym instanceof ClassSymbol c) {
				    cc = c.getSuperclass();
				} else if (cct.tsym instanceof TypeVariableSymbol tv) {
				    if (tv.getBounds().size() == 0) {
				        // Always expect a bound
				        cc = syms.objectType;
				    } else {
				        tv.getBounds().forEach(b->classes.add(0,b));
				        cc = classes.remove(0);
				    }
				} else {
				    // Unhandled kind of symbol - PackageSymbol, ModuleSymbol
	                utils.warning("jml.internal",  "Did not expect this kind of symbol when finding parents of " + targetClassWithMetadata + ": " + cct.tsym);
	                break;
				}
//				if (cc == null) System.out.println("NULL SUPER TYPE FIELD OF " + cct + " " + cct.tsym + " " + cct.tsym.type + " " + ((Type.ClassType) cct.tsym.type).supertype_field);
//				if (cc == null)
//					cc = ((Type.ClassType) cct.tsym.type).supertype_field;

			} else if (cc instanceof Type.ArrayType) {
				cc = syms.objectType;
			} else if (cc instanceof Type.TypeVar ctv) {
				cc = ctv.getUpperBound();
			} else {
			    utils.warning("jml.message",  "Did not expect this class type when finding parents of " + targetClassWithMetadata + ": " + cc + " " + cc.getClass());
				break;
			}
		}

		java.util.List<Type> interfacesToDo = new LinkedList<Type>();
		java.util.List<Type> interfaces = new LinkedList<Type>();
		for (Type cty : classes) {
			if (cty instanceof Type.ClassType cct) {
			    if (cct.tsym instanceof ClassSymbol cctsym) {
			        List<Type> ifs = cctsym.getInterfaces();
			        if (cc == null) System.out.println("NULL INTERFACE FIELD OF " + cct);
			        if (ifs == null)
			            ifs = ((Type.ClassType) cct.tsym.type).interfaces_field;
			        if (cc == null) System.out.println("STILL NULL INTERFACE FIELD OF " + cct);
			        if (ifs != null)
			            interfacesToDo.addAll(ifs);
			    }
			}
		}

		// 'interfacesToDo has all the immediate interfaces of everything in 'classes', with potential duplicates
		while (!interfacesToDo.isEmpty()) {
			Type ifc = interfacesToDo.remove(0);
			// already in the final list?
			if (interfaces.stream().anyMatch(t -> types.isSameType(t, ifc))) continue;
			// if not prepend it
			interfaces.add(0, ifc);
			// and add all of its direct interface to the todo list
			List<Type> ints = ((Type.ClassType) ifc.tsym.type).interfaces_field;
			if (ints != null) interfacesToDo.addAll(ints);
		}
		// Now put Object at the front and all other classes at the end
		if (classes.size() > 0) {
			Type obj = classes.remove(0);
			interfaces.addAll(classes);
			interfaces.add(0, obj);
		} else {
		    utils.warning("jml.internal", "Unexpected branch in JmlAssertionAdder.parents " + targetClassWithMetadata);
		}
		return interfaces;
	}

	public Type typevarValue(Type tv, Map<TypeSymbol, Type> typevarMap) {
		if (typevarMap == null || !(tv instanceof Type.TypeVar))
			return tv;
		Type v = typevarMap.get(((Type.TypeVar) tv).tsym);
		// System.out.println("MAPPED " + tv + " TO " + (v == null ? tv : v));
		return v == null ? tv : v;
	}

	public Map<TypeSymbol, Type> typemapping(JCMethodInvocation apply, Map<TypeSymbol, Type> map) {
		if (map == null)
			map = new HashMap<TypeSymbol, Type>();
		// FIXME - static methods, classes as receiver types
		if (apply.meth instanceof JCFieldAccess) {
			JCFieldAccess fa = (JCFieldAccess) apply.meth;
			// Map fa.type to fa.sym.type // method type
			map = unify(fa.type, fa.sym.type, map);
			// Map fa.selected.type to fa.sym.owner.type // receiver
			map = unify(fa.selected.type, fa.sym.owner.type, map);
			// Map each element of m.

		} else if (apply.meth instanceof JCIdent) {
			JCIdent id = (JCIdent) apply.meth;
			// Map id.type to id.sym.type // method type
			map = unify(id.type, id.sym.type, map);
			// Map fa.selected.type to fa.sym.owner.type // receiver
			map = unify(currentEnv.currentReceiver.type, id.sym.owner.type, map);
			// Map each element of m.

		} else {
			System.out.println("UNKNOWN INVOCATION " + apply);
		}
		// System.out.println("MAP " + apply + " " + map);
		return map;
	}

	public Map<TypeSymbol, Type> unify(Type actual, Type formal, Map<TypeSymbol, Type> map) {
		// System.out.println("UNIFYING " + actual + " TO " + formal + " ( " +
		// actual.getClass() + " " + formal.getClass() + ")");
		if (types.isSameType(actual, formal))
			return map;
		if (formal instanceof Type.TypeVar) {
			map.put(((Type.TypeVar) formal).tsym, actual);
			return map;
		}
		if (formal instanceof Type.ArrayType && actual instanceof Type.ArrayType) {
			return unify(((Type.ArrayType) actual).elemtype, ((Type.ArrayType) formal).elemtype, map);
		}
		if (formal instanceof Type.ClassType && actual instanceof Type.ClassType) {
			Type.ClassType cformal = ((Type.ClassType) formal);
			Type.ClassType cactual = ((Type.ClassType) actual);
			if (cactual.tsym == cformal.tsym) {
				Iterator<Type> actualiter = cactual.getTypeArguments().iterator();
				Iterator<Type> formaliter = cformal.getTypeArguments().iterator();
				while (actualiter.hasNext() && formaliter.hasNext()) {
					map = unify(actualiter.next(), formaliter.next(), map);
				}
				if (actualiter.hasNext() || formaliter.hasNext()) {
					// It seems type checking should have failed
					// log.error("jml.message","Actual and formal types have different numbers of
					// type arguments: " + actual + " vs. " + formal);
				}
				return map;
			}
		}
		// System.out.println("CANNOT MAP " + actual + " TO " + formal + " ( " +
		// actual.getClass() + " " + formal.getClass() + ")");
		return map;
	}

	public Map<TypeSymbol, Type> typemapping(Type ct, Symbol sym, List<JCExpression> typeargs,
			Map<TypeSymbol, Type> vars) {
		return typemapping(ct, sym, typeargs, null, vars);
	}

	public Map<TypeSymbol, Type> typemapping(Type ct, Symbol sym, List<JCExpression> typeargs,
			Type.MethodType methodType, Map<TypeSymbol, Type> vars) {
		vars = new HashMap<TypeSymbol, Type>();
		if (ct instanceof Type.ClassType) {
			Type ect = ct.getEnclosingType();
			if (ect != null)
				vars = typemapping(ect, sym, typeargs, methodType, vars);
		}
		if (ct instanceof Type.ClassType && !((Type.ClassType) ct).getTypeArguments().isEmpty()) {
			Iterator<Type> ity = ((Type.ClassType) ct).getTypeArguments().iterator();
			for (TypeSymbol tsym : ct.tsym.getTypeParameters()) {
				Type cty = ity.next();
				vars.put(tsym, cty);
			}
		}

		if (sym != null && sym.type instanceof Type.ForAll) {
			if (typeargs != null && !typeargs.isEmpty()) {
				List<Type> tlist = ((Type.ForAll) sym.type).tvars;
				Iterator<JCExpression> ita = typeargs.iterator();
				for (Type t : tlist) {
					JCExpression tta = ita.next();
					vars.put(t.tsym, tta.type);
				}
			} else if (methodType != null) {
				// Unify to find types
				// FIXME - just doing simple unification for now
				List<Type> tt = methodType.getParameterTypes();
				List<Type> tlist = ((Type.ForAll) sym.type).getParameterTypes();
				Iterator<Type> tlisti = tlist.iterator();
				Iterator<Type> tti = tt.iterator();
				while (tti.hasNext()) {
					Type t1 = tlisti.next();
					Type t2 = tti.next();
					unifyTypes(t1, t2, vars);
				}
			}
		}
		if (sym != null && methodType != null && sym.type instanceof Type.MethodType) {
			// Match arguments of sym.type to methodType
			List<Type> args = ((Type.MethodType) sym.type).argtypes;
			List<Type> tt = methodType.getParameterTypes();
			for (Type t : args) {
				Type value = tt.head;
				unifyTypes(t, value, vars);
				tt = tt.tail;
			}
		}
		return vars;
	}

	public boolean unifyTypes(Type t1, Type t2, Map<TypeSymbol, Type> vars) {
		if (t1 instanceof Type.TypeVar) {
			vars.put(t1.tsym, t2);
			return true;
		}
		if (t1 instanceof Type.ArrayType && t2 instanceof Type.ArrayType) {
			t1 = ((Type.ArrayType) t1).getComponentType();
			t2 = ((Type.ArrayType) t2).getComponentType();
			return unifyTypes(t1, t2, vars);
		}
		return false;
	}

	public java.util.List<Pair<MethodSymbol, Type>> parents(MethodSymbol m, Type classType) {
		java.util.List<Pair<MethodSymbol, Type>> methods = new LinkedList<Pair<MethodSymbol, Type>>();
		if (utils.isJMLStatic(m)) {
			methods.add(pair(m, m.owner.type));
		} else if (m.isConstructor()) {
			methods.add(pair(m, m.owner.type));
		} else {
			// System.out.println(" CHECKING " + classType.tsym + " " +
			// classType.tsym.getClass() + " " + classType.getClass());
			// if (classType instanceof Type.TypeVar) {
			// System.out.println( "BOUND " + classType.getLowerBound() + " " +
			// classType.getUpperBound());
			// }
			for (ClassSymbol csym : utils.parents(classType.tsym, true)) {
				// System.out.println(" CHECKING " + csym + " FOR " + classType.tsym);
				for (Symbol mem : csym.getEnclosedElements()) {
					if (mem instanceof MethodSymbol && // FIXME - not static, not private
							mem.name.equals(m.name)
							&& (mem == m || m.overrides(mem, csym, Types.instance(context), true)
									|| ((MethodSymbol) mem).overrides(m, (TypeSymbol) m.owner, Types.instance(context),
											true))) {
						methods.add(pair((MethodSymbol) mem, csym.type));
					}
				}
			}
		}
		// System.out.println("PARENTS " + m + " " + methods);
		return methods;
	}

	public static <F, S> Pair<F, S> pair(F f, S s) {
		return new Pair<F, S>(f, s);
	}

	public static class Pair<F, S> {
		public F first;
		public S second;

		public Pair(F f, S s) {
			first = f;
			second = s;
		}
	}

//    public java.util.List<JCExpression> makeMethodAxioms(JmlMethodDecl methodDecl) {
//        // requires that method is pure
//        // create an axiom from specification case that is normal_behavior
//        // or has no signals clause, or a signals clause that is Exception false
//        java.util.List<JCExpression> axioms = new LinkedList<JCExpression>();
//        for (MethodSymbol msym: utils.parents(methodDecl.sym)) {
//            JmlSpecs.MethodSpecs mspecs = specs.getSpecs(msym);
//            for (JmlSpecificationCase cs: mspecs.cases.cases) {
//                boolean makeAxiom = false;
//                if (cs.token == JmlToken.NORMAL_BEHAVIOR) makeAxiom = true;
//                //FIXME - check signals clauses?
//                
//                if (!makeAxiom) continue;
//                
//                // Make signature and call instance
//                
//                ListBuffer<JCVariableDecl> decls = new ListBuffer<JCVariableDecl>();
//                ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
//                Map<Object,JCExpression> substitutions = new HashMap<Object,JCExpression>();
//                JmlTreeSubstitute subst = new JmlTreeSubstitute(context,M,substitutions); // TODO - use a factory?
//                
//                if (!msym.isStatic()) {
//                    // Add in a slot for the receiver
//                }
//                for (VarSymbol vsym : msym.params) {
//                    JCVariableDecl decl = treeutils.makeVariableDecl(vsym.name,  vsym.type, null, cs.pos);
//                    decl.sym.owner = methodDecl.sym;
//                    decls.add(decl);
//                    JCIdent id = M.at(decl.pos).Ident(decl.sym);
//                    substitutions.put(decl.sym, id);
//                    args.add(id);
//                }
//                
//                // Assemble pre and post condition
//                JCExpression pre = null;
//                JCExpression post = null;
//                for (JmlMethodClause cl : cs.clauses) {
//                    if (cl.token == JmlToken.REQUIRES) {
//                        JCExpression ex = ((JmlMethodClauseExpr)cl).expression;
//                        ex = subst.copy(ex);
//                        pre = pre == null ? ex : treeutils.makeAnd(pre.pos, pre, ex);
//                    }
//                    if (cl.token == JmlToken.ENSURES) {
//                        JCExpression ex = ((JmlMethodClauseExpr)cl).expression;
//                        ex = subst.copy(ex);
//                        post = post == null ? ex : treeutils.makeAnd(post.pos, post, ex);
//                    }
//                }
//                if (pre == null) pre = treeutils.trueLit;
//                if (treeutils.isFalseLit(pre)) continue; // trivial axiom
//                if (post == null || treeutils.isTrueLit(post)) continue; // trivial axiom
//                JCExpression ex = treeutils.makeImplies(cs.pos, pre, post);
//                
//                // Wrap in a forall
//                JmlQuantifiedExpr q = M.JmlQuantifiedExpr(JmlToken.FORALL, decls.toList(), null, ex);
//                q.pos = cs.pos;
//                q.type = syms.booleanType;
//                axioms.add(q);
//                
//                log.noticeWriter.println("For " + msym + " : " + q);
//            }
//        }
//        
//        
//        return axioms;
//        
//    }
    
    public class Copier extends org.jmlspecs.openjml.visitors.JmlTreeCopier {

		public Copier(Context context, JmlTree.Maker maker) {
			super(context, maker);
		}
		
//		public JCTree copy(JCTree that) {
//			return copy(that,null);
//		}
//
//		public JCExpression copy(JCExpression that) {
//			return copy(that,null);
//		}

	    @Override
	    public JCTree visitAnnotation(AnnotationTree that, Void p) {
	        // Only needed for a full tree copy
	        // A JCAnnotation is a kind of JCExpression
//	        if (fullTranslation) {
	            var t = super.visitAnnotation(that,p);
	            treeutils.copyEndPosition(t,(JCAnnotation)that);
	            return t;
//	        } else {
//	            result = eresult = that;
//	        }
	    }
	    
	    @Override
	    public JCTree visitLambda(JCLambda that, Void p) {
	    	ListBuffer<JCStatement> check = pushBlock(); // To swallow and ignore the addStat of a block in visitBlock which no longer happens
	    	boolean saved = translatingJML;
	    	translatingJML = false;
	    	JmlLambda nthat = M.at(that.pos).JmlLambda(copy(that.params, null), copy(that.body, null), copy(((JmlLambda) that).jmlType));
	    	nthat.type = that.type;
	    	nthat.literal = copy(((JmlLambda) that).literal);
	    	nthat.sourceLocation = ((JmlLambda) that).sourceLocation;
	    	result = eresult = nthat;
	    	translatingJML = saved;
	    	popBlock(that, check);
	    	//System.out.println("COPY LAMBDA " + that + " " + nthat);
	    	return nthat;
	    }
	    @Override
	    public JCTree visitLambdaExpression(LambdaExpressionTree node, Void p) {
	    	ListBuffer<JCStatement> check = pushBlock(); // To swallow and ignore the addStat of a block in visitBlock which no longer happens
	    	boolean saved = translatingJML;
	    	translatingJML = false;
	    	JmlLambda that = (JmlLambda)node;
	    	JmlLambda nthat = M.at(that.pos).JmlLambda(copy(that.params, null), copy(that.body, null), copy(that.jmlType));
	    	nthat.type = that.type;
	    	nthat.literal = copy(that.literal);
	    	nthat.sourceLocation = that.sourceLocation;
	    	result = eresult = nthat;
	    	translatingJML = saved;
	    	popBlock(that, check);
	    	//System.out.println("COPY LAMBDAEXPR " + that + " " + nthat);
	    	return nthat;
	    }
    }
    

	public static class WellDefined {
		public MethodSymbol sym;
		public JCExpression wellDefinedExpression;
		public DiagnosticPosition pos;
		public JavaFileObject source;
		public boolean alltrue;
	}

	protected Name newNameForCallee(int pos, MethodSymbol msym, boolean useheap) {
		int heap = currentEnv.stateLabel != null ? labelPropertiesStore.get(currentEnv.stateLabel).heapCount : heapCount;
//		if (msym.getTypeParameters().size() != 0) {
//		    System.out.println("NEWNAME " + utils.qualifiedName(msym).replace('.', '_') + " " + msym.asType());
//            System.out.println("TYPEPARAMS " + msym.getTypeParameters());
//            System.out.println("TYPEARGS " + msym.getTypeParameters());
//		    
//		}
		String typeArguments = Utils.join("_", msym.getTypeParameters()); // FIXME - need type arguments, not parameters
		return names
				.fromString(utils.qualifiedName(msym).replace('.', '_') + "$" + typeArguments + (!useheap ? "_" : "_H" + heap + "_") + pos);
	}

	/**
	 * Creates and adds to the current statements axioms for the method given by
	 * msym. Suppose method M(T i) has a spec requires P; ensures Q;. Then we define
	 * a function M(heap,i) and assume (for each postcondition) (\forall T i; P;
	 * (M(heap,i) == Q)) and we define a well-definedness criterion M_WD(heap,i) and
	 * assume (\forall T i; ; (M_WD(heap,i) == P))
	 */
	int depth = 0;

	// Uses current heap (or heap for currentEnv.stateLabel)
	protected void makeAndSaveMethodSymbol(DiagnosticPosition callLocation, MethodSymbol msym,
	                        Type receiverType, Type returnType) {
	    try {
	        int hc = currentEnv.stateLabel == null ? heapCount : labelPropertiesStore.get(currentEnv.stateLabel).heapCount;
	        boolean isFunction = isHeapIndependent(msym);
	        boolean isStatic = utils.isJMLStatic(msym);
	        boolean isPrimitiveType = utils.isJavaOrJmlPrimitiveType(msym.owner.type);

	        Symbol ownerSym = inClassDecl() ? classDecl.sym : methodDecl.sym;
	        JCTree ownerDecl = inClassDecl() ? classDecl : methodDecl;

	        JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(msym);
	        // FIXME - we get calleeSpecs == null when using -no-internalSpecs - shoudl we?
	        int calleeDeclPos = calleeSpecs != null && calleeSpecs.decl != null ? calleeSpecs.decl.pos : methodDecl.pos;
	        DiagnosticPosition calleeDeclDPos = calleeSpecs != null && calleeSpecs.decl != null ? calleeSpecs.decl
	            : methodDecl;
	        JavaFileObject calleeDeclSource = calleeSpecs != null && calleeSpecs.decl != null ? calleeSpecs.decl.sourcefile
	            : methodDecl.sourcefile;

	        //System.out.println("METHSYM " + msym + " " + receiverType + " " + returnType + " " + isStatic + " " + isFunction + " " + isPrimitiveType + " " + useNamesForHeap);
	        //System.out.println("SPECS " + msym.params + " " + (calleeSpecs != null) + " " + (calleeSpecs.decl != null));
	        // Construct the lists of parameters and parameter types for the logical
	        // function representing the pure function
	        ListBuffer<JCVariableDecl> newDecls = new ListBuffer<JCVariableDecl>();
	        ListBuffer<JCExpression> newparamsWithHeap = new ListBuffer<JCExpression>();
	        if (!isFunction && !useNamesForHeap) {
	            newparamsWithHeap.add(convert(treeutils.makeIdent(Position.NOPOS, heapSym)));
	        }
	        JCIdent qthisid = null;
	        JCExpression qthisnn = null;
	        if (!isStatic) {
	            JCVariableDecl newDecl = treeutils.makeVarDef(receiverType, names.fromString("QQHIS"), ownerSym, calleeDeclPos);
	            newDecls.add(newDecl);
	            qthisid = treeutils.makeIdent(callLocation, newDecl.sym);
	            //System.out.println("QTHIS " + qthisid + " " + qthisid.type + " " + qthisid.sym);
	            newparamsWithHeap.add(qthisid);
	            if (!isPrimitiveType) {
	                qthisnn = treeutils.makeNotNull(qthisid.pos, qthisid);
	            }
	        }
	        currentEnv.currentReceiver = qthisid;
	        if (calleeSpecs != null && calleeSpecs.decl != null) {
	            //System.out.println("PARAMS " + calleeSpecs + " " + calleeSpecs.decl.params);
	            for (JCVariableDecl d : calleeSpecs.decl.params) {
	                JCVariableDecl newDecl = treeutils.makeVarDef(d.sym.type, d.name, ownerSym, d.pos);
	                newDecls.add(newDecl);
	                JCIdent id = treeutils.makeIdent(d, newDecl.sym);
	                newparamsWithHeap.add(id);
	            }
	        } else if (msym.params != null) {
	            for (VarSymbol d : msym.params) {
	                JCVariableDecl newDecl = treeutils.makeVarDef(d.type, d.name, ownerSym, ownerDecl.pos);
	                newDecls.add(newDecl);
	                JCIdent id = treeutils.makeIdent(callLocation, newDecl.sym);
	                newparamsWithHeap.add(id);
	            }
	        } else {
	            //	                                int i = 0;
	            //	                                for (VarSymbol d : msym.type.params) {
	            //	                                    JCVariableDecl newDecl = treeutils.makeVarDef(d.type, names.fromString("ZZ" + (i++)), methodDecl.sym, methodDecl.pos);
	            //	                                    newDecls.add(newDecl);
	            //	                                    JCIdent id = treeutils.makeIdent(callLocation,newDecl.sym);
	            //	                                    newparamsWithHeap.add(id);
	            //	                                }
	        }

	        List<JCExpression> newParamsWithHeap = newparamsWithHeap.toList();
	        //System.out.println("NEWPARAMS " + newParamsWithHeap);
	        ListBuffer<Type> newparamtypes = new ListBuffer<Type>();
	        for (JCExpression e : newParamsWithHeap) {
	            newparamtypes.add(e.type);
	        }
	        List<Type> newParamTypes = newparamtypes.toList();
            //System.out.println("NEWPARAMS " + newParamsWithHeap);
            //System.out.println("NEWPARAMTYPES " + newParamTypes);
	        MethodSymbol newsym = makeAndSaveNewMethodName(msym, returnType, isFunction, calleeSpecs, calleeDeclPos, newParamTypes);
	        //System.out.println("LOGICAL METHOD SYM " + newsym + "  FOR " + msym + " " + hc);
	    } catch (Throwable e) {
	        utils.error("jml.internal","EXCEPTION IN makeAndSaveMethodSymbol " + msym);
	        e.printStackTrace(System.out);
	    } finally {
	    }
	}

	// ListBuffer<JCStatement> savedForAxioms = null;
	protected JCBlock addMethodAxioms(DiagnosticPosition callLocation, MethodSymbol msym,
			java.util.List<Pair<MethodSymbol, Type>> overridden, Type receiverType, Type returnType) {
		int hc = currentEnv.stateLabel == null ? heapCount : labelPropertiesStore.get(currentEnv.stateLabel).heapCount;
//		 if (utils.debug() || true) System.out.println("ADDMETHODAXIOMS "+
//		 " " + hc + " " + + heapCount + " " + heapCountForAxioms + " " + msym + " " +
//		 axiomsAdded);
		if (!addAxioms(hc, msym)) {
			return null;
		}
		if (Utils.debug("trans")) System.out.println("ADDING METHODAXIOMS " + msym);
//        if (!receiverType.toString().contains("<") && msym.owner.type.toString().contains("<")
//                                && msym.owner.type.toString().startsWith(receiverType.toString())) {
//            System.out.println("REPLACING " + receiverType + " WITH " + msym.owner.type);  // FIXME - a temporary hack
//            receiverType = msym.owner.type;
//        }
		boolean isFunction = isHeapIndependent(msym);
		JCExpression savedCondition = condition;
		if (isFunction) condition = treeutils.trueLit;
		boolean isStatic = utils.isJMLStatic(msym);
		boolean isPrimitiveType = utils.isJavaOrJmlPrimitiveType(msym.owner.type);

		JCExpression savedResultExpr = resultExpr;
		JCExpression savedCurrentThisExpr = currentEnv.currentReceiver;
		boolean savedSplitExpressions = splitExpressions;
		Map<Object, JCExpression> savedParamActuals = paramActuals_;

		Symbol ownerSym = inClassDecl() ? classDecl.sym : methodDecl.sym;
		JCTree ownerDecl = inClassDecl() ? classDecl : methodDecl;

		splitExpressions = false;
		ListBuffer<JCStatement> check = pushBlock();
		ListBuffer<JCStatement> savedForAxioms = currentStatements;

		JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(msym);
		// FIXME - we get calleeSpecs == null when using -no-internalSpecs - shoudl we?
		int calleeDeclPos = calleeSpecs != null && calleeSpecs.decl != null ? calleeSpecs.decl.pos : methodDecl.pos;
		DiagnosticPosition calleeDeclDPos = calleeSpecs != null && calleeSpecs.decl != null ? calleeSpecs.decl
				: methodDecl;
		JavaFileObject calleeDeclSource = calleeSpecs != null && calleeSpecs.decl != null ? calleeSpecs.decl.sourcefile
				: methodDecl.sourcefile;

		addStat(comment(callLocation, "Axioms for method " + utils.qualifiedMethodSig(msym), null));
		JCExpression combinedPre = null;
		JCExpression falses = null;

		JmlMethodClause clauseToReference = null;
		try {

			// Construct the lists of parameters and parameter types for the logical
			// function representing the pure function
			ListBuffer<JCVariableDecl> newDecls = new ListBuffer<JCVariableDecl>();
			ListBuffer<JCExpression> newparamsWithHeap = new ListBuffer<JCExpression>();
			if (!isFunction && !useNamesForHeap) {
				newparamsWithHeap.add(convert(treeutils.makeIdent(Position.NOPOS, heapSym)));
			}
			JCIdent qthisid = null;
			JCExpression qthisnn = null;
			if (!isStatic) {
				JCVariableDecl newDecl = treeutils.makeVarDef(receiverType, names.fromString("QQHIS"), ownerSym, calleeDeclPos);
				newDecls.add(newDecl);
				qthisid = treeutils.makeIdent(callLocation, newDecl.sym);
				newparamsWithHeap.add(qthisid);
				if (!isPrimitiveType) {
				    qthisnn = treeutils.makeNotNull(qthisid.pos, qthisid);
				}
			}
			currentEnv.currentReceiver = qthisid;
			if (calleeSpecs != null && calleeSpecs.decl != null) {
				var mspecs = specs.getDenestedSpecs(msym);
				if (mspecs != null)
					for (JCVariableDecl d : mspecs.decl.params) {
						JCVariableDecl newDecl = treeutils.makeVarDef(d.sym.type, d.name, ownerSym, d.pos);
						newDecls.add(newDecl);
						JCIdent id = treeutils.makeIdent(d, newDecl.sym);
						newparamsWithHeap.add(id);
					}
			} else if (msym.params != null) {
				for (VarSymbol d : msym.params) {
					JCVariableDecl newDecl = treeutils.makeVarDef(d.type, d.name, ownerSym, ownerDecl.pos);
					newDecls.add(newDecl);
					JCIdent id = treeutils.makeIdent(callLocation, newDecl.sym);
					newparamsWithHeap.add(id);
				}
			} else {
//                int i = 0;
//                for (VarSymbol d : msym.type.params) {
//                    JCVariableDecl newDecl = treeutils.makeVarDef(d.type, names.fromString("ZZ" + (i++)), methodDecl.sym, methodDecl.pos);
//                    newDecls.add(newDecl);
//                    JCIdent id = treeutils.makeIdent(callLocation,newDecl.sym);
//                    newparamsWithHeap.add(id);
//                }
			}

			List<JCExpression> newParamsWithHeap = newparamsWithHeap.toList();
			ListBuffer<Type> newparamtypes = new ListBuffer<Type>();
			for (JCExpression e : newParamsWithHeap) {
				newparamtypes.add(e.type);
			}
			List<Type> newParamTypes = newparamtypes.toList();

			MethodSymbol newsym = makeAndSaveNewMethodName(msym, returnType, isFunction, calleeSpecs, calleeDeclPos, newParamTypes);

			List<JCVariableDecl> newDeclsList = newDecls.toList();

			Name newMethodNameWithHeap = newsym.name;

			// Construct axioms for the type of the result
			if (msym.getReturnType().isPrimitiveOrVoid()) {
				// FIXME - add any range restrictions for primtiive types
			} else if (utils.isJavaOrJmlPrimitiveType(msym.getReturnType())) {
				// These are user-defined primitive types - do nothing
			} else {
				// Result of call is null or the correct type
				JCExpression fcn = treeutils.makeIdent(Position.NOPOS, newsym);
				JCMethodInvocation call = M.at(Position.NOPOS).Apply(List.<JCExpression>nil(), fcn, newParamsWithHeap);
				call.type = newsym.getReturnType();

				JavaFileObject clauseSource = log.currentSourceFile();
				DiagnosticPosition dpos = callLocation;
				// JCExpression e =
				// M.at(dpos).TypeTest(call,M.Type(msym.getReturnType())).setType(syms.booleanType);
				JCExpression e = treeutils.makeInstanceOf(dpos.getPreferredPosition(), call, M.Type(msym.getReturnType()));
				e = treeutils.makeOr(dpos.getPreferredPosition(), treeutils.makeEqNull(dpos.getPreferredPosition(), call), e);
				if (newDeclsList.isEmpty()) {
					// e is just e;
				} else {
					JmlQuantifiedExpr qe = M.at(dpos).JmlQuantifiedExpr(qforallKind, newDeclsList, // FIXME - is it OK
																									// that we use the
																									// same copy of this
																									// array (and so the
																									// same symbols) for
																									// each
																									// postcondition
																									// expression
							// FIXME - if not, we have to conjoin all the ensures
							treeutils.trueLit, e);
					qe.triggers = List.<JCExpression>of(call);
					e = qe;
					e.type = syms.booleanType;
				}
				ListBuffer<JCStatement> ch = pushBlock();
				addAssume(dpos, Label.IMPLICIT_ASSUME, e, dpos, clauseSource);
				savedForAxioms.add(popBlock(callLocation, ch));

			}

			// Now go through each spec case for each overridden method and construct axioms
			// for each ensures clause
			for (Pair<MethodSymbol, Type> pair : overridden) {
				MethodSymbol mpsym = pair.first;
				Type classType = pair.second;
				typevarMapping = typemapping(classType, mpsym, null, null);
				// typevarMapping = typemapping(apply, typevarMapping);

				// This initial logic must match that above for preconditions
				calleeSpecs = specs.getDenestedSpecs(mpsym);
				if (!specs.statusOK(mpsym)) continue; // FIXME - abort
				if (calleeSpecs == null) continue; // FIXME - not sure about this
				if (calleeSpecs.decl == null && !mpsym.owner.isEnum() && !isStatic && (mpsym.name != names.values)) continue; // FIXME - only values?

				// Now map the formals as used in the overridden method to
				// identifiers used in the axioms being constructed
				var pmap = paramActuals_ = new HashMap<Object, JCExpression>();
				Iterator<JCVariableDecl> iter = newDeclsList.iterator();
				currentEnv.currentReceiver = isStatic ? null : M.at(calleeSpecs.decl).Ident(iter.next().sym);
				// FIXME - calleeSpecs.decl is null for implicitly generated methods (like those
				// from Enum)
				// FIXME - but the following seems correct only for non-heap-dependent functions
				// that have no parameters
				if (calleeSpecs.decl != null) {
					for (JCVariableDecl d : calleeSpecs.decl.params) {
						JCIdent id = treeutils.makeIdent(d, iter.next().sym);
						pmap.put(d.sym, id);
					}
				}

				// Create an instance of a call of the new method, to be used in place of
				// \result in translating the method specs
				JCExpression fcn = treeutils.makeIdent(Position.NOPOS, newsym);
				JCMethodInvocation call = M.at(Position.NOPOS).Apply(List.<JCExpression>nil(), fcn, newParamsWithHeap);
				call.type = newsym.getReturnType();
				resultExpr = call;

				ListBuffer<JCStatement> ignore = currentStatements = new ListBuffer<JCStatement>();
				// We capture and ignore the assertions that come out of
				// transforming the pre and post conditions of the callee.
				// These are checked when the method is verified.
				// Also they would need to be captured and proved in the
				// the context of a quantification.

				JCExpression savedElseExpression = elseExpression;
				elseExpression = treeutils.falseLit;
				for (JmlSpecificationCase cs : calleeSpecs.cases) {
					//if (!utils.jmlvisible(mpsym, classDecl.sym, mpsym.owner, cs.modifiers.flags, methodDecl.mods.flags)) continue;
	                if (!doSpecificationCase(methodDecl, msym, mpsym, cs)) continue;
					// if (!utils.visible(classDecl.sym, mpsym.owner, cs.modifiers.flags/*,
					// methodDecl.mods.flags*/)) continue;
					//if (cs.token == exceptionalBehaviorClause) continue;
					// FIXME - will need to add OLD and FORALL clauses in here
					//if (cs.code && mpsym.owner != msym.owner) continue;

					JCExpression pre = qthisnn != null ? qthisnn : treeutils.trueLit;
					if (isPrimitiveType) {
						pre = treeutils.trueLit;
					} else if (qthisid != null && classType != syms.objectType) {
						// FIXME - not sure this is needed and it makes valid assertions harder to prove
						if (true || !types.isSubtype(receiverType, classType)) {
							pre = treeutils.makeInstanceOf(cs.pos, qthisid, classType);
							pre = copy(pre);
						}
						pre = treeutils.makeAnd(cs.pos, treeutils.makeNotNull(cs.pos, copy(qthisid)), pre);
					} else {
						pre = copy(pre);
						pre.pos = cs.pos;
					}
					try {
						JmlMethodClause mcc = null; // Remember the first requires clause in the specification case
						currentStatements = ignore;
						for (JmlMethodClause clause : cs.clauses) {
							try {
								if (clause.clauseKind == requiresClauseKind) {
									if (mcc == null)
										mcc = clause;
									JmlMethodClauseExpr mce = (JmlMethodClauseExpr) clause;
									// convertJML will use paramActuals
									JCExpression e = convertNoSplit(mce.expression, pre, false); // Might throw an
																									// exception
									pre = treeutils.makeAndSimp(pre.pos, pre, e);
								}
								if (clause.clauseKind == MethodDeclClauseExtension.oldClause) {
									notImplemented(clause,
											"method axioms with old clauses: method " + msym.toString(),
											clause.source());
								}
							} catch (JmlNotImplementedException e) {
								notImplemented("requires clause containing ", e, clause.source());
								pre = treeutils.falseLit;
								break;
							}
						}
						if (mcc != null) clauseToReference = mcc;
					} catch (NoModelMethod e) {
						pre = treeutils.falseLit;
					} finally {
						currentStatements = savedForAxioms;
					}

					combinedPre = treeutils.makeOrSimp(pre.pos, combinedPre, copy(pre));
					if (treeutils.isFalseLit(pre)) continue; // Don't bother with postconditions if corresponding precondition is explicitly false

					for (JmlMethodClause clause : cs.clauses) {
						DiagnosticPosition dpos = clause;
						// FIXME - clause.sourceFile should never be null?
						JavaFileObject clauseSource = clause.sourcefile == null ? log.currentSourceFile()
								: clause.sourcefile;
						if (clause.clauseKind == MethodExprClauseExtensions.ensuresClauseKind) {
							JmlMethodClauseExpr enclause = (JmlMethodClauseExpr) clause;
							// localVariables.put(heapSym,heapSym); // FIXME - explain

							try {
								currentStatements = ignore;
								// addStat(comment(clause));
								// Note - convertJML uses resultExpr and currentEnv.currentReceiver and paramActuals
								JCExpression e = convertNoSplit(enclause.expression, condition, false);
								//if (msym.toString().contains("empty")) System.out.println("MAX FOR " + enclause + " IS " + e);
								if (treeutils.isFalseLit(e)) {
									JCExpression not = treeutils.makeNot(pre.pos, copy(pre));
									falses = falses == null ? not : treeutils.makeAndSimp(falses.pos, falses, not);
									continue;
								}
								elseExpression = treeutils.makeBitOr(cs.pos, elseExpression, pre);
								if (newDeclsList.isEmpty()) {
									e = treeutils.makeImplies(e.pos, copy(pre), e);
								} else {
									JmlQuantifiedExpr qe = M.at(dpos).JmlQuantifiedExpr(qforallKind, newDeclsList, // FIXME
																													// -
																													// is
																													// it
																													// OK
																													// that
																													// we
																													// use
																													// the
																													// same
																													// copy
																													// of
																													// this
																													// array
																													// (and
																													// so
																													// the
																													// same
																													// symbols)
																													// for
																													// each
																													// postcondition
																													// expression
											// FIXME - if not, we have to conjoin all the ensures
											copy(pre), e);
									qe.triggers = List.<JCExpression>of(call);
									e = qe;
									e.type = syms.booleanType;
								}
								currentStatements = savedForAxioms;
								addAssume(dpos, Label.IMPLICIT_ASSUME, e, dpos, clauseSource);
			                    //if (msym.toString().contains("empty")) System.out.println("METHOD AXIOM-A " + msym + " " + e);
							} catch (NoModelMethod e) {
								// Just skip this ensures clause
							} catch (JmlNotImplementedException e) {
								notImplemented(clause.clauseKind.keyword() + " clause containing ", e, clause.source());
							} finally {
								currentStatements = savedForAxioms;
								// localVariables.remove(heapSym);
							}
						}
					}
				}
				//paramActuals = null;
				elseExpression = savedElseExpression;
			}
			if (falses != null) {
				combinedPre = combinedPre != null ? treeutils.makeAnd(combinedPre.pos, combinedPre, falses) : falses;
			}

			currentStatements = savedForAxioms;
			if (combinedPre == null || treeutils.isTrueLit(combinedPre)) {
				WellDefined info = new WellDefined();
				info.alltrue = true;
				info.wellDefinedExpression = treeutils.trueLit;
				wellDefinedCheck.put(msym, info);
			} else {
				MethodSymbol methodDefinedSym = treeutils.makeMethodSym(methodDecl.mods,
						names.fromString("_JML_METHODEF__" + newMethodNameWithHeap.toString()), syms.booleanType,
						classDecl.sym, newParamTypes);
				JCExpression methodDefinedFcn = M.at(calleeDeclPos).Ident(methodDefinedSym);
				JCMethodInvocation wellDefinedCall = M.at(calleeDeclPos).Apply(List.<JCExpression>nil(),
						methodDefinedFcn, newParamsWithHeap);
				wellDefinedCall.type = syms.booleanType;
				WellDefined info = new WellDefined();
				info.sym = methodDefinedSym;
				info.wellDefinedExpression = combinedPre;
//                info.pos = clauseToReference != null ? clauseToReference : methodDecl;
//                info.source = clauseToReference != null ? clauseToReference.source() : methodDecl.source();
				info.pos = calleeDeclDPos;
				info.source = calleeDeclSource;
				info.alltrue = false;
				wellDefinedCheck.put(msym, info);

				if (newDeclsList.isEmpty()) {
					addAssume(clauseToReference, Label.IMPLICIT_ASSUME, combinedPre);
				} else {
					JCExpression ei = null;
//                    if (!qthisid.sym.type.isPrimitive()) {
//                        ei = treeutils.makeInstanceOf(qthisid.pos,convertCopy(qthisid),qthisid.sym.type);
//                    }

					JmlQuantifiedExpr e = M.at(calleeDeclPos).JmlQuantifiedExpr(qforallKind, newDeclsList, ei,
							treeutils.makeEquality(calleeDeclPos, wellDefinedCall, combinedPre));
					e.triggers = List.<JCExpression>of(wellDefinedCall);
					e.type = syms.booleanType;
					addAssume(clauseToReference, useNamesForHeap ? Label.METHOD_DEFINITION : Label.IMPLICIT_ASSUME, e);
					if (msym.toString().contains("empty")) System.out.println("METHOD AXIOM " + msym + " " + e);
				}
			}
		} catch (Exception e) { // FIXME - intentional aborts should be passed alont
			utils.unexpectedException(e, "ADD METHOD AXIOMS");
		} finally {
			resultExpr = savedResultExpr;
			currentEnv.currentReceiver = savedCurrentThisExpr;
			paramActuals_ = savedParamActuals;
			splitExpressions = savedSplitExpressions;
			condition = savedCondition;
			depth--;
			if (depth == 0)
				savedForAxioms = null;
		}
		JCBlock bl = popBlock(null, check);
//		if (collectedAxioms != null) {
//			collectedAxioms.add(bl);
//			bl = null;
//		}
		currentEnv.heap.methodAxiomsBlock.stats = currentEnv.heap.methodAxiomsBlock.stats.append(bl);
		return null;
	}

	public boolean isHeapIndependent(MethodSymbol msym) {
		boolean isFunction = attr.isHeapIndependent(msym);
		if (msym.owner.isEnum()
				&& (msym.name == names.values || msym.name == names.valueOf || msym.name == names.ordinal))
			isFunction = true; // FIXME - make these modifiers at the point of declaration
		return isFunction;
	}

	Map<Integer, Map<Symbol, MethodSymbol>> heapMethods = new HashMap<>();

    public MethodSymbol getNewMethodSymbol(MethodSymbol msym) {
        Integer hc = currentEnv.stateLabel == null ? heapCount : labelPropertiesStore.get(currentEnv.stateLabel).heapCount;
        return getNewMethodSymbol(msym, hc);
    }

    public MethodSymbol getNewMethodSymbol(MethodSymbol msym, int hc) {
        Map<Symbol, MethodSymbol> mm = heapMethods.get(hc);
        if (mm == null) {
            heapMethods.put(hc, mm = new HashMap<Symbol, MethodSymbol>());
            return null;
        }
        MethodSymbol ms = mm.get(msym);
        if (Utils.debug("trans"))
            System.out.println("GETMETHODNAME " + currentEnv.stateLabel + " " + hc + " " + msym + " " + ms);
        return ms;
    }

	public MethodSymbol makeAndSaveNewMethodName(MethodSymbol msym, Type returnType, boolean isFunction,
			JmlMethodSpecs calleeSpecs, int calleeDeclPos, List<Type> newParamTypes) {

		Integer hc = currentEnv.stateLabel == null ? heapCount : labelPropertiesStore.get(currentEnv.stateLabel).heapCount;
		Map<Symbol, MethodSymbol> mm = heapMethods.get(hc);
		if (mm == null) {
			heapMethods.put(hc, mm = new HashMap<Symbol, MethodSymbol>());
		}
		MethodSymbol newsym = mm.get(msym);
		if (newsym != null) return newsym;

       // Create the symbol for the new method
		//System.out.println("NEWPARAMTYPES " + newParamTypes);
		Name newMethodNameWithHeap = newNameForCallee(calleeDeclPos, msym, 
				(useNamesForHeap && !isFunction && !msym.owner.toString().startsWith("org.jmlspecs.lang.")));
		JCModifiers newmods;
		if (inClassDecl()) {
			// Declaration within a class
			newmods = M.at(calleeSpecs.decl.mods.pos).Modifiers(calleeSpecs.decl.mods.flags | Flags.STATIC,
					calleeSpecs.decl.mods.annotations); // Note: annotations not duplicated
			newsym = treeutils.makeMethodSym(newmods, newMethodNameWithHeap, returnType, classDecl.sym, newParamTypes);
		} else {
			// Declaration within a method body
			newmods = M.at(methodDecl.mods.pos).Modifiers(methodDecl.mods.flags | Flags.STATIC,
					methodDecl.mods.annotations); // Note: annotations not duplicated
			newsym = treeutils.makeMethodSym(newmods, newMethodNameWithHeap, returnType,
					(TypeSymbol) methodDecl.sym.owner, newParamTypes);
		}
		// Save the symbol
		mm.put(msym, newsym);
		if (Utils.debug("trans"))
			System.out.println("NEW METHOD NAME " + currentEnv.stateLabel + " " + hc + " " + msym.owner + " " + msym + " " + newsym + " " + returnType + " " + newsym.getReturnType() + " " + (newsym.type instanceof Type.MethodType mt ? mt.getReturnType() : "---") + " " + newmods);
		return newsym;
	}

	public JCExpression simplifySubset(JCExpression that, TranslationEnv targetEnv, boolean isSmallerConverted) {
		if (!(that instanceof JmlMethodInvocation mi && mi.kind == LocsetExtensions.subsetKind)) {
			// ERROR
			return null;
		}
		JCExpression smaller = mi.args.head;
		JCExpression bigger = mi.args.tail.head;
		return simplifySubset(smaller, bigger, targetEnv, isSmallerConverted);
	}

	public JCExpression simplifySubset(JCExpression smaller, JCExpression bigger, TranslationEnv targetEnv,
			boolean isSmallerConverted) {
		if (smaller instanceof JmlStoreRef sr) {
	        //System.out.println("SMALLER " + sr);
			if (sr.isEverything) {
				// \everything
				return containsEverything(smaller, targetEnv, bigger);

			} else if (sr.local != null) {
				// local variable
				return containsLocal(smaller, targetEnv, sr.local, bigger);

			} else if (sr.expression != null) {
				// general expression
				if (sr.expression instanceof JmlMethodInvocation mi) {
					if (mi.kind == LocsetExtensions.unionKind) {
						JCExpression e = treeutils.makeBooleanLiteral(sr.expression, false);
						for (JCExpression arg : mi.args) {
							var ee = simplifySubset(arg, bigger, targetEnv, isSmallerConverted);
							e = treeutils.makeAndSimp(arg, e, ee);
						}
						return e;
					} else if (mi.kind == oldKind) {
						var newenv = targetEnv.newEnvCopy();
						newenv.stateLabel = mi.args.size() == 1 ? null : ((JCIdent) mi.args.get(1)).name;
						return simplifySubset(smaller, mi.args.head, newenv, isSmallerConverted);
					}
				}
				{
					JCExpression e = containsEverything(smaller, targetEnv, bigger);
					if (treeutils.isTrueLit(e))
						return e;
					// FIXME - unsimplifiable
					return treeutils.makeSubset(smaller, sr, treeutils.makeOld(smaller, bigger, targetEnv.stateLabel));
				}

			} else if (sr.receiver != null && sr.range != null) {
				// array elements
				JCExpression ft = freshTest(smaller, sr.receiver, targetEnv.allocCount);
//				System.out.println("ARRAYELE " + sr + " " + sr.receiver + " " + sr.receiver.type + " " + allocCounter + " " + targetEnv.allocCount + " " + ft);
				ft = convertJML(ft); // Convert in current (smaller) environment
//				System.out.println("CONVERTED FT " + ft);
				JCExpression ok = containsArray(smaller, targetEnv, isSmallerConverted, sr.receiver, sr.range, bigger);
				return ft == null ? ok : treeutils.makeOrSimp(smaller,  ft,  ok);
			} else {
			    JCExpression ft = null;
			    if (sr.receiver != null) {
	                JCExpression nn = treeutils.makeNotNull(sr.receiver,  sr.receiver);
	                ft = freshTest(smaller, sr.receiver, targetEnv.allocCount);
	                ft = treeutils.makeImplies(sr.receiver, nn, ft);
	                ft = convertJML(ft); // Convert in current envirnment
			    }
				
				// fields
				JCExpression e = containsField(smaller, targetEnv, isSmallerConverted, sr.receiver, sr.field, bigger);
				return ft == null ? e : treeutils.makeOr(smaller, ft, e);
			}
		} else {
			// ERROR
			return treeutils.makeBooleanLiteral(smaller.getPreferredPosition(), false);
		}
	}
	
	public JCExpression simplifyNonDisjoint(DiagnosticPosition pos, java.util.List<StoreRefGroup> reads, java.util.List<StoreRefGroup> writes) {
	    JCExpression tLit = treeutils.makeBooleanLiteral(pos, true);
	    JCExpression fLit = treeutils.makeBooleanLiteral(pos, false);
	    JCExpression hasIntersection = fLit;
	    for (var r: reads) {
	        JCExpression rguard = r.guard;
	        for (var ritem: r.items) {
	            for (var w: writes) {
	                JCExpression wguard = w.guard;
	                var guard = treeutils.makeAndSimp(pos, rguard, wguard);
	                JCExpression ex = fLit;
	                for (var witem: w.items) {
	                    //System.out.println(" ITEMS " + ritem + " " + ritem.kind + " " + witem + " " + witem.kind);
	                    var e = switch (ritem.kind) {
	                      case NOTHING -> fLit;
                          case EVERYTHING -> 
                            switch (witem.kind) {
                                case NOTHING -> fLit;
                                case EXPRESSION -> tLit; // FIXME - except if expression evaluates to empty set
                                default -> tLit;
                            };
                          case INSTANCE_FIELD -> 
                            switch (witem.kind) {
                                case NOTHING -> fLit;
                                case INSTANCE_FIELD -> // FIXME - what if datagroups overlap but one is not in the other
                                    !(isContainedIn(ritem.field, witem.field)||isContainedIn(witem.field,ritem.field)) ? 
                                        fLit : treeutils.makeEqObject(pos, ritem.receiver, witem.receiver);
                                case EXPRESSION -> tLit; // FIXME - depends what expression evaluates to
                                default -> tLit;
                            };
                          case STATIC_FIELD -> 
                            switch (witem.kind) {
                                case NOTHING -> fLit;
                                case STATIC_FIELD ->  // FIXME - what if datagroups overlap but one is not in the other
                                    !(isContainedIn(ritem.field, witem.field)||isContainedIn(witem.field,ritem.field)) ? fLit : tLit;
                                case EXPRESSION -> tLit; // FIXME - depends what expression evaluates to
                                default -> tLit;
                            };
	                      case ARRAY_ELEMENTS -> 
	                        switch (witem.kind) {
	                            case NOTHING -> fLit;
	                            case ARRAY_ELEMENTS -> {
	                                JCExpression sameArray = treeutils.makeEqObject(pos, ritem.receiver, witem.receiver);
                                    JCExpression rlo = ritem.range.lo;
                                    if (rlo == null) rlo = treeutils.makeIntLiteral(pos.getPreferredPosition(), 0);
                                    JCExpression wlo = witem.range.lo;
                                    if (wlo == null) wlo = treeutils.makeIntLiteral(pos.getPreferredPosition(), 0);
                                    JCExpression rhi = ritem.range.hi;
                                    var e1 = (rhi != null) ? treeutils.makeBinary(pos, Tag.LE, wlo, rhi)
                                                           : treeutils.makeBinary(pos, Tag.LT, wlo, treeutils.makeLength(pos,ritem.receiver));
                                    JCExpression whi = witem.range.hi;
                                    var e2 = (whi == null) ? treeutils.makeBinary(pos, Tag.LE, rlo, whi)
                                                           : treeutils.makeBinary(pos, Tag.LT, rlo, treeutils.makeLength(pos,witem.receiver));
	                                JCExpression overlap = treeutils.makeAnd(pos,e1,e2);
	                                yield treeutils.makeAnd(pos, sameArray, overlap);
	                            }
	                            default -> tLit;
	                        };
	                      case EXPRESSION -> 
	                        switch (witem.kind) {
	                            case NOTHING -> fLit;
	                            case EVERYTHING -> tLit; // FIXME - unless expression evaluates to empty set
	                            case EXPRESSION -> tLit; // FIXME - needs work
	                            default -> tLit; // FIXME - depends what expression evaluates to
	                        };
	                      case LOCAL -> fLit; // FIXME - should not have a local in a readsList
	                    };
	                    //System.out.println("  CONDITION " + e);
	                    ex = treeutils.makeOrSimp(pos, ex, e);
	                }
                    hasIntersection = treeutils.makeOrSimp(pos, hasIntersection, treeutils.makeImpliesSimp(pos, guard, ex));
	            }
	        }
	    }
	    return hasIntersection;
	}

    public JCExpression simplifyNonDisjoint(JCExpression smaller, JCExpression bigger, TranslationEnv targetEnv,
                            boolean isSmallerConverted) {
        int pos = smaller.pos; // FIXME - should be the whole experession
        if (smaller instanceof JmlStoreRef sr) {
            //System.out.println("SMALLER " + sr);
            if (sr.isNothing()) return treeutils.makeBooleanLiteral(pos, false);
            if (bigger instanceof JmlStoreRef srr ) {
                if (srr.isNothing()) return treeutils.makeBooleanLiteral(pos, false);
                if (srr.isEverything()) return treeutils.makeBooleanLiteral(pos, true);
            }
            if (sr.isEverything()) return treeutils.makeBooleanLiteral(pos, true);
            if (sr.local != null) {
                // local variable
                return containsLocal(smaller, targetEnv, sr.local, bigger);

            } else if (sr.expression != null) {
                // general expression
                if (sr.expression instanceof JmlMethodInvocation mi) {
                    if (mi.kind == LocsetExtensions.unionKind) {
                        JCExpression e = treeutils.makeBooleanLiteral(sr.expression, false);
                        for (JCExpression arg : mi.args) {
                            var ee = simplifyNonDisjoint(arg, bigger, targetEnv, isSmallerConverted);
                            e = treeutils.makeOrSimp(arg, e, ee);
                        }
                        return e;
                    } else if (mi.kind == oldKind) {
                        var newenv = targetEnv.newEnvCopy();
                        newenv.stateLabel = mi.args.size() == 1 ? null : ((JCIdent) mi.args.get(1)).name;
                        return simplifyNonDisjoint(smaller, mi.args.head, newenv, isSmallerConverted);
                    }
                }
                {
                    JCExpression e = containsEverything(smaller, targetEnv, bigger);
                    if (treeutils.isTrueLit(e))
                        return e;
                    // FIXME - unsimplifiable  -- at least make a disjoint
                    return treeutils.makeSubset(smaller, sr, treeutils.makeOld(smaller, bigger, targetEnv.stateLabel));
                }

            } else if (sr.receiver != null && sr.range != null) {
                // array elements
                JCExpression ft = null;
//                ft = freshTest(smaller, sr.receiver, targetEnv.allocCount);
//                //                              System.out.println("ARRAYELE " + sr + " " + sr.receiver + " " + sr.receiver.type + " " + allocCounter + " " + targetEnv.allocCount + " " + ft);
//                ft = convertJML(ft); // Convert in current (smaller) environment
//                //                              System.out.println("CONVERTED FT " + ft);
                JCExpression ok = containsArray(smaller, targetEnv, isSmallerConverted, sr.receiver, sr.range, bigger);
                return ft == null ? ok : treeutils.makeOr(smaller,  ft,  ok);
            } else {
                JCExpression ft = null;
//                JCExpression ft = sr.receiver == null ? null : freshTest(smaller, sr.receiver, targetEnv.allocCount);
//                ft = convertJML(ft); // Convert in current envirnment  // FIXME - already converted???

                // fields
                JCExpression e = containsField(smaller, targetEnv, isSmallerConverted, sr.receiver, sr.field, bigger);
                //System.out.println("CHECKED " + sr.field + " VS " + bigger + " " + e);
                return ft == null ? e : treeutils.makeOr(smaller, ft, e);
            }
        } else {
            if (smaller instanceof JmlMethodInvocation mi) {
                if (mi.kind == LocsetExtensions.unionKind) {
                    JCExpression e = treeutils.makeBooleanLiteral(smaller, false);
                    for (JCExpression arg : mi.args) {
                        var ee = simplifyNonDisjoint(arg, bigger, targetEnv, isSmallerConverted);
                        e = treeutils.makeOrSimp(arg, e, ee);
                    }
                    return e;
                } else if (mi.kind == oldKind) {
                    var newenv = targetEnv.newEnvCopy();
                    newenv.stateLabel = mi.args.size() == 1 ? null : ((JCIdent) mi.args.get(1)).name;
                    return simplifyNonDisjoint(smaller, mi.args.head, newenv, isSmallerConverted);
                }
            }
            {
                JCExpression e = containsEverything(smaller, targetEnv, bigger);
                if (treeutils.isTrueLit(e)) return e;
                // FIXME - unsimplifiable  -- at least make a disjoint
                return treeutils.makeSubset(smaller, smaller, treeutils.makeOld(smaller, bigger, targetEnv.stateLabel));
            }
        }
    }

	public JCExpression expand(DiagnosticPosition pos, TranslationEnv targetEnv, JCExpression srexpr,
			java.util.function.Function<JCExpression, JCExpression> a) {
		if (srexpr instanceof JmlMethodInvocation mi && mi.kind == LocsetExtensions.unionKind) {
			JCExpression e = treeutils.makeBooleanLiteral(pos, false);
			for (JCExpression ee : mi.args) {
				var eee = a.apply(ee);
				e = treeutils.makeOrSimp(pos.getPreferredPosition(), e, eee);
			}
			return e;
		} else if (srexpr instanceof JmlMethodInvocation mi && mi.kind == oldKind) {
			var newenv = targetEnv.newEnvCopy();
			newenv.stateLabel = ((JCIdent) mi.args.get(1)).name;
			return expand(pos, newenv, mi.args.head, a);
		} else {
			// ERROR
			return treeutils.makeBooleanLiteral(pos, false);
		}
	}

	public JCExpression containsEverything(DiagnosticPosition pos, TranslationEnv targetEnv, JCExpression bigger) {
		if (bigger instanceof JmlStoreRef sr) {
			if (sr.expression != null) {
				return expand(pos, targetEnv, sr.expression, s -> containsEverything(pos, targetEnv, s));
			} else {
				return treeutils.makeBooleanLiteral(pos, sr.isEverything);
			}
		} else {
			// ERROR
			return treeutils.makeBooleanLiteral(pos, false);
		}
	}

	public JCExpression containsLocal(DiagnosticPosition pos, TranslationEnv targetEnv, Symbol vsym,
			JCExpression bigger) {
		if (bigger instanceof JmlStoreRef sr) {
			// System.out.println("LOCAL " + vsym + " " + sr.isEverything + " " +
			// sr.expression + " " + sr.local + " " + targetEnv.label + " " +
			// vsym.owner.getClass());
			if (sr.isEverything) {
				return treeutils.makeBooleanLiteral(pos, true);
			} else if (targetEnv.stateLabel == attr.preLabel) {
				// The target is in the pre-state and we have a local variable
				return treeutils.makeBooleanLiteral(pos, true);
			} else if (sr.expression != null) {
				return expand(pos, targetEnv, sr.expression, s -> containsLocal(pos, targetEnv, vsym, s));
			} else {
				return treeutils.makeBooleanLiteral(pos, sr.local == vsym);
			}
		} else {
			// ERROR
			return treeutils.makeBooleanLiteral(pos, false);
		}
	}

	public JCExpression containsField(DiagnosticPosition pos, TranslationEnv targetEnv, boolean isSmallerConverted,
			JCExpression receiver, VarSymbol field, JCExpression bigger) {
		if (bigger instanceof JmlStoreRef sr) {
			if (sr.isEverything) {
				return treeutils.makeBooleanLiteral(pos, true);
			} else if (sr.field != null) {
				// If all model fields were expanded we could just compare field == sr.field, but model field
			    // definitions can be recursive, so we can't always do that expansion
			    //System.out.println("FIELDS " + field + " VS " + sr.field);
				if (field == sr.field || (field != null && isContainedIn(field, sr.field))) {
					var ee = utils.isJMLStatic(field) ? treeutils.makeBooleanLiteral(pos, true)
							: treeutils.makeEqObject(pos.getPreferredPosition(),
									isSmallerConverted ? receiver : convertJML(receiver),
											convertJML(sr.receiver, targetEnv));
					return ee;
				} else {
				    // Now check all the maps clauses   // FIXME !!!
				    
					return treeutils.makeBooleanLiteral(pos, false);
				}
			} else if (sr.local != null) {
				if (sr.local.owner instanceof TypeSymbol) {
					if (sr.local.isStatic()) {
						// static field
						return treeutils.makeBooleanLiteral(pos, sr.local == field);
					} else {
						// A field with implicit this as receiver
						JCExpression e = treeutils.makeBooleanLiteral(pos, true);
						var v = field;
						{
							if (sr.local == v) {
								var ee = treeutils.makeEqObject(pos.getPreferredPosition(),
										isSmallerConverted ? receiver : convertJML(receiver), targetEnv.currentReceiver);
								e = treeutils.makeAnd(pos, e, ee);
							} else {
								return treeutils.makeBooleanLiteral(pos, false);
							}
						}
						return e;
					}
				} else {
					// An actual local field FIXME - in the target now
					return treeutils.makeBooleanLiteral(pos, false);
				}
			} else if (sr.expression != null) {
			    //System.out.println("BIGGER IS " + sr.expression);
				return expand(pos, targetEnv, sr.expression,
						s -> containsField(pos, targetEnv, isSmallerConverted, receiver, field, s));
			} else {
				return treeutils.makeBooleanLiteral(pos, false);
			}
		} else {
            //System.out.println("BIGGER-F IS " + bigger);
            return expand(pos, targetEnv, bigger,
                    s -> containsField(pos, targetEnv, isSmallerConverted, receiver, field, s));
		}
	}

	public JCExpression containsArray(DiagnosticPosition pos, TranslationEnv targetEnv, boolean isSmallerConverted,
			JCExpression receiver, JmlRange range, JCExpression bigger) {
		if (bigger instanceof JmlStoreRef sr) {
			// System.out.println("CARR " + receiver + " " + range + " " + bigger + " " +
			// targetEnv.label);
			if (sr.isEverything) {
				return treeutils.makeBooleanLiteral(pos, true);
			} else if (sr.receiver != null && sr.range != null) {
				var e1 = treeutils.makeEqObject(pos.getPreferredPosition(),
						isSmallerConverted ? receiver : convertJML(receiver), convertJML(sr.receiver, targetEnv));
				var e2 = treeutils.makeBinary(pos, JCTree.Tag.LE, convertJML(sr.range.lo, targetEnv),
						isSmallerConverted ? range.lo : convertJML(range.lo));
				var e3 = treeutils.makeBinary(pos, JCTree.Tag.LE, isSmallerConverted ? range.hi : convertJML(range.hi),
						convertJML(sr.range.hi, targetEnv));
				return treeutils.makeAnd(pos, e1, treeutils.makeAnd(pos, e2, e3));
			} else if (sr.field != null) {
				//System.out.println("CARR " + receiver + " " + range + " " + sr + " : " + sr.modelFieldContents);
				JCExpression r = treeutils.makeBooleanLiteral(pos, false);
				//System.out.println("CARR-Z " + sr + " " + r);
				return r;
			} else if (sr.expression != null) {
				return expand(pos, targetEnv, sr.expression,
						s -> containsArray(pos, targetEnv, isSmallerConverted, receiver, range, s));
			} else {
				return treeutils.makeBooleanLiteral(pos, false);
			}
		} else {
            return expand(pos, targetEnv, bigger,
                s -> containsArray(pos, targetEnv, isSmallerConverted, receiver, range, s));
		}
	}
	
	public List<JmlStoreRef> collectModelFieldContents(DiagnosticPosition pos, ClassSymbol rootClass, JCExpression receiver, VarSymbol modelField) {
		//System.out.println("COLLECTING MODEL FIELD CONTENTS " + modelField.owner + " " + modelField + " " + rootClass);
		ListBuffer<JmlStoreRef> maps = new ListBuffer<>();
		for (Type t : parents(rootClass.type, false)) {
			if (modelField == null) {
				// wild-card field -- include all fields
				for (Symbol s : t.tsym.getEnclosedElements()) {
					if (s instanceof VarSymbol vs && !vs.isFinal() && utils.isJMLStatic(vs) == (receiver == null)) {
						JmlStoreRef sr = M.at(pos).JmlStoreRef(false,null,null,receiver,null,vs,null);
						maps.add(sr);
					}
				}
			} else {
				//System.out.println("   SEARCHING " + t + " " + jmltypes.isSubtype(t, modelField.owner.type));
				if (jmltypes.isSubtype(t, modelField.owner.type)) {
					for (Symbol s : t.tsym.getEnclosedElements()) {
						//System.out.println("   SYMBOL " + t + " " + s + " " + s.getClass());
						if (s instanceof VarSymbol vs) {
							JmlSpecs.FieldSpecs fs = specs.getAttrSpecs(vs);
							if (fs != null) for (var cl : fs.list) {
								if (cl instanceof JmlTypeClauseMaps m) {
									//System.out.println("MAPS CLAUSE " + t + " " + s + " " + cl);
									for (JmlGroupName g : m.list) {
										if (isContainedIn(g.sym, modelField)) {
										    m.expressions.forEach( e->
											  { var srs = makeJmlStoreRef(e, e, rootClass, false);
											    maps.addAll(srs); });
										}
									}
								}
								if (cl instanceof JmlTypeClauseIn m && !vs.isFinal()) {
									//System.out.println("IN CLAUSE " + t + " " + s + " " + cl);
									for (JmlGroupName g : m.list) {
										if (isContainedIn(g.sym, modelField)) {
											JmlStoreRef sr = M.at(cl).JmlStoreRef(false,null,null,receiver,null,vs,null);
											maps.add(sr);
										}
									}
								}
							}

						}
					}
				}
			}
		}
		//System.out.println("COLLECTED " + modelField + " : " + maps);
		return maps.toList();
	}

	public /* @ nullable */ java.util.List<JmlStatementExpr> getWellDefinedAsserts(JCExpression expr,
			Map<Object, JCExpression> replacements) {
		WellDefinedCheck check = new WellDefinedCheck(replacements);
		return expr.accept(check, null);
	}

	public class WellDefinedCheck extends JmlExpressionVisitor<java.util.List<JmlStatementExpr>, Void> {

		Map<Object, JCExpression> replacements;
		JmlTreeSubstitute sub;

		public WellDefinedCheck(Map<Object, JCExpression> replacements) {
			this.replacements = replacements;
			sub = new JmlTreeSubstitute(context, M, replacements);
		}

		/* @ nullable */ java.util.List<JmlStatementExpr> combine(/* @ nullable */ java.util.List<JmlStatementExpr> a,
				/* @ nullable */ java.util.List<JmlStatementExpr> b) {
			if (a == null)
				return b;
			if (b == null)
				return a;
			a.addAll(b);
			return a;
		}

		/* @ nullable */ java.util.List<JmlStatementExpr> combine(/* @ nullable */ java.util.List<JmlStatementExpr> a,
				JmlStatementExpr b) {
			if (a == null)
				a = new LinkedList<JmlStatementExpr>();
			a.add(b);
			return a;
		}

		/* @ nullable */ java.util.List<JmlStatementExpr> prepend(JCExpression cond,
				/* @ nullable */ java.util.List<JmlStatementExpr> list) {
			for (JmlStatementExpr a : list) {
				a.expression = treeutils.makeImplies(a.expression.pos, cond, a.expression);
			}
			return list;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlStoreRef(JmlStoreRef node, Void p) {
			/* @ nullable */ java.util.List<JmlStatementExpr> e = null, ee = null, eee = null;
			if (node.expression != null)
				e = node.expression.accept(this, p);
			if (node.receiver != null) {
				var ex = treeutils.makeNotNull(node.receiver, node.receiver);
				ee = ex.accept(this, p);
			}
			if (node.range != null) {
				JCExpression ex = null;
				if (node.range.lo != null
						&& !(node.range.lo instanceof JCLiteral lit && ((Number) lit.value).longValue() >= 0)) {
					var lhs = treeutils.makeLit(node.pos, jmltypes.BIGINT, 0);
					var rhs = node.range.lo;
					ex = treeutils.makeBinary(node.pos, JCTree.Tag.LE, lhs, rhs);
				}
				if (node.range.hi != null) {
					var lhs = node.range.hi;
					var rhs = node.range.lo;
					var exx = treeutils.makeBinary(node.pos, JCTree.Tag.LE, lhs, rhs);
					ex = ex == null ? exx : treeutils.makeAnd(node.pos, ex, exx);
				}
				eee = node.range.accept(this, p);
			}
			if (e == null && ee == null && eee == null)
				return null;
			var list = new java.util.LinkedList<JmlStatementExpr>();
			if (e != null)
				list.addAll(e);
			if (ee != null)
				list.addAll(ee);
			if (eee != null)
				list.addAll(eee);
			return list;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitBinary(BinaryTree that, Void p) {
			JCBinary bin = (JCBinary) that;
			JCExpression lhs = bin.lhs;
			JCExpression rhs = bin.rhs;
			JCTree.Tag op = bin.getTag();
			/* @ nullable */ java.util.List<JmlStatementExpr> elhs = lhs.accept(this, p);
			/* @ nullable */ java.util.List<JmlStatementExpr> erhs = rhs.accept(this, p);
			/* @ nullable */ java.util.List<JmlStatementExpr> e = combine(elhs, erhs);
			if (op == JCTree.Tag.DIV) {
				JCExpression ee = treeutils
						.makeBinary(rhs.pos, JCTree.Tag.NE, treeutils.intneqSymbol, sub.copy(rhs), treeutils.zero)
						.setType(syms.booleanType);
				JmlStatementExpr a = treeutils.makeAssert(rhs, Label.UNDEFINED_DIV0, ee);
				e = combine(e, a);
			} else if (op == JCTree.Tag.AND) {
				JCExpression copy = sub.copy(lhs);
				e = prepend(copy, e);
			} else if (op == JCTree.Tag.OR) {
				JCExpression copy = treeutils.makeNot(lhs.pos, sub.copy(lhs));
				e = prepend(copy, e);
			}
			// FIXME - shifts, arithmetic overflow
			return e;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitLetExpr(LetExpr that, Void p) {
			ListBuffer<JCVariableDecl> newdecls = new ListBuffer<JCVariableDecl>();
			ListBuffer<JCExpression> inits = new ListBuffer<JCExpression>();
			/* @ nullable */ java.util.List<JmlStatementExpr> asserts = null;
			try {
				for (JCStatement st : that.defs) {
					if (!(st instanceof JCVariableDecl))
						continue;
					JCVariableDecl decl = (JCVariableDecl) st;
					/* @ nullable */ java.util.List<JmlStatementExpr> init = decl.init.accept(this, p);
					asserts = combine(asserts, init);
					inits.add(sub.copy(decl.init));
				}
				for (JCStatement st : that.defs) {
					if (!(st instanceof JCVariableDecl))
						continue;
					JCVariableDecl decl = (JCVariableDecl) st;
					JCVariableDecl nd = treeutils.makeVarDef(decl.type, decl.name, decl.sym.owner, inits.remove());
					newdecls.add(nd);
					JCExpression was = replacements.put(decl.sym, treeutils.makeIdent(decl.pos, nd.sym));
					if (was != null)
						throw new RuntimeException("Same Decl in replacement map");
				}
				/* @ nullable */ java.util.List<JmlStatementExpr> value = that.expr.accept(this, p);

				// FIXME
//                if (value != null) for (JmlStatementExpr a: value) {
//                    // FIXME - all the let expressions are using the same decls with the same symbols and same initializers
//                    LetExpr q = M.at(that.pos).LetExpr(newdecls.toList(), a.expression);
//                    q.setType(that.type);
//                    a.expression = q;
//                }
				return combine(asserts, value);

			} finally {
				for (JCStatement st : that.defs) {
					if (st instanceof JCVariableDecl)
						replacements.remove(((JCVariableDecl) st).sym);
				}
			}
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitLambdaExpression(LambdaExpressionTree that,
				Void p) {
			// FIXME
			JCTree.JCLambda exp = (JCTree.JCLambda) that;
			notImplemented("Lambda Expression not implemented", null);
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitMethodInvocation(MethodInvocationTree node,
				Void p) {
			JCMethodInvocation that = (JCMethodInvocation) node;
			/* @ nullable */ java.util.List<JmlStatementExpr> wellDefined = that.meth.accept(this, p);
			for (JCExpression arg : that.args) {
				wellDefined = combine(wellDefined, arg.accept(this, p));
			}

			// TODO Auto-generated method stub
			return wellDefined;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitClass(ClassTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitConditionalExpression(
				ConditionalExpressionTree node, Void p) {
			JCConditional that = (JCConditional) node;
			JCExpression cond = that.cond;
			JCExpression lhs = that.truepart;
			JCExpression rhs = that.falsepart;
			/* @ nullable */ java.util.List<JmlStatementExpr> wellDefinedCond = cond.accept(this, p);
			/* @ nullable */ java.util.List<JmlStatementExpr> wellDefinedTrue = lhs.accept(this, p);
			/* @ nullable */ java.util.List<JmlStatementExpr> wellDefinedFalse = rhs.accept(this, p);

			JCExpression condTrue = sub.copy(cond);
			JCExpression condFalse = treeutils.makeNot(cond.pos, sub.copy(cond));

			wellDefinedTrue = prepend(condTrue, wellDefinedTrue);
			wellDefinedFalse = prepend(condFalse, wellDefinedFalse);

			wellDefinedCond = combine(combine(wellDefinedCond, wellDefinedTrue), wellDefinedFalse);
			return wellDefinedCond;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitErroneous(ErroneousTree node, Void p) {
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitIdentifier(IdentifierTree node, Void p) {
			// FIXME - what if a model field
			// FIXME - non null ?
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitArrayAccess(ArrayAccessTree node, Void p) {
			JCArrayAccess aa = (JCArrayAccess) node;
			JCExpression array = aa.getExpression();
			/* @ nullable */ java.util.List<JmlStatementExpr> wellDefined = array.accept(this, p);

			JCExpression index = aa.getIndex();
			wellDefined = combine(wellDefined, index.accept(this, p));
			JCExpression e;
			JmlStatementExpr a;
			if (!utils.isJavaOrJmlPrimitiveType(array.type)) {
				e = treeutils.makeNotNull(array.pos, sub.copy(array));
				a = treeutils.makeAssert(aa, Label.UNDEFINED_NULL_DEREFERENCE, e);
				wellDefined = combine(wellDefined, a);
			}

			e = treeutils.makeBinary(index.pos, JCTree.Tag.LE, treeutils.intleSymbol, treeutils.zero, sub.copy(index));
			a = treeutils.makeAssert(index, Label.UNDEFINED_NEGATIVEINDEX, e);
			wellDefined = combine(wellDefined, a);

			e = treeutils.makeLength(aa, sub.copy(array));
			e = treeutils.makeBinary(index.pos, JCTree.Tag.LT, treeutils.intltSymbol, sub.copy(index), e);
			a = treeutils.makeAssert(aa, Label.UNDEFINED_TOOLARGEINDEX, e);
			wellDefined = combine(wellDefined, a);

			return wellDefined;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitLiteral(LiteralTree node, Void p) {
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitNewArray(NewArrayTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitNewClass(NewClassTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitParenthesized(ParenthesizedTree node, Void p) {
			return node.getExpression().accept(this, p);
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitMemberSelect(MemberSelectTree node, Void p) {
			JCFieldAccess fa = (JCFieldAccess) node;
			JCExpression lhs = fa.getExpression();
			/* @ nullable */ java.util.List<JmlStatementExpr> wellDefinedLhs = fa.accept(this, p);
			JCExpression e = treeutils.makeNotNull(lhs.pos, sub.copy(lhs));
			JmlStatementExpr a = treeutils.makeAssert(fa, Label.UNDEFINED_NULL_DEREFERENCE, e);
			return combine(wellDefinedLhs, a);
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitTypeCast(TypeCastTree node, Void p) {
			// TODO Auto-generated method stub
			return node.getExpression().accept(this, p);
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitInstanceOf(InstanceOfTree node, Void p) {
			// TODO Auto-generated method stub
			return node.getExpression().accept(this, p);
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitUnary(UnaryTree node, Void p) {
			JCUnary that = (JCUnary) node;
			JCExpression arg = that.arg;
			JCTree.Tag op = that.getTag();
			/* @ nullable */ java.util.List<JmlStatementExpr> earg = arg.accept(this, p);
			if (op == JCTree.Tag.NEG) {
				JCExpression e = treeutils.makeBinary(arg.pos, JCTree.Tag.NE, treeutils.intneqSymbol, sub.copy(arg),
						treeutils.makeIntLiteral(arg.pos, Integer.MIN_VALUE)).setType(syms.booleanType);
				JmlStatementExpr a = treeutils.makeAssert(that, Label.ARITHMETIC_OP_RANGE, e);
				earg = combine(earg, a);
			}
			return earg;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitVariable(VariableTree node, Void p) {
			// TODO Auto-generated method stub
			// Model fields? nonnull vcheck?
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlBinary(JmlBinary that, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlChained(JmlChained that, Void p) {
			/* @ nullable */ java.util.List<JmlStatementExpr> elhs = that.conjuncts.head.lhs.accept(this, p);
			/* @ nullable */ java.util.List<JmlStatementExpr> e = elhs;
			for (JCBinary b : that.conjuncts) {
				/* @ nullable */ java.util.List<JmlStatementExpr> erhs = b.rhs.accept(this, p);
				e = combine(e, erhs);
			}
			return e;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitBlock(BlockTree that, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitLabeledStatement(LabeledStatementTree that,
				Void p) {
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlInlinedLoop(JmlInlinedLoop that, Void p) {
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlLblExpression(JmlLblExpression that, Void p) {
			return that.expression.accept(this, p);
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlMatchExpression(JmlMatchExpression that,
				Void p) {
			return that.expression.accept(this, p);
			// FIXME - check well definedess of each case?
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlMethodInvocation(JmlMethodInvocation that,
				Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that,
				Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlQuantifiedExpr(JmlQuantifiedExpr that,
				Void p) {

			ListBuffer<JCVariableDecl> newdecls = new ListBuffer<JCVariableDecl>();
			try {
				for (JCVariableDecl decl : that.decls) {
					JCVariableDecl nd = treeutils.makeVarDef(decl.type, decl.name, decl.sym.owner, decl.pos);
					newdecls.add(nd);
					JCExpression was = replacements.put(decl.sym, treeutils.makeIdent(decl.pos, nd.sym));
					if (was != null)
						throw new RuntimeException("Same Decl in replacement map");
				}
				/* @ nullable */ java.util.List<JmlStatementExpr> range = that.range == null ? null
						: that.range.accept(this, p);
				/* @ nullable */ java.util.List<JmlStatementExpr> value = that.value.accept(this, p);
				if (that.range != null)
					value = prepend(sub.copy(that.range), value);

				if (range != null)
					for (JmlStatementExpr a : range) {
						// FIXME - all the quantified expressions are using the same decls with the same
						// symbols
						JmlQuantifiedExpr q = M.at(that.pos).JmlQuantifiedExpr(that.kind, newdecls.toList(), null,
								a.expression);
						q.setType(syms.booleanType);
						a.expression = q;
					}
				if (value != null)
					for (JmlStatementExpr a : value) {
						// FIXME - all the quantified expressions are using the same decls with the same
						// symbols
						JmlQuantifiedExpr q = M.at(that.pos).JmlQuantifiedExpr(that.kind, newdecls.toList(),
								that.range == null ? null : sub.copy(that.range), a.expression);
						q.setType(syms.booleanType);
						a.expression = q;
					}
				return combine(range, value);

			} finally {
				for (JCVariableDecl decl : that.decls) {
					replacements.remove(decl.sym);
				}
			}
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlSetComprehension(JmlSetComprehension that,
				Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlRange(JmlRange that, Void p) {
			/* @ nullable */ java.util.List<JmlStatementExpr> lo = that.lo == null ? null : that.lo.accept(this, p);
			/* @ nullable */ java.util.List<JmlStatementExpr> hi = that.hi == null ? null : that.hi.accept(this, p);
			return combine(lo, hi);
		}

		@Override
		public /* @ nullable */ java.util.List<JmlStatementExpr> visitJmlSingleton(JmlSingleton that, Void p) {
			return null;
		}

		public java.util.List<JmlStatementExpr> visitJmlTuple(JmlTuple that, Void p) {
			for (JCExpression e : that.values)
				e.accept(this, p);
			return null;
		}

		@Override
		public java.util.List<JmlStatementExpr> visitBindingPattern(BindingPatternTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

                @Override
                public java.util.List<JmlStatementExpr> visitDeconstructionPattern(DeconstructionPatternTree node, Void p) {
                       // TODO
                       return null;
                }

                @Override
                public java.util.List<JmlStatementExpr> visitPatternCaseLabel(PatternCaseLabelTree node, Void p) {
                       // TODO
                       return null;
                }

                @Override
                public java.util.List<JmlStatementExpr> visitConstantCaseLabel(ConstantCaseLabelTree node,Void p) {
                       // TODO
                       return null;
                }

                @Override
                public java.util.List<JmlStatementExpr> visitDefaultCaseLabel(DefaultCaseLabelTree node, Void p) {
                       // TODO
                       return null;
                }

                @Override
                public java.util.List<JmlStatementExpr> visitAnyPattern(AnyPatternTree node, Void p) {
                       // TODO
                       return null;
                }

                @Override
                public java.util.List<JmlStatementExpr> visitStringTemplate(StringTemplateTree node, Void p) {
                       // TODO
                       return null;
                }

		@Override
		public java.util.List<JmlStatementExpr> visitPackage(PackageTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public java.util.List<JmlStatementExpr> visitSwitchExpression(SwitchExpressionTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public java.util.List<JmlStatementExpr> visitModule(ModuleTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public java.util.List<JmlStatementExpr> visitExports(ExportsTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public java.util.List<JmlStatementExpr> visitOpens(OpensTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public java.util.List<JmlStatementExpr> visitProvides(ProvidesTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public java.util.List<JmlStatementExpr> visitRequires(RequiresTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public java.util.List<JmlStatementExpr> visitUses(UsesTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public java.util.List<JmlStatementExpr> visitYield(YieldTree node, Void p) {
			// TODO Auto-generated method stub
			return null;
		}

	}

	// The following are used to identify an int with each file used, as a kind of
	// hash.
	// The association is only valid during the translation of a given method.

	/** Holds the URI to Integer mapping */
	public Map<URI, Integer> jfoToInt = new HashMap<>();
	/** Holds the int to file object mapping, the reverse of jfoToInt */
	public ArrayList<JavaFileObject> intToJfo = new ArrayList<>();

	/**
	 * Returns the (non-negative) index for a given file, creasting one if needed
	 */
	public int getFileIndex(JavaFileObject jfo) {
		URI uri = jfo.toUri();
		Integer i = jfoToInt.get(uri);
		if (i == null) {
			i = jfoToInt.size();
			jfoToInt.put(uri, i);
			intToJfo.add(i, jfo);
		}
		return i;
	}

	/** Returns the file object for a given index */
	public JavaFileObject getFileByIndex(int i) {
		return intToJfo.get(i);
	}

	public static class CheckTree extends JmlTreeScanner {
		public Utils utils;

		public CheckTree(Context context) {
			super(context);
			utils = Utils.instance(context);
		}

		public static void check(Context context, JCTree tree) {
			new CheckTree(context).scan(tree);
		}

		@Override
		public void scan(JCTree tree) {
			if (tree == null) return;
			JavaFileObject prev = null;
			if (tree instanceof JCExpression) {
				if (((JCExpression) tree).type == null)
					utils.note(tree, "jml.message", "Expression has no type: " + JmlPretty.write(tree));
			}
			if (tree instanceof JmlSource s) {
				if (context != null) prev = Log.instance(context).useSource(s.source());
			}
			super.scan(tree);
			if (prev != null) Log.instance(context).useSource(prev);
		}

		public void visitCompilationUnit(JCCompilationUnit tree) {
			super.visitTopLevel(tree);
		}

		@Override
		public void visitAnnotation(JCAnnotation tree) {
			if (tree.type == null)
				utils.note(tree, "jml.message", "Annotation has no type: " + JmlPretty.write(tree));
			if (tree.annotationType.type == null)
				utils.note(tree, "jml.message", "Annotation has no annotationType.type: " + JmlPretty.write(tree));
		}

		@Override
		public void visitIdent(JCIdent tree) {
			if (tree.sym == null)
				utils.note(tree, "jml.message", "Ident has no sym: " + JmlPretty.write(tree));
//    		if (tree.sym != null && tree.sym.owner instanceof ClassSymbol && JmlSpecs.instance(context).get((ClassSymbol)tree.sym.owner) == null)  utils.error(tree, "jml.message", tree.sym.owner + " has no specs: "  + JmlPretty.write(tree));
//    		if (tree.sym != null && tree.sym.owner instanceof ClassSymbol && tree.sym instanceof MethodSymbol && JmlSpecs.instance(context).getSpecs((MethodSymbol)tree.sym) == null)  utils.error(tree, "jml.message", tree.sym + " has no specs: "  + JmlPretty.write(tree));
//    		if (tree.sym != null && tree.sym.owner instanceof ClassSymbol && tree.sym instanceof VarSymbol && JmlSpecs.instance(context).getSpecs((VarSymbol)tree.sym) == null)  utils.error(tree, "jml.message", tree.sym + " has no specs: "  + JmlPretty.write(tree));
			super.visitIdent(tree);
		}

		@Override
		public void visitImport(JCImport tree) {
			// do nothing
		}

		@Override
		public void visitPackageDef(JCPackageDecl tree) {
			// do nothing
		}
	}
	
	/** This class encapsulates information that is fixed for a method, but needs to be 
	 * pushed/popped as other metehods are translated recursively 
	 */
	
	public static class MethodEnv implements Cloneable {
        public MethodEnv() {} // Just for the very first initialization

	    public MethodEnv(Context context, boolean esc, boolean rac) {
	        String ss = JmlOption.value(context, JmlOption.RAC_SHOW_SOURCE);
	        this.showRacSource = "none".equals(ss) ? 0 : "line".equals(ss) ? 1 : 2;
	        this.racCheckAssumeStatements = JmlOption.isOption(context, JmlOption.RAC_CHECK_ASSUMPTIONS);
	        this.javaChecks = esc || (rac && JmlOption.isOption(context, JmlOption.RAC_JAVA_CHECKS));
	    }

//        public MethodEnv() {
//            this.receiver = receiver;
//            this.stateLabel = stateLabel;
//            this.allocCount = allocCount;
//            this.methodSym = methodSym;
//            this.enclosingClauseKind = null;
//        }

        /*@ nullable */ public MethodEnv previousEnv; 
        /**
         * If true, then error messages in generated RAC code include source code
         * snippets with the customary textual ^ pointers to error locations. This adds
         * bulk to the RAC-ed program, though I've not measured whether it is
         * significant. The field is initialized from a user option and not meant to be
         * set externally.
         */
        protected int showRacSource;

        /**
         * If true, then in the RAC translation, assume statements and assumptions
         * implied by JML are checked as if they were assert statements. The field is
         * initialized from a user option and not meant to be set externally.
         */
        protected boolean racCheckAssumeStatements;

        /**
         * If true, then explicit checks are included even when the Java language would
         * catch the error itself (e.g., OpenJML will check for a null reference in
         * advance of a dereference and Java throwing a NullPointerException). This
         * should always be true for esc, but only true for rac if the appropriate
         * option is set.
         */
        public boolean javaChecks;

        /** We have the same Map for the whole method translation, but the content of the Map does change */
        public Map<Integer, HeapInfo> allHeaps = new HashMap<>();
        
        public MethodEnv popEnv() {
            // System.out.println("POPENV " + this.hashCode() + " TO " + previousEnv.hashCode());
            return previousEnv;
        }

        public MethodEnv pushEnvCopy() {
            try {
                var t = (MethodEnv)this.clone();
                t.previousEnv = this;
                // System.out.println("PUSHENV " + this.hashCode() + " TO " + t.hashCode());
                return t;
            } catch (CloneNotSupportedException e) {
                throw new RuntimeException(e);
            }
        }

        public MethodEnv newEnvCopy() {
            try {
                var t = (MethodEnv)this.clone();
                t.previousEnv = null;
                return t;
            } catch (CloneNotSupportedException e) {
                throw new RuntimeException(e);
            }
        }
        
        public MethodEnv pushEnvInit(Context context, boolean esc, boolean rac) {
            var t = new MethodEnv(context,esc,rac);
            t.previousEnv = this;
            return t;
        }
	}
	
	MethodEnv methodEnv = new MethodEnv();


	// This class encapsulates information about the environment in which a
	// translation is being performed; these are values that can change in the
	// course of translating a method and need to be pushed and popped as the AST is visited.
	// It is helpful because the visit methods do not take an auxiliary argument in
	// which such information could be passed.
	public static class TranslationEnv implements Cloneable {
		public TranslationEnv() {
		}

		public TranslationEnv(JCExpression receiver, Name stateLabel, int allocCount, MethodSymbol methodSym) {
			this.currentReceiver = receiver;
			this.stateLabel = stateLabel;
			this.allocCount = allocCount;
			this.methodSym = methodSym;
			this.enclosingClauseKind = null;
		}

        /*@ nullable */ public TranslationEnv previousEnv; 
        /*@ nullable */ public JCExpression currentReceiver; // what 'this' is currently. null in a static environment; already translated
 
 //       public Map<Object, JCExpression> paramActuals = new HashMap<>();/// mapping from formals to actual parameters; already translated
        
        /**
         * Used to note the environment (e.g., \old label) under which we are currently
         * evaluating expressions; null indicates the current state; the value preLabel indicates
         * the pre-state, etc.
         */
        /*@ nullable */ public Name stateLabel; // the current heap state. null means the current state
        public int allocCount = 0;
        
        /** The method being translated */
        public MethodSymbol methodSym;
        
        /** The clause being translated (null if not in one) */
        //@ nullable
        public IJmlClauseKind enclosingClauseKind;
        
        /** Where to store yield values; null if we are not in a switch */
        public JCIdent yieldIdent = null;

        /** Current arithmetic mode */
        public IArithmeticMode arithmeticMode = null;

        /** Info about the current heap */
        public HeapInfo heap;
        
		public TranslationEnv popEnv() {
			// System.out.println("POPENV " + this.hashCode() + " TO " + previousEnv.hashCode());
			return previousEnv;
		}

        public TranslationEnv pushEnvCopy() {
            try {
                var t = (TranslationEnv)this.clone();
                t.previousEnv = this;
                // System.out.println("PUSHENV " + this.hashCode() + " TO " + t.hashCode());
                return t;
            } catch (CloneNotSupportedException e) {
                throw new RuntimeException(e);
            }
        }

        public TranslationEnv pushEnvCopy(TranslationEnv t) {
            t.previousEnv = this;
            // System.out.println("PUSHENV " + this.hashCode() + " TO " + t.hashCode());
            return t;
        }

        public TranslationEnv newEnvCopy() {
            try {
                var t = (TranslationEnv)this.clone();
                t.previousEnv = null;
                return t;
            } catch (CloneNotSupportedException e) {
                throw new RuntimeException(e);
            }
        }

        public TranslationEnv pushEnvInit() {
            var t = new TranslationEnv();
            t.previousEnv = this;
            //System.out.println("PUSHENV " + this.hashCode() + " TO " + t.hashCode());
            return t;
        }

	}

    TranslationEnv currentEnv = new TranslationEnv();

}
