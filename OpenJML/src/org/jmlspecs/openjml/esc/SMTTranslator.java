/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.util.*;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
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
import org.jmlspecs.openjml.JmlTree.JmlStatementDecls;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import org.jmlspecs.openjml.JmlTree.JmlStatementSpec;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefListExpression;
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
import org.smtlib.ICommand;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_check_sat;
import org.smtlib.command.C_declare_fun;
import org.smtlib.command.C_declare_sort;
import org.smtlib.command.C_define_fun;
import org.smtlib.command.C_push;
import org.smtlib.command.C_set_logic;
import org.smtlib.command.C_set_option;
import org.smtlib.impl.Factory;
import org.smtlib.impl.Script;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlType;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.model.JavacTypes;
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
import com.sun.tools.javac.tree.JCTree.JCTypeUnion;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCWildcard;
import com.sun.tools.javac.tree.JCTree.LetExpr;
import com.sun.tools.javac.tree.JCTree.TypeBoundKind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

/** This class translates a BasicBlock program into SMTLIB;
 *  a new instance of the class is needed for each BasicBlock program translated.
 *  <P>
 * The input program is a BasicBlock program, which may consist of the
 * following kinds of statements:
 * <UL>
 * <LI>declaration statements with or without initializers (TODO - what kinds of types)
 * <LI>JML assume statements
 * <LI>JML assert statements
 * <LI>JML comment statements
 * </UL>
 * Expressions may include the following:
 * <UL>
 * <LI>Java operators: + - * / % comparisons bit-operations logic-operators
 * <LI>field access - TODO?
 * <LI>array access - TODO?
 * <LI>STORE and SELECT functions using Java method class (JCMethodInvocation)
 * <LI>method calls (TODO - any restrictions?)
 * </UL>
 */
public class SMTTranslator extends JmlTreeScanner {

    /** The compilation context */
    protected Context context;
    
    /** The error log */
    final protected Log log;
    
    /** The symbol table for this compilation context */
    final protected Symtab syms;
    
    /** The Names table for this compilation context */
    final protected Names names;
    
    /** Cached value of the types tool */
    final protected javax.lang.model.util.Types types;
    
    final protected JmlTypes jmltypes;
    
    /** Cached instance of the JmlTreeUtils tool for the context. */
    final protected JmlTreeUtils treeutils;
    
    /** The factory for creating SMTLIB expressions */
    final protected Factory F;
    
    /** Commonly used SMTLIB expressions - using these shares structure */
    final protected ISort bv32Sort;
    final protected ISort bv64Sort;
    final protected ISort bv16Sort;
    final protected ISort bv8Sort;
    final protected ISort intSort;
    final protected ISort boolSort;
          protected ISort realSort;
    final protected IExpr.ISymbol distinctSym;
    final protected IExpr.ISymbol arraySym;
    final protected IExpr.ISymbol eqSym;
    final protected IExpr.ISymbol impliesSym;
    final protected IExpr.ISymbol selectSym;
    final protected IExpr.INumeral zero;
    
    /** Commonly used SMT terms that model Java+JML - using these shares structure */
    final protected ISort refSort;
    final protected ISort javaTypeSort;
    final protected ISort jmlTypeSort;
    final protected IExpr.ISymbol thisSym;
    final protected IExpr.ISymbol nullSym;

    final protected IExpr.ISymbol lengthSym;
    
    public boolean useBV;
    public boolean quantOK = true;

    // These are strings that are part of our modeling of Java+JML and are
    // more or less arbitrary. Strings like these that are used only once
    // may be simply used in place.
    // Strings that are defined by SMTLIB are used explicitly in place.
    public static final String NULL = "NULL";
    public static final String this_ = Strings.thisName; // Must be the same as the id used in JmlAssertionAdder
    public static final String REF = "REF"; // SMT sort for Java references
    public static final String JAVATYPESORT = REF; // "JavaTypeSort";
    public static final String JMLTYPESORT = "JMLTypeSort";
    public static final String JAVASUBTYPE = "javaSubType";
    public static final String JMLSUBTYPE = "jmlSubType";
    public static final String arrayLength = "__JMLlength"; // array length
    public static final String arrays_ = BasicBlocker2.ARRAY_BASE_NAME; // Must match BasicBlocker2
    public static final String concat = "stringConcat";
    public static final String nonnullelements = "nonnullelements";
    public static final String arrayElemType = "__arrayElemType";

    /** A convenience declaration, to avoid calling the constructor for every empty list */
    public static final List<ISort> emptyList = new LinkedList<ISort>();
    
    /** SMTLIB subexpressions - the result of each visit call */
    protected IExpr result;
    
    /** The SMTLIB script as it is being constructed */
    protected IScript script;
    
    /** Identification of the source material, such as the method being translated, for error messages */
    protected String source;
    
    /** An alias to script.commands() */
    protected List<ICommand> commands;
    
    /** A list that accumulates all the Java type constants used */
    final protected Set<Type> javaTypes = new HashSet<Type>();

    /** A list that accumulates all the Java type constants used */
    final protected Map<String,IExpr> javaParameterizedTypes = new HashMap<String,IExpr>();

    /** A list that accumulates all the Java type names as used in SMT */
    final protected Set<String> javaTypeSymbols = new HashSet<String>();
    
    /** A counter used to make String literal identifiers unique */
    int stringCount = 0;

    /** A counter used to make double literal identifiers unique */
    int doubleCount = 0;

    /** A counter used to make identifiers unique */
    int uniqueCount = 0;
    
    private int assumeCount = -2;
    
    /** An internal field used to indicate whether we are translating expressions inside a quantified expression */
    boolean inQuant = false;

    /** A mapping from Java expressions to/from SMT expressions */
    final public BiMap<JCExpression,IExpr> bimap = new BiMap<JCExpression,IExpr>();
    
    /** The constructor - create a new instance for each Basic Program to be translated */
    public SMTTranslator(Context context, String source) {
        this.context = context;
        this.source = source;
        // OpenJDK tools
        log = Log.instance(context);
        syms = Symtab.instance(context);
        names = Names.instance(context);
        types = JavacTypes.instance(context);
        treeutils = JmlTreeUtils.instance(context);
        jmltypes = JmlTypes.instance(context);
        
        // Options
        useBV = JmlOption.isOption(context,JmlOption.ESC_BV);
        quantOK = !useBV;
        
        // SMT factory and commonly used objects
        F = new org.smtlib.impl.Factory();
        boolSort = F.createSortExpression(F.symbol("Bool")); // From SMT
        intSort = F.createSortExpression(F.symbol("Int")); // From SMT
        {
            List<INumeral> bits = new LinkedList<INumeral>();
            bits.add(F.numeral(32));
            bv32Sort = F.createSortExpression(F.id(F.symbol("BitVec"), bits));
            bits = new LinkedList<INumeral>(); bits.add(F.numeral(64));
            bv64Sort = F.createSortExpression(F.id(F.symbol("BitVec"), bits));
            bits = new LinkedList<INumeral>(); bits.add(F.numeral(16));
            bv16Sort = F.createSortExpression(F.id(F.symbol("BitVec"), bits));
            bits = new LinkedList<INumeral>(); bits.add(F.numeral(8));
            bv8Sort = F.createSortExpression(F.id(F.symbol("BitVec"), bits));
        }
        arraySym = F.symbol("Array"); // From SMT Array theory
        eqSym = F.symbol("="); // Name determined by SMT Core theory
        distinctSym = F.symbol("distinct"); // Name determined by SMT Core theory
        impliesSym = F.symbol("=>"); // Name determined by SMT Core theory
        selectSym = F.symbol("select"); // Name determined by SMT Array Theory
        zero = F.numeral(0);
        
        // Names used in mapping Java/JML to SMT
        refSort = F.createSortExpression(F.symbol(REF));
        nullSym = F.symbol(NULL);
        thisSym = F.symbol(this_);
        javaTypeSort = F.createSortExpression(F.symbol(JAVATYPESORT));
        jmlTypeSort = F.createSortExpression(F.symbol(JMLTYPESORT));
        lengthSym = F.symbol(arrayLength);
        
    }
    
    /** Adds symbols for the theory of Reals, if they are used */
    protected void addReal() {
        if (realSort == null) {
            realSort = F.createSortExpression(F.symbol("Real")); // From SMT
            List<ISort> args = Arrays.asList(refSort); // List of one element 
            ICommand c = new C_declare_fun(F.symbol("realValue"),args, realSort);
            commands.add(c);
        }
    }
    
    /** Adds all the definitions and axioms regarding the types used in the program */
    protected int addTypeModel(SMT smt) {
        List<ISort> args = Arrays.asList(refSort); // List of one element 
        ICommand c;
        // (declare-sort JavaTypeSort 0)
        if (JAVATYPESORT != REF) {
            c = new C_declare_sort(F.symbol(JAVATYPESORT),zero);
            commands.add(c);
        }
        String q = JmlOption.value(context, JmlOption.QUANTS_FOR_TYPES);
        boolean quants = false;
        if ("true".equals(q)) quants = true;
        else if ("false".equals(q)) quants = false;
        else {
            boolean b = JmlOption.isOption(context, JmlOption.MINIMIZE_QUANTIFICATIONS);
            quants = false; // FIXME - set true if there are any type variables
        }
        // (declare-sort JMLTypeSort 0)
        c = new C_declare_sort(F.symbol(JMLTYPESORT),zero);
        commands.add(c);
        // (declare-fun javaTypeOf (REF) JAVATYPESORT))
        c = new C_declare_fun(F.symbol("javaTypeOf"),args, javaTypeSort);
        commands.add(c);
        // (declare-fun jmlTypeOf (REF) JMLTYPESORT))
        c = new C_declare_fun(F.symbol("jmlTypeOf"),args, jmlTypeSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("typearg1_1"), Arrays.asList(new ISort[]{jmlTypeSort}), jmlTypeSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("typearg2_1"), Arrays.asList(new ISort[]{jmlTypeSort}), jmlTypeSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("typearg2_2"), Arrays.asList(new ISort[]{jmlTypeSort}), jmlTypeSort);
        commands.add(c);
        // (declare-fun JAVASUBTYPE (JAVATYPESORT JAVATYPESORT) Bool)
        c = new C_declare_fun(F.symbol(JAVASUBTYPE),
                Arrays.asList(new ISort[]{javaTypeSort,javaTypeSort}), 
                boolSort);
        commands.add(c);
        // (declare-fun JMLSUBTYPE (JMLTYPESORT JMLTYPESORT) Bool)
        c = new C_declare_fun(F.symbol(JMLSUBTYPE),
                Arrays.asList(new ISort[]{jmlTypeSort,jmlTypeSort}), 
                boolSort);
        commands.add(c);
        // (declare-fun erasure (JMLTYPESORT) JAVATYPESORT)
        c = new C_declare_fun(F.symbol("erasure"),
                Arrays.asList(new ISort[]{jmlTypeSort}), 
                javaTypeSort);
        commands.add(c);

        addCommand(smt,"(declare-fun _JMLT_0 ("+JAVATYPESORT+") "+JMLTYPESORT+")");
        addCommand(smt,"(declare-fun _JMLT_1 ("+JAVATYPESORT+" "+JMLTYPESORT+") "+JMLTYPESORT+")");
        addCommand(smt,"(declare-fun _JMLT_2 ("+JAVATYPESORT+" "+JMLTYPESORT+" "+JMLTYPESORT+") "+JMLTYPESORT+")");

        if (quantOK) addCommand(smt,"(assert (forall ((o REF)) (= (erasure (jmlTypeOf o)) (javaTypeOf o))))");
        
        addCommand(smt,"(declare-fun _makeArrayType ("+JAVATYPESORT+") "+JAVATYPESORT+")");
        addCommand(smt,"(declare-fun _isArrayType ("+JAVATYPESORT+") Bool)");
        addCommand(smt,"(declare-fun _makeJMLArrayType ("+JMLTYPESORT+") "+JMLTYPESORT+")");
        addCommand(smt,"(declare-fun _isJMLArrayType ("+JMLTYPESORT+") Bool)");
        addCommand(smt,"(declare-fun "+arrayElemType+" ("+JMLTYPESORT+") "+JMLTYPESORT+")");
        if (quantOK) {
        addCommand(smt,"(assert (forall ((T "+JMLTYPESORT+")) (= (erasure (_makeJMLArrayType T)) (_makeArrayType (erasure T)))))");
        addCommand(smt,"(assert (forall ((T1 "+JMLTYPESORT+")(T2 "+JMLTYPESORT+"))  (=> ("+JMLSUBTYPE+" T1 T2) ("+JAVASUBTYPE+" (erasure T1) (erasure T2)))))");
        addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(T2 "+JAVATYPESORT+")(T3 "+JMLTYPESORT+"))  (= ("+JAVASUBTYPE+" T1 T2) ("+JMLSUBTYPE+" (_JMLT_1 T1 T3) (_JMLT_1 T2 T3)))))");
        addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(T2 "+JAVATYPESORT+")(T3 "+JMLTYPESORT+")(T4 "+JMLTYPESORT+"))  (=> (and ("+JAVASUBTYPE+" T1 T2) (not (= T3 T4))) (not ("+JMLSUBTYPE+" (_JMLT_1 T1 T3) (_JMLT_1 T2 T4))))))");
        addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(T2 "+JAVATYPESORT+")(T3 "+JMLTYPESORT+")(T4 "+JMLTYPESORT+"))  (=> ("+JMLSUBTYPE+" (_JMLT_1 T1 T3) (_JMLT_1 T2 T4))   (and ("+JAVASUBTYPE+" T1 T2) (= T3 T4)) ) )))");
        addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(T2 "+JAVATYPESORT+")(T3 "+JMLTYPESORT+")(T4 "+JMLTYPESORT+"))  (=> (= (_JMLT_1 T1 T3) (_JMLT_1 T2 T4))   (and (= T1 T2) (= T3 T4)) ) )))");
        //addCommand(smt,"(assert (forall ((T "+JAVATYPESORT+")) (= ( "+arrayElemType+" (_makeArrayType T)) T)))");
        }
        if (quants && quantOK) {
            addCommand(smt,"(assert (forall ((T "+JMLTYPESORT+")) (= ( "+arrayElemType+" (_makeJMLArrayType T)) T)))");
            addCommand(smt,"(assert (forall ((T "+JAVATYPESORT+")) (_isArrayType (_makeArrayType T)) ))");
            addCommand(smt,"(assert (forall ((T "+JMLTYPESORT+")) (_isJMLArrayType (_makeJMLArrayType T)) ))");
            addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(T2 "+JAVATYPESORT+"))  (= ("+JAVASUBTYPE+" (_makeArrayType T1)(_makeArrayType T2)) ("+JAVASUBTYPE+" T1 T2))))");
            addCommand(smt,"(assert (forall ((T1 "+JMLTYPESORT+")(T2 "+JMLTYPESORT+"))  (= ("+JMLSUBTYPE+" (_makeJMLArrayType T1)(_makeJMLArrayType T2)) ("+JMLSUBTYPE+" T1 T2))))");
        }

        // The declaration + assertion form is nominally equivalent to the define_fcn form, but works better
        // for SMT solvers with modest (or no) support for quantifiers (like yices2)
        if (false) {
            // (define_fcn nonnullelements ((a REF)(arrays (Array REF (Array Int REF)))) 
            //                             Bool
            //                             (forall ((i Int)) (=> (and (<= 0 i) (< i (length a))) (distinct NULL (select (select arrays a) i)))))
            c = new C_define_fun(F.symbol(nonnullelements),
                    Arrays.asList(new IDeclaration[]{F.declaration(F.symbol("a"),refSort),
                            F.declaration(F.symbol("arrays"),
                                    F.createSortExpression(arraySym,
                                            refSort,
                                            F.createSortExpression(arraySym,intSort,refSort)))}), 
                    boolSort,
                    F.forall(Arrays.asList(new IDeclaration[]{F.declaration(F.symbol("i"),intSort)}),
                            F.fcn(impliesSym,
                                    F.fcn(F.symbol("and"),
                                            F.fcn(F.symbol("<="),F.numeral("0"),F.symbol("i")),
                                            F.fcn(F.symbol("<"), F.symbol("i"), F.fcn(selectSym,lengthSym,F.symbol("a")))
                                            ),
                                    F.fcn(distinctSym,
                                            nullSym,
                                            F.fcn(selectSym,
                                                    F.fcn(selectSym,F.symbol("arrays"),F.symbol("a")),
                                                    F.symbol("i"))))));
            commands.add(c);
        } else if (!useBV) {
            // (declare_fcn nonnullelements ((a REF)(arrays (Array REF (Array Int REF)))) Bool)
            // (assert (forall ((a REF)(arrays (Array REF (Array Int REF)))) (= (nonnullelements a arrays)
            //                             (forall ((i Int)) (=> (and (<= 0 i) (< i (length a))) (distinct NULL (select (select arrays a) i)))))
            c = new C_declare_fun(F.symbol(nonnullelements),
                    Arrays.asList(new ISort[]{refSort,
                            F.createSortExpression(arraySym,
                                    refSort,
                                    F.createSortExpression(arraySym,intSort,refSort))}), 
                    boolSort);
            commands.add(c);
            c = new C_assert(
                    F.forall(Arrays.asList(F.declaration(F.symbol("a"),refSort),
                                           F.declaration(F.symbol("arrays"),
                                                   F.createSortExpression(arraySym,
                                                           refSort,
                                                           F.createSortExpression(arraySym,intSort,refSort)))
                                           ),
                            F.fcn(eqSym,
                                    F.fcn(F.symbol(nonnullelements), F.symbol("a"), F.symbol("arrays")),
                                    F.forall(Arrays.asList(F.declaration(F.symbol("i"),intSort)),
                                            F.fcn(impliesSym,
                                                    F.fcn(F.symbol("and"),
                                                            F.fcn(F.symbol("<="),F.numeral("0"),F.symbol("i")),
                                                            F.fcn(F.symbol("<"), F.symbol("i"), F.fcn(selectSym,lengthSym,F.symbol("a")))
                                                            ),
                                                    F.fcn(distinctSym,
                                                            F.symbol(NULL),
                                                            F.fcn(selectSym,F.fcn(selectSym,F.symbol("arrays"),F.symbol("a")),F.symbol("i"))
                                                            )
                                                    )
                                             )
                                    )));
            commands.add(c);
        }

        if (quants && quantOK) {
            // (forall ((t JMLTYPESORT) (tt JMLTYPESORT)) (==> (jmlSubtype t tt) (javaSubtype (erasure t) (erasure tt)))) 
            c = new C_assert(
                    F.forall(Arrays.asList(F.declaration(F.symbol("t"),jmlTypeSort),
                                           F.declaration(F.symbol("tt"),jmlTypeSort)
                                           ),
                            F.fcn(impliesSym,
                                    F.fcn(F.symbol(JMLSUBTYPE), F.symbol("t"), F.symbol("tt")),
                                    F.fcn(F.symbol(JAVASUBTYPE), F.fcn(F.symbol("erasure"), F.symbol("t")), F.fcn(F.symbol("erasure"), F.symbol("tt")))
                                    )));
            commands.add(c);
//            // (forall ((r REF)) (= (erasure (jmlTypeOf r)) (javaTypeof r)))
//            c = new C_assert(
//                    F.forall(Arrays.asList(F.declaration(F.symbol("r"),refSort)),
//                            F.fcn(eqSym,
//                                    F.fcn(F.symbol("erasure"), F.fcn(F.symbol("jmlTypeOf"), F.symbol("r"))),
//                                    F.fcn(F.symbol("javaTypeOf"), F.symbol("r"))
//                                    )));
//            commands.add(c);
            
            addCommand(smt,"(assert (forall ((JVT "+JAVATYPESORT+")(JVT2 "+JAVATYPESORT+")(JMLT "+JMLTYPESORT+")) (distinct (_JMLT_0 JVT) (_JMLT_1 JVT2 JMLT))))");
            addCommand(smt,"(assert (forall ((JVT "+JAVATYPESORT+")(JVT2 "+JAVATYPESORT+")(JMLT "+JMLTYPESORT+")(JMLT2 "+JMLTYPESORT+")) (distinct (_JMLT_0 JVT) (_JMLT_2 JVT2 JMLT JMLT2))))");
            addCommand(smt,"(assert (forall ((JVT "+JAVATYPESORT+")(JVT2 "+JAVATYPESORT+")(JMLT "+JMLTYPESORT+")(JMLT2 "+JMLTYPESORT+")(JMLT3 "+JMLTYPESORT+")) (distinct (_JMLT_1 JVT JMLT3) (_JMLT_2 JVT2 JMLT JMLT2))))");

            addCommand(smt,"(assert (forall ((JVT "+JAVATYPESORT+")(JVT2 "+JAVATYPESORT+")(JMLT "+JMLTYPESORT+")(JMLT2 "+JMLTYPESORT+")) (= (= (_JMLT_1 JVT JMLT) (_JMLT_1 JVT2 JMLT2)) (and (= JVT JVT2) (= JMLT JMLT2)))))");

            addCommand(smt,"(assert (forall ((JVT "+JAVATYPESORT+")(JMLT "+JMLTYPESORT+")) (= (erasure (_JMLT_1 JVT JMLT)) JVT)))");
            addCommand(smt,"(assert (forall ((JVT "+JAVATYPESORT+")(JMLT "+JMLTYPESORT+")) (= (typearg1_1 (_JMLT_1 JVT JMLT)) JMLT)))");
            addCommand(smt,"(assert (forall ((JVT "+JAVATYPESORT+")(JMLT1 "+JMLTYPESORT+")(JMLT2 "+JMLTYPESORT+")) (=> (= (_JMLT_1 JVT JMLT1)(_JMLT_1 JVT JMLT2)) (= JMLT1 JMLT2))))");

            addCommand(smt,"(assert (forall ((JVT "+JAVATYPESORT+")(JMLT1 "+JMLTYPESORT+")(JMLT2 "+JMLTYPESORT+")) (= (erasure (_JMLT_2 JVT JMLT1 JMLT2)) JVT)))");
            addCommand(smt,"(assert (forall ((JVT "+JAVATYPESORT+")(JMLT1 "+JMLTYPESORT+")(JMLT2 "+JMLTYPESORT+")) (= (typearg2_2 (_JMLT_2 JVT JMLT1 JMLT2)) JMLT2)))");
            
            addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(T2 "+JAVATYPESORT+")(J1 "+JMLTYPESORT+")(J2 "+JMLTYPESORT+")) (=> (= (_JMLT_1 T1 J1)(_JMLT_1 T2 J2)) (and (= T1 T2) (= J1 J2)))))");
            addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(T2 "+JAVATYPESORT+")(J1 "+JMLTYPESORT+")) (=> ("+JAVASUBTYPE+" T1 T2) ("+JMLSUBTYPE+" (_JMLT_1 T1 J1) (_JMLT_1 T2 J1) ))))"); // FIXME - this is true for collections, but necessarily always true?
            addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(T2 "+JAVATYPESORT+")(J1 "+JMLTYPESORT+")(J2 "+JMLTYPESORT+")) (=> (and ("+JAVASUBTYPE+" T1 T2) (distinct J1 J2)) (not ("+JMLSUBTYPE+" (_JMLT_1 T1 J1) (_JMLT_1 T2 J2) )) )))"); // FIXME - this is true for collections, but necessarily always true?
            addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(J1 "+JMLTYPESORT+")(J2 "+JMLTYPESORT+")) (= ("+JMLSUBTYPE+" (_JMLT_1 T1 J1)(_JMLT_1 T1 J2)) (= J1 J2))))");
            
            addCommand(smt,"(assert (forall ((T1 "+JAVATYPESORT+")(T2 "+JAVATYPESORT+")) (=> (= T1 T2) ("+JAVASUBTYPE+" T1 T2))))");
            addCommand(smt,"(assert (forall ((T1 "+JMLTYPESORT+")(T2 "+JMLTYPESORT+")) (=> (= T1 T2) ("+JMLSUBTYPE+" T1 T2))))");

            addCommand(smt,"(assert (forall ((T1 "+JMLTYPESORT+")(T2 "+JMLTYPESORT+")) (=> ("+JMLSUBTYPE+" T1 T2) ("+JAVASUBTYPE+" (erasure T1) (erasure T2)))))");
        }
        
        // Record the location in the commands list at which all the type
        // definitions will be inserted
        return commands.size();
    }
    
    protected void addTypeRelationships(int loc, SMT smt) {
        // Insert type relationships, now that we have accumulated them all
        // Each type has a representation as a Java (erased type) and a JML type
        int len = javaTypes.size();
        List<ICommand> tcommands = new ArrayList<ICommand>(len*len*2 + 3*len);
        List<IExpr> typesymbols = new ArrayList<IExpr>(len);
        List<IExpr> jmltypesymbols = new ArrayList<IExpr>(len);
    	List<ICommand> saved = commands;
    	commands = tcommands;
        
        for (Type ti: javaTypes) {
            if (ti.getTag() == TypeTag.TYPEVAR) {
                if (ti instanceof Type.CapturedType) continue; 
                tcommands.add(new C_declare_fun(
                        (ISymbol)jmlTypeSymbol(ti),
                        emptyList,
                        jmlTypeSort));
            }
        }
        for (Type ti: javaTypes) {
            if (ti.getTag() == TypeTag.WILDCARD) continue;  // Did these already, so they are done before they are used
            if (ti.getTag() == TypeTag.TYPEVAR) continue; // Did these already, so they are done before they are used
            // (declare-fun tjava () JavaTypeSort)
            // (declare-fun tjml () JMLTypeSort)
            // (assert (= (erasure tjml) tjava))
            ISymbol tisym = (ISymbol)javaTypeSymbol(ti);
            tcommands.add(new C_declare_fun(
                    tisym,
                    emptyList,
                    javaTypeSort));
            typesymbols.add(tisym);
            if (!ti.tsym.type.isParameterized()) {
                // Note: ti.isParameterized() is true if the type name has actual parameters
                // ti.tsym.type.isParameterized() is true if the declaration has parameters
                // e.g.  java.util.Set is false on the first, but true on the second
                ISymbol tjsym = (ISymbol)jmlTypeSymbol(ti);
                tcommands.add(new C_declare_fun(
                        tjsym,
                        emptyList,
                        jmlTypeSort));
                jmltypesymbols.add(tjsym);
            }
        }
        for (Type ti: javaTypes) {
            if (ti.getTag() == TypeTag.WILDCARD) continue;  // Did these already, so they are done before they are used
            if (ti.getTag() == TypeTag.TYPEVAR) continue; // Did these already, so they are done before they are used
            // (declare-fun tjava () JavaTypeSort)
            // (declare-fun tjml () JMLTypeSort)
            // (assert (= (erasure tjml) tjava))
            ISymbol tisym = (ISymbol)javaTypeSymbol(ti);
            tcommands.add(new C_assert(F.fcn(F.symbol("not"),F.fcn(F.symbol("_isArrayType"), javaTypeSymbol(ti))) ));
            if ((ti.tsym.flags() & Flags.FINAL) != 0) {
            	if (quantOK) addCommand(smt,"(assert (forall ((t "+JAVATYPESORT+")) (=> ("+JAVASUBTYPE+" t "+tisym.toString()+")  (= t "+tisym.toString()+"))))");
            }
            if (!ti.tsym.type.isParameterized()) {
                // Note: ti.isParameterized() is true if the type name has actual parameters
                // ti.tsym.type.isParameterized() is true if the declaration has parameters
                // e.g.  java.util.Set is false on the first, but true on the second
            	ISymbol tjsym = (ISymbol)jmlTypeSymbol(ti);
                tcommands.add(new C_assert(F.fcn(F.symbol("not"),F.fcn(F.symbol("_isJMLArrayType"), tjsym)) ));
                tcommands.add(new C_assert(F.fcn(
                        eqSym, 
                        F.fcn(F.symbol("_JMLT_0"),tisym),
                        tjsym)));
                tcommands.add(new C_assert(F.fcn(
                        eqSym, 
                        F.fcn(F.symbol("erasure"),tjsym),
                        tisym)));
                if ((ti.tsym.flags() & Flags.FINAL) != 0) {
                    if (quantOK) addCommand(smt,"(assert (forall ((t "+JMLTYPESORT+")) (=> ("+JMLSUBTYPE+" t "+tjsym.toString()+")  (= t "+tjsym.toString()+"))))");
                } 
            } else {
                // currently we add the symbols even if the type is parameterized,
                // because it's not clear what to do differently with parameterized types;
                // the code below is copied directly from the if branch
                IExpr tjsym = jmlTypeSymbol(ti);
                if (tjsym instanceof ISymbol) {
                    tcommands.add(new C_declare_fun(
                            (ISymbol)tjsym,
                            emptyList,
                            jmlTypeSort));
                }
                tcommands.add(new C_assert(F.fcn(F.symbol("not"),F.fcn(F.symbol("_isJMLArrayType"), tjsym)) ));
                tcommands.add(new C_assert(F.fcn(
                        eqSym, 
                        F.fcn(F.symbol("erasure"),tjsym),
                        tisym)));
                if ((ti.tsym.flags() & Flags.FINAL) != 0) {
                    if (quantOK) addCommand(smt,"(assert (forall ((t "+JMLTYPESORT+")) (=> ("+JMLSUBTYPE+" t "+tjsym.toString()+")  (= t "+tjsym.toString()+"))))");
                } 
            }
        }

        tcommands.add(new C_assert(F.fcn(F.symbol("distinct"),typesymbols)));
        tcommands.add(new C_assert(F.fcn(F.symbol("distinct"),jmltypesymbols)));
        
        for (Type ti: javaTypes) {
            if (ti instanceof ArrayType) tcommands.add(new C_assert(F.fcn(
                    F.symbol(JAVASUBTYPE), javaTypeSymbol(ti), F.symbol("T_java_lang_Object"))));
        }
        for (Type ti: javaTypes) {
            if (ti.getTag() == TypeTag.TYPEVAR) continue; 
            if (ti.getTag() == TypeTag.WILDCARD) continue; 
            for (Type tj: javaTypes) {
                if (tj.getTag() == TypeTag.TYPEVAR) continue; 
                if (tj.getTag() == TypeTag.WILDCARD) continue; 
                // (assert (javaSubType t1 t2)) - or assert the negation
                // (assert (jmlSubType t1jml t2jml)) - or assert the negation
                
                boolean b;
                if (ti.isPrimitive() && tj.isPrimitive()) b = types.isSameType(ti, tj);
                else b = types.isSubtype(types.erasure(ti),types.erasure(tj));
                
                IExpr comp = F.fcn(F.symbol(JAVASUBTYPE), javaTypeSymbol(ti), javaTypeSymbol(tj));
                if (!b) comp = F.fcn(F.symbol("not"),comp);
                tcommands.add(new C_assert(comp));
                comp = F.fcn(F.symbol(JAVASUBTYPE), F.fcn(F.symbol("_makeArrayType"),javaTypeSymbol(ti)), F.fcn(F.symbol("_makeArrayType"),javaTypeSymbol(tj)));
                if (!b) comp = F.fcn(F.symbol("not"),comp);
                tcommands.add(new C_assert(comp));
                
                if (!ti.tsym.type.isParameterized() && !tj.tsym.type.isParameterized() ) {
                    if (ti.isPrimitive() && tj.isPrimitive()) b = types.isSameType(ti, tj);
                    else b = types.isSubtype(ti,tj);

                    comp = F.fcn(F.symbol(JMLSUBTYPE), jmlTypeSymbol(ti), jmlTypeSymbol(tj));
                    if (!b) comp = F.fcn(F.symbol("not"),comp);
                    tcommands.add(new C_assert(comp));
                    comp = F.fcn(F.symbol(JMLSUBTYPE), F.fcn(F.symbol("_makeJMLArrayType"),jmlTypeSymbol(ti)), F.fcn(F.symbol("_makeJMLArrayType"),jmlTypeSymbol(tj)));
                    if (!b) comp = F.fcn(F.symbol("not"),comp);
                    tcommands.add(new C_assert(comp));
                }
            }
        }
        if (quantOK) {
            // Transitivity of Java subtype
            // Note: We try to avoid needing this (because it is quantified) 
            // by instantiating all the subtype
            // relationships of all of the known types, but it is still needed sometimes.
            // An example is catching exceptions thrown from a method: The callee
            // declares a thrown exception, but the actual exception is an unknown
            // subclass (t1) of the declared type (t2). A catch block that catches
            // exception (t3) that is a superclass of t2 (t2 is a subclass of t3)
            // must catch t1 - so we need to infer that t1 is a subclass of t3.
            //
            // So far we don't seem to need transitivity of JML types (TODO)
            List<IDeclaration> params = new LinkedList<IDeclaration>();
            params.add(F.declaration(F.symbol("t1"),javaTypeSort));
            params.add(F.declaration(F.symbol("t2"),javaTypeSort));
            params.add(F.declaration(F.symbol("t3"),javaTypeSort));
            IExpr e = F.forall(params, 
                    F.fcn(F.symbol("=>"), 
                          F.fcn(F.symbol("and"), 
                                  F.fcn(F.symbol(JAVASUBTYPE),F.symbol("t1"),F.symbol("t2")),
                                  F.fcn(F.symbol(JAVASUBTYPE),F.symbol("t2"),F.symbol("t3"))
                                  ),
                          F.fcn(F.symbol(JAVASUBTYPE),F.symbol("t1"),F.symbol("t3"))
                          ));
            tcommands.add(new C_assert(e));
        }
        if (quantOK) {
            // Transitivity of JML subtype
            // Note: We try to avoid needing this (because it is quantified) 
            // by instantiating all the subtype
            // relationships of all of the known types, but it is still needed sometimes.
            // An example is catching exceptions thrown from a method: The callee
            // declares a thrown exception, but the actual exception is an unknown
            // subclass (t1) of the declared type (t2). A catch block that catches
            // exception (t3) that is a superclass of t2 (t2 is a subclass of t3)
            // must catch t1 - so we need to infer that t1 is a subclass of t3.
            //
            // So far we don't seem to need transitivity of JML types (TODO)
            List<IDeclaration> params = new LinkedList<IDeclaration>();
            params.add(F.declaration(F.symbol("t1"),jmlTypeSort));
            params.add(F.declaration(F.symbol("t2"),jmlTypeSort));
            params.add(F.declaration(F.symbol("t3"),jmlTypeSort));
            IExpr e = F.forall(params, 
                    F.fcn(F.symbol("=>"), 
                          F.fcn(F.symbol("and"), 
                                  F.fcn(F.symbol(JMLSUBTYPE),F.symbol("t1"),F.symbol("t2")),
                                  F.fcn(F.symbol(JMLSUBTYPE),F.symbol("t2"),F.symbol("t3"))
                                  ),
                          F.fcn(F.symbol(JMLSUBTYPE),F.symbol("t1"),F.symbol("t3"))
                          ));
            tcommands.add(new C_assert(e));
        }
        
        List<IExpr> javatypelist = new LinkedList<IExpr>();
        for (Type t: javaTypes) {
            if (t.getTag() != TypeTag.TYPEVAR && t.getTag() != TypeTag.WILDCARD) {
                javatypelist.add(javaTypeSymbol(t));
            }
        }
        tcommands.add(new C_assert(F.fcn(distinctSym, javatypelist)));
        List<IExpr> jmltypelist = new LinkedList<IExpr>();
        for (IExpr e: javaParameterizedTypes.values()) {
            jmltypelist.add(e);
        }
        tcommands.add(new C_assert(F.fcn(distinctSym, jmltypelist)));

        for (int i=1; i<=wildcardCount; ++i) {
            ISymbol sym = F.symbol("JMLTV_"+"WILD"+i);
            tcommands.add(0,new C_declare_fun(sym,emptyList,jmlTypeSort));
        }

        // Add all the type definitions into the command script before all the uses
        // of the types in the various basic block translations
        commands = saved;
        commands.addAll(loc,tcommands);

    }
    
    /** This is called by visit methods, and super.scan calls accept methods;
     * clients should call scan instead of accept so that there is a common
     * processing point as well as the type-specific processing in accept methods.
     */
    @Override
    public void scan(JCTree t) {
        result = null;
        if (t != null) {
            super.scan(t);
            if (result != null) {
                // This mapping is used in associating original source code 
                // sub-expressions with SMT expressions that give their values
                // in a counterexample.
                if (t instanceof JCExpression) bimap.put((JCExpression)t, result);
                else if (t instanceof JmlVariableDecl) {
                    JCIdent id = ((JmlVariableDecl)t).ident;
                    bimap.put(id, result);
                }
            }
        }
    }
    
    // TODO - want to be able to produce AUFBV programs as well
    // TODO - this converts the whole program into one big SMT program
    //  - might want the option to produce many individual programs, i.e.
    //  one for each assertion, or a form that accommodates push/pop/coreids etc.
    
    public ICommand.IScript convert(BasicProgram program, SMT smt) {
        script = new Script();
        ICommand c;
        commands = script.commands();
        
        // FIXME - use factory for the commands?
        // set any options
        c = new C_set_option(F.keyword(":produce-models"),F.symbol("true"));
        commands.add(c);
        
        // set the logic
        String s = JmlOption.value(context, JmlOption.LOGIC);
        if (useBV && !s.equals("ALL")) s = "QF_AUFBV";
        c = new C_set_logic(F.symbol(s));
        commands.add(c);
        
        // add background statements
        // declare the sorts we use to model Java+JML
        // (declare-sort REF 0)
        c = new C_declare_sort(F.symbol(REF),zero);
        commands.add(c);
        // define NULL as a REF: (declare-fun NULL () REF)
        c = new C_declare_fun(nullSym,emptyList, refSort);
        commands.add(c);
        // define THIS as a REF: (declare-fun THIS () REF)
        c = new C_declare_fun(thisSym,emptyList, refSort);
        commands.add(c);
        // define stringConcat: (declare-fun stringConcat (REF,REF) REF)
        c = new C_declare_fun(F.symbol(concat),Arrays.asList(refSort,refSort), refSort);
        commands.add(c);
        if (!useBV) {
        	// define stringLength: (declare-fun stringLength (REF) Int)
        	c = new C_declare_fun(F.symbol("stringLength"),Arrays.asList(refSort), intSort); // FIXME - not sure this =is used
        	commands.add(c);
        }
        // THIS != NULL: (assert (distinct THIS NULL))
        c = new C_assert(F.fcn(distinctSym, thisSym, nullSym)); // SMT defined name
        commands.add(c);
        // (assert __JMLlength () (Array REF Int))
        if (!useBV) {
        	c = new C_declare_fun(lengthSym,
        			emptyList, 
        			F.createSortExpression(arraySym,refSort,intSort)
        			);
        	commands.add(c);  // FIXME - is this a duplicate ?
            // array lengths are always non-negative
        	if (quantOK) addCommand(smt,"(assert (forall ((o "+REF+")) (>= (select "+arrayLength+" o) 0)))");
        }

            // result of string concatenation is always non-null
        if (quantOK) addCommand(smt,"(assert (forall ((s1 "+REF+")(s2 "+REF+")) (distinct ("+concat+" s1 s2) "+NULL+")))");

        // The following functions model aspects of Java+JML;
        // The strings here are arbitrary except that they must not conflict with 
        // identifiers from the Java program as mapped into SMT identifiers
        List<ISort> args = Arrays.asList(refSort); // List of one element 
        if (!useBV) {
        	c = new C_declare_fun(F.symbol("asIntArray"),args, F.createSortExpression(arraySym,intSort,intSort));
        	commands.add(c);
            c = new C_declare_fun(F.symbol("asREFArray"),args, F.createSortExpression(arraySym,intSort,refSort));
            commands.add(c);
        	c = new C_declare_fun(F.symbol("intValue"),args, intSort);
        	commands.add(c);
        }
        c = new C_declare_fun(F.symbol("booleanValue"),args, boolSort);
        commands.add(c);
//        if (!useBV) {
//        	c = new C_declare_fun(lengthSym,
//        			Arrays.asList(new ISort[]{refSort}), 
//        			intSort);
//        	commands.add(c);
//        }
        
        int loc = addTypeModel(smt);
        
        // List types that we always want defined in the SMT script, whether
        // or not they are explicitly used in the input program 
        addType(syms.objectType);
        addType(syms.exceptionType);
        addType(syms.runtimeExceptionType);
        
        // Now translate all the programs background assertions
        for (JCExpression e: program.background()) {
            try {
                scan(e);
                commands.add(new C_assert(result));
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better error recovery?
            }
        }
        
        // The 'defined' set holds all Names that have already had SMT definitions issued
        // We have already defined some names - record that fact.
        
        defined.add(names.fromString(this_));
        defined.add(names.fromString(arrayLength));
        
        // Add the rest that are recorded in the basic block program
        for (JCIdent id: program.declarations) {
            if (defined.add(id.name)) {
                try {
                    ISort sort = convertSort(id.type);
                    String nm = id.name.toString();
                    // FIXME - I don't think 'this' should ever get this far
                    if (id.sym.owner instanceof Symbol.ClassSymbol && !Utils.instance(context).isJMLStatic(id.sym) && !id.sym.name.toString().equals("this")) {
                        // The name is a non-static field of a class, so the sort is an SMT Array
                        sort = F.createSortExpression(arraySym,refSort,sort);
                    } else if (nm.startsWith(arrays_)) {
                        // FIXME - review modeling of arrays
                        sort = convertSort(((Type.ArrayType)id.type).getComponentType());
                        sort = F.createSortExpression(arraySym,intSort,sort); // The type of the index is Int
                        sort = F.createSortExpression(arraySym,refSort,sort);
                    }
                    ISymbol sym = F.symbol(nm);
                    c = new C_declare_fun(sym,emptyList,sort);
                    commands.add(c);
                    bimap.put(id,sym);
                } catch (RuntimeException ee) {
                    // skip - error already issued// FIXME - better error recovery?
                }
            }
        }
        
        // add definitions
        for (BasicProgram.Definition e: program.definitions()) {
            try {
                scan(e.value);
                ISymbol sym = F.symbol(e.id.toString());
                c = new C_define_fun(sym,
                        new LinkedList<IDeclaration>(),
                        convertSort(e.id.type),
                        result);
                commands.add(c);
                bimap.put(e.id,sym);
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better error recovery?
            }
        }
        
        // Because blocks have forward references to later blocks, but
        // backward references to variables in earlier blocks, we declare
        // all the block variables first
        for (BasicProgram.BasicBlock b: program.blocks()) {
            ICommand cc = new C_declare_fun(F.symbol(b.id.toString()), emptyList, F.Bool());
            commands.add(cc);
        }
        
        // add blocks
        for (BasicProgram.BasicBlock b: program.blocks()) {
            convertBasicBlock(b);
        }
        
        {
            // Add an assertion that negates the start block id
            LinkedList<IExpr> argss = new LinkedList<IExpr>();
            argss.add(F.symbol(program.startId().name.toString()));
            IExpr negStartID = F.fcn(F.symbol("not"), argss);
            ICommand cc = new C_assert(negStartID);
            commands.add(cc);
        }
        
        // (push 1)
        ICommand cc = new C_push(F.numeral(1));
        commands.add(cc);
        // (assert (= __JML_AssumeCheck 0)) 
        IExpr.ILiteral z = !useBV ? zero : F.hex("00000000");
        cc = new C_assert(F.fcn(eqSym,F.symbol(JmlAssertionAdder.assumeCheckVar),z));
        commands.add(cc);
        // (push 1)
        cc = new C_push(F.numeral(1));
        commands.add(cc);
        // (check-sat)
        cc = new C_check_sat();
        commands.add(cc);
        
        addTypeRelationships(loc,smt);
        
        return script;
    }
    
    /** Adds a command expressed as a string */
    protected void addCommand(SMT smt, String command) {
        try {
            Configuration cf = smt.smtConfig;
            ICommand c = cf.smtFactory.createParser(cf,cf.smtFactory.createSource(command,null)).parseCommand();
            commands.add(c);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }
    
    /** The String that is the encoding of a given Type */
    // Note: Various SMT solvers do not yet handle special characters 
    // properly - some do not like the vertical bar quotes and some don't like
    // periods.
    public String typeString(Type t) {
        if (t.getTag() == TypeTag.ARRAY){
            return typeString(((ArrayType)t).elemtype) + "_A_";
        }
        return t.tsym.toString().replace(".", "_");
    }
    
//    public String arrayOf(Type t) {
//        return "T_" + typeString(t) + "_A_";
//    }
//    
//    public String jmlarrayOf(Type t) {
//        return "JMLT_" + typeString(t) + "_A_";
//    }
    
    /** Returns an SMT Symbol representing the given Java type */
    public IExpr javaTypeSymbol(Type t) {
        //String s = "|T_" + t.toString() + "|";
        if (t.getTag() == TypeTag.ARRAY) {
            Type comptype = ((Type.ArrayType)t).getComponentType();
            IExpr e = javaTypeSymbol(comptype);
            return F.fcn(F.symbol("_makeArrayType"),e);
        }
        if (t.getTag() == TypeTag.BOT) t = syms.objectType;
        else if (!t.isPrimitive()) t = t.tsym.erasure(jmltypes);
        
        String s = "T_" + typeString(t);
        return F.symbol(s);
    }
    
    private int wildcardCount = 0;
    
    /** Returns an SMT IExpr representing the given JML type */
    public IExpr jmlTypeSymbol(Type t) {
        if (t.getTag() == TypeTag.BOT) t = syms.objectType;
        if (t.getTag() == TypeTag.ARRAY) {
            Type comptype = ((Type.ArrayType)t).getComponentType();
            IExpr e = jmlTypeSymbol(comptype);
            return F.fcn(F.symbol("_makeJMLArrayType"),e);
        }
        if (t.getTag() == TypeTag.TYPEVAR) {
            String s = "JMLTV_" + typeString(t);
            return F.symbol(s);
        } else if (!t.tsym.type.isParameterized() || t.getTypeArguments().isEmpty()) {
            if (t instanceof Type.WildcardType || t instanceof Type.CapturedType) {
                String s = "JMLTV_" + "WILD" + (++wildcardCount);
                ISymbol sym = F.symbol(s);
                return sym;
            } else {
                String s = "JMLT_" + typeString(t);
                return F.symbol(s);
            }
        } else {
            List<Type> params = t.getTypeArguments();
            List<IExpr> args = new LinkedList<IExpr>();
            args.add(javaTypeSymbol(t));
            for (Type tt: params) {
                args.add(jmlTypeSymbol(tt));
            }
            return F.fcn(F.symbol("_JMLT_"+params.size()), args);
        }
    }
    
    /** Records a type as defined. */
    public void addType(Type t) {
        // FIXME - what if t is the type of an explicit null?
        if (t instanceof ArrayType) {
            t = ((ArrayType)t).getComponentType();
            addType(t);
        } else {
            if (javaTypeSymbols.add(t.tsym.toString())) {
                javaTypes.add(t);
                // We must record the bounds, but with caution since it can cause infinite recursion, in cases such as class Test<K extends Comparable<K>, O>
                if (t.getTag()  == TypeTag.TYPEVAR && !(t instanceof Type.WildcardType)) {
                    addType( ((Type.TypeVar)t).getUpperBound() );
                }
            }
            if (t.tsym.type.isParameterized()) { // true if is or should be parameterized
                if (t.getTypeArguments().size() != 0) {
                    boolean ok = true;
                    for (Type ti: t.getTypeArguments()) {
                        if (ti.getTag() == TypeTag.TYPEVAR) ok = false; 
                        if (ti.getTag() == TypeTag.WILDCARD) ok = false; 
                        addType(ti);
                    }
                    if (ok) javaParameterizedTypes.put(t.toString(),jmlTypeSymbol(t));  // FIXME - only when fully a constant and fully parameterized?
                } else {
                    if (javaTypeSymbols.add(t.tsym.toString())) {
                        javaTypes.add(t);
                    }
                    // This is an unparameterized use of a should-be-parameterized class symbol
//                    javaParameterizedTypes.put(t.toString(),jmlTypeSymbol(t)); // FIXME - should we make an implicit argument?
                }
            } else if (t.getTag() != TypeTag.TYPEVAR && t.getTag() != TypeTag.WILDCARD) {
                IExpr tt = F.fcn(F.symbol("_JMLT_0"),javaTypeSymbol(t));
                javaParameterizedTypes.put(tt.toString(),tt);  // FIXME - only when fully a constant?
            }
        }
//        if (t.getTag() == TypeTag.TYPEVAR && !(t instanceof Type.WildcardType)) {
//            addType( ((Type.TypeVar)t).getUpperBound() );
//        }
    }
    
    /** Converts a BasicBlock into SMTLIB, adding commands into the
     * current 'commands' list.
     */
    public void convertBasicBlock(BasicProgram.BasicBlock block) {
        ListIterator<JCStatement> iter = block.statements.listIterator();
        IExpr tail; 
        if (block.followers.isEmpty()) {
            tail = F.symbol("true");
        } else if (block.followers.size() == 1) {
            tail = F.symbol(block.followers.get(0).id.name.toString());
        } else {
            ArrayList<IExpr> args = new ArrayList<IExpr>();
            for (BasicProgram.BasicBlock bb: block.followers) {
                args.add(F.symbol(bb.id.name.toString()));
            }
            tail = F.fcn(F.symbol("and"),args);
        }
        
        // First add all declarations
        while (iter.hasNext()) {
            convertDeclaration(iter.next());
        }
        // Then construct the block expression from the end to the start
//        iter = block.statements.listIterator();
//        tail = convertList(iter,tail);
        tail = convertList(block.statements,tail);
        
        // This would be an excellent candidate for iterating through the list of 
        // statements in the block in reverse order, since that is the
        // natural way to construct the block expression and avoids having
        // a deep call stack (of the length of a block). However, the statements
        // in the block have to be translated in forward order, or auxiliary
        // commands produced in their translations are added to 'commands' in
        // reverse order.
        //        while (iter.hasPrevious()) {
        //            tail = convertStatement(iter.previous(),tail);
        //        }
        LinkedList<IExpr> args = new LinkedList<IExpr>();
        args.add(F.symbol(block.id.toString()));
        args.add(tail);
        tail = F.fcn(eqSym,args);
        commands.add(new C_assert(tail));
        
    }
    
    /** If the statement is a variable declaration, converts it to an SMT
     * declare-fun or define-fun of the appropriate sort, depending on whether
     * there is an initializer or not.
     * @param stat
     */
    public void convertDeclaration(JCStatement stat) {
        if (stat instanceof JmlVariableDecl) {
            try {
                JmlVariableDecl decl = (JmlVariableDecl)stat;
                // convert to a declaration or definition
                IExpr init = decl.init == null ? null : convertExpr(decl.init);
                
                ISymbol sym = F.symbol(decl.name.toString());
                ICommand c = init == null ?
                        new C_declare_fun(
                                sym,
                                emptyList,
                                convertSort(decl.type))
                : new C_define_fun(
                        sym,
                        new LinkedList<IDeclaration>(),
                        convertSort(decl.type),
                        init);
                 commands.add(c);
                 // An identifier may be appended to a JmlVariableDecl simply
                 // to have an expression with which to associated an SMT value
                 if (decl.ident != null) bimap.put(decl.ident, sym);
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better recovery
            }
        }
    }
    
    /** The alternate implementation, commented out below, uses recursive calls
     * to assemble the block encoding. That can give quite deep call stacks. 
     * Instead we iterate down the list and back, storing each expression on 
     * a stack. So replace the call stack with a simple expression stack.
     */
    public IExpr convertList(List<JCStatement> list, IExpr tail) {
        ListIterator<JCStatement> iter = list.listIterator();
        Stack<IExpr> stack = new Stack<IExpr>();
        
        while (iter.hasNext()) {
            JCStatement stat = iter.next();
            try {
                if (stat instanceof JmlVariableDecl) {
                    continue;
                } else if (stat instanceof JmlStatementExpr) {
                    JmlStatementExpr s = (JmlStatementExpr)stat;
                    if (s.token == JmlTokenKind.ASSUME) {
                        if (s.label == Label.METHOD_DEFINITION) {
                            JCExpression ex = s.expression;
                            ex = ((JmlQuantifiedExpr)ex).value;
                            JCExpression lhs = ((JCTree.JCBinary)ex).lhs;
                            JCTree.JCMethodInvocation mcall = (JCTree.JCMethodInvocation)lhs;
                            JCExpression nm = mcall.meth;
                            JCExpression rhs = ((JCTree.JCBinary)ex).rhs;
                            addFunctionDefinition(nm.toString(),mcall.args,rhs);
                        } else {
                            IExpr exx = convertExpr(s.expression);
                            stack.push(exx);
                        }
                    } else if (s.token == JmlTokenKind.ASSERT) {
                        IExpr exx = convertExpr(s.expression);
                        stack.push(exx);
                    } else if (s.token == JmlTokenKind.COMMENT) {
                        if (s.id == null || !s.id.startsWith("ACHECK")) continue;
                        int k = s.id.indexOf(" ");
                        k = Integer.valueOf(s.id.substring(k+1));
                        s.optionalExpression = k != assumeCount ? null : (treeutils.falseLit);;
                        if (k != assumeCount) continue;
                        IExpr exx = convertExpr(treeutils.falseLit);
                        stack.push(exx);
                    } else {
                        log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.token);
                        break;
                    }
                } else {
                    log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
                    break;
                }
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better recovery
                break;
            }
        }
        while (iter.hasPrevious()) {
            JCStatement stat = iter.previous();
            try {
                if (stat instanceof JmlVariableDecl) {
                    continue;
                } else if (stat instanceof JmlStatementExpr) {
                    JmlStatementExpr s = (JmlStatementExpr)stat;
                    if (s.token == JmlTokenKind.ASSUME) {
                        if (s.label == Label.METHOD_DEFINITION) {
                            // skip
                        } else {
                            IExpr exx = stack.pop();
                            tail = F.fcn(impliesSym, exx, tail);
                        }
                    } else if (s.token == JmlTokenKind.ASSERT) {
                        IExpr exx = stack.pop();
                        // The first return is the classic translation; the second
                        // effectively inserts an assume after an assert. I'm not
                        // sure it makes any difference. TODO - evaluate this sometime.
                        //return F.fcn(F.symbol("and"), exx, tail);
                        tail = F.fcn(F.symbol("and"), exx, F.fcn(impliesSym, exx, tail));
                    } else if (s.token == JmlTokenKind.COMMENT) {
                        if (s.id == null || !s.id.startsWith("ACHECK")) continue;
                        int k = s.id.indexOf(" ");
                        k = Integer.valueOf(s.id.substring(k+1));
                        if (k != assumeCount) continue;
                        IExpr exx = stack.pop();
                        tail = exx;
                    } else {
                        log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.token);
                        break;
                    }
                } else {
                    log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
                    break;
                }
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better recovery
                break;
            }
        }
        return tail;
    }
    
//    public IExpr convertList(ListIterator<JCStatement> iter, IExpr tail) {
//        //Stack<IExpr> stack = new Stack<IExpr>();
//        
//        while (iter.hasNext()) {
//            JCStatement stat = iter.next();
//            try {
//                if (stat instanceof JmlVariableDecl) {
//                    continue;
//                } else if (stat instanceof JmlStatementExpr) {
//                    JmlStatementExpr s = (JmlStatementExpr)stat;
//                    if (s.token == JmlToken.ASSUME) {
//                        IExpr exx = convertExpr(s.expression);
//                        tail = convertList(iter,tail);
//                        return F.fcn(impliesSym, exx, tail);
//                    } else if (s.token == JmlToken.ASSERT) {
//                        IExpr exx = convertExpr(s.expression);
//                        tail = convertList(iter,tail);
//                        // The first return is the classic translation; the second
//                        // effectively inserts an assume after an assert. I'm not
//                        // sure it makes any difference. TODO - evaluate this sometime.
//                        //return F.fcn(F.symbol("and"), exx, tail);
//                        return F.fcn(F.symbol("and"), exx, F.fcn(impliesSym, exx, tail));
//                    } else if (s.token == JmlToken.COMMENT) {
//                        continue;
//                    } else {
//                        log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.token);
//                        break;
//                    }
//                } else {
//                    log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
//                    break;
//                }
//            } catch (RuntimeException ee) {
//                // skip - error already issued // FIXME - better recovery
//                break;
//            }
//        }
//        return tail;
//    }
    
    /** Converts a basic block statement to an SMT expression, tacking it on
     * the front of tail and returning the composite expression.
     */
    public IExpr convertStatement(JCStatement stat, IExpr tail) {
        try {
            if (stat instanceof JmlVariableDecl) {
                 return tail;
            } else if (stat instanceof JmlStatementExpr) {
                JmlStatementExpr s = (JmlStatementExpr)stat;
                if (s.token == JmlTokenKind.ASSUME) {
                    IExpr exx = convertExpr(s.expression);
                    LinkedList<IExpr> args = new LinkedList<IExpr>();
                    args.add(exx);
                    args.add(tail);
                    return F.fcn(impliesSym, args);
                } else if (s.token == JmlTokenKind.ASSERT) {
                    IExpr exx = convertExpr(s.expression);
                    LinkedList<IExpr> args = new LinkedList<IExpr>();
                    args.add(exx);
                    args.add(tail);
                    return F.fcn(F.symbol("and"), args);
                } else if (s.token == JmlTokenKind.COMMENT) {
                    return tail;
                } else {
                    log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.token);
                }
            } else {
                log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
            }
        } catch (RuntimeException ee) {
            // skip - error already issued // FIXME - better recovery
        }
        return tail;
        
    }
    
    
    // FIXME - review this - need to choose between java and jml - may depend on the artihmetic mode
    /** Converts a Java/JML type into an SMT Sort */
    public ISort convertSort(Type t) {
        if ( t == null) {
            log.error("jml.internal", "No type translation implemented when converting a BasicProgram to SMTLIB: " + t);
            throw new RuntimeException();
        } else {
 //           if (t.toString().equals("\\bigint")) Utils.stop();
            TypeTag tag = t.getTag();
            if (tag == TypeTag.BOOLEAN) {
                return F.Bool();
            } else if (tag == TypeTag.INT) { 
                return useBV ? bv32Sort : intSort;
            } else if (tag == syms.objectType.getTag()) {
                return refSort;
            } else if (tag == TypeTag.SHORT) { 
                return useBV ? bv16Sort : intSort;
            } else if (tag == TypeTag.CHAR) { 
                return intSort;
            } else if (tag == TypeTag.BYTE) { 
                return useBV ? bv8Sort : intSort;
            } else if (tag == TypeTag.LONG) { 
                return useBV ? bv64Sort : intSort;
            } else if (tag == TypeTag.FLOAT) { 
                addReal();
                return realSort;
            } else if (tag == TypeTag.DOUBLE) { 
                addReal();
                return realSort;
            } else if (tag == TypeTag.ARRAY) {
                return refSort;
            } else if (tag == TypeTag.BOT) {
                return refSort;
            } else if (tag == TypeTag.NONE || tag == TypeTag.UNKNOWN){
                if (t instanceof JmlType) {
                    JmlType jt = (JmlType)t;
                    if (jt.jmlTypeTag() == JmlTokenKind.BSBIGINT) return intSort; 
                    if (jt.jmlTypeTag() == JmlTokenKind.BSREAL) return realSort; 
                    if (jt.jmlTypeTag() == JmlTokenKind.BSTYPEUC) return jmlTypeSort;
                }
                // FIXME - errors
                return refSort; // FIXME - just something
            } else if (t instanceof Type.TypeVar) {
                return refSort;
            } else {
                // FIXME - what gets here?
                return F.createSortExpression((ISymbol)javaTypeSymbol(t)); // FIXME - use the common method for translating to type names?
                //            log.error("jml.internal", "No type translation implemented when converting a BasicProgram to SMTLIB: " + t);
                //            throw new RuntimeException();
            }
        }
    }
    
    /** Converts an AST expression into SMT form. */
    public IExpr convertExpr(JCExpression expr) {
        scan(expr);
        return result;
    }
    
    // We need to be able to translate expressions
    
    /** Issues a error message about the AST node not being implemented */
    public void notImpl(JCTree tree) {
        log.error(tree, "esc.not.implemented","Not yet supported expression node in converting BasicPrograms to SMTLIB: " + tree.getClass());
    }
    
    /** Issues an error message about something not being implemented */
    public void notImpl(DiagnosticPosition pos, String msg) {
        log.error(pos, "esc.not.implemented","Not yet supported feature in converting BasicPrograms to SMTLIB: " + msg);
    }
    
    /** Issues an error message that a particular AST node should not be being used in the input basic block program */
    public void shouldNotBeCalled(JCTree tree) {
        log.error(tree, "jml.internal","This node should not be present in converting BasicPrograms to SMTLIB: " + tree.getClass() + " " + tree.toString());
    }
    
    /** A set to hold the names of implicit functions that have been defined so far
     * (so we don't duplicate definitions).
     */
    protected Set<String> fcnsDefined = new HashSet<String>();
    
    /** Adds a function with the given name and a definition if it is not already added. */
    protected void addFcn(String newname, JCMethodInvocation tree) {
        if (fcnsDefined.add(newname)) {
            // Was not already present
            ISymbol n = F.symbol(newname);
            ISort resultSort = convertSort(tree.type);
            List<ISort> argSorts = new LinkedList<ISort>();
//            // Adds an argument for the receiver, if the function is not static - TODO: do we ever use this?
//            if (tree.meth instanceof JCFieldAccess && ((JCFieldAccess)tree.meth).selected != null && !((JCFieldAccess)tree.meth).sym.isStatic()) {
//                argSorts.add(refSort);
//            }
            for (JCExpression e: tree.args) {
                argSorts.add(convertSort(e.type));
            }
            C_declare_fun c = new C_declare_fun(n,argSorts,resultSort);
            commands.add(c);
        }
        
    }
    
    protected void addFunctionDefinition(String newname, List<JCExpression> args, JCExpression expr) {
        if (fcnsDefined.add(newname)) {
            // Was not already present
            ISymbol n = F.symbol(newname);
            ISort resultSort = convertSort(expr.type);
            List<IDeclaration> argDecls = new LinkedList<IDeclaration>();
//            // Adds an argument for the receiver, if the function is not static - TODO: do we ever use this?
//            if (tree.meth instanceof JCFieldAccess && ((JCFieldAccess)tree.meth).selected != null && !((JCFieldAccess)tree.meth).sym.isStatic()) {
//                argSorts.add(refSort);
//            }
            for (JCExpression e: args) {
                IDeclaration d = F.declaration(F.symbol(e.toString()),convertSort(e.type));
                argDecls.add(d);
            }
            C_define_fun c = new C_define_fun(n, argDecls, resultSort, convertExpr(expr));
            commands.add(c);
        }
        
    }
    
    // FIXME - review this
    @Override
    public void visitApply(JCMethodInvocation tree) {
        JCExpression m = tree.meth;
        if (m instanceof JCIdent) {
            String name = ((JCIdent)m).name.toString();
            String newname = name;
            addFcn(newname,tree);
            List<IExpr> newargs = new LinkedList<IExpr>();
            for (JCExpression arg: tree.args) {
                newargs.add(convertExpr(arg));
            }
            if (newargs.isEmpty()) result = F.symbol(newname);
            else result = F.fcn(F.symbol(newname),newargs);
            return;

        } else if (m == null) {
            if (tree instanceof JmlBBFieldAssignment) {
                IExpr.IFcnExpr right = F.fcn(F.symbol("store"),
                        convertExpr(tree.args.get(1)),
                        convertExpr(tree.args.get(2)),
                        convertExpr(tree.args.get(3))
                        );
                result = F.fcn(eqSym, convertExpr(tree.args.get(0)),right);
                return;
            }
            else if (tree instanceof JmlBBArrayAssignment) {
                if (tree.args.length() > 3) {
                    // [0] = store([1],[2], store(select([1],[2]),[3],[4]))
                    IExpr.IFcnExpr sel = F.fcn(selectSym,
                            convertExpr(tree.args.get(1)),
                            convertExpr(tree.args.get(2))
                            );
                    IExpr.IFcnExpr newarray = F.fcn(F.symbol("store"),
                            sel,
                            convertExpr(tree.args.get(3)),
                            convertExpr(tree.args.get(4))
                            );

                    IExpr.IFcnExpr right = F.fcn(F.symbol("store"),
                            convertExpr(tree.args.get(1)),
                            convertExpr(tree.args.get(2)),
                            newarray
                            );
                    result = F.fcn(eqSym, convertExpr(tree.args.get(0)),right);
                } else {
                    // [0] = store([1],[2], select([0],[2]))
                    IExpr arg0 = convertExpr(tree.args.get(0));
                    IExpr arg2 = convertExpr(tree.args.get(2));
                    IExpr.IFcnExpr sel = F.fcn(selectSym,
                            arg0,
                            arg2
                            );

                    IExpr.IFcnExpr newarray = F.fcn(F.symbol("store"),
                            convertExpr(tree.args.get(1)),
                            arg2,
                            sel
                            );
                    result = F.fcn(eqSym, arg0,newarray);                    
                }
                return;
            }
        } else if (m instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)m;
            String name = fa.name.toString();
            String newname = null;
            if (Utils.instance(context).isJMLStatic(fa.sym)) {
                // FIXME The fully qualifiedness should be done in BasicBlocking
                newname = "_" + m.toString();
                addFcn(newname,tree);
            } else {
                // FIXME - the non-static should have a fiully qualified name as well
                newname = name;
                addFcn(newname,tree);
            }
            List<IExpr> newargs = new LinkedList<IExpr>();
            if (!Utils.instance(context).isJMLStatic(fa.sym)) newargs.add(convertExpr(fa.selected));
            for (JCExpression arg: tree.args) {
                newargs.add(convertExpr(arg));
            }
            result = F.fcn(F.symbol(newname),newargs);
            
        }
    }
    
    /** Converts a JML function-like expression: 
     * \type, \typeof, <:, \nonnullelements
     *
     */
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        if (that.token == JmlTokenKind.BSTYPELC) {
            if (that.toString().equals("\\typej(short)")) Utils.stop();
            Type t = that.args.get(0).type;
            addType(t);
            result = that.javaType ? javaTypeSymbol(t) : jmlTypeSymbol(t);
            return;
        }
        List<IExpr> newargs = new LinkedList<IExpr>();
        for (JCExpression e: that.args) {
            scan(e);
            newargs.add(result);
        }
        if (that.token == JmlTokenKind.SUBTYPE_OF) {
            result = F.fcn(F.symbol(JMLSUBTYPE), newargs);
        } else if (that.token == JmlTokenKind.JSUBTYPE_OF) {
            result = F.fcn(F.symbol(JAVASUBTYPE), newargs);
        } else if (that.token == JmlTokenKind.BSTYPEOF) {
            ISymbol s = that.javaType ? F.symbol("javaTypeOf") : F.symbol("jmlTypeOf");
            result = F.fcn(s, newargs);
        } else if (that.token == JmlTokenKind.BSNONNULLELEMENTS) {
            result = F.fcn(F.symbol(nonnullelements), newargs);
        } else if (that.token == JmlTokenKind.BSELEMTYPE) {
            result = F.fcn(F.symbol(arrayElemType), newargs);
        } else if (that.token == JmlTokenKind.BSERASURE) {
            result = F.fcn(F.symbol("erasure"), newargs);
        } else if (that.token == JmlTokenKind.BSDISTINCT) {
            result = F.fcn(distinctSym, newargs);
        } else if (that.meth != null) {
            // Built-in methods
            String n = that.meth.toString();
            if (n.equals("shortValue") || n.equals("byteValue") || n.equals("charValue") || n.equals("longValue")) n = "intValue";
            else if (n.equals("floatValue") || n.equals("doubleValue")) n = "realValue";
            result = F.fcn(F.symbol(n),newargs);
        } else {
            result = newargs.get(0); // FIXME - this is needed for \old and \pre but a better solution should be found (cf. testLabeled)
        }
    }

    @Override
    public void visitNewClass(JCNewClass tree) {
        shouldNotBeCalled(tree);
        super.visitNewClass(tree);
    }

    @Override
    public void visitNewArray(JCNewArray tree) {
        shouldNotBeCalled(tree);
        super.visitNewArray(tree);
    }

    @Override
    public void visitAssign(JCAssign tree) {
        shouldNotBeCalled(tree);
        super.visitAssign(tree);
    }

    @Override
    public void visitAssignop(JCAssignOp tree) {
        shouldNotBeCalled(tree);
        super.visitAssignop(tree);
    }

    @Override
    public void visitUnary(JCUnary tree) {
        JCTree.Tag op = tree.getTag();
        IExpr arg = convertExpr(tree.arg);
        LinkedList<IExpr> args = new LinkedList<IExpr>();
        args.add(arg);
        switch (op) {
            case NOT:
                result = F.fcn(F.symbol("not"), args);
                break;
            case NEG:
                if (useBV) 
                    result = F.fcn(F.symbol("bvneg"), args);
                else
                    result = F.fcn(F.symbol("-"), args);
                break;
            default:
                log.error("jml.internal","Don't know how to translate expression to SMTLIB: " + JmlPretty.write(tree));
                throw new RuntimeException();
        }
    }
    
    @Override public void visitParens(JCParens that) {
        // Since SMT-LIB consists of S-expressions, we do not need to 
        // add additional parentheses for resolving precedence
        super.visitParens(that);
    }


    @Override
    public void visitBinary(JCBinary tree) {
        JCTree.Tag op = tree.getTag();
        if (op == JCTree.Tag.EQ && tree.lhs.toString().equals("(double)0")) Utils.stop();
        IExpr lhs = convertExpr(tree.lhs);
        IExpr rhs = convertExpr(tree.rhs);
        LinkedList<IExpr> args = new LinkedList<IExpr>();
        args.add(lhs);
        args.add(rhs);
        switch (op) {
            case EQ:
                result = F.fcn(eqSym, args);
                if (result.toString().equals("(= java.lang.Short_TYPE JMLT_short)")) Utils.stop();
                break;
            case NE:
                result = F.fcn(distinctSym, args);
                break;
            case AND:
                result = F.fcn(F.symbol("and"), args);
                break;
            case OR:
                result = F.fcn(F.symbol("or"), args);
                break;
            case LT:
                if (useBV) 
                    result = F.fcn(F.symbol("bvslt"), args);
                else
                    result = F.fcn(F.symbol("<"), args);
                break;
            case LE:
                if (useBV) 
                    result = F.fcn(F.symbol("bvsle"), args);
                else
                    result = F.fcn(F.symbol("<="), args);
                break;
            case GT:
                if (useBV) 
                    result = F.fcn(F.symbol("bvsgt"), args);
                else
                    result = F.fcn(F.symbol(">"), args);
                break;
            case GE:
                if (useBV) 
                    result = F.fcn(F.symbol("bvsge"), args);
                else
                    result = F.fcn(F.symbol(">="), args);
                break;
            case PLUS:
                if (tree.lhs.type.getTag() == TypeTag.CLASS) {
                    result = F.fcn(F.symbol(concat), args);
                } else if (useBV) {
                	result = F.fcn(F.symbol("bvadd"), args);
                } else {
                    result = F.fcn(F.symbol("+"), args);
                }
                break;
            case MINUS:
            	if (useBV)
            		result = F.fcn(F.symbol("bvsub"), args);
            	else
            		result = F.fcn(F.symbol("-"), args);
                break;
            case MUL:
            	if (useBV)
            		result = F.fcn(F.symbol("bvmul"), args);
            	else
            		result = F.fcn(F.symbol("*"), args);
                break;
            case DIV:
                // FIXME - what kinds of primitive types should be expected
                if (tree.type.getTag() == TypeTag.FLOAT)
                    result = F.fcn(F.symbol("/"), args);
                else if (tree.type.getTag() == TypeTag.DOUBLE)
                    result = F.fcn(F.symbol("/"), args);
                else if (useBV)
                	result = F.fcn(F.symbol("bvdiv"), args);
                else
                    result = F.fcn(F.symbol("div"), args);
                break;
            case MOD:
                if (useBV)
                    result = F.fcn(F.symbol("bvurem"), args);
                else
                    result = F.fcn(F.symbol("mod"), args);
                break;
                // FIXME - implement bit operations
            case BITAND:
                if (tree.type.getTag() == TypeTag.BOOLEAN) {
                    result = F.fcn(F.symbol("and"), args);
                } else if (useBV) {
                	result = F.fcn(F.symbol("bvand"), args);
                } else {
                    notImpl(tree, "Bit-operation " + op);
                }
                break;
            case BITOR:
                if (tree.type.getTag() == TypeTag.BOOLEAN) {
                    result = F.fcn(F.symbol("or"), args);
                } else if (useBV) {
                	result = F.fcn(F.symbol("bvor"), args);
                } else {
                    notImpl(tree, "Bit-operation " + op);
                }
                break;
            case BITXOR:
                if (tree.type.getTag() == TypeTag.BOOLEAN) {
                    result = F.fcn(F.symbol("distinct"), args);
                } else if (useBV) {
                	result = F.fcn(F.symbol("bvxor"), args);
                } else {
                    notImpl(tree, "Bit-operation " + op);
                }
                break;
            case SL:
            	if (useBV) {
            		result = F.fcn(F.symbol("bvshl"), args);
            	} else {
            		notImpl(tree, "Bit-operation " + op);
            	}
                break;
            case SR:
            	if (useBV) {
            		result = F.fcn(F.symbol("bvshr"), args);
            	} else {
            		notImpl(tree, "Bit-operation " + op);
            	}
                break;
            case USR:
            	if (useBV) {
            		result = F.fcn(F.symbol("bvlshl"), args);
            	} else {
            		notImpl(tree, "Bit-operation " + op);
            	}
                break;
            default:
                log.error("jml.internal","Don't know how to translate expression to SMTLIB: " + JmlPretty.write(tree));
                throw new RuntimeException();
        }
    }

    @Override
    public void visitTypeCast(JCTypeCast tree) {
        result = convertExpr(tree.expr);
        if (tree.type.isPrimitive() == tree.expr.type.isPrimitive()) {
            TypeTag tagr = tree.type.getTag();
            TypeTag tage = tree.expr.type.getTag();
            if (tagr == TypeTag.NONE || tagr == TypeTag.UNKNOWN) { 
                if (tage == TypeTag.NONE || tage == TypeTag.UNKNOWN) { 
                    if (((JmlType)tree.type).jmlTypeTag() == JmlTokenKind.BSBIGINT) {
                        if (((JmlType)tree.expr.type).jmlTypeTag() == JmlTokenKind.BSBIGINT) {
                            // \bigint to \bigint -- OK
                        } else if ( ((JmlType)tree.expr.type).jmlTypeTag() == JmlTokenKind.BSREAL) {
                            // \real to \bigint
                            result = F.fcn(F.symbol("to_int"), result);
                        } else {
                            // FIXME - error
                        }
                    } else if ( ((JmlType)tree.type).jmlTypeTag() == JmlTokenKind.BSREAL) {
                        if (((JmlType)tree.expr.type).jmlTypeTag() == JmlTokenKind.BSBIGINT) {
                            // \bigint to \real
                            result = F.fcn(F.symbol("to_real"), result);
                        } else if ( ((JmlType)tree.expr.type).jmlTypeTag() == JmlTokenKind.BSREAL) {
                            // \real to \real -- OK
                        } else {
                            // FIXME - error
                        }
                    } else {
                        // FIXME - error
                    }
                    
                } else if (treeutils.isIntegral(tage)) {
                    if (((JmlType)tree.type).jmlTypeTag() == JmlTokenKind.BSBIGINT) {
                        // int to \bigint -- OK
                    } else if ( ((JmlType)tree.type).jmlTypeTag() == JmlTokenKind.BSREAL) {
                        // int to \real
                        result = F.fcn(F.symbol("to_real"), result);
                    } else {
                        // FIXME - error
                    }
                } else {
                    if (((JmlType)tree.type).jmlTypeTag() == JmlTokenKind.BSBIGINT) {
                        // float/double to \bigint
                        result = F.fcn(F.symbol("to_int"), result);
                    } else if ( ((JmlType)tree.type).jmlTypeTag() == JmlTokenKind.BSREAL) {
                        // float/double to \real -- OK
                    } else {
                        // FIXME - error
                    }
                }
            } else if (tage == TypeTag.NONE || tage == TypeTag.UNKNOWN) { 
                if (treeutils.isIntegral(tagr)) {
                    if (((JmlType)tree.expr.type).jmlTypeTag() == JmlTokenKind.BSBIGINT) {
                        // \bigint to int -- OK
                    } else if ( ((JmlType)tree.expr.type).jmlTypeTag() == JmlTokenKind.BSREAL) {
                        // \real to int -- FIXME
                        result = F.fcn(F.symbol("to_int"), result);
                    } else {
                        // FIXME - error
                    }
                } else {
                    if (((JmlType)tree.expr.type).jmlTypeTag() == JmlTokenKind.BSBIGINT) {
                        // \bigint to float/double -- FIXME
                        result = F.fcn(F.symbol("to_real"), result);
                    } else if ( ((JmlType)tree.expr.type).jmlTypeTag() == JmlTokenKind.BSREAL) {
                        // \real to float/double -- OK
                    } else {
                        // FIXME - error
                    }
                }
            } else if (!tree.type.isPrimitive()) {
                // This is a cast from reference type to reference type, we can ignore it
            } else if (tree.expr instanceof JCLiteral) {
                // Cast from one primitive literal to a another primitive type
                // Note that in SMT there is only Int and Real types (or bit-value types)
                // any restrictions on the range of a value must already be stated using assertions 
                Object v = ((JCLiteral)tree.expr).getValue();
                if (tage == tagr) {
                    // OK -- no change in type
                } else if (treeutils.isIntegral(tage) == treeutils.isIntegral(tagr)) {
                    // Both are integral or both are floating point
                    // OK -- no change in SMT type
                } else if (treeutils.isIntegral(tage)) {
                    // integral to real literal
                    java.math.BigInteger val = ((IExpr.INumeral)result).value();
                    result = makeRealValue(val.doubleValue());
                } else if (!treeutils.isIntegral(tage)) {
                    // FIXME - cast from double to integral
                } else if (tagr.ordinal() == TypeTag.DOUBLE.ordinal() || tagr.ordinal() == TypeTag.FLOAT.ordinal()) {
                    // Cast to real FIXME - already done?
                    Double d = new Double(v.toString());
                    result = makeRealValue(d.doubleValue());
                }
            } else {
                // cast from primitive to primitive for an expression
                boolean argIsInt = treeutils.isIntegral(tage);
                boolean resultIsInt = treeutils.isIntegral(tagr);
                if (argIsInt && !resultIsInt) {
                    // Requires int and real logic
                    // integral to real
                    result = F.fcn(F.symbol("to_real"), result);
                } else if (!argIsInt && resultIsInt) {
                    // Requires int and real logic
                    // real to int
                    result = F.fcn(F.symbol("to_int"), result);
                } else {
                    // no change in result
                }
            }
        } else if (!tree.type.isPrimitive()) {
            // Cast from primitive to object
            log.error(tree,"jml.internal","Do not expect casts to reference type in expressions: " + JmlPretty.write(tree));
        } else {
            // unboxing cast from object to primitive
            log.error(tree,"jml.internal","Do not expect casts from reference type in expressions: " + JmlPretty.write(tree));
            TypeTag tag = tree.type.getTag();
            switch (tag) {
                case INT:
                case LONG:
                case SHORT:
                case BYTE:
                case CHAR:
                case DOUBLE:
                case FLOAT:
                case BOOLEAN:
                    // FIXME - should this ever happen?
                    break;
                default:
                    log.error(tree,"jml.internal","Unknown type tag in translating an unboxing cast: " + tag + " " + JmlPretty.write(tree));
                    
            }
        }
    }

    @Override
    public void visitTypeTest(JCInstanceOf tree) {
        addType(tree.clazz.type);
        IExpr e = convertExpr(tree.expr);
        // instanceof is always false if the argument is null
        // and javaTypeOf is not defined for null arguments
        IExpr r1 = F.fcn(distinctSym, e, nullSym);
        IExpr r2 = F.fcn(F.symbol(JAVASUBTYPE),
                F.fcn(F.symbol("javaTypeOf"), e),
                javaTypeSymbol(tree.clazz.type));
        result = F.fcn(F.symbol("and"), r1, r2);
    }

    @Override
    public void visitIndexed(JCArrayAccess tree) {
        if (tree instanceof JmlBBArrayAccess) {
            JmlBBArrayAccess aa = (JmlBBArrayAccess)tree;
            // select(select(arraysId,a).i)
            IExpr.IFcnExpr sel = F.fcn(selectSym,
                    convertExpr(aa.arraysId),
                    convertExpr(aa.indexed)
                    );
            sel = F.fcn(selectSym,
                    sel,
                    convertExpr(aa.index)
                    );
            result = sel;
            return;
        }

        shouldNotBeCalled(tree);
    }
    
    @Override 
    public void visitConditional(JCConditional that) { 
        result = F.fcn(F.symbol("ite"), 
                convertExpr(that.cond), 
                convertExpr(that.truepart), 
                convertExpr(that.falsepart)
                );
    }


    /** A set of names of fields that are already defined */
    protected java.util.Set<Name> defined = new java.util.HashSet<Name>();
    
    @Override
    public void visitSelect(JCFieldAccess tree) {
        // o.f becomes f[o] where f has sort (Array REF type)
        if (tree.selected != null) {
            JCExpression object = tree.selected;
            Symbol field = tree.sym;
            if (field != syms.lengthVar) {
                IExpr.ISymbol name = F.symbol(tree.name.toString());
                if (defined.add(tree.name)) {
                    ISort arrsort = F.createSortExpression(arraySym,refSort,convertSort(field.type));
                    ICommand c = new C_declare_fun(name,emptyList,arrsort);
                    commands.add(c);
                }
                if (Utils.instance(context).isJMLStatic(field)) {
                    result = name;
                } else {
                    result = F.fcn(selectSym,
                                name,
                                object == null ? thisSym: convertExpr(object)
                                );
                }
            } else {
                IExpr sel = convertExpr(object);
                result = F.fcn(selectSym,F.symbol(arrayLength),sel);
                return;
            }
        }
        else shouldNotBeCalled(tree);
    }
    
    @Override
    public void visitIdent(JCIdent tree) {
        String n = tree.name.toString();
        if (n.equals("length")) { // FIXME - not sure about this - length as array length is always a field name
            result = F.symbol(arrayLength);
        } else {
            result = F.symbol(n);
        }
    }
    
    protected Map<Double,String> reals = new HashMap<Double,String>();
    
    @Override
    public void visitLiteral(JCLiteral tree) {
        Object v = tree.getValue();
        if (tree.typetag == TypeTag.BOOLEAN) {
           result = F.symbol(((Boolean)v) ?"true":"false"); 
        } else if (tree.typetag == TypeTag.INT || tree.typetag == TypeTag.LONG || tree.typetag == TypeTag.SHORT || tree.typetag == TypeTag.BYTE) {
        	long k = Long.parseLong(v.toString());
            if (useBV) {
            	int bits = tree.typetag == TypeTag.INT ? 32 :
     	                   tree.typetag == TypeTag.SHORT? 16 :
        	               tree.typetag == TypeTag.BYTE? 8 :
            	           tree.typetag == TypeTag.LONG? 64 :
            	        	0;
            	int digits = bits/4;
            	String format = "%0" + digits + "x";
            	String s = String.format(format, k); // Since k is a long, negative numbers are padded out with f's to a long length
            	if (s.length() != digits) {
            	    s = s.substring(s.length()-digits);
            	}
            	result = F.hex(s); // The string should not have leading 0x
            } else {
                result = k >= 0 ? F.numeral(k) : -k >= 0 ? F.fcn(F.symbol("-"), F.numeral(-k)) : F.fcn(F.symbol("-"), F.numeral(v.toString().substring(1)));
            }
        } else if (tree.typetag == TypeTag.CHAR) {
            long k = (v instanceof Character) ? (long) ((Character)v).charValue() : Long.parseLong(v.toString());
            result = F.numeral(k);
        } else if (tree.typetag == TypeTag.BOT) {
            result = nullSym;
        } else if (tree.typetag == TypeTag.CLASS) {
            // FIXME - every literal is different and we don't remember the value
            ISymbol sym = F.symbol("STRINGLIT"+(++stringCount)); 
            ICommand c = new C_declare_fun(sym,emptyList, refSort);
            commands.add(c);
            result = sym;
        } else if (tree.typetag == TypeTag.FLOAT || tree.typetag == TypeTag.DOUBLE) {
            result = makeRealValue((Double)v);
        } else {
            notImpl(tree);
            super.visitLiteral(tree);
        }
    }
    
    ISymbol makeRealValue(Double v) {
        // FIXME - we don't remember the value
        String id = reals.get(v);
        if (id == null) {
            id = "REALLIT"+(++doubleCount);
            reals.put(v, id);
            ISymbol sym = F.symbol(id);
            addReal();
            ICommand c = new C_declare_fun(sym,emptyList,realSort); // use definefun and a constant FIXME
            commands.add(c);
            return sym;
        } else {
            ISymbol sym = F.symbol(id);
            return sym;
        }
    }

    @Override public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) { notImpl(that); } // FIXME - maybe
    @Override public void visitJmlSetComprehension(JmlSetComprehension that) { notImpl(that); }
    @Override public void visitJmlSingleton(JmlSingleton that)               { notImpl(that); }

    @Override public void visitLetExpr(LetExpr that) { 
        
        Iterator<JCVariableDecl> iter = that.defs.iterator();
        result = doLet(iter,(JCExpression)that.expr);
    }
    
    // We need to create nested let expressions because the SMT let expression
    // does parallel bindings of initializers to variables, while Java does
    // sequential bindings.
    private IExpr doLet(Iterator<JCVariableDecl> iter, JCExpression expr) {
        if (iter.hasNext()) {
            JCVariableDecl decl = iter.next();
            IExpr.ISymbol sym = F.symbol(decl.name.toString());
            IExpr e = convertExpr(decl.init);
            List<IBinding> bindings = new LinkedList<IBinding>();
            bindings.add(F.binding(sym,e));
            return F.let(bindings, doLet(iter,expr));
        } else {
            return convertExpr(expr);
        }
    }

    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        boolean prev = inQuant;
        try {
            inQuant = true;
            List<IDeclaration> params = new LinkedList<IDeclaration>();
            for (JCVariableDecl decl: that.decls) {
                IExpr.ISymbol sym = F.symbol(decl.name.toString());
                ISort sort = convertSort(decl.type);
                params.add(F.declaration(sym, sort));
            }
            scan(that.range);
            IExpr range = result;
            scan(that.value);
            IExpr value = result;
            if (that.op == JmlTokenKind.BSFORALL) {
                if (range != null) value = F.fcn(impliesSym,range,value);
                result = F.forall(params,value);
            } else if (that.op == JmlTokenKind.BSEXISTS) {
                if (range != null) value = F.fcn(F.symbol("and"),range,value);
                result = F.exists(params,value);
            } else {
                notImpl(that, "JML Quantified expression using " + that.op.internedName());
            }
            // Can't do this, because then the quantified expression is evaluated
            // in the wrong context (I think)
            if (false && !prev) {
                // Because SMTLIB does not allow getValue to have arguments containing
                // quantifiers, we do the following: as long as the quantified
                // expression is not nested within another (technically could be
                // as long as it is closed), we define a temporary variable to
                // hold its value. We could use named 
                // SMTLIB expressions, but I'm not sure how widespread support
                // for that feature is.
                ISymbol tmp = F.symbol("_JMLSMT_tmp_" + (++uniqueCount));
                ICommand c = new C_declare_fun(tmp,emptyList,boolSort);
                commands.add(c);
                c = new C_assert(F.fcn(eqSym,  tmp, result));
                commands.add(c);
                result = tmp;
            }
        } finally {
            inQuant = prev;
        }
    }

    // FIXME - review and implement all these generic type visit functions,
    // or declare that they should not be called
    
    @Override
    public void visitTypeIdent(JCPrimitiveTypeTree tree) {
        notImpl(tree);
        super.visitTypeIdent(tree);
    }

    @Override
    public void visitTypeArray(JCArrayTypeTree tree) {
        notImpl(tree);
        super.visitTypeArray(tree);
    }

    @Override
    public void visitTypeApply(JCTypeApply tree) {
        notImpl(tree);
        super.visitTypeApply(tree);
    }

    @Override
    public void visitTypeUnion(JCTypeUnion tree) {
        notImpl(tree);
        super.visitTypeUnion(tree);
    }

    @Override
    public void visitTypeParameter(JCTypeParameter tree) {
        notImpl(tree);
        super.visitTypeParameter(tree);
    }

    @Override
    public void visitWildcard(JCWildcard tree) {
        notImpl(tree);
        super.visitWildcard(tree);
    }

    @Override
    public void visitTypeBoundKind(TypeBoundKind tree) {
        notImpl(tree);
        super.visitTypeBoundKind(tree);
    }
    
    // These should all be translated away prior to calling the basic blocker,
    // or should never be called in the first place, because they are not
    // expressions
    // FIXME - what about calls of anonymous classes
    @Override public void visitTopLevel(JCCompilationUnit that)    { shouldNotBeCalled(that); }
    @Override public void visitImport(JCImport that)               { shouldNotBeCalled(that); }
    @Override public void visitJmlCompilationUnit(JmlCompilationUnit that)   { shouldNotBeCalled(that); }
    @Override public void visitJmlImport(JmlImport that)                     { shouldNotBeCalled(that); }
    @Override public void visitMethodDef(JCMethodDecl that)        { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodDecl(JmlMethodDecl that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlBinary(JmlBinary that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlChoose(JmlChoose that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlClassDecl(JmlClassDecl that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodSig(JmlMethodSig that) { shouldNotBeCalled(that); }
    @Override public void visitJmlDoWhileLoop(JmlDoWhileLoop that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitJmlForLoop(JmlForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitJmlGroupName(JmlGroupName that) { shouldNotBeCalled(that); }
    @Override public void visitJmlLblExpression(JmlLblExpression that) { shouldNotBeCalled(that); }    
    @Override public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodSpecs(JmlMethodSpecs that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlModelProgramStatement(JmlModelProgramStatement that) { shouldNotBeCalled(that); }
    @Override public void visitJmlSpecificationCase(JmlSpecificationCase that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementDecls(JmlStatementDecls that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementExpr(JmlStatementExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementLoop(JmlStatementLoop that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementSpec(JmlStatementSpec that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseIn(JmlTypeClauseIn that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) { shouldNotBeCalled(that); }
    @Override public void visitJmlVariableDecl(JmlVariableDecl that) { shouldNotBeCalled(that); }
    @Override public void visitJmlWhileLoop(JmlWhileLoop that) { shouldNotBeCalled(that); }

    @Override public void visitClassDef(JCClassDecl that) { shouldNotBeCalled(that); }
    @Override public void visitVarDef(JCVariableDecl that)  { shouldNotBeCalled(that); }
    @Override public void visitSkip(JCSkip that) { shouldNotBeCalled(that); }
    @Override public void visitBlock(JCBlock that) { shouldNotBeCalled(that); }
    @Override public void visitDoLoop(JCDoWhileLoop that) { shouldNotBeCalled(that); }
    @Override public void visitWhileLoop(JCWhileLoop that) { shouldNotBeCalled(that); }
    @Override public void visitForLoop(JCForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitForeachLoop(JCEnhancedForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitLabelled(JCLabeledStatement that) { shouldNotBeCalled(that); }
    @Override public void visitSwitch(JCSwitch that) { shouldNotBeCalled(that); }
    @Override public void visitCase(JCCase that) { shouldNotBeCalled(that); }
    @Override public void visitSynchronized(JCSynchronized that) { shouldNotBeCalled(that); }
    @Override public void visitTry(JCTry that) { shouldNotBeCalled(that); }
    @Override public void visitCatch(JCCatch that) { shouldNotBeCalled(that); }
    @Override public void visitIf(JCIf that) { shouldNotBeCalled(that); }
    @Override public void visitExec(JCExpressionStatement that) { shouldNotBeCalled(that); }
    @Override public void visitBreak(JCBreak that) { shouldNotBeCalled(that); }
    @Override public void visitContinue(JCContinue that) { shouldNotBeCalled(that); }
    @Override public void visitReturn(JCReturn that) { shouldNotBeCalled(that); }
    @Override public void visitThrow(JCThrow that) { shouldNotBeCalled(that); }
    @Override public void visitAssert(JCAssert that) { shouldNotBeCalled(that); }
    @Override public void visitAnnotation(JCAnnotation that) { shouldNotBeCalled(that); }
    @Override public void visitModifiers(JCModifiers that) { shouldNotBeCalled(that); }
    @Override public void visitErroneous(JCErroneous that) { shouldNotBeCalled(that); }

}
