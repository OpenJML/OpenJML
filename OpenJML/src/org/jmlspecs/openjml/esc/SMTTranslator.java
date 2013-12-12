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

import com.sun.tools.javac.code.JmlType;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.TypeTags;
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
    
    /** Cached instance of the JmlTreeUtils tool for the context. */
    final protected JmlTreeUtils treeutils;
    
    /** The factory for creating SMTLIB expressions */
    final protected Factory F;
    
    /** Commonly used SMTLIB expressions - using these shares structure */
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

    // These are strings that are part of our modeling of Java+JML and are
    // more or less arbitrary. Strings like these that are used only once
    // may be simply used in place.
    // Strings that are defined by SMTLIB are used explicitly in place.
    public static final String NULL = "NULL";
    public static final String this_ = Strings.thisName; // Must be the same as the id used in JmlAssertionAdder
    public static final String REF = "REF"; // SMT sort for Java references
    public static final String JAVATYPESORT = "JavaTypeSort";
    public static final String JMLTYPESORT = "JMLTypeSort";
    public static final String JAVASUBTYPE = "javaSubType";
    public static final String JMLSUBTYPE = "jmlSubType";
    public static final String arrayLength = "__JMLlength"; // array length
    public static final String arrays_ = BasicBlocker2.ARRAY_BASE_NAME; // Must match BasicBlocker2
    public static final String concat = "stringConcat";
    public static final String nonnullelements = "nonnullelements";

    /** A convenience declaration, to avoid calling the constructor for every empty list */
    public static final List<ISort> emptyList = new LinkedList<ISort>();
    
    /** SMTLIB subexpressions - the result of each visit call */
    protected IExpr result;
    
    /** The SMTLIB script as it is being constructed */
    protected IScript script;
    
    /** An alias to script.commands() */
    protected List<ICommand> commands;
    
    /** A list that accumulates all the Java type constants used */
    final protected Set<Type> javaTypes = new HashSet<Type>();

    /** A list that accumulates all the Java type names as used in SMT */
    final protected Set<String> javaTypeSymbols = new HashSet<String>();
    
    /** A counter used to make String literal identifiers unique */
    int stringCount = 0;

    /** A counter used to make double literal identifiers unique */
    int doubleCount = 0;

    /** A counter used to make identifiers unique */
    int uniqueCount = 0;
    
    /** An internal field used to indicate whether we are translating expressions inside a quantified expression */
    boolean inQuant = false;

    /** A mapping from Java expressions to/from SMT expressions */
    final public BiMap<JCExpression,IExpr> bimap = new BiMap<JCExpression,IExpr>();
    
    /** The constructor - create a new instance for each Basic Program to be translated */
    public SMTTranslator(Context context) {
        this.context = context;
        // OpenJDK tools
        log = Log.instance(context);
        syms = Symtab.instance(context);
        names = Names.instance(context);
        types = JavacTypes.instance(context);
        treeutils = JmlTreeUtils.instance(context);
        
        // SMT factory and commonly used objects
        F = new org.smtlib.impl.Factory();
        boolSort = F.createSortExpression(F.symbol("Bool")); // From SMT
        intSort = F.createSortExpression(F.symbol("Int")); // From SMT
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
        c = new C_set_logic(F.symbol(s));
        commands.add(c);
        
        // add background statements
        // declare the sorts we use to model Java+JML
        // (declare-sort REF 0)
        c = new C_declare_sort(F.symbol(REF),zero);
        commands.add(c);
        // (declare-sort JavaTypeSort 0)
        c = new C_declare_sort(F.symbol(JAVATYPESORT),zero);
        commands.add(c);
        // (declare-sort JMLTypeSort 0)
        c = new C_declare_sort(F.symbol(JMLTYPESORT),zero);
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
        // define stringLength: (declare-fun stringLength (REF) Int)
        c = new C_declare_fun(F.symbol("stringLength"),Arrays.asList(refSort), intSort); // FIXME - not sure this =is used
        commands.add(c);
        // THIS != NULL: (assert (distinct THIS NULL))
        c = new C_assert(F.fcn(distinctSym, thisSym, nullSym)); // SMT defined name
        commands.add(c);
        // (assert __JMLlength () (Array REF Int))
        c = new C_declare_fun(lengthSym,
                emptyList, 
                F.createSortExpression(arraySym,refSort,intSort)
                );
        commands.add(c);

            // array lengths are always non-negative
        addCommand(smt,"(assert (forall ((o "+REF+")) (>= (select "+arrayLength+" o) 0)))");
            // result of string concatenation is always non-null
        addCommand(smt,"(assert (forall ((s1 "+REF+")(s2 "+REF+")) (distinct ("+concat+" s1 s2) "+NULL+")))");

        // The following functions model aspects of Java+JML;
        // The strings here are arbitrary except that they must not conflict with 
        // identifiers from the Java program as mapped into SMT identifiers
        List<ISort> args = Arrays.asList(refSort); // List of one element 
        c = new C_declare_fun(F.symbol("asIntArray"),args, F.createSortExpression(arraySym,intSort,intSort));
        commands.add(c);
        c = new C_declare_fun(F.symbol("asREFArray"),args, F.createSortExpression(arraySym,intSort,refSort));
        commands.add(c);
        c = new C_declare_fun(F.symbol("intValue"),args, intSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("booleanValue"),args, boolSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("javaTypeOf"),args, javaTypeSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("jmlTypeOf"),args, jmlTypeSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol(JAVASUBTYPE),
                Arrays.asList(new ISort[]{javaTypeSort,javaTypeSort}), 
                boolSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol(JMLSUBTYPE),
                Arrays.asList(new ISort[]{jmlTypeSort,jmlTypeSort}), 
                boolSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("erasure"),
                Arrays.asList(new ISort[]{jmlTypeSort}), 
                javaTypeSort);
        commands.add(c);
        c = new C_declare_fun(lengthSym,
                Arrays.asList(new ISort[]{refSort}), 
                intSort);
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
        } else {
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
        
        // Record the location in the commands list at which all the type
        // definitions will be inserted
        int loc = commands.size();
        
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
        cc = new C_assert(F.fcn(eqSym,F.symbol(JmlAssertionAdder.assumeCheckVar),zero));
        commands.add(cc);
        // (push 1)
        cc = new C_push(F.numeral(1));
        commands.add(cc);
        // (check-sat)
        cc = new C_check_sat();
        commands.add(cc);
        
        // Insert type relationships, now that we have accumulated them all
        // Each type has a representation as a Java (erased type) and a JML type
        int len = javaTypes.size();
        List<ICommand> tcommands = new ArrayList<ICommand>(len*len*2 + 3*len);
        for (Type ti: javaTypes) {
            // (declare-fun tjava () JavaTypeSort)
            // (declare-fun tjml () JMLTypeSort)
            // (assert (= (erasure tjml) tjava))
            tcommands.add(new C_declare_fun(
                    javaTypeSymbol(ti),
                    emptyList,
                    javaTypeSort));
            tcommands.add(new C_declare_fun(
                    jmlTypeSymbol(ti),
                    emptyList,
                    jmlTypeSort));
            tcommands.add(new C_assert(F.fcn(
                    eqSym, 
                    F.fcn(F.symbol("erasure"),jmlTypeSymbol(ti)),
                    javaTypeSymbol(ti))));

        }
        for (Type ti: javaTypes) {
            for (Type tj: javaTypes) {
                // (assert (javaSubType t1 t2)) - or assert the negation
                // (assert (jmlSubType t1jml t2jml)) - or assert the negation
                
                boolean b = types.isSubtype(types.erasure(ti),types.erasure(tj));
                IExpr comp = F.fcn(F.symbol(JAVASUBTYPE), javaTypeSymbol(ti), javaTypeSymbol(tj));
                if (!b) comp = F.fcn(F.symbol("not"),comp);
                tcommands.add(new C_assert(comp));
                
                b = types.isSubtype(ti,tj);
                comp = F.fcn(F.symbol(JMLSUBTYPE), jmlTypeSymbol(ti), jmlTypeSymbol(tj));
                if (!b) comp = F.fcn(F.symbol("not"),comp);
                tcommands.add(new C_assert(comp));
            }
        }
        {
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
        
        // Add all the type definitions into the command script before all the uses
        // of the types in the various basic block translations
        commands.addAll(loc,tcommands);
        
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
        if (t.tag == TypeTags.ARRAY){
            return typeString(((ArrayType)t).elemtype) + "_A_";
        }
        return t.toString().replace(".", "_");
    }
    
    /** Returns an SMT Symbol representing the given Java type */
    public IExpr.ISymbol javaTypeSymbol(Type t) {
        //String s = "|T_" + t.toString() + "|";
        if (t.tag == TypeTags.BOT) t = syms.objectType;
        String s = "T_" + typeString(t);
        return F.symbol(s);
    }
    
    /** Returns an SMT Symbol representing the given JML type */
    public IExpr.ISymbol jmlTypeSymbol(Type t) {
        if (t.tag == TypeTags.BOT) t = syms.objectType;
        //String s = "|JMLT_" + t.toString() + "|" ;
        String s = "JMLT_" + typeString(t);
        return F.symbol(s);
    }
    
    /** Records a type as defined. */
    public void addType(Type t) {
        // FIXME - what if t is the type of an explicit null?
        if (javaTypeSymbols.add(t.toString())) javaTypes.add(t);
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
        while (iter.hasPrevious()) {
            tail = convertStatement(iter.previous(),tail);
        }
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
    
    /** Converts a basic block statement to an SMT expression, tacking it on
     * the front of tail and returning the composite expression.
     */
    public IExpr convertStatement(JCStatement stat, IExpr tail) {
        try {
            if (stat instanceof JmlVariableDecl) {
                 return tail;
            } else if (stat instanceof JmlStatementExpr) {
                JmlStatementExpr s = (JmlStatementExpr)stat;
                if (s.token == JmlToken.ASSUME) {
                    IExpr exx = convertExpr(s.expression);
                    LinkedList<IExpr> args = new LinkedList<IExpr>();
                    args.add(exx);
                    args.add(tail);
                    return F.fcn(impliesSym, args);
                } else if (s.token == JmlToken.ASSERT) {
                    IExpr exx = convertExpr(s.expression);
                    LinkedList<IExpr> args = new LinkedList<IExpr>();
                    args.add(exx);
                    args.add(tail);
                    return F.fcn(F.symbol("and"), args);
                } else if (s.token == JmlToken.COMMENT) {
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
        } else if (t.tag == TypeTags.BOOLEAN) {
            return F.Bool();
        } else if (t.tag == TypeTags.INT) { 
            return intSort;
        } else if (t.tag == syms.objectType.tag) {
            return refSort;
        } else if (t.tag == TypeTags.SHORT) { 
            return intSort;
        } else if (t.tag == TypeTags.CHAR) { 
            return intSort;
        } else if (t.tag == TypeTags.BYTE) { 
            return intSort;
        } else if (t.tag == TypeTags.LONG) { 
            return intSort;
        } else if (t.tag == TypeTags.FLOAT) { 
            addReal();
            return realSort;
        } else if (t.tag == TypeTags.DOUBLE) { 
            addReal();
            return realSort;
        } else if (t.tag == TypeTags.ARRAY) {
            return refSort;
        } else if (t.tag == TypeTags.BOT) {
            return refSort;
        } else if (t.tag == TypeTags.UNKNOWN){
            if (t instanceof JmlType) {
                JmlType jt = (JmlType)t;
                if (jt.jmlTypeTag() == JmlToken.BSBIGINT) return intSort; 
                if (jt.jmlTypeTag() == JmlToken.BSREAL) return realSort; 
                if (jt.jmlTypeTag() == JmlToken.BSTYPEUC) return intSort; // FIXME
            }
            // FIXME - errors
            return refSort; // FIXME - just something
        } else if (t instanceof Type.TypeVar) {
            return refSort;
        } else {
            // FIXME - what gets here?
            return F.createSortExpression(javaTypeSymbol(t)); // FIXME - use the common method for translating to type names?
//            log.error("jml.internal", "No type translation implemented when converting a BasicProgram to SMTLIB: " + t);
//            throw new RuntimeException();
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
        log.error("esc.not.implemented","Not yet supported expression node in converting BasicPrograms to SMTLIB: " + tree.getClass());
    }
    
    /** Issues an error message about something not being implemented */
    public void notImpl(String msg) {
        log.error("esc.not.implemented","Not yet supported feature in converting BasicPrograms to SMTLIB: " + msg);
    }
    
    /** Issues an error message that a particular AST node should not be being used in the input basic block program */
    public void shouldNotBeCalled(JCTree tree) {
        log.error("jml.internal","This node should not be present in converting BasicPrograms to SMTLIB: " + tree.getClass());
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
            // Adds an argument for the receiver, if the function is not static
            if (!Utils.instance(context).isJMLStatic(treeutils.getSym(tree))) {
                argSorts.add(refSort);
            }
            for (JCExpression e: tree.args) {
                argSorts.add(convertSort(e.type));
            }
            C_declare_fun c = new C_declare_fun(n,argSorts,resultSort);
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
            if (JmlAssertionAdder.useMethodAxioms && !Utils.instance(context).isJMLStatic(treeutils.getSym(tree))) {
                JCExpression e = ((JCFieldAccess)tree.meth).selected;
                scan(e);
                newargs.add(convertExpr(e));
            }
            for (JCExpression arg: tree.args) {
                scan(arg);
                newargs.add(convertExpr(arg));
            }
            result = F.fcn(F.symbol(newname),newargs);
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
        if (that.token == JmlToken.BSTYPELC) {
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
        if (that.token == JmlToken.SUBTYPE_OF) {
            result = F.fcn(F.symbol(JMLSUBTYPE), newargs);
        } else if (that.token == JmlToken.BSTYPEOF) {
            ISymbol s = that.javaType ? F.symbol("javaTypeOf") : F.symbol("jmlTypeOf");
            result = F.fcn(s, newargs);
        } else if (that.token == JmlToken.BSNONNULLELEMENTS) {
            result = F.fcn(F.symbol(nonnullelements), newargs);
        } else if (that.token == JmlToken.BSDISTINCT) {
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
        int op = tree.getTag();
        IExpr arg = convertExpr(tree.arg);
        LinkedList<IExpr> args = new LinkedList<IExpr>();
        args.add(arg);
        switch (op) {
            case JCTree.NOT:
                result = F.fcn(F.symbol("not"), args);
                break;
            case JCTree.NEG:
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
        int op = tree.getTag();
        IExpr lhs = convertExpr(tree.lhs);
        IExpr rhs = convertExpr(tree.rhs);
        LinkedList<IExpr> args = new LinkedList<IExpr>();
        args.add(lhs);
        args.add(rhs);
        switch (op) {
            case JCTree.EQ:
                result = F.fcn(eqSym, args);
                break;
            case JCTree.NE:
                result = F.fcn(distinctSym, args);
                break;
            case JCTree.AND:
                result = F.fcn(F.symbol("and"), args);
                break;
            case JCTree.OR:
                result = F.fcn(F.symbol("or"), args);
                break;
            case JCTree.LT:
                result = F.fcn(F.symbol("<"), args);
                break;
            case JCTree.LE:
                result = F.fcn(F.symbol("<="), args);
                break;
            case JCTree.GT:
                result = F.fcn(F.symbol(">"), args);
                break;
            case JCTree.GE:
                result = F.fcn(F.symbol(">="), args);
                break;
            case JCTree.PLUS:
                if (tree.lhs.type.tag == TypeTags.CLASS) {
                    result = F.fcn(F.symbol(concat), args);
                } else {
                    result = F.fcn(F.symbol("+"), args);
                }
                break;
            case JCTree.MINUS:
                result = F.fcn(F.symbol("-"), args);
                break;
            case JCTree.MUL:
                result = F.fcn(F.symbol("*"), args);
                break;
            case JCTree.DIV:
                // FIXME - what kinds of primitive types should be expected
                if (tree.type.tag == TypeTags.FLOAT)
                    result = F.fcn(F.symbol("/"), args);
                else if (tree.type.tag == TypeTags.DOUBLE)
                    result = F.fcn(F.symbol("/"), args);
                else
                    result = F.fcn(F.symbol("div"), args);
                break;
            case JCTree.MOD:
                result = F.fcn(F.symbol("mod"), args);
                break;
                // FIXME - implement bit operations
            case JCTree.BITAND:
                if (tree.type.tag == TypeTags.BOOLEAN) {
                    result = F.fcn(F.symbol("and"), args);
                } else {
                    notImpl("Bit-operation " + op);
                }
                break;
            case JCTree.BITOR:
                if (tree.type.tag == TypeTags.BOOLEAN) {
                    result = F.fcn(F.symbol("or"), args);
                } else {
                    notImpl("Bit-operation " + op);
                }
                break;
            case JCTree.BITXOR:
                if (tree.type.tag == TypeTags.BOOLEAN) {
                    result = F.fcn(F.symbol("distinct"), args);
                } else {
                    notImpl("Bit-operation " + op);
                }
                break;
            case JCTree.SL:
            case JCTree.SR:
            case JCTree.USR:
                notImpl("Bit-operation " + op);
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
            int tagr = tree.type.tag;
            int tage = tree.expr.type.tag;
            if (tage == TypeTags.UNKNOWN || tagr == TypeTags.UNKNOWN) { 
                if (tage <= TypeTags.LONG && tagr == TypeTags.UNKNOWN && ((JmlType)tree.type).jmlTypeTag() == JmlToken.BSBIGINT) {
                    // int to \bigint -- OK
                } else {
                    // ????? FIXME
                }
            } else if (!tree.type.isPrimitive()) {
                // If this is a cast from reference type to reference type, we can ignore it
            } else if (tree.expr instanceof JCLiteral) {
                Object v = ((JCLiteral)tree.expr).getValue();
                if (tage == tagr) {
                    // OK
                } else if ((tage <= TypeTags.LONG) == (tagr <= TypeTags.LONG)) {
                    // Both integral or both floating point
                    // OK
                } else if (tage <= TypeTags.LONG) {
                    java.math.BigInteger val = ((IExpr.INumeral)result).value();
                    result = makeRealValue(val.doubleValue());
                } else if (tage > TypeTags.LONG) {
                    // FIXME - cast from double to integral
                }
            } else {
                if (tage <= TypeTags.LONG && tagr > TypeTags.LONG) {
                    // integral to real
                } else {
                    
                }
            }
            if (tree.expr instanceof JCLiteral) {
                
            } else {
                result = convertExpr(tree.expr);
            }
        } else if (!tree.type.isPrimitive()) {
            // Cast from primitive to object
            log.error(tree,"jml.internal","Do not expect casts to reference type in expressions: " + JmlPretty.write(tree));
        } else {
            // unboxing cast from object to primitive
            int tag = tree.type.tag;
            switch (tag) {
                case TypeTags.INT:
                case TypeTags.LONG:
                case TypeTags.SHORT:
                case TypeTags.BYTE:
                case TypeTags.CHAR:
                case TypeTags.DOUBLE:
                case TypeTags.FLOAT:
                case TypeTags.BOOLEAN:
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
        if (tree.typetag == TypeTags.BOOLEAN) {
           result = F.symbol(((Boolean)v) ?"true":"false"); 
        } else if (tree.typetag == TypeTags.INT || tree.typetag == TypeTags.LONG || tree.typetag == TypeTags.SHORT || tree.typetag == TypeTags.BYTE) {
            long k = Long.parseLong(v.toString());
            result = k >= 0 ? F.numeral(k) : F.fcn(F.symbol("-"), F.numeral(-k));
        } else if (tree.typetag == TypeTags.CHAR) {
            long k = (v instanceof Character) ? (long) ((Character)v).charValue() : Long.parseLong(v.toString());
            result = F.numeral(k);
        } else if (tree.typetag == TypeTags.BOT) {
            result = nullSym;
        } else if (tree.typetag == TypeTags.CLASS) {
            // FIXME - every literal is different and we don't remember the value
            ISymbol sym = F.symbol("STRINGLIT"+(++stringCount)); 
            ICommand c = new C_declare_fun(sym,emptyList, refSort);
            commands.add(c);
            result = sym;
        } else if (tree.typetag == TypeTags.FLOAT || tree.typetag == TypeTags.DOUBLE) {
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
            if (that.op == JmlToken.BSFORALL) {
                if (range != null) value = F.fcn(impliesSym,range,value);
                result = F.forall(params,value);
            } else if (that.op == JmlToken.BSEXISTS) {
                if (range != null) value = F.fcn(F.symbol("and"),range,value);
                result = F.exists(params,value);
            } else {
                notImpl("JML Quantified expression using " + that.op.internedName());
            }
            if (!prev) {
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
