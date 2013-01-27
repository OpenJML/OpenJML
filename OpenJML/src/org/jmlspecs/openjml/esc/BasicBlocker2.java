/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
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
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.esc.BoogieProgram.BoogieBlock;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCAssert;
import com.sun.tools.javac.tree.JCTree.JCAssign;
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
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.tree.JCTree.JCReturn;
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
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

/** This class converts a Java AST into basic block form (including DSA and
 * passification). All Java (and JML) statements are rewritten into assume and
 * assert statements, with basic blocks being created to represent the control
 * flow. In addition, note the following:
 * <UL>
 * <LI> No assertions to represent Java or JML semantics are added, except for those
 * needed to convert control flow into basic blocks
 * <LI> The name field of JCIdent nodes are rewritten in place to
 * convert the program to single-assignment form. Note that this means that 
 * expressions and subexpressions of the input tree may not be shared across statements or 
 * within expressions.
 * <LI> The JML \\old and \\pre expressions are recognized and translated to use
 * the appropriate single-assignment identifiers.
 * </UL>
 * <P>
 * The input tree must consist of (FIXME)
 * <UL>
 * <LI> A valid Java program (with any Java constructs)
 * <LI> JML assume and assert statements, with JML expressions
 * <LI> The JML expressions contain only
 * <UL>
 * <LI> Java operators
 * <LI> quantified expressions
 * <LI> set comprehension expressions
 * <LI> \\old and \\pre expressions
 * <LI> [ FIXME ??? JML type literals, subtype operations, method calls in specs?]
 * </UL
 * </UL>
 *
 * <P>
 * Basic block output form contains only this subset of AST nodes: (FIXME)
 * <UL>
 * <LI> JCLiteral - numeric (all of them? FIXME), null, boolean, class (String?, character?)
 * <LI> JCIdent
 * <LI> JCParens
 * <LI> JCUnary
 * <LI> JCBinary
 * <LI> JCConditional
 * <LI> JmlBBFieldAccess
 * <LI> JmlBBArrayAccess
 * <LI> JmlBBFieldAssign
 * <LI> JmlBBArrayAssign
 * <LI> JCMethodInvocation - only pure methods within specifications
 * <LI> JmlMethodInvocation - old, typeof
 * <LI> JmlQuantifiedExpr - only forall and exists
 * <LI> JCTypeCast - but the clazz element now has a JCLiteral (which is a type literal)
 * <LI> [JCInstanceOf - not present - use a typeof and a subtype operation]
 * </UL>
 * 
 * @author David Cok
 */
public class BasicBlocker2 extends BasicBlockerParent<BasicProgram.BasicBlock,BasicProgram>  {

    /** Creates an empty new BasicProgram */
    @Override
    public BasicProgram newProgram(Context context) {
        return new BasicProgram(context);
    }
    
    /** Creates an empty new BasicBlock */
    @Override
    public BasicProgram.BasicBlock newBlock(JCIdent id){
        return new BasicProgram.BasicBlock(id);
    }
    
    
    /////// To have a unique BasicBlocker2 instance for each method translated
    // In the initialization of tools, call  BasicBlocker2.Factory.preRegister(context);
    // Obtain a new BasicBlocker2 when desired with  context.get(BasicBlocker2.class);
        
//    /** Register a BasicBlocker Factory, if nothing is registered yet */
//    public static void preRegister(final Context context) {
//        //if (context.get(key) != null) return;
//        context.put(key, new Context.Factory<BasicBlocker2>() {
//            @Override
//            public BasicBlocker2 make(Context context) {
//                return new BasicBlocker2(context);
//            }
//        });
//    }
//    
//    final public static Context.Key<BasicBlocker2> key =
//        new Context.Key<BasicBlocker2>();
    
    /////// To have one BasicBlocker2 instance per context use this method without the pre-registration
    // Don't need pre-registration since we are not replacing any tool and not using a factory
    // To obtain a reference to the instance of BasicBlocker2 for the current context
    //                                 BasicBlocker2.instance(context);
    
//    /** Get the instance for this context. 
//     * 
//     * @param context the compilation context
//     * @return a (unique for the context) BasicBlocker instance
//     */
//    public static BasicBlocker2 instance(@NonNull Context context) {
//        BasicBlocker2 instance = context.get(key);
//        // This is lazily initialized so that a derived class can preRegister to
//        // replace this BasicBlocker
//        if (instance == null) {
//            instance = new BasicBlocker2(context);
//        }
//        return instance;
//    }
    
    // Options
    
    // TODO - document
    // Turned this off - with it on, Java assert statements are declared out of order and fail.
    // There is still a problem with Java assert and JML assert being handled differently, with different naming
    static boolean useAssertDefinitions = false;

    // This implements checking of assumption feasibility.  After an 
    // assumption that is to be checked, we add the assertion
    //       assert assumeCheck$<uniqueint>$<label>
    // and the definition
    //       assume assumeCheck$<uniqueint>$<label> == <assumecheckvar> != <uniqueint>
    // where <uniqueint> is a positive integer not used elsewhere for 
    // this purpose.  Here we use the source code location so that it
    // can be used as well to generate error messages.
    // Then we also add to the VC the assumption
    //       assume <assumecheckvar> == 0
    // That way all the inserted assertions above are true.  However, we
    // can change any one of them to false by replacing the assumption
    // above with
    //       assume <assumecheckvar> == <uniqueid>
    // using the specific <uniqueint> of the assumption we want to test
    
    // FIXME - review and document
    static public boolean insertAssumptionChecks = true;
    
    // FIXME - review and document
    static boolean useCountedAssumeCheck = true;
    // FIXME - review and document
    static JCExpression booleanAssumeCheck;
    // FIXME - review and document
    JCExpression assumeCheck = null;

    /** This static field controls whether (user) assume statements are turned into assumptions tracked
     * with the assume count variable; if so, then there is an easy mechanism to test whether 
     * the assumptions are feasible.
     */
    public static boolean useAssumeDefinitions = false;
    

    // THE FOLLOWING ARE ALL FIXED STRINGS
    
    // TODO - many of these can be moved to JmlAssertionAdder???
    
    //-----------------------------------------------------------------
    // Names for a bunch of synthetic variables 
    
    /** Standard name for the variable that represents the heap (which excludes local variables) */
    public static final @NonNull String HEAP_VAR = "_heap__";
    
    /** Standard name for the variable that tracks allocations */
    public static final @NonNull String ALLOC_VAR = "_alloc__";
    
    /** Prefix for assumptions defined in the basic block */
    public static final String ASSUMPTION_PREFIX = "assumption";
    
    /** Name of the encoded this variable */
    public static final String THIS = "THIS_";
    
    /** The prefix of the variables used in checking assumptions */
    public static final String ASSUME_CHECK_PREFIX = "ASSUMECHECK_";
    
    /** A variable name used in checking assumptions */
    public static final String ASSUME_CHECK_COUNT = "__assumeCheckCount";
    
    /** The prefix for names of switch expressions */
    public static final String SWITCH_EXPR_PREFIX = "__switch_expression__";
    
    /** Name of length field */
    public static final String LENGTH = "length";
    
    /** Name of the SELECT function for arrays. */
    public static final String SELECTString = "SELECT";
    
    /** The Name of the SELECT function for arrays. */
    public final Name SELECT;
    
    /** String of the STORE function for arrays. */
    public static final String STOREString = "STORE";
    
    /** The Name of the STORE function for arrays. */
    public final Name STORE;
    
    //-----------------------------------------------------------------
    // Names for various basic blocks
    
    /** Standard name for the block that starts the body */
    public static final @NonNull String BODY_BLOCK_NAME = "bodyBegin";
    
    /** Standard name for the starting block of the program (just has the preconditions) */
    public static final @NonNull String START_BLOCK_NAME = "Start";
    
    /** Standard name for the return block, whether or not a value is returned */
    public static final @NonNull String RETURN_BLOCK_NAME = blockPrefix + "return";
    
    /** Standard name for the exception block */
    public static final @NonNull String EXCEPTION_BLOCK_NAME = blockPrefix + "exception";
    
    /** Suffix for the name of a basic block for a finally block */
    public static final String FINALLY = "_finally";
    
    /** Suffix for the name of a basic block for a finally block */
    public static final String AFTERTRY = "_AfterTry";
    
    /** Suffix for the name of a basic block holding the body of a loop */
    public static final String LOOPBODY = "_LoopBody";
    
    /** Suffix for the name of a basic block holding the code after a loop */
    public static final String LOOPAFTER = "_LoopAfter";
    
    /** Suffix for the name of a basic block holding the code after a loop */
    public static final String LOOPAFTERDO = "_LoopAfterDo";
    
    /** Suffix for the name of a basic block holding the code where continue statements go */
    public static final String LOOPCONTINUE = "_LoopContinue";
    
    /** Suffix for the name of a basic block holding the code where break statements go */
    public static final String LOOPBREAK = "_LoopBreak";
    
    /** Suffix for the name of a basic block to which control transfers if the loop condition fails */
    public static final String LOOPEND = "_LoopEnd";
    
    /** Suffix for the name of a basic block for the then branch of an if statement */
    public static final String THENSUFFIX = "_then";
    
    /** Suffix for the name of a basic block for the else branch of an if statement */
    public static final String ELSESUFFIX = "_else";
    
    /** Suffix for the name of a basic block after an if statement */
    public static final String AFTERIF = "_afterIf";
    
//    /** Prefix for branch condition variables */
//    public static final String BRANCHCONDITION_PREFIX = "branchCondition_";
    

    
    // THE FOLLOWING FIELDS ARE EXPECTED TO BE CONSTANT FOR THE LIFE OF THE OBJECT
    // They are either initialized in the constructor or initialized on first use
    
    /** The compilation context */
    @NonNull final protected Context context;
    
    /** The log to which to send error, warning and notice messages */
    @NonNull final protected Log log;
    
    /** The specifications database for this compilation context, initialized in the constructor */
    @NonNull final protected JmlSpecs specs;
    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull final protected Symtab syms;
    
    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull final protected Names names;
    
    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    @NonNull final protected JmlTreeUtils treeutils;
    
    /** The object that desugars JML */
    @NonNull final protected JmlTranslator treetrans;
    
    /** General utilities */
    @NonNull final protected Utils utils;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull final protected JmlTree.Maker factory;

    // Caution - the following are handy, but they are shared, so they won't
    // have proper position information
    
    /** Holds an AST node for a boolean true literal, initialized in the constructor */
    @NonNull final protected JCLiteral trueLiteral;
    
    /** Holds an AST node for a boolean false literal, initialized in the constructor */
    @NonNull final protected JCLiteral falseLiteral;
    
    /** Holds an AST node for a null literal, initialized in the constructor */
    @NonNull final protected JCLiteral nullLiteral;
    
    /** Holds an AST node for a null literal, initialized in the constructor */
    @NonNull final protected JCLiteral zeroLiteral;
    
    /** Identifier of a synthesized object field holding the allocation time of the object, initialized in the constructor */
    @NonNull protected JCIdent allocIdent;

    /** A counter to ensure unique instances of alloc identifiers */
    protected int allocCount = 0;
    
    /** Symbol of a synthesized object field holding the allocation time of the object, initialized in the constructor */
    @NonNull protected VarSymbol allocSym;

    /** Symbol of a synthesized object field holding the allocation time of the object, initialized in the constructor */
    @NonNull protected VarSymbol terminationSym;

    /** Identifier of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull protected JCIdent lengthIdent;

    /** Symbol of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull protected VarSymbol lengthSym;
    
    /** A fixed id for 'this' of the method being translated (see currentThisId
     * for the 'this' of called methods). */
    @NonNull protected JCIdent thisId;

    // THE FOLLOWING FIELDS ARE USED IN THE COURSE OF DOING THE WORK OF CONVERTING
    // TO BASIC BLOCKS.  They are fields of the class because they need to be
    // shared across the visitor methods.
    
    
    /** Place to put new definitions, such as the equalities defining auxiliary variables */
    protected List<BasicProgram.Definition> newdefs;
    
    // FIXME - fold into background???
    protected List<JCExpression> newpdefs;
    
    /** Place to put new background assertions, such as class predicates */
    protected List<JCExpression> background;
    
//    /** List of blocks completed processing - in basic block state */
//    protected java.util.List<BasicBlock> blocksCompleted;
//    
//    /** A map of names to blocks */
//    protected java.util.Map<String,BasicBlock> blockLookup;
//    
//    /** A variable to hold the block currently being processed */
//    protected BasicBlock currentBlock;
    
    /** The variable name that is currently the 'this' variable */
    protected JCIdent currentThisId;
    
//    /** Ordered list of statements from the current block that are yet to be processed into basic program form */
//    protected List<JCStatement> remainingStatements;
//    
//    /** The program being constructed */
//    protected BasicProgram program = null;
    
    // Characteristics of the method under study
    // FIXME - what about methods in anonymous classes - do we have to be reentrant?
    
//    /** The declaration of the method under conversion */
//    protected JmlMethodDecl methodDecl;
//    
//    /** True if the method being converted is a constructor */
//    protected boolean isConstructor;
//    
//    /** True if the method being converted is static */
//    protected boolean isStatic;
//    

    // FIXME - document the following; check when initialized
    // FIXME - exceptionVar and terminationVar are no longer needed I think
    protected JCIdent exceptionVar = null;
    protected JCIdent heapVar;
    protected JCIdent terminationVar;  // 0=no termination requested; 1=return executed; 2 = exception happening
    
    protected JCIdent assumeCheckCountVar; // FIXME - initialized?
    protected int assumeCheckCount;  // FIXME - initialized?
    
    /** This is an integer that rises monotonically on each use and is used
     * to make sure new identifiers are unique.
     */
    protected int unique;
    
//    /** Holds the result of any of the visit methods that produce JCExpressions, since the visitor
//     * template used here does not have a return value.  [We could have used the templated visitor,
//     * but other methods do not need to return anything, we don't need the additional parameter,
//     * and that visitor is complicated by the use of interfaces for the formal parameters.]
//     */
//    private JCExpression result;
    
    /** A mapping from BasicBlock to the sym->incarnation map giving the map that
     * corresponds to the state at the exit of the BasicBlock.
     */
    @NonNull protected Map<BasicBlock,VarMap> blockmaps = new HashMap<BasicBlock,VarMap>();
    
    /** A mapping from labels to the sym->incarnation map operative at the position
     * of the label.
     */
    @NonNull protected Map<Name,VarMap> labelmaps = new HashMap<Name,VarMap>();
        
    /** The map from symbol to incarnation number in current use */
    @NonNull protected VarMap currentMap;
    
    /** The map immediately after declaration of method parameters; this is
        the mapping of variables to incarnations to use when in the scope of 
        an \old */
    @NonNull protected VarMap premap;
    
    final protected Set<Name> isDefined = new HashSet<Name>();

    /** The jfoMap and jfoArray keep track of a mapping between JavaFileObjects and
     * unique Integers. When position information in an encoded identifier refers to 
     * a file that is not the file containing the implementation of the method being
     * translated and verified, then we have to indicate which file contains the source
     * for the position reference. This indication is an @ followed by an integer included in the identifier,
     * where the integer is a unique positive integer associated with the file. Since
     * these mappings are static, the associations remain constant across different methods
     * and different compilation contexts.
     * <BR>
     * jfoMap is a mapping from JavaFileObject to Integer
     */
    // FIXME - should reconsider whether these mappings should be static
    static Map<JavaFileObject,Integer> jfoMap = new HashMap<JavaFileObject,Integer>();

    /** Maps integers to JavaFileObject, the reverse of the mapping in jfoMap */
    static ArrayList<JavaFileObject> jfoArray = new ArrayList<JavaFileObject>();
    static {
        jfoArray.add(0,null);
    }
    
    /** Returns the int associated with a file, creating it if necessary */
    // FIXME - check what equals and hashmap are being used.
    public static int getIntForFile(JavaFileObject jfo) {
        Integer i = jfoMap.get(jfo);
        int k;
        if (i == null) {
            k = jfoArray.size();
            jfoArray.add(k,jfo);
            jfoMap.put(jfo,k);
        } else {
            k = i;
        }
        return k;
    }
    
    /** Returns the file associated with an int */
    public static JavaFileObject getFileForInt(int i) {
        return jfoArray.get(i);
    }
    
    /** The constructor, but use the instance() method to get a new instance,
     * in order to support extension.  This constructor should only be
     * invoked by a derived class constructor.
     * @param context the compilation context
     */
    protected BasicBlocker2(@NonNull Context context) {
        super(context);
        
//        context.put(key, this);
        this.context = context;
        this.log = Log.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context); // FIXME - can this go away?
        this.treeutils = JmlTreeUtils.instance(context);
        this.treetrans = JmlTranslator.instance(context); // FIXME - can this go away?
        this.utils = Utils.instance(context);
        this.scanMode = AST_JAVA_MODE;
        
        unique = 0;
        
        trueLiteral = treeutils.trueLit;
        falseLiteral = treeutils.falseLit;
        nullLiteral = treeutils.nulllit;
        zeroLiteral = treeutils.zero;
        
        // This is the field name used to access the allocation time of an object
        allocSym = newVarSymbol(0,ALLOC_VAR,syms.intType,0);
        allocIdent = newAuxIdent(allocSym,0);

        // This is the symbol to access the length of an array 
        lengthSym = syms.lengthVar;
        lengthIdent = newAuxIdent(lengthSym,0);
        
        SELECT = names.fromString(SELECTString);
        STORE = names.fromString(STOREString);
    }
    
    /** This class implements a map from variable (as a Symbol) to a unique name
     * as used in Single-Assignment form. At any given point in the program there is
     * a current mapping from symbols to names, giving the name that holds the value
     * for the symbol at that location. When a variable is assigned a new value, it
     * gets a new current Single-Assignment name and the map is updated. Copies of 
     * these maps are saved with each block, representing the state of the map at the
     * end of the block.
     * <P>
     * FIXME - explain this better, and the everythingIncarnation
     * Each Symbol also has an incarnation number. The number is incremented as new
     * incarnations happen. The number is used to form the variables SA name.
     */
    public class VarMap {
        // The maps allow VarSymbol or TypeSymbol (for TypeVar)
        private Map<VarSymbol,Integer> map = new HashMap<VarSymbol,Integer>();
        private Map<TypeSymbol,Integer> maptypename = new HashMap<TypeSymbol,Integer>();
        private Map<Symbol,Name> mapn = new HashMap<Symbol,Name>();
        int everythingIncarnation = 0;
        
        /** Makes a checkpoint copy of the map */
        public VarMap copy() {
            VarMap v = new VarMap();
            v.map.putAll(this.map);
            v.maptypename.putAll(this.maptypename);
            v.mapn.putAll(this.mapn);
            v.everythingIncarnation = this.everythingIncarnation;
            return v;
        }
        
        /** Returns the name for a variable symbol as stored in this map */
        public /*@Nullable*/ Name getName(VarSymbol vsym) {
            Name s = mapn.get(vsym);
            return s;
        }
        
        /** Returns the name for a variable symbol as stored in this map, creating (and
         * storing) one if it is not present. */
        public /*@NonNull*/ Name getCurrentName(VarSymbol vsym) {
            Name s = mapn.get(vsym);
            if (s == null) {
                s = encodedName(vsym,everythingIncarnation);
                put(vsym,everythingIncarnation,s);
            }
            return s;
        }
        
        /** Returns the name for a type symbol as stored in this map; returns null
         * if no name is stored */
        public /*@ Nullable */ Name getName(TypeSymbol vsym) {
            Name s = mapn.get(vsym);
            return s;
        }
        
        /** Returns the name for a type symbol as stored in this map, creating (and
         * storing) one if it is not present. */
        public /*@NonNull*/ Name getCurrentName(TypeSymbol vsym) {
            Name s = mapn.get(vsym);
            if (s == null) {
                s = encodedName(vsym,everythingIncarnation);
                put(vsym,everythingIncarnation,s);
            }
            return s;
        }
        
        /** Returns the incarnation number for the symbol */
        public Integer get(VarSymbol vsym) {
            Integer i = map.get(vsym);
            if (i == null) {
                i = everythingIncarnation;
                map.put(vsym,i);
            }
            return i;
        }
        
        /** Returns the incarnation number for the type symbol */
        public Integer get(TypeSymbol vsym) {
            Integer i = maptypename.get(vsym);
            if (i == null) {
                i = everythingIncarnation;
                maptypename.put(vsym,i);
            }
            return i;
        }
        
        /** Stores a new incarnation of a symbol */
        public void put(VarSymbol vsym, Integer i, Name s) {
            map.put(vsym,i);
            mapn.put(vsym,s);
        }
        
        /** Stores a new incarnation of a symbol */
        public void put(TypeSymbol vsym, Integer i, Name s) {
            maptypename.put(vsym,i);
            mapn.put(vsym,s);
        }

        /** Adds everything in the argument map into the receiver's map */
        public void putAll(VarMap m) {
            map.putAll(m.map);
            maptypename.putAll(m.maptypename);
            mapn.putAll(m.mapn);
            everythingIncarnation = m.everythingIncarnation;
        }
        
        /** Removes a symbol from the map, as when it goes out of scope or
         * when a temporary variable is no longer needed. */
        public Integer remove(Symbol v) {
            mapn.remove(v);
            return map.remove(v);
        }
        
        /** Returns the Set of all variable Symbols that are in the map;
         * note that variables that are in scope but have not been used
         * will not necessarily be present in the map. */
        public Set<VarSymbol> keySet() {
            return map.keySet();
        }
        
        /** Returns a debug representation of the map */
        public String toString() {
            StringBuilder s = new StringBuilder();
            s.append("[");
            Iterator<Map.Entry<VarSymbol,Integer>> entries = map.entrySet().iterator();
            while (entries.hasNext()) {
                Map.Entry<VarSymbol,Integer> entry = entries.next();
                s.append(entry.getKey());
                s.append("=");
                s.append(entry.getValue());
                s.append(",");
            }
            Iterator<Map.Entry<TypeSymbol,Integer>> entriest = maptypename.entrySet().iterator();
            while (entries.hasNext()) {
                Map.Entry<TypeSymbol,Integer> entry = entriest.next();
                s.append(entry.getKey());
                s.append("=");
                s.append(entry.getValue());
                s.append(",");
            }
            s.append("]");
            return s.toString();
        }
    }
    
    // METHODS

//    @Override
//    public void scan(com.sun.tools.javac.util.List<? extends JCTree> trees) {
//        if (trees != null)
//        for (com.sun.tools.javac.util.List<? extends JCTree> l = trees; l.nonEmpty(); l = l.tail) {
//            scan(l.head);
//        }
//    }

    public void scanList(com.sun.tools.javac.util.List<JCExpression> trees) {
        if (trees != null)
        for (com.sun.tools.javac.util.List<JCExpression> l = trees; l.nonEmpty(); l = l.tail) {
            scan(l.head);
            l.head = result;
        }
    }

    /** Should not need this when everything is implemented */
    protected void notImpl(JCTree that) {
        log.noticeWriter.println("NOT IMPLEMENTED: BasicBlocker2 - " + that.getClass());
        result = trueLiteral;
    }
    
    /** Called by visit methods that should never be called. */
    protected void shouldNotBeCalled(JCTree that) {
        log.error("esc.internal.error","Did not expect to be calling a " + that.getClass() + " within BasicBlocker2");
        throw new JmlInternalError();
    }
    
    /** Creates a translated expression whose value is the given type;
     * the result is a JML type, e.g. a representation of an instantiated generic.*/
    protected JCExpression makeTypeLiteral(Type type, int pos) {
        return treeutils.trType(pos,type);
    }
    

    // FIXME - review
    /** Creates an encoded name from a symbol and an incarnation position of the form
     *    <symbol name>$<declaration position>$<use position>$<unique-id>
     * If the symbol has a negative declaration position, that value is not included in the string
     * @param sym the symbol being given a logical name
     * @param incarnationPosition the incarnation position for which to give a new name
     * @return the new name
     */
    protected Name encodedName(VarSymbol sym, int incarnationPosition) {
        if (incarnationPosition == 0 || sym.owner == null) {
            Name n = sym.getQualifiedName();
            if (isDefined.add(n)) {
                //System.out.println("AddedC " + sym + " " + n);
                JCIdent id = treeutils.makeIdent(0, sym);
                id.name = n;
                program.declarations.add(id);
            }
            return n;
        } else
            return names.fromString(sym.getQualifiedName() + (sym.pos < 0 ? "_" : ("_" + sym.pos + "_")) + incarnationPosition + "___" + (unique++));
    }
    
    protected Name encodedArrayName(VarSymbol sym, int incarnationPosition) {
        Name n;
        if (incarnationPosition == 0) {
            n = sym.getQualifiedName();
        } else {
            n = names.fromString(sym.getQualifiedName() + (sym.pos < 0 ? "_" : ("_" + sym.pos + "_")) + incarnationPosition + "___" + (unique++));
        }
        if (isDefined.add(n)) {
            //System.out.println("AddedC " + sym + " " + n);
            JCIdent id = treeutils.makeIdent(0, sym);
            id.name = n;
            program.declarations.add(id);
        }
        return n;
    }
    
    // FIXME - review and document
    protected Name encodedName(TypeSymbol tp, int incarnationPosition) {
        return names.fromString(tp.name + "_" + incarnationPosition);
    }
    
    // FIXME - review and document
    protected Name encodedNameNoUnique(VarSymbol sym, int incarnationPosition) {
        return names.fromString(sym.getQualifiedName() + (sym.pos < 0 ? "_" : ("_" + sym.pos + "_")) + incarnationPosition);
    }
    
    // FIXME - review
    /** Creates an encoded name for a Type variable.  There is no incarnation position
     * because type variables are not assigned after initialization.
     * @param sym
     * @param declarationPosition
     * @return the new name
     */
    protected Name encodedTypeName(TypeSymbol sym, int declarationPosition) {
        return names.fromString(sym.flatName() + "_" + declarationPosition);
    }
    
    // FIXME - review
    /** Creates an encoded name from a symbol and an incarnation position of the form
     *    <symbol name>$<declaration position>$<use position>
     * Does not include a unique id
     * If the symbol has a negative declaration position, that value is not included in the string
     * @param sym the symbol being given a logical name
     * @param incarnationPosition the incarnation position for which to give a new name
     * @return the new name
     */
    protected Name encodedName(MethodSymbol sym, int declpos, int incarnationPosition) {
        return names.fromString(sym.getQualifiedName() + (declpos < 0 ? "_" : ("_" + declpos + "_")) + incarnationPosition);
    }
    
    /** Cached value of the SELECT symbol */
    Symbol selectSym = null;
    /** Cached value of the STORE Symbol. */
    Symbol storeSym = null;
    
    protected JCExpression makeSelect(JCExpression array, JCExpression index) {
        if (selectSym == null) {
            selectSym = new VarSymbol(0,SELECT,null,null); // FIXME - OK to have no type or owner?
        }
        JCMethodInvocation app = factory.Apply(
                com.sun.tools.javac.util.List.<JCExpression>nil(),
                treeutils.makeIdent(Position.NOPOS, selectSym),
                com.sun.tools.javac.util.List.<JCExpression>of(index));
        return app;
    }
    
    protected JCExpression makeStore(JCExpression array, JCExpression index, JCExpression value) {
        if (storeSym == null) {
            storeSym = new VarSymbol(0,STORE,null,null);
        }
        JCMethodInvocation app = factory.Apply(
                com.sun.tools.javac.util.List.<JCExpression>nil(),
                treeutils.makeIdent(Position.NOPOS, storeSym),
                com.sun.tools.javac.util.List.<JCExpression>of(array,index,value));
        return app;
    }
    

    
    // FIXME - review
    /** Creates a new Ident node, but in this case we are not using the name from
     * the current incarnation map - so we supply the name. This is just used for
     * DSA assignments.
     */
    protected JCIdent newIdentUse(VarSymbol sym, Name name, int useposition) {
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }
    
    // FIXME - review and document
    protected JCIdent newIdentUse(VarMap map, VarSymbol sym, int useposition) {
        Name name = map.getCurrentName(sym); // Creates a name if ther has not been one created yet
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }
    
    // FIXME - review
    /** Creates an identifier node for a use of a variable at a given source code
     * position; the current incarnation value is used
     * @param sym the underlying symbol (which gives the declaration location)
     * @param useposition the source position of its use
     * @return the new JCIdent node
     */
    protected JCIdent newIdentUse(VarSymbol sym, int useposition) {
        Name name = currentMap.getCurrentName(sym);
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }
    
    /** Returns the name to use for a symbol under the current Map. */
    protected Name getCurrentName(VarSymbol sym) {
        return currentMap.getCurrentName(sym);
    }
    
    // FIXME - review and document
    protected JCIdent newTypeIdentUse(TypeSymbol sym, int useposition) {
        Name name = currentMap.getCurrentName(sym);
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }
    
    // FIXME - review
    /** Creates an identifier nodes for a new incarnation of the variable, that is,
     * when the variable is assigned to.
     * @param id the old identifier, giving the root name, symbol and type
     * @param incarnationPosition the position (and incarnation number) of the new variable
     * @return the new identifier
     */
    protected JCIdent newIdentIncarnation(JCIdent id, int incarnationPosition) {
        return newIdentIncarnation((VarSymbol)id.sym,incarnationPosition);
    }
    
    // FIXME - review
    /** Creates a new incarnation of a variable, with unique id added */
    protected JCIdent newIdentIncarnation(VarSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedName(vsym,incarnationPosition));
        n.type = vsym.type;
        n.sym = vsym;
        currentMap.put(vsym,incarnationPosition,n.name);
        return n;
    }
    
    protected JCIdent newArrayIdentIncarnation(VarSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedArrayName(vsym,incarnationPosition));
        n.type = vsym.type;
        n.sym = vsym;
        currentMap.put(vsym,incarnationPosition,n.name);
        return n;
    }
    
    // FIXME - review
    /** Creates a newly incarnated variable corresponding to the given declaration.
     * The incarnation number will be the position of the declaration for some
     * declarations, but not, for example, for a formal argument of a method call -
     * then it would be the position of the actual parameter expression.
     * @param id the original declaration
     * @param incarnation the incarnation number to use
     * @return the new variable node
     */
    protected JCIdent newIdentIncarnation(JCVariableDecl id, int incarnation) {
        JCIdent n = factory.at(incarnation).Ident(encodedName(id.sym,incarnation));
        n.sym = id.sym;
        n.type = id.type;
        // FIXME - end information?
        currentMap.put(id.sym,incarnation,n.name);
        return n;
    }
    
    // FIXME - review and document
    protected JCIdent newIdentIncarnation(TypeSymbol id, int incarnation) {
        JCIdent n = factory.at(incarnation).Ident(encodedName(id,incarnation));
        n.sym = id;
        n.type = id.type;
        // FIXME - end information?
        currentMap.put(id,incarnation,n.name);
        return n;
    }
    
    // FIXME - review and document
    protected JCIdent newTypeVarIncarnation(TypeSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedTypeName(vsym,incarnationPosition));
        n.type = JmlAttr.instance(context).TYPE;
        n.sym = vsym;
        currentMap.put(vsym,incarnationPosition,n.name);
        return n;
    }
    
    // FIXME - document
    protected JCIdent newArrayIncarnation(Type componentType, int usePosition) {
        JCIdent id = getArrayIdent(componentType);
        id = newArrayIdentIncarnation((VarSymbol)id.sym,usePosition);
        //currentMap.put((VarSymbol)id.sym,Integer.valueOf(usePosition),id.name);
        return id;
    }
    
    // FIXME - review
    /** Creates an attributed, untranslated JCIdent and accompanying VarSymbol using the given name and type;
     * the given pos is used as the textual position of the JCIdent node; also, if incarnations is
     * true, pos is used as the declaration position of the new identifier, with the implication that
     * additional incarnations will be defined later. The new Symbol has no modifiers and no owner.
     * @param name the Name to use for the new symbol
     * @param type the type of the new symbol
     * @param pos the declaration position of the new symbol, if incarnations is true
     * @param incarnations whether there will be multiple incarnations of this symbol
     * @return a JCIdent tree node representing a use of the new symbol
     */
    protected JCIdent newAuxIdent(@NonNull String name, @NonNull Type type, int pos, boolean incarnations) {
        return newAuxIdent(names.fromString(name),type,pos,incarnations);
    }
    
    // FIXME - review
    /** Creates an attributed, untranslated JCIdent and accompanying VarSymbol using the given name and type;
     * the given pos is used as the textual position of the JCIdent node; also, if incarnations is
     * true, pos is used as the declaration position of the new identifier, with the implication that
     * additional incarnations will be defined later. The new Symbol has no modifiers and no owner.
     * @param name the Name to use for the new symbol
     * @param type the type of the new symbol
     * @param pos the declaration position of the new symbol, if incarnations is true
     * @param incarnations whether there will be multiple incarnations of this symbol
     * @return a JCIdent tree node representing a use of the new symbol
     */
    protected JCIdent newAuxIdent(@NonNull Name name, @NonNull Type type, int pos, boolean incarnations) {
        VarSymbol s = new VarSymbol(0,name,type,null);
        s.pos = incarnations ? pos : Position.NOPOS;
        return newAuxIdent(s,pos);
    }
    
    // FIXME - review - same as treeutils.makeIdent
    /** Creates an attributed JCIdent from the given VarSymbol;
     * the given pos is used as the textual position of the JCIdent node;
     * @param sym a Variable Symbol
     * @param pos the use position of the new tree node
     * @return a JCIdent tree node representing a use of the new symbol
     */
    protected JCIdent newAuxIdent(VarSymbol sym, int pos) {
        JCIdent id = factory.at(pos).Ident(sym.name);
        id.sym = sym;
        id.type = sym.type;
        return id;
    }

    // FIXME - review - change to treeutils.makeVarSymbol
    /** Creates a new VarSymbol with the given name and type and modifier flags (and no owner);
     * the declaration position is 'pos'. */
    protected VarSymbol newVarSymbol(long flags, @NonNull String name, @NonNull Type type, int pos) {
        // We leave the symbol's declaration position as Position.NOPOS (-1).
        VarSymbol v = new VarSymbol(flags,names.fromString(name),type,null);
        v.pos = pos;
        return v;
    }
    

    /** Sets all the variables that are supposed to stay in synch with the value of
     * currentBlock
     * @param b the new currentBlock
     */
    @Override
    protected void setCurrentBlock(BasicBlock b) {
        super.setCurrentBlock(b);
        currentMap = blockmaps.get(b);
        if (currentMap == null) currentMap = initMap(currentBlock); // FIXME - under what circumstances is the currentMap already available?
    }
    
    /** Files away a completed block, adding it to the blocksCompleted list and
     * to the lookup Map.
     * @param b the completed block
     */
    @Override
    protected boolean completed(@NonNull BasicBlock b) {
        if (super.completed(b)) return true;
        blockmaps.put(b,currentMap);
        currentMap = null; // Defensive - so no inadvertent assignments
        //log.noticeWriter.println("Completed block " + b.id);
        return false;
    }
    
    /** Converts the top-level block of a method into the elements of a BasicProgram 
     * 
     * @param methodDecl the method to convert to to a BasicProgram
     * @param denestedSpecs the specs of the method
     * @param classDecl the declaration of the containing class
     * @return the completed BasicProgram
     */
    protected @NonNull BasicProgram convertMethodBody(JCBlock block, @NonNull JCMethodDecl methodDecl, 
            JmlMethodSpecs denestedSpecs, @NonNull JCClassDecl classDecl, @NonNull JmlAssertionAdder assertionAdder) {
        initialize(methodDecl,classDecl);
        this.isDefined.clear();
        unique = 0;
//        inSpecExpression = false;
        if (classDecl.sym == null) {
            log.error("jml.internal","The class declaration in BasicBlocker.convertMethodBody appears not to be typechecked");
            return null;
        }

//        JmlClassInfo classInfo = getClassInfo(classDecl.sym);
//        if (classInfo == null) {
//            log.error("jml.internal","There is no class information for " + classDecl.sym);
//            return null;
//        }
        newdefs = new LinkedList<BasicProgram.Definition>();
        newpdefs = new LinkedList<JCExpression>();
        background = new LinkedList<JCExpression>();
        blockmaps.clear();
        labelmaps.clear();
        
        terminationSym = (VarSymbol)assertionAdder.terminationSymbols.get(methodDecl);
        terminationVar = newAuxIdent(terminationSym,0);
        exceptionVar = treeutils.makeIdent(Position.NOPOS,assertionAdder.exceptionSymbols.get(methodDecl)); // newAuxIdent(EXCEPTION,syms.exceptionType,0,true);
        heapVar = newAuxIdent(HEAP_VAR,syms.intType,0,true); // FIXME - would this be better as its own uninterpreted type?
        assumeCheckCountVar = newAuxIdent(ASSUME_CHECK_COUNT,syms.intType,0,false);
        assumeCheckCount = 0;
        
        BasicProgram.Definition def = new BasicProgram.Definition(0,assumeCheckCountVar,treeutils.zero);
        newdefs.add(def);

        // Define the start block
        int pos = methodDecl.pos;
        BasicBlock startBlock = newBlock(START_BLOCK_NAME,pos);

        // Define the body block
        // Put all the program statements in the Body Block
        BasicBlock bodyBlock = newBlock(BODY_BLOCK_NAME,methodDecl.body.pos);

        // Add declarations of method parameters
        for (JCVariableDecl d: methodDecl.params) {
            // We reset this with a location of 0 so that the name does not get
            // changed. This is only because the premap does not know these names.
            // And will probablly have to change when encodedName is made more robust. FIXME
            JCVariableDecl dd = treeutils.makeVarDef(d.type,d.name,d.sym.owner,0);
            bodyBlock.statements.add(dd);
        }
        
        // Then the program
        bodyBlock.statements.addAll(block.getStatements());
        follows(startBlock,bodyBlock);
        
        // Handle the start block a little specially
        // It does not have any statements in it
        startBlock(startBlock); // Start it so the currentMap, currentBlock, remainingStatements are defined

        // Define the thisId
        if (this.methodDecl._this != null) {
            currentMap.put(this.methodDecl._this, currentMap.everythingIncarnation, this.methodDecl._this.name);
            thisId = newAuxIdent(this.methodDecl._this.name.toString(),methodDecl.sym.owner.type,pos,false);
            currentThisId = thisId;
        }


        // FIXME - these no longer belong here, I think
        newIdentIncarnation(heapVar,0);
        newIdentIncarnation(allocSym,allocCount);
        currentMap.put(syms.lengthVar, 0, names.fromString(LENGTH)); // TODO: Some places use 'length' without encoding, so we store an unencoded name

        premap = currentMap.copy();
        

        // FIXME - have to do static vars of super types also
        // FIXME - and all the model fields
        // FIXME - and all the fields of referenced classes
        // We have to create and store incarnations of class fields so that there is a record of
        // them in the oldMap. Otherwise, if the variables are used within \old later on, a new 
        // identifier will be created, with a new unique number.
//        for (JCTree tree: classInfo.decl.defs ) {
//            if (tree instanceof JCVariableDecl) {
//                JCVariableDecl d = (JCVariableDecl)tree;
//                newIdentIncarnation(d.sym,0);
//            }
//        }

        completed(currentBlock);

        processBlock(bodyBlock);
        
        // Finished processing all the blocks
        // Make the BasicProgram
        program.startId = startBlock.id;
        program.blocks.addAll(blocksCompleted);
        if (assumeCheck != null) booleanAssumeCheck = assumeCheck;
        program.definitions = newdefs;
        program.pdefinitions = newpdefs;
        program.background = background;
        program.assumeCheckVar = assumeCheckCountVar;
        program.toLogicalForm = toLogicalForm;
        return program;
    }
    
    
    /** Adds an assert statement into the given statement list
     * @param label the label for the assert statement
     * @param that the expression which must be true
     * @param declpos the associated position (e.g. of the declaration that causes the assertion)
     * @param statements the statement list to which to add the new assert statement
     * @param usepos the source position at which the expression is asserted
     * @param source the source file corresponding to usepos
     * @param statement
     */
    protected void addAssert(Label label, JCExpression that, int declpos, List<JCStatement> statements, int usepos, JavaFileObject source, JCTree statement) {
        JmlTree.JmlStatementExpr st = factory.at(statement.pos()).JmlExpressionStatement(JmlToken.ASSERT,label,that);
        st.optionalExpression = null;
        st.source = source;
        st.line = -1; // ????? FIXME
        st.associatedPos = declpos;
        st.associatedSource = null; // OK - always same as source
        st.type = null; // no type for a statement
        copyEndPosition(st,statement);
        statements.add(st);
    }
    
    
//    // FIXME - REVIEW and document
//    /** Adds an assertion with an untranslated expression to the given statement list; 
//     * it is presumed the statement will be translated later */
//    protected void addUntranslatedAssert(Label label, JCExpression that, int declpos, List<JCStatement> statements, int usepos, /*@Nullable*/JavaFileObject source) {
//        JmlStatementExpr st;
//        st = factory.at(usepos).JmlExpressionStatement(JmlToken.ASSERT,label,that);
//        st.optionalExpression = null;
//        st.source = source;
//        st.associatedPos = declpos;
//        st.type = null; // no type for a statement
//        statements.add(st);
//    }
//    
    // FIXME - REVIEW and document
    /** Adds an assertion to the given statement list; the expression is presumed translated */
    protected void addAssertNoTrack(Label label, JCExpression that, List<JCStatement> statements, int usepos, /*@Nullable*/JavaFileObject source) {
        JmlStatementExpr st;
        st = factory.at(usepos).JmlExpressionStatement(JmlToken.ASSERT,label,that);
        st.optionalExpression = null;
        st.type = null; // no type for a statement
        st.source = source;
        st.associatedPos = usepos;// FIXME - what should this be set to?
        statements.add(st);
    }
    
    /** Adds a new assume statement to the end of the currentBlock; the assume statement is
     * given the declaration pos and label from the arguments; it is presumed the input expression is
     * translated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param expr the (translated) expression being assumed
     */
    protected void addAssume(int pos, Label label, JCExpression expr) {
        addAssume(pos,label,expr,currentBlock.statements);
    }
    
    // FIXME - REVIEW and document
    /** Adds a new assume statement to the end of the given statements list; the assume statement is
     * given the declaration pos and label from the arguments; it is presumed the input expression is
     * translated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param that the (translated) expression being assumed
     * @param statements the list to add the new assume statement to
     */
    protected JmlStatementExpr addAssume(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        factory.at(pos);
        JmlStatementExpr st;
        if (useAssumeDefinitions) {
            JCIdent id = factory.Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
            id.type = syms.booleanType;
            newdefs.add(new BasicProgram.Definition(that.pos,id,that)); // FIXME- end position?
            st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,id);
        } else {
            st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,that);
        }
        copyEndPosition(st,that);
        st.type = null; // statements do not have a type
        statements.add(st);
        return st;
    }
    
    // FIXME - REVIEW and document
    protected JmlStatementExpr addAssume(int startpos, JCTree endpos, Label label, JCExpression that, List<JCStatement> statements) {
        if (startpos < 0) startpos = that.pos; // FIXME - temp 
        factory.at(startpos);
        JmlStatementExpr st;
        if (useAssumeDefinitions) {
            JCIdent id = factory.Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
            id.type = syms.booleanType;
            newdefs.add(new BasicProgram.Definition(that.pos,id,that)); // FIXME- start, end position?
            st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,id);
        } else {
            st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,that);
        }
        copyEndPosition(st,endpos);
        st.type = null; // statements do not have a type
        statements.add(st);
        return st;
    }
    
//    // FIXME - REVIEW and document
//    protected JmlStatementExpr addAssumeNoDef(int startpos, JCTree endpos, Label label, JCExpression that, List<JCStatement> statements) {
//        if (startpos < 0) startpos = that.pos; // FIXME - temp 
//        factory.at(startpos);
//        JmlStatementExpr st;
//        st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,that);
//        copyEndPosition(st,endpos);
//        st.type = null; // statements do not have a type
//        statements.add(st);
//        return st;
//    }
    
    // FIXME - REVIEW and document
    /** Adds a new UNTRANSLATED assume statement to the end of the given statements list; the statements list
     * should be a list of statements that will be processed (and translated) at some later time;
     * the assume statement is
     * given the declaration pos and label from the arguments; it is presumed the input expression is
     * untranslated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param that the (untranslated) expression being assumed
     * @param statements the list to add the new assume statement to
     */
    protected JmlStatementExpr addUntranslatedAssume(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        JmlStatementExpr st = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,label,that);
        st.type = null; // statements do not have a type
        copyEndPosition(st,that);
        statements.add(st);
        return st;
    }
    
//    // FIXME - REVIEW and document
//    protected JmlStatementExpr addUntranslatedAssume(int pos, JCTree posend, Label label, JCExpression that, List<JCStatement> statements) {
//        JmlStatementExpr st = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,label,that);
//        st.type = null; // statements do not have a type
//        copyEndPosition(st,posend);
//        statements.add(st);
//        return st;
//    }
    
    // FIXME - REVIEW and document
    /** Adds an axiom to the axiom set */
    protected void addAxiom(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        newpdefs.add(that);
    }
    
    // FIXME - REVIEW and document
    static public String encodeType(Type t) {   // FIXME String? char? void? unsigned?
        if (t instanceof ArrayType) {
            return "refA$" + encodeType(((ArrayType)t).getComponentType());
        } else if (!t.isPrimitive()) {
            return "REF";
        } else if (t.tag == TypeTags.INT || t.tag == TypeTags.SHORT || t.tag == TypeTags.LONG || t.tag == TypeTags.BYTE) {
            return "int";
        } else if (t.tag == TypeTags.BOOLEAN) {
            return "bool";
        } else if (t.tag == TypeTags.FLOAT || t.tag == TypeTags.DOUBLE) {
            return "real";
        } else if (t.tag == TypeTags.CHAR) {
            return "int";
        } else {
            return "unknown";
        }
    }
    
    // FIXME - review and document
    private Map<String,JCIdent> arrayIdMap = new HashMap<String,JCIdent>();
    
    // FIXME - review and document
    protected JCIdent getArrayIdent(Type componentType) {
        String s = "arrays_" + encodeType(componentType);
        JCIdent id = arrayIdMap.get(s);
        if (id == null) {
            id = factory.Ident(names.fromString(s));
            id.pos = 0;
            id.type = new ArrayType(componentType,syms.arrayClass);
            VarSymbol sym = new VarSymbol(0,id.name,id.type,null);
            sym.pos = 0;
            id.sym = sym;
            arrayIdMap.put(s,id);
        }
        id = newIdentUse((VarSymbol)id.sym,0);
        return id;
    }
    
    /** Creates a auxiliary variable and inserts an assumption about its value.
     * Any new generated statements are added into the currentBlock
     * @param name the name of the auxiliary variable, including any label and position encoding
     * @param type the type of the variable (e.g. syms.booleanType)
     * @param expr the (untranslated) value of the variable
     * @return the variable corresponding the the given String argument
     */
    // FIXME - REVIEW and document
    // FIXME - modifies the content of currentBlock.statements
    protected @NonNull JCIdent addAuxVariable(@NonNull String name, @NonNull Type type, @NonNull JCExpression expr, boolean makeDefinition, boolean saveInMap) {
        JCExpression newexpr = expr;//trExpr(expr);
        int pos = expr == null ? Position.NOPOS : expr.getPreferredPosition(); // FIXME - NOPOS is not really want we want
        JCIdent vd = newAuxIdent(name,type,pos,false);
        if (saveInMap) {
            currentMap.put((VarSymbol)vd.sym,pos,vd.name);
        }
        // FIXME - use a definition?
        if (makeDefinition) {
            //newdefs.add(treeutils.makeEquality(newexpr.pos,vd,newexpr));
            newdefs.add(new BasicProgram.Definition(pos,vd,newexpr));
        } else {
            JmlTree.JmlStatementExpr asm = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,treeutils.makeEquality(newexpr.pos,vd,newexpr));
            currentBlock.statements.add(asm);
        }
        return vd;
    }
    
    
    
//    /** Adds assumptions to equate parameters of a overridden method with those 
//     * of an overriding method.
//     * @param baseMethod the overriding method
//     * @param otherMethod the overridden method
//     * @param pos a position to use in creating new variable locations
//     * @param b the block into which to add the assumptions
//     */ // FIXME - check that the names are different when a method is used in multiple locations
//    protected void addParameterMappings(@NonNull JCMethodDecl baseMethod, @NonNull JCMethodDecl otherMethod, int pos, BasicBlock b) {
//        if (baseMethod == null) return;  // FIXME - this happens on <array>.clone() - any other time?
//        Iterator<JCVariableDecl> baseParams = baseMethod.params.iterator();
//        Iterator<JCVariableDecl> newParams = otherMethod.params.iterator();
//        while (baseParams.hasNext()) {
//            JCVariableDecl base = baseParams.next();
//            JCVariableDecl newp = newParams.next();
//            JCIdent baseId = newIdentUse(base.sym,pos);
//            JCIdent newId = newIdentIncarnation(newp,0);
//            //JCExpression eq = trSpecExpr(treeutils.makeEquality(pos,newId,baseId),((ClassSymbol)baseMethod.sym.owner).sourcefile);
//            JCExpression eq = (treeutils.makeEquality(pos,newId,baseId));
//            addAssume(pos,Label.SYN,eq,b.statements);
//        }
//    }
//    
//    // FIXME - REVIEW and document
//    // FIXME - change to this use everywhere - sort out positions
//    protected void addParameterMappings(@NonNull MethodSymbol baseMethod, @NonNull JCMethodDecl otherMethod, int pos, BasicBlock b) {
//        Iterator<VarSymbol> baseParams = baseMethod.params.iterator();
//        Iterator<JCVariableDecl> newParams = otherMethod.params.iterator();
//        while (baseParams.hasNext()) {
//            VarSymbol base = baseParams.next();
//            JCVariableDecl newp = newParams.next();
//            JCIdent baseId = newIdentUse(base,pos);
//            JCIdent newId = newIdentIncarnation(newp,0);
//            //JCExpression eq = trSpecExpr(treeutils.makeEquality(pos,newId,baseId),((ClassSymbol)baseMethod.owner).sourcefile);
//            JCExpression eq = (treeutils.makeEquality(pos,newId,baseId));
//            addAssume(pos,Label.SYN,eq,b.statements);
//        }
//    }
    
//    /** This generates a comment statement (not added to any statement list) whose content is the
//     * given String.
//     */
//    public JmlStatementExpr comment(int pos, String s) {
//        return factory.at(pos).JmlExpressionStatement(JmlToken.COMMENT,null,factory.Literal(s));
//    }
//    
//    public JmlStatementExpr comment(DiagnosticPosition pos, String s) {
//        return factory.at(pos).JmlExpressionStatement(JmlToken.COMMENT,null,factory.Literal(s));
//    }
//    
//    /** This generates a comment statement (not in any statement list) whose content is the
//     * given JCTree, pretty-printed.
//     */
//    public JmlStatementExpr comment(JCTree t) {
//        return comment(t.pos(),JmlPretty.write(t,false));
//    }
    
    /** Returns the initial VarMap of the given block; the returned map is a combination
     * of the maps from all preceding blocks, with appropriate DSA assignments added.
     * @param block
     * @return the VarMap for the given block
     */
    protected VarMap initMap(BasicBlock block) {
        VarMap newMap = new VarMap();
        currentMap = newMap;
        if (block.preceders.size() == 0) {
            // keep the empty one
        } else if (block.preceders.size() == 1) {
            newMap.putAll(blockmaps.get(block.preceders.get(0))); 
        } else {
            // Here we do the DSA step of combining the results of the blocks that precede
            // the block we are about to process. The situation is this: a particular symbol,
            // sym say, may have been modified in any of the preceding blocks. In each case
            // a new incarnation and a new identifier Name will have been assigned. A record
            // of that current Identifer Name is in the VarMap for the block. But we need a single
            // Name to use in this new block.  So we pick a Name (e.g. sym$k$nnn) to use for the new block,
            // and for each preceding block we add an assumption of the form sym$k$mmm = sym$k$nnn.
            // This assumption is added to the end of the preceding block.
            // In this version, we use the minimum incarnation as the new name, 
            // so that it is defined before all the blocks that use it.
            // FIXME - review this again, expecially the statement above.
            List<VarMap> all = new LinkedList<VarMap>();
            VarMap combined = new VarMap();
            int maxe = -1;
            for (BasicBlock b : block.preceders) {
                VarMap m = blockmaps.get(b);
                all.add(m);
                combined.putAll(m);
                if (maxe < m.everythingIncarnation) maxe = m.everythingIncarnation;
            }
            combined.everythingIncarnation = maxe;
            for (VarSymbol sym: combined.keySet()) {
                if (sym.owner instanceof Symbol.ClassSymbol) {
                    // If the symbol is owned by the class, then it is implicitly part of each VarMap,
                    // even if it is not explicitly listed.

                    Name maxName = null;
                    int max = -1;
                    int num = 0;
                    for (VarMap m: all) {
                        Integer i = m.get(sym);
                        if (i != max) num++;
                        if (i > max) {
                            max = i;
                            maxName = m.getName(sym);
                        }
                    }
                    Name newName = maxName;
                    if (num > 1) {
                        max++;
                        JCIdent id = newIdentIncarnation(sym,max); // relies on the uniqueness value to be different
                        // Need to declare this before all relevant blocks, so we do it at the very beginning
                        program.declarations.add(id);
                        newName = id.name;
                    }
                    newMap.put(sym,max,newName);

                    for (BasicBlock b: block.preceders) {
                        VarMap m = blockmaps.get(b);
                        Integer i = m.get(sym);
                        if (i < max) {
                            // No position information for these nodes
                            // Type information put in, though I don't know that we need it
                            JCIdent pold = newIdentUse(m,sym,0);
                            JCIdent pnew = newIdentUse(newMap,sym,0);
                            JCBinary eq = treeutils.makeEquality(0,pnew,pold);
                            addAssume(0,Label.DSA,eq,b.statements);
                        }
                    }
                } else {
                    // If the symbol is owned by the method, then if it is not in every inherited map,
                    // then it has gone out of scope and need not be repeated.
                    Name maxName = null;
                    int max = -1;
                    int num = 0;
                    boolean skip = false;
                    for (VarMap m: all) {
                        Name n = m.getName(sym);
                        if (n == null) { skip = true; break; }
                        Integer i = m.get(sym);
                        if (i > max) {
                            max = i;
                            maxName = n;
                        }
                    }
                    if (skip) continue;
                    Name newName = maxName;
                    boolean different = false;
                    for (VarMap m: all) {
                        Name n = m.getName(sym);
                        if (!newName.equals(n)) { different = true; break; }
                    }
                    if (different) {
                        max++;
                        JCIdent id = newIdentIncarnation(sym,max); // relies on the uniqueness value to be different
                        // Need to declare this before all relevant blocks, so we do it at the very beginning
                        program.declarations.add(id);
                        newName = id.name;
                    }
                    newMap.put(sym,max,newName);
                    if (different) {
                        for (BasicBlock b: block.preceders) {
                            VarMap m = blockmaps.get(b);
                            Integer i = m.get(sym);
                            if (i < max) {
                                // No position information for these nodes
                                // Type information put in, though I don't know that we need it
                                JCIdent pold = newIdentUse(m,sym,0);
                                JCIdent pnew = newIdentUse(newMap,sym,0);
                                JCBinary eq = treeutils.makeEquality(0,pnew,pold);
                                addAssume(0,Label.DSA,eq,b.statements);
                            }
                        }
                    }
                }
            }
        }
        return newMap;
    }
    

    // FIXME - probably use this in JmlAssertionAdder, rather than here
    
    
    
    // FIXME - meethodInfo objects are going to be recomputed for every instance of BasicBlocker

    // FIXME - review and document
    Map<Symbol,JmlMethodInfo> methodInfoMap = new HashMap<Symbol,JmlMethodInfo>();

    // FIXME - review and document
    JmlMethodInfo getMethodInfo(MethodSymbol msym) {
        JmlMethodInfo mi = methodInfoMap.get(msym);
        if (mi == null) {
            mi = computeMethodInfo(msym);
            methodInfoMap.put(msym,mi);
        }
        return mi;
    }


    // FIXME - when run standalone (not in Eclipse), this method is called with the Object constructor 
    // as its argument, but with method.sym == null - is this because it is Binary?  is it not seeing the specs?
    protected JmlMethodInfo computeMethodInfo(MethodSymbol msym) {
        JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(msym);
        if (mspecs == null) {
            // The specs may be null because none were ever written (and there
            // was not even a declaration of the method to which an empty spec
            // was attached).
            mspecs = JmlSpecs.defaultSpecs(null);
        }
        // Note: The mspecs.decl may be null if the original class is only
        // binary and no specs file was written (so there is no source code
        // declaration anywhere).

        JmlMethodInfo mi = mspecs.cases.decl == null ? new JmlMethodInfo(msym,context) : new JmlMethodInfo(mspecs.cases.decl,context);
        JmlMethodSpecs denestedSpecs = msym == null ? null : specs.getDenestedSpecs(msym);
        if (JmlEsc.escdebug) log.noticeWriter.println("SPECS FOR " + msym.owner + " " + msym + " " + (denestedSpecs != null));
        if (JmlEsc.escdebug) log.noticeWriter.println(denestedSpecs == null ? "     No denested Specs" : ("   " + denestedSpecs.toString())); // FIXME - bad indenting

        List<JCStatement> prev = currentBlock.statements;
        currentBlock.statements = new LinkedList<JCStatement>();
        if (denestedSpecs != null) {
            // preconditions
            JCExpression pre = denestedSpecs.cases.size() == 0 ? treeutils.makeBooleanLiteral(mspecs.cases.decl==null?0:mspecs.cases.decl.pos,true) : null;
            int num = 0;
            JavaFileObject source = null;
            for (JmlSpecificationCase spc: denestedSpecs.cases) {
                treetrans.pushSource(spc.sourcefile);
                if (source == null) source = spc.sourcefile;
                
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.FORALL) {
                        JmlMethodClauseDecl d = (JmlMethodClauseDecl)c;
                        for (JCVariableDecl stat: d.decls) {
                            JCVariableDecl newstat = treetrans.translate(stat);
                            mi.foralls.add(newstat);
                        }
                    } else if (c.token == JmlToken.OLD) {
                        JmlMethodClauseDecl d = (JmlMethodClauseDecl)c;
                        for (JCVariableDecl stat: d.decls) {
                            JCVariableDecl newstat = treetrans.translate(stat);
                            mi.olds.append(newstat);
                        }
                    }
                }
                JCExpression spre = null;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.REQUIRES) {
                        num++;
                        JCExpression e = treetrans.translate((((JmlMethodClauseExpr)c).expression));
                        e.pos = c.pos;
                        copyEndPosition(e,c); // FIXME - these lines should be part of translate
                        if (spre == null) {
                            spre = e;
                        } else {
                            spre = treeutils.makeBinary(spre.pos,JCTree.AND,spre,e);
                            copyEndPosition(spre,e);
                        }
                    }
                }
                if (spre == null) {
                    spre = treeutils.makeBooleanLiteral(spc.pos,true);
                    copyEndPosition(spre,spc);
                }
                if (pre == null) pre = spre;
                else {
                    pre = treeutils.makeBinary(pre.pos,JCTree.BITOR,pre,spre);
                    copyEndPosition(pre,spre);
                }
                treetrans.popSource();
            }{
                JmlMethodClauseExpr p = factory.at(pre.pos).JmlMethodClauseExpr(JmlToken.REQUIRES,pre);
                p.sourcefile = source != null ? source : log.currentSourceFile();
                if (num == 1) copyEndPosition(p,pre);
                mi.requiresPredicates.add(p);  // Just one composite precondition for all of the spec cases
            }
            
            // postconditions
            for (JmlSpecificationCase spc: denestedSpecs.cases) {
                JCExpression spre = null;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.REQUIRES) {
                        if (spre == null) {
                            JCExpression cexpr = ((JmlMethodClauseExpr)c).expression;
                            spre = treetrans.translate((cexpr));
                            copyEndPosition(spre,cexpr); // FIXME _ included in translate?
                        } else {
                            int pos = spre.getStartPosition();
                            JCExpression cexpr = ((JmlMethodClauseExpr)c).expression;
                            spre = treeutils.makeBinary(pos,JCTree.AND,spre,treetrans.translate((cexpr)));
                            copyEndPosition(spre,cexpr);
                        }
                    }
                }
                if (spre == null) {
                    spre = treeutils.makeBooleanLiteral(Position.NOPOS, true);
                    // FIXME - fix position?
                }
                // FIXME - set startpos for JmlMethodInvocation
                JCExpression nspre = factory.at(spre.getStartPosition()).JmlMethodInvocation(JmlToken.BSOLD,com.sun.tools.javac.util.List.of(spre));
                copyEndPosition(nspre,spre);
                nspre.type = spre.type;
                spre = nspre;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.ENSURES) {
                        JCExpression e = treetrans.translate(((JmlMethodClauseExpr)c).expression);
                        copyEndPosition(e,((JmlMethodClauseExpr)c).expression); // FIXME - fold into translate
                        JCExpression post = treeutils.makeJmlBinary(e.getStartPosition(),JmlToken.IMPLIES,spre,e);
                        copyEndPosition(post,e);// FIXME - fold into translate; wathc out for different source files
                        JmlMethodClauseExpr p = factory.at(c.pos).JmlMethodClauseExpr(JmlToken.ENSURES,post);
                        p.sourcefile = c.source();
                        copyEndPosition(p,c);
                        int sp1 = post.getStartPosition();
                        int ep1 = post.getEndPosition(log.currentSource().getEndPosTable());
                        int sp2 = spre.getStartPosition();
                        int ep2 = spre.getEndPosition(log.currentSource().getEndPosTable());
                        int sp3 = e.getStartPosition();
                        int ep3 = e.getEndPosition(log.currentSource().getEndPosTable());
                        mi.ensuresPredicates.add(p);
                    } else if (c.token == JmlToken.ASSIGNABLE) {
                        JmlMethodClauseStoreRef mod = (JmlMethodClauseStoreRef)c;
                        // spre is the precondition under which the store-refs are modified
                        List<JCExpression> list = mod.list; // store-ref expressions
                        mi.assignables.add(new JmlMethodInfo.Entry(spre,list));
                    } else if (c.token == JmlToken.SIGNALS) {
                        // FIXME - what if there is no variable? - is there one already inserted or is it null?
                        JmlMethodClauseSignals mod = (JmlMethodClauseSignals)c;
                        JCExpression e = treetrans.translate(mod.expression);
                        copyEndPosition(e,mod.expression); // FIXME - fold into translate
                        boolean isFalse = (e instanceof JCLiteral) && ((JCLiteral)e).value.equals(0);
                        // If vardef is null, then there is no declaration in the signals clause (e.g. it is just false).
                        // We use the internal \exception token instead; we presume the type is java.lang.Exception 
                        JCExpression post = treeutils.makeJmlBinary(e.getStartPosition(),JmlToken.IMPLIES,spre,e);
                        copyEndPosition(post,e);// FIXME - fold into translate; wathc out for different source files
                        if (!isFalse) {
                            if (mod.vardef != null) {
                                JCIdent id = treeutils.makeIdent(mod.vardef.pos,mod.vardef.sym);
                                e = makeNNInstanceof(id,c.pos, mod.vardef.type, mod.vardef.pos);
                                post = treeutils.makeJmlBinary(c.pos,JmlToken.IMPLIES,e,post);
                            } else {
                                JCExpression id = factory.at(c.pos).JmlSingleton(JmlToken.BSEXCEPTION);
                                e = makeNNInstanceof(id,c.pos, syms.exceptionType, c.pos);
                                post = treeutils.makeJmlBinary(c.pos,JmlToken.IMPLIES,e,post);
                            }
                            copyEndPosition(post,mod.expression);
                        }
                        JmlMethodClauseExpr p = factory.at(c.pos).JmlMethodClauseExpr(JmlToken.SIGNALS,post);
                        copyEndPosition(p,c);
                        p.sourcefile = c.source();
                        // expression is    pre ==> post
                        // or               (\typeof(exVar) <: ExTYPE) ==> (pre ==> post)
                        mi.exPredicates.add(p);
                    } else if (c.token == JmlToken.DIVERGES) {
                        JCExpression e = treetrans.translate(((JmlMethodClauseExpr)c).expression);
                        JCExpression post = treeutils.makeJmlBinary(e.getStartPosition(),JmlToken.IMPLIES,spre,e);
                        JmlMethodClauseExpr p = factory.at(post.pos).JmlMethodClauseExpr(JmlToken.DIVERGES,post);
                        p.sourcefile = c.source();
                        mi.divergesPredicates.add(p);
                    } else if (c.token == JmlToken.SIGNALS_ONLY) {
                        JCExpression post = makeSignalsOnly((JmlMethodClauseSignalsOnly)c);
                        JmlMethodClauseExpr p = factory.at(post.pos).JmlMethodClauseExpr(JmlToken.SIGNALS,post);
                        p.sourcefile = c.source();
                        mi.sigPredicates.add(p);
                    }
                    // FIXME - is signals_only desugared or handled here?
                    // FIXME - we are ignoring forall old when duration working_space callable accessible measured_by captures
                }
            }
        }
        currentBlock.statements = prev;
        return mi;
    }
    
    // FIXME - do we need this - here?
    /** Makes a JML \typeof expression, with the given expression as the argument */
    protected JCExpression makeTypeof(JCExpression e) {
        JCExpression typeof = factory.at(e.pos).JmlMethodInvocation(JmlToken.BSTYPEOF,e);
        typeof.type = syms.classType;
        return typeof;
    }
    
    // FIXME - review and document
    /** Makes a Java this parse tree node (attributed) */
    protected JCIdent makeThis(int pos) {
        return treeutils.makeIdent(pos,methodDecl._this);
    }
    
    // FIXME - review and document
    /** Makes the equivalent of an instanceof operation: \typeof(e) <: \type(type) */
    protected JCExpression makeNNInstanceof(JCExpression e, int epos, Type type, int typepos) {
        JCExpression e1 = makeTypeof(e);
        JCExpression e2 = makeTypeLiteral(type,typepos);
        //if (inSpecExpression) e2 = trSpecExpr(e2,null);
        JCExpression ee = treeutils.makeJmlBinary(epos,JmlToken.SUBTYPE_OF,e1,e2);
        return ee;
    }
    
    // FIXME - review and document
    /** Makes the equivalent of an instanceof operation: e !=null && \typeof(e) <: \type(type) */
    protected JCExpression makeInstanceof(JCExpression e, int epos, Type type, int typepos) {
        JCExpression e1 = treeutils.makeNeqObject(epos,e,nullLiteral);
        JCExpression e2 = treeutils.makeJmlBinary(epos,JmlToken.SUBTYPE_OF,makeTypeof(e),makeTypeLiteral(type,typepos));
        //if (inSpecExpression) e2 = trSpecExpr(e2,null);
        JCExpression ee = treeutils.makeBinary(epos,JCTree.AND,e1,e2);
        return ee;
    }
    
    // FIXME - review and document
    protected MethodSymbol makeFunction(Name name, Type resultType, Type... argTypes) {
        ListBuffer<Type> args = new ListBuffer<Type>().appendArray(argTypes);
        MethodType methodType = new MethodType(args.toList(),resultType,com.sun.tools.javac.util.List.<Type>nil(),syms.methodClass);
        MethodSymbol meth = new MethodSymbol(Flags.STATIC,name,methodType,null); // no owner
        return meth;
    }
    
    // FIXME - review and document
    protected JCExpression makeFunctionApply(int pos, MethodSymbol meth, JCExpression... args) {
        JCIdent methid = factory.at(pos).Ident(meth);
        JCExpression e = factory.at(pos).Apply(null,methid,new ListBuffer<JCExpression>().appendArray(args).toList());
        e.type = meth.getReturnType();
        return e;
    }
    
    // FIXME - review and document
    protected JCExpression makeSignalsOnly(JmlMethodClauseSignalsOnly clause) {
        JCExpression e = treeutils.makeBooleanLiteral(clause.pos,false);
        JCExpression id = factory.at(0).JmlSingleton(JmlToken.BSEXCEPTION);
        for (JCExpression typetree: clause.list) {
            int pos = typetree.getStartPosition();
            e = treeutils.makeBinary(pos, 
                    JCTree.OR, makeNNInstanceof(id, pos, typetree.type, pos), e);
        }
        return e;
    }

    // FIXME - review and document
    protected int endPos(JCTree t) {
        if (t instanceof JCBlock) {
            return ((JCBlock)t).endpos;
        } else if (t instanceof JCMethodDecl) {
            return endPos(((JCMethodDecl)t).body);
        } else {
            // FIXME - fix this sometime - we don't know the end position of
            // statements that are not blocks
            if (JmlEsc.escdebug) log.noticeWriter.println("UNKNOWN END POS");
            return t.pos;
        }
    }


    // STATEMENT NODES
    
//    // Just process all the statements in the block prior to any other
//    // remaining statements 
//    // OK
//    public void visitBlock(JCBlock that) {
//        List<JCStatement> s = that.getStatements();
//        if (s != null) remainingStatements.addAll(0,s);
//    }
    
//    protected void __visitForeachLoopWithSpecs(JCEnhancedForLoop that, com.sun.tools.javac.util.List<JmlStatementLoop> loopSpecs) {
//        int pos = that.pos;
//        if (that.expr.type.tag == TypeTags.ARRAY) {
//            // for (T v; arr) S
//            // becomes
//            //   for (int $$index=0; $$index<arr.length; $$index++) { v = arr[$$index]; S }
//            
//            // make   int $$index = 0;   as the initialization
////            Name name = names.fromString("$$index$"+that.pos);
////            JCVariableDecl decl = makeVariableDecl(name,syms.intType,treeutils.makeIntLiteral(0,pos),pos);
////            JCVariableDecl decl = ((JmlEnhancedForLoop)that).indexDecl;
////            JCVariableDecl vdecl = ((JmlEnhancedForLoop)that).indexDecl;
////            com.sun.tools.javac.util.List<JCStatement> initList = com.sun.tools.javac.util.List.<JCStatement>of(decl,vdecl);
//
//            // make assume \values.size() == 0
//            
////            // make   $$index < <expr>.length   as the loop test
////            JCIdent id = (JCIdent)factory.at(pos).Ident(decl);
////            id.type = decl.type;
////            JCExpression fa = factory.at(pos).Select(that.getExpression(),syms.lengthVar);
////            fa.type = syms.intType;
////            JCExpression test = treeutils.makeBinary(pos,JCTree.LT,id,fa);
//
////            // make   $$index = $$index + 1  as the update list
////            JCIdent idd = (JCIdent)factory.at(pos+1).Ident(decl);
////            id.type = decl.type;
////            JCAssign asg = factory.at(idd.pos).Assign(idd,
////                    treeutils.makeBinary(idd.pos,JCTree.PLUS,id,treeutils.makeIntLiteral(pos,1)));
////            asg.type = syms.intType;
////            JCExpressionStatement update = factory.at(idd.pos).Exec(asg);
////            com.sun.tools.javac.util.List<JCExpressionStatement> updateList = com.sun.tools.javac.util.List.<JCExpressionStatement>of(update);
//            
////            // make   <var> = <expr>[$$index]    as the initialization of the target and prepend it to the body
////            JCArrayAccess aa = factory.at(pos).Indexed(that.getExpression(),id);
////            aa.type = that.getVariable().type;
////            JCIdent v = (JCIdent)factory.at(pos).Ident(that.getVariable());
////            v.type = aa.type;
////            asg = factory.at(pos).Assign(v,aa);
////            asg.type = v.type;
//            ListBuffer<JCStatement> newbody = new ListBuffer<JCStatement>();
////            newbody.append(factory.at(pos).Exec(asg));
//            newbody.append(that.body);
//            
//            // add 0 <= $$index && $$index <= <expr>.length
//            // as an additional loop invariant
////            JCExpression e1 = treeutils.makeBinary(pos,JCTree.LE,treeutils.makeIntLiteral(pos,0),id);
////            JCExpression e2 = treeutils.makeBinary(pos,JCTree.LE,id,fa);
////            JCExpression e3 = treeutils.makeBinary(pos,JCTree.AND,e1,e2);
////            JmlStatementLoop inv =factory.at(pos).JmlStatementLoop(JmlToken.LOOP_INVARIANT,e3);
////            if (loopSpecs == null) {
////                loopSpecs = com.sun.tools.javac.util.List.<JmlStatementLoop>of(inv);
////            } else {
////                ListBuffer<JmlStatementLoop> buf = new ListBuffer<JmlStatementLoop>();
////                buf.appendList(loopSpecs);
////                buf.append(inv);
////                loopSpecs = buf.toList();
////            }
//            visitLoopWithSpecs(that,null,treeutils.trueLit,null,factory.at(that.body.pos).Block(0,newbody.toList()),null);
//            
//            
//        } else {
//            notImpl(that); // FIXME
//        }
//    }
//    
//    public void visitDoLoop(JCDoWhileLoop that) {
//        currentBlock.statements.add(comment(that.pos,"do..."));
//        visitDoLoopWithSpecs(that,null);
//    }    
//
//    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
//        currentBlock.statements.add(comment(that.pos,"do..."));
//        visitDoLoopWithSpecs(that,that.loopSpecs);
//    }

    // OK
    @Override
    public void visitLabelled(JCLabeledStatement that) {
        VarMap map = currentMap.copy();
        labelmaps.put(that.label,map);
        super.visitLabelled(that);
    }
    
//    // Translation of a switch statement
//    //  switch (swexpr) {
//    //       case A:
//    //              SA;
//    //              break;
//    //       case B:
//    //              SB;
//    //              // fall through
//    //       case C:
//    //              SC;
//    //              break;
//    //       default:
//    //              SD;
//    //   }
//    //   translates to
//    //   -- continuation of current block:
//    //          assume $$switchExpr$<pos>$<unique> == swexpr;
//    //          goto $$case$<A>,$$case$<B>,$$case$<C>
//    //     $$case$<A>:
//    //          assume $$switchExpr$<pos>$<unique> == A;
//    //          SA
//    //          goto $$BL$<pos>$switchAfter
//    //     $$case$<B>:
//    //          assume $$switchExpr$<pos>$<unique> == B;
//    //          SB
//    //          goto $$caseBody$<C>
//    //     $$case$<C>:
//    //          assume $$switchExpr$<pos>$<unique> == C;
//    //          goto $$caseBody$<C>
//    //     $$caseBody$<C>:  // Need this block because B fallsthrough to C
//    //          SC
//    //          goto $$BL$<pos>$switchAfter
//    //     $$defaultcase$<N>:
//    //          assume !($$switchExpression$<pos>$<pos> == A && ...);
//    //          SD
//    //          goto $$BL$<pos>$switchAfter
//    //     $$BL$<pos>$switchAfter:
//    //          ....
//    //     
//    // OK
//    public void visitSwitch(JCSwitch that) { 
//        currentBlock.statements.add(comment(that.pos(),"switch ..."));
//        int pos = that.pos;
//        scan(that.selector);
//        JCExpression switchExpression = that.selector;
//        int swpos = switchExpression.getStartPosition();
//        List<JCCase> cases = that.cases;
//        
//        // The block that follows the switch statement
//        BasicBlock brest = null;
//        
//        try {
//            breakStack.add(0,that);
//
//            // We create a new auxiliary variable to hold the switch value, so 
//            // we can track its value and so the subexpression does not get
//            // replicated.  We add an assumption about its value and add it to
//            // list of new variables
//            Name switchName = names.fromString(SWITCH_EXPR_PREFIX + pos + "__" + (unique++));
// 
//            JCIdent vd = newAuxIdent(switchName,switchExpression.type,swpos,false);
//            program.declarations.add(vd);
//            JCExpression newexpr = treeutils.makeBinary(swpos,JCTree.EQ,vd,switchExpression);
//            addAssume(swpos,switchExpression,Label.SWITCH_VALUE,newexpr,currentBlock.statements);
//            BasicBlock switchStart = currentBlock;
//
//            // Now create an (unprocessed) basic block for everything that follows the
//            // switch statement
//            brest = newBlockWithRest("switchAfter",pos);// it gets all the followers of the current block
//
//            // Now we need to make an unprocessed basic block for each of the case statements,
//            // adding them to the todo list at the end
//            // Note that there might be nesting of other switch statements etc.
//            java.util.LinkedList<BasicBlock> blocks = new java.util.LinkedList<BasicBlock>();
//            BasicBlock prev = null;
//            JCExpression defaultCond = falseLiteral;
//            JmlTree.JmlStatementExpr defaultAsm = null;
//            for (JCCase caseStatement: cases) {
//                /*@ nullable */ JCExpression caseValue = caseStatement.getExpression();
//                List<JCStatement> stats = caseStatement.getStatements();
//                int casepos = caseStatement.getStartPosition();
//                
//                // create a block for this case test
//                BasicBlock blockForTest = newBlock(caseValue == null ? "default" : "case", casepos);
//                blocks.add(blockForTest);
//                follows(switchStart,blockForTest);
//                
//                // create the case test, or null if this is the default case
//                /*@ nullable */ JCBinary eq = caseValue == null ? null : treeutils.makeBinary(caseValue.getStartPosition(),JCTree.EQ,vd,caseValue);
//                JmlStatementExpr asm = addAssume(caseStatement.pos,Label.CASECONDITION,eq,blockForTest.statements);
//                //checkAssumption(caseStatement.pos,Label.CASECONDITION,blockForTest.statements);
//                
//                // continue to build up the default case test
//                if (caseValue == null) defaultAsm = asm; // remember the assumption for the default case
//                else defaultCond = treeutils.makeOr(caseValue.getStartPosition(),eq,defaultCond);
//
//                // determine whether this case falls through to the next
//                boolean fallthrough = stats.isEmpty() || !(stats.get(stats.size()-1) instanceof JCBreak);
//                
//                if (prev == null) {
//                    // statements can go in the same block
//                    blockForTest.statements.addAll(stats);
//                    follows(blockForTest,brest); // The following block is reset if there is fallthrough to a next block
//                    prev = fallthrough ? blockForTest : null;
//                } else {
//                    // falling through from the previous case
//                    // since there is fall-through, the statements need to go in their own block
//                    BasicBlock blockForStats = newBlock("caseBody",casepos);
//                    blockForStats.statements.addAll(stats);
//                    follows(blockForTest,blockForStats);
//                    replaceFollows(prev,blockForStats);
//                    follows(blockForStats,brest);
//                    blocks.add(blockForStats);
//                    prev = fallthrough ?  blockForStats : null;
//                }
//            }
//
//            // Now fix up the default case (which is not necessarily last).
//            // Fortunately we remembered it
//            int dpos = defaultAsm == null ? pos : defaultAsm.pos;
//            JCExpression eq = treeutils.makeUnary(dpos,JCTree.NOT,defaultCond);
//            if (defaultAsm != null) {
//                // There was a default case already made, but at the time we just
//                // put in null for the case condition, since we did not know it
//                // yet (and we wanted to process the statements in textual order).
//                // So here we violate encapsulation a bit and poke it in.
//                defaultAsm.expression = eq;
//            } else {
//                // There was no default - we need to construct an empty one
//                // create a block for this case test
//                BasicBlock blockForTest = newBlock("defaultcase",pos);
//                blocks.add(blockForTest);
//                follows(switchStart,blockForTest);
//                follows(blockForTest,brest);
//                
//                addAssume(pos,Label.CASECONDITION,eq,blockForTest.statements);
//            }
//            
//            processBlockStatements(true); // Complete the current block
//            // Now process all of the blocks we created
//            for (BasicBlock b: blocks) {
//                processBlock(b);
//            }
//        } finally {
//            breakStack.remove(0);
//        }
//        // Should never actually be null
//        if (brest != null) processBlock(brest);
//    }
    
    // OK
    /** Should call this because case statements are handled in switch. */
    public void visitCase(JCCase that) { shouldNotBeCalled(that); }
    
    
    // FIXME - REVIEW
    public void visitExec(JCExpressionStatement that)    { 
        // This includes assignments and stand-alone method invocations
        scan(that.expr);
    }
        
    // FIXME - needs review - al;ready converted to a BasicBlock assert?
    public void visitAssert(JCAssert that) { // This is a Java assert statement
        currentBlock.statements.add(comment(that));
        scan(that.cond);
        scan(that.detail);
        JCExpression cond = (that.cond);
        //JCExpression detail = (that.detail);
        // FIXME - what to do with detail
        // FIXME - for now turn cond into a JML assertion
        // FIXME - need a label for the assert statement
        // FIXME - set line and source
        addAssert(Label.EXPLICIT_ASSERT, cond, that.cond.getStartPosition(), currentBlock.statements, that.cond.getStartPosition(),log.currentSourceFile(),that);
    }
    
    // FIXME - needs review
    public void visitApply(JCMethodInvocation that) { 
        // This is an expression so we just use trExpr
        JCExpression now;
        JCExpression obj;
        MethodSymbol msym;
        Type.ForAll tfa = null;
        if (that.meth instanceof JCIdent) {
            now = (that.meth);
            if (  ((JCIdent)now).sym instanceof MethodSymbol) {

                msym = (MethodSymbol)((JCIdent)now).sym;
                if (msym.isStatic()) obj = null;
                else obj = currentThisId;

            } else { msym=null; obj = null; } // FIXME - this shouldn't really happen - there is a mis translation in creating makeTYPE expressions

        } else if (that.meth instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)that.meth;
            msym = (MethodSymbol)(fa.sym);
            if (msym == null || msym.isStatic()) obj = null; // msym is null for injected methods such as box and unbox
            else {
                obj = ( fa.selected );
                // FIXME - should do better than converting to String
                //if (!fa.selected.type.toString().endsWith("JMLTYPE")) checkForNull(obj,fa.pos,trueLiteral,null);
            }
//        } else if (that.token == null) {
//            super.visitApply(that);  // See testBox - this comes from the implicitConversion - should it be a JCMethodInvocation instead?
//            scan(that.typeargs);
//            scan(that.meth);
//            that.meth = result;
//            scanList(that.args);
//            result = that;
        } else {
            // FIXME - not implemented
            log.warning("esc.not.implemented","BasicBlocker.visitApply for " + that.meth.getClass());
            msym = null;
            obj = null;
            result = trueLiteral;
            return;
        }
        if (msym != null && msym.type instanceof Type.ForAll) tfa = (Type.ForAll)msym.type;

        // FIXME - what does this translation mean?
        //        ListBuffer<JCExpression> newtypeargs = new ListBuffer<JCExpression>();
        //        for (JCExpression arg: that.typeargs) {
        //            JCExpression n = trExpr(arg);
        //            newtypeargs.append(n);
        //        }

        ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
        for (JCExpression arg: that.args) {
            JCExpression n = (arg);
            newargs.append(n);
        }

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

        // FIXME - concerned that the position here is not after the
        // positions of all of the arguments
//        if (inSpecExpression) {
//            result = insertSpecMethodCall(that.pos,msym,obj,that.typeargs,newargs.toList());
//        } else {
//            result = insertMethodCall(that,msym,obj,that.getTypeArguments(),newargs.toList()); // typeargs ? FIXME
//        }

        //popTypeArgs();
        toLogicalForm.put(that,result);
        return;
    }

    // FIXME - review this
    //boolean extraEnv = false;
    public void visitJmlMethodInvocation(JmlMethodInvocation that) { 
        if (that.token == JmlToken.BSOLD || that.token == JmlToken.BSPRE) {
            VarMap savedMap = currentMap;
            try {
                if (that.args.size() == 1) {
                    currentMap = premap;
                    that.args.get(0).accept(this);
                } else {
                    JCIdent label = (JCIdent)that.args.get(1);
                    currentMap = labelmaps.get(label.name);
                    if (currentMap == null) {
                        // This should have already been reported
                        log.error(label.pos,"jml.unknown.label",label.name.toString());
                        // Use premap, just to keep going, though that may
                        // cause other errors
                        currentMap = premap;
                    }
                    that.args.get(0).accept(this);
                    that.args = com.sun.tools.javac.util.List.<JCExpression>of(that.args.get(0));
                }
                that.token = JmlToken.BSSAME; // A no-op // TODO - Review this
            } finally {
                currentMap = savedMap;
            }
        } else if (that.token == null) {
            //super.visitApply(that);  // See testBox - this comes from the implicitConversion - should it be a JCMethodInvocation instead?
            scan(that.typeargs);
            scan(that.meth);
            that.meth = result;
            scanList(that.args);
            result = that;
        } else {
            log.error(that.pos, "esc.internal.error", "Did not expect this kind of Jml node in BasicBlocker: " + that.token.internedName());
//            for (JCExpression e: that.args) {
//                e.accept(this);
//            }
        }
    }
    
    
    // FIXME - REVIEW and document
    protected List<Type> allTypeArgs(Type type) {
        ListBuffer<Type> list = new ListBuffer<Type>();
        allTypeArgs(list,type);
        return list.toList();
    }
    
    // FIXME - REVIEW and document
    protected void allTypeArgs(ListBuffer<Type> list, Type type) {
        if (type == Type.noType) return;
        allTypeArgs(list,type.getEnclosingType());
        list.appendList(type.getTypeArguments());
    }
    
//    // FIXME - REVIEW and document
//    // Generate a (translated) allocation predicate // FIXME - check this out and use it
//    protected void declareAllocated(VarSymbol vsym, int pos) {
//        JCIdent var = newIdentUse(vsym,pos);
//        declareAllocated(var,pos);
//    }
//    
//    // Generate a (translated) allocation predicate // FIXME - check this out and use it
//    protected void declareAllocated(JCExpression e, int pos) {
//        currentBlock.statements.add(comment(pos, e + " != null || " + e + " .alloc < " + allocSym));
//        JCExpression eee = new JmlBBFieldAccess(allocIdent,e);
//        eee.pos = pos;
//        eee.type = syms.intType;
//        eee = treeutils.makeBinary(pos,JCTree.LE,eee,newIdentUse(allocSym,pos));
//        eee = treeutils.makeBinary(pos,JCTree.OR,treeutils.makeEqObject(pos,e,nullLiteral),eee);
//        addAssume(pos,Label.SYN,eee,currentBlock.statements);
//    }
    
    // Generate a (translated) alloc comparison // FIXME - check this out and use it and docuiment
    protected JCExpression allocCompare(int pos, JCExpression e) {
        JCExpression eee = new JmlBBFieldAccess(allocIdent,e);
        eee.pos = pos;
        eee.type = syms.intType;
        eee = treeutils.makeBinary(pos,JCTree.LE,eee,newIdentUse(allocSym,pos));
        return eee;
    }

    // Generate a (translated) alloc selection // FIXME - check this out and use it and document
    protected JCExpression allocSelect(int pos, JCExpression e) {
        JCExpression eee = new JmlBBFieldAccess(allocIdent,e);
        eee.pos = pos;
        eee.type = syms.intType;
        return eee;
    }

    
    // FIXME - review and document
    protected void havocAssignables(int pos, JmlMethodInfo mi) {
////        * a store-ref
////        *  is a JCIdent, a JCSelect (potentially with a null field), or a JmlStoreRefArrayRange;
////        *  there may be more than one use of a JmlStoreRefArrayRange, e.g. a[2..3][4..5] or
////        *  a.f[4..5].g[6..7]
//        for (JmlMethodInfo.Entry entry: mi.assignables) {
//            JCExpression preCondition = trSpecExpr(entry.pre,log.currentSourceFile()); // FIXME - fix this
//            for (JCTree sr: entry.storerefs) {
//                if (sr == null) {
//                    log.error(pos,"jml.internal","Unexpected null store-ref in BasicBlocker.havocAssignables");
//                    continue;
//                }
//                int npos = pos*100000 + sr.pos;
//                JCExpression prevCondition = condition;
//                if (sr instanceof JCIdent) {
//                    JCIdent id = (JCIdent)sr;
//                    if (utils.isJMLStatic(id.sym)) {
//                        JCExpression oldid = trSpecExpr(id,log.currentSourceFile()); // FIXME
//                        JCIdent newid = newIdentIncarnation(id,npos); // new incarnation
//                        // newid == precondition ? newid : oldid
//                        JCExpression e = factory.at(pos).Conditional(preCondition,newid,oldid);
//                        e.type = newid.type;
//                        e = treeutils.makeBinary(pos,JCTree.EQ,newid,e);
//                        addAssume(pos,Label.HAVOC,e,currentBlock.statements);
//                    } else {
//                        // Same as for JCFieldAccess except that fa.selected is always 'this' (currentThisId)
//                        Type type = id.type;
//                        checkForNull(currentThisId,id.pos,preCondition,null);
//
//                                JCExpression indexlo = trSpecExpr(ar.lo,log.currentSourceFile()); // FIXME
//                                if (indexlo != null) checkArrayAccess(array,indexlo,sr.pos);
//                                else indexlo = zeroLiteral;
//                                
//                                JCExpression indexhi = trSpecExpr(ar.hi,log.currentSourceFile()); // FIXME
//                                boolean above = false;
//                                if (indexhi != null) checkArrayAccess(array,indexhi,sr.pos);
//                                else {
//                                    //indexhi = factory.at(sr.pos).Select(array,lengthSym);
//                                    indexhi = new JmlBBFieldAccess(lengthIdent,array);
//                                    indexhi.pos = sr.pos;
//                                    indexhi.type = syms.intType;
//                                    above = true;
//                                }
//                                
//                                
//                                JCIdent nid = newArrayIncarnation(sr.type,pos);
//                                JCExpression e = new JmlBBArrayHavoc(nid,arrayId,array,indexlo,indexhi,preCondition,above);
//
//                                addAssume(pos,Label.HAVOC,e,currentBlock.statements);
//
//                            }
//                        } else {
//                            // single element at the top level
//
//                            if (ns.size() > 0) {
//                                // FIXME - this is all wrong
//                                // But wild-cards within the ar.expression
//
////                                JCIdent label = newAuxIdent("havoclabel$"+npos,syms.intType,npos,false);
////                                labelmaps.put(label.name,currentMap.copy());
////                                JCExpression oldaccess = factory.at(npos).JmlMethodInvocation(JmlToken.BSOLD,access,label);
////
////                                JCArrayAccess newaccess = factory.at(access.pos).Indexed(access.indexed,access.index);
////                                newaccess.type = access.type;
////
////                                //                            JCIdent meth = newAuxIdent("arbitrary$",syms.intType,npos);
////                                //                            ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
////                                //                            for (Name n: ns) {
////                                //                                JCIdent id = factory.at(npos).Ident(n);
////                                //                                id.type = syms.intType;
////                                //                                args.append(id);
////                                //                            }
////                                //                            JCMethodInvocation app = factory.at(npos).Apply(null,meth,args.toList());
////                                //                            app.type = ar.type;
////
////                                JCConditional cond = factory.at(sr.pos).Conditional(
////                                        treeutils.makeBinary(JCTree.AND,entry.pre,accumRange,npos),newaccess,oldaccess);
////                                cond.type = access.type;
////
////                                JCExpression assign = treeutils.makeBinary(JCTree.EQ,newaccess,cond,npos);
////
////                                JmlQuantifiedExpr quant = factory.at(sr.pos).JmlQuantifiedExpr(JmlToken.BSFORALL,null,factory.Type(syms.intType),ns,fullRange,assign);
////
////                                JCIdent nid = newArrayIncarnation(sr.type,npos);                            
////                                JmlQuantifiedExpr trQuant = (JmlQuantifiedExpr)trSpecExpr(quant,log.currentSourceFile()); // FIXME
////                                // Now we fix up the expression
////                                JCExpression predicate = trQuant.predicate;
////                                JCBinary bin = (JCBinary)predicate;
////                                cond = (JCConditional)bin.rhs;
////                                JmlBBArrayAccess newaa = (JmlBBArrayAccess)cond.truepart;
////                                JmlBBArrayAccess oldaa = (JmlBBArrayAccess)cond.falsepart;
////
////                                JCExpression expr = new JmlBBArrayAssignment(nid,oldaa.arraysId,oldaa.indexed,oldaa.index,cond);
////                                expr.pos = sr.pos;
////                                expr.type = cond.type;
////
////                                trQuant.predicate = expr;
////
////                                addAssume(pos,Label.HAVOC,trQuant,currentBlock.statements,false);
//
//                            } else {
//                                // single element
//                                // a'[i] = preCondition ? a'[i] : a[i];
//
//                                array = trSpecExpr(array,log.currentSourceFile()); // FIXME
//                                checkForNull(array,sr.pos,trueLiteral,null);
//
//                                JCExpression index = trSpecExpr(ar.lo,log.currentSourceFile()); // FIXME
//                                checkArrayAccess(array,index,sr.pos);
//
//                                JCIdent arrayID = getArrayIdent(sr.type);
//                                JCExpression oldvalue = new JmlBBArrayAccess(arrayID,array,index,sr.pos,sr.type);
//
//                                JCIdent nid = newArrayIncarnation(sr.type,pos);
//                                JCExpression newvalue = new JmlBBArrayAccess(nid,array,index,sr.pos,sr.type);
//
//                                JCExpression condValue = factory.at(sr.pos).Conditional(preCondition,newvalue,oldvalue);
//                                condValue.type = oldvalue.type;
//
//                                JCExpression expr = new JmlBBArrayAssignment(nid,arrayID,array,index,condValue);
//                                expr.pos = sr.pos;
//                                expr.type = oldvalue.type;
//                                addAssume(pos,Label.HAVOC,expr,currentBlock.statements);
//                            }
//                        }
//                    } finally {
//                        condition = prevCondition;
//                    }
//                    
//                } else if (sr instanceof JmlStoreRefKeyword) {
//                    if (((JmlStoreRefKeyword)sr).token == JmlToken.BSNOTHING) {
//                        // OK
//                    } else {
//                        havocEverything(preCondition,sr.pos);
//                    }
//                } else if (sr instanceof JmlSingleton) { // FIXME - why do we get JmlSingleton as a store-ref?
//                    if (((JmlSingleton)sr).token == JmlToken.BSNOTHING) {
//                        // OK
//                    } else {
//                        havocEverything(preCondition,sr.pos);
//                    }
//                } else {
//                    log.error(sr.pos,"jml.internal","Unexpected kind of store-ref in BasicBlocker.havocAssignables: " + sr.getClass());
//                }
//            }
//        }
    }
    
    // FIXME - review and document
    private JCExpression fullRange;
    private JCExpression accumRange;
    protected JCExpression extractQuantifiers(JCExpression expr, ListBuffer<Name> ns) {
        if (expr instanceof JCIdent) {
            accumRange = trueLiteral;
            fullRange = trueLiteral;
            return expr;
        } else if (expr instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange a = (JmlStoreRefArrayRange)expr;
            JCExpression e = extractQuantifiers(a.expression,ns);
            JCExpression id;
            if (a.lo == a.hi && a.lo != null) {
                id = a.lo;
            } else {
                Name n = names.fromString("i"+(ns.size()+1));
                id = factory.at(expr.pos).Ident(n); // No symbol - FIXME ???
                id.type = syms.intType;
                ns.append(n);
                fullRange = treeutils.makeBinary(a.pos,JCTree.AND,fullRange,treeutils.makeBinary(a.pos,JCTree.LE,zeroLiteral,id));
                //JCExpression len = factory.at(a.pos).Select(a.expression,lengthSym);
                JCExpression len = new JmlBBFieldAccess(lengthIdent,a.expression);
                len.pos = a.pos;
                len.type = syms.intType;
                fullRange = treeutils.makeBinary(a.pos,JCTree.AND,fullRange,treeutils.makeBinary(a.pos,JCTree.LT,id,len));
                if (a.lo != null) accumRange = treeutils.makeBinary(a.lo.pos,JCTree.AND,accumRange,treeutils.makeBinary(a.lo.pos,JCTree.LE,a.lo,id));
                if (a.hi != null) accumRange = treeutils.makeBinary(a.hi.pos,JCTree.AND,accumRange,treeutils.makeBinary(a.hi.pos,JCTree.LE,id,a.hi));
            }
            e = factory.at(expr.pos).Indexed(e,id);
            e.type = expr.type;
            return e;
        } else if (expr instanceof JCFieldAccess) {
            JCFieldAccess a = (JCFieldAccess)expr;
            JCExpression e = extractQuantifiers(a.selected,ns);
            if (e == a.selected) return e;
            e = factory.at(expr.pos).Select(e,a.sym);
            e.type = a.type;
            return e;
        } else {
            return expr;
        }
    }
    
    // FIXME - review and document
    protected void havocField(VarSymbol vsym, JCExpression selected, int pos, int npos, Type type, JCExpression preCondition) {
        JCIdent oldid = newIdentUse(vsym,pos);
        JCFieldAccess oldaccess = new JmlBBFieldAccess(oldid,selected);
        oldaccess.pos = pos;
        oldaccess.type = type;

        JCIdent newid = newIdentIncarnation(oldid,npos);
        JCFieldAccess newaccess = new JmlBBFieldAccess(newid,selected);
        newaccess.pos = pos;
        newaccess.type = type;

        JCExpression right = factory.at(pos).Conditional(preCondition,newaccess,oldaccess);
        right.type = type;
        
        JCExpression expr = new JmlBBFieldAssignment(newid,oldid,selected,right);
        expr.pos = pos;
        expr.type = type;

        addAssume(pos,Label.HAVOC,expr,currentBlock.statements);

    }
    
    // FIXME - review and document
    protected void havoc(JCExpression storeref) {
        if (storeref instanceof JCIdent) {
            JCIdent id = newIdentIncarnation((JCIdent)storeref,storeref.pos);
            program.declarations.add(id);
            //} else if (e instanceof JCFieldAccess) {
            //} else if (e instanceof JCArrayAccess) {

        } else {
            // FIXME - havoc in loops
            log.noticeWriter.println("UNIMPLEMENTED HAVOC  " + storeref.getClass());
        }

    }
    

    
    // FIXME - review and document
    protected void havocEverything(JCExpression preCondition, int newpos) {
        // FIXME - if the precondition is true, then we do not need to add the 
        // assumptions - we just need to call newIdentIncarnation to make a new
        // value in the map.  This would shorten the VC.  How often is this
        // really the case?  Actually the preCondition does not need to be true,
        // it just needs to encompass all allowed cases.
        
        // FIXME - check on special variables - should they/are they havoced?
        // this
        // terminationVar
        // exceptionVar
        // resultVar
        // exception
        // others?
        
        // Change everything in the current map
        for (VarSymbol vsym : currentMap.keySet()) {
            if (vsym.owner == null || vsym.owner.type.tag != TypeTags.CLASS) {
                continue;
            }
            JCIdent oldid = newIdentUse(vsym,newpos);
            JCIdent newid = newIdentIncarnation(vsym,newpos);
            JCExpression e = factory.at(newpos).Conditional(preCondition,newid,oldid);
            e.type = vsym.type;
            e = treeutils.makeEquality(newpos,newid,e);
            addAssume(newpos,Label.HAVOC,e,currentBlock.statements);
        }
        currentMap.everythingIncarnation = newpos; // FIXME - this now applies to every not-yet-referenced variable, independent of the preCondition
    }

    /** This method is not called for top-level classes, since the BasicBlocker is invoked
     * directly for each method.
     */
    // FIXME - what about for anonymous classes or local classes or nested classes
    @Override
    public void visitClassDef(JCClassDecl that) {
        // Nested classes are found in JmlEsc.  We get to this point if there is a local
        // class declaration within method body.
        
        JmlEsc.instance(context).visitClassDef(that);
    }

    // FIXME - review this, and compare to the above
    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        // Nested classes are found in JmlEsc.  We get to this point if there is a local
        // class declaration within method body.
        
        JmlEsc.instance(context).visitClassDef(that);
    }


    
    // OK
    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) { 
        if (that.token == JmlToken.COMMENT) {
            currentBlock.statements.add(that);
        } else if (that.token == JmlToken.ASSUME || that.token == JmlToken.ASSERT) {
            scan(that.expression);
            currentBlock.statements.add(that);
        } else {
            log.error(that.pos,"esc.internal.error","Unknown token in BasicBlocker2.visitJmlStatementExpr: " + that.token.internedName());
        }
    }
    
    // OK
    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) { 
        for (JCExpression item : that.storerefs) {
            havoc(item);
        }
    }
    

    // We introduce the name 'assumeCheck$<int>$<label>' in order to make
    // it easy to identify the places where assumptions are being checked.
    /** Adds (translated) assertions/assumptions that do assumption feasibility checking 
     * for an assumption that is just added to the currentBlock
     * @param pos a positive integer different than that used for any other checkAssumption call;
     *    it should also be the textual location of the assumption being tested
     * @param label a Label giving the kind of assumption being tested (in order to
     *    better interpret the implications of the assumptino not being feasible)
     */
    
    // FIXME - REVIEW and document
    protected void checkAssumption(int pos, /*@ non_null*/ Label label, List<JCStatement> statements) {
        if (!insertAssumptionChecks) return;
        JCExpression e;
        JCIdent id;
        String n = ASSUME_CHECK_PREFIX + pos + "" + label.toString();
        if (useCountedAssumeCheck) {
            JCExpression count = treeutils.makeIntLiteral(pos,pos);
            e = treeutils.makeBinary(pos,JCTree.NE,assumeCheckCountVar,count);
            id = newAuxIdent(n,syms.booleanType,pos,false);
            //e = treeutils.makeBinary(pos,JCTree.EQ,id,e);
            // assume assumeCheck$<int>$<label> == <assumeCheckCountVar> != <int>
            // To do the coreId method, we need to put this in the definitions list
            // instead.  And it does not hurt anyway.
            //addAssume(pos,Label.ASSUME_CHECK,e); // adds to the currentBlock
            BasicProgram.Definition def = new BasicProgram.Definition(pos,id,e);
            newdefs.add(def);
            e = def.expr(context);
        } else {
            id = newAuxIdent(n,syms.booleanType,pos,false);
            e = id;
            if (assumeCheck == null) assumeCheck = e;
            else assumeCheck = treeutils.makeBinary(pos,JCTree.AND,e,assumeCheck);
        }
        program.assumptionsToCheck.add(new Entry(e,n));
        // an assert without tracking
        // assert assumeCheck$<int>$<label>
        addAssertNoTrack(Label.ASSUME_CHECK,id,statements,pos,null); // FIXME - need the position of the assume, I think
    }

    // FIXME - REVIEW and document
    protected void checkAssumption(int pos, /*@ non_null*/ Label label) {
        checkAssumption(pos,label,currentBlock.statements);
    }

    // FIXME - REVIEW and document
    public static class Entry implements Map.Entry<JCExpression,String> {
        JCExpression key;
        String value;
        public Entry(JCExpression e, String s) { key=e; value=s; }
        public JCExpression getKey() { return key; }
        public String getValue() { return value; }
        public String setValue(String value) { String v = value; this.value = value; return v;}
    }

    // Visit methods for Expressions for the most part just use the super class's
    // visit methods. These just call visitors on each subexpression.
    // Everything is transformed in place.
    // There are a few nodes that get special treatment:
    //  JCIdent - the name is overwritten with the single-assignment name (note that
    //     the name will be out of synch with the symbol)
    //  \old and \pre expressions - these need to find the correct scope and translate
    //     JCIdent nodes within their scopes using the correct single-assignment names
        
    
    public Map<JCTree,JCTree> toLogicalForm = new HashMap<JCTree,JCTree>();
//    public Map<JCTree,String> toValue = new HashMap<JCTree,String>();
    
    // OK
    @Override
    public void visitIdent(JCIdent that) {
        if (that.sym instanceof Symbol.VarSymbol){ 
            Symbol.VarSymbol vsym = (Symbol.VarSymbol)that.sym;
            that.name = getCurrentName(vsym);
            if (isDefined.add(that.name)) {
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("Added " + that.sym + " " + that.name);
                program.declarations.add(that);
            }
        } else if (that.sym == null) {
            // Temporary variables that are introduced by decomposing expressions do not have associated symbols
            // They are also only initialized once and only used locally, so we do not track them for DSA purposes
            // Just skip
        } else if (that.sym instanceof Symbol.ClassSymbol) {
            // Just skip
        } else if (that.sym instanceof Symbol.PackageSymbol) {
            // Just skip
        } else {
            log.error(that.pos,"jml.internal","THIS KIND OF IDENT IS NOT HANDLED: " + that + " " + that.sym.getClass());
        }
        result = that;
    }

    // OK
    public void visitLiteral(JCLiteral tree) {
        result = tree;
    }


    @Override
    public void visitSelect(JCFieldAccess that) {
        if (!(that.sym instanceof Symbol.VarSymbol)) return; // This is a qualified type name 
        if (that.sym.isStatic()) {
            that.name = getCurrentName((Symbol.VarSymbol)that.sym);
            JCIdent id = treeutils.makeIdent(that.pos,that.sym);
            id.name = that.name;
            if (isDefined.add(that.name)) {
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedF " + that.sym + " " + that.name);
                program.declarations.add(id);
            }
            result = id;
            
        } else {
            that.name = getCurrentName((Symbol.VarSymbol)that.sym);
            if (isDefined.add(that.name)) {
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedF " + that.sym + " " + that.name);
                JCIdent id = treeutils.makeIdent(that.pos,that.sym);
                id.name = that.name;
                program.declarations.add(id);
            }
            result = that;
        }
    }
    
    public void visitIndexed(JCArrayAccess that) {
        scan(that.indexed);
        JCExpression indexed = result;
        scan(that.index);
        JCExpression index = result;
        JCIdent arr = getArrayIdent(that.type);
        if (that instanceof JmlBBArrayAccess) {
            that.indexed = indexed;
            that.index = index;
            ((JmlBBArrayAccess)that).arraysId = arr;
            result = that;
        } else {
            log.warning(that,"jml.internal","Did not expect a JCArrayAccess node in BasicBlocker2.visitIndexed");
            result = new JmlBBArrayAccess(arr,indexed,index);
        }
    }


    
    
    // FIXME - review
    public void visitAssign(JCAssign that) {
        //scan(that.lhs);
        scan(that.rhs);
        JCExpression left = that.lhs;
        JCExpression right = that.rhs;
        result = doAssignment(that.type,left,right,that.pos,that);
        copyEndPosition(result,that);
    }
//    
    // FIXME - embedded assignments to array elements are not implemented; no warning either
    // FIXME - is all implicit casting handled
    // Note that only the right expression is translated.
    protected JCExpression doAssignment(Type restype, JCExpression left, JCExpression right, int pos, JCExpression statement) {
        if (left instanceof JCIdent) {
            JCIdent id = (JCIdent)left;
            JCIdent newid = newIdentIncarnation(id,left.pos);
            currentBlock.statements.add(treeutils.makeVarDef(newid.type, newid.name, id.sym.owner, pos));
            JCBinary expr = treeutils.makeEquality(pos,newid,right);
            copyEndPosition(expr,right);
            addAssume(TreeInfo.getStartPos(statement),Label.ASSIGNMENT,expr);
            return newid;
        } else if (left instanceof JCArrayAccess) {
            JCIdent arr = getArrayIdent(right.type);
            JCExpression ex = ((JCArrayAccess)left).indexed;
            JCExpression index = ((JCArrayAccess)left).index;
            JCIdent nid = newArrayIncarnation(right.type,left.pos);
            
            //JCExpression rhs = makeStore(ex,index,right);
            JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,((JCArrayAccess)left).index,right);
            expr.pos = pos;
            expr.type = restype;

            // FIXME - set line and source
//            JCBinary bin = treeutils.makeEquality(Position.NOPOS,nid,expr);
//            copyEndPosition(bin,expr);
            addAssume(TreeInfo.getStartPos(left),Label.ASSIGNMENT,expr,currentBlock.statements);
            //newIdentIncarnation(heapVar,pos);
            return right;
        } else if (left instanceof JCFieldAccess) {
            VarSymbol sym = (VarSymbol)selectorSym(left);
            if (sym.isStatic()) {
                JCIdent id = newIdentUse(sym,left.pos);
                JCIdent newid = newIdentIncarnation(id,left.pos);
                currentBlock.statements.add(treeutils.makeVarDef(newid.type, newid.name, id.sym.owner, pos));
                JCBinary expr = treeutils.makeEquality(pos,newid,right);
                copyEndPosition(expr,right);
                addAssume(TreeInfo.getStartPos(statement),Label.ASSIGNMENT,expr);
                return newid;
            } else {
                JCFieldAccess fa = (JCFieldAccess)left;
                JCIdent oldfield = newIdentUse((VarSymbol)fa.sym,pos);
                if (isDefined.add(oldfield.name)) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedFF " + oldfield.sym + " " + oldfield.name);
                    program.declarations.add(oldfield);
                }
                JCIdent newfield = newIdentIncarnation(oldfield,pos);
                if (isDefined.add(newfield.name)) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedFF " + newfield.sym + " " + newfield.name);
                    program.declarations.add(newfield);
                }
                JCExpression expr = new JmlBBFieldAssignment(newfield,oldfield,fa.selected,right);
                expr.pos = pos;
                expr.type = restype;

                // FIXME - set line and source
                addAssume(TreeInfo.getStartPos(left),Label.ASSIGNMENT,expr,currentBlock.statements);
                newIdentIncarnation(heapVar,pos);
            }
            return left;
        } else {
            log.error("jml.internal","Unexpected case in BasicBlocker.doAssignment: " + left.getClass() + " " + left);
            return null;
        }
    }
    
    protected Symbol selectorSym(JCTree tree) {
        if (tree instanceof JCIdent) return ((JCIdent)tree).sym;
        if (tree instanceof JCFieldAccess) return ((JCFieldAccess)tree).sym;
        log.error("jml.internal","Unexpected case in selectorSym: " + tree.getClass() + " " + tree);
        return null;
    }

    // OK -= except FIXME - review newIdentIncarnation
    public void visitVarDef(JCVariableDecl that) { 
        currentBlock.statements.add(comment(that));
        JCIdent lhs = newIdentIncarnation(that,that.getPreferredPosition());
        isDefined.add(lhs.name);
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("Added " + lhs.sym + " " + lhs.name);
        if (that.init != null) {
            // Create and store the new lhs incarnation before translating the
            // initializer because the initializer is in the scope of the newly
            // declared variable.  Actually if there is such a situation, it 
            // will likely generate an error about use of an uninitialized variable.
            scan(that.init);
            JCBinary expr = treeutils.makeBinary(that.pos,JCBinary.EQ,lhs,that.init);
            addAssume(that.getStartPosition(),Label.ASSIGNMENT,expr,currentBlock.statements);
        }
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        if (that.sym == null || that.sym.owner == null) {
            if (that.init != null) {
                scan(that.init);
                that.init = result;
            }
            // FIXME - clean up this
            if (that.init instanceof JCMethodInvocation) {
                //that.init = null; - we do want to pass functions on to the logic encoding
                currentBlock.statements.add(that);
            } else {
                currentBlock.statements.add(that);
            }
        } else if (that.init == null) {
            JCIdent lhs = newIdentIncarnation(that,that.getPreferredPosition());
            currentBlock.statements.add(treeutils.makeVarDef(that.type, lhs.name, that.sym.owner, that.pos));
        } else {
            JCIdent lhs = newIdentIncarnation(that,that.getPreferredPosition());
            scan(that.init);
            that.init = result;
            currentBlock.statements.add(treeutils.makeVarDef(that.type, lhs.name, that.sym.owner, that.init));
        }

        
//        if (that.init != null) scan(that.init);
//        if (that.sym != null) currentMap.put(that.sym, currentMap.everythingIncarnation, that.name);
//        currentBlock.statements.add(that);
//        currentBlock.statements.add(comment(that));
//        // FIXME - need to add various field specs tests
//        JCIdent vd = newIdentIncarnation(that,that.pos);
//        toLogicalForm.put(that,vd);
//        if (that.init != null) {
//            int p = that.init.pos;
//            boolean prevInSpecExpression = inSpecExpression;
//            try {
//                if (Utils.instance(context).isJML(that.mods)) inSpecExpression = true;
//                JCExpression ninit = (that.init);
//                addAssume(TreeInfo.getStartPos(that),Label.ASSIGNMENT,treeutils.makeEquality(p,vd,ninit));
//            } finally {
//                inSpecExpression = prevInSpecExpression;
//            }
//        }
    }
    

    // OK
    @Override
    public void visitSynchronized(JCSynchronized that)   { 
        super.visitSynchronized(that);
    }
    
    public void visitTypeIdent(JCPrimitiveTypeTree that) { notImpl(that); }
    public void visitTypeArray(JCArrayTypeTree that)     { notImpl(that); }
    public void visitTypeApply(JCTypeApply that)         { notImpl(that); }
    public void visitTypeParameter(JCTypeParameter that) { notImpl(that); }
    public void visitWildcard(JCWildcard that)           { notImpl(that); }
    public void visitTypeBoundKind(TypeBoundKind that)   { notImpl(that); }
    public void visitAnnotation(JCAnnotation that)       { notImpl(that); }
    public void visitModifiers(JCModifiers that)         { notImpl(that); }
    public void visitErroneous(JCErroneous that)         { notImpl(that); }
    public void visitLetExpr(LetExpr that)               { notImpl(that); }
    


    // FIXME _ implement
    @Override public void visitJmlSetComprehension(JmlSetComprehension that) { notImpl(that); }
    
    
    @Override public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) { notImpl(that); }
    @Override public void visitJmlChoose(JmlChoose that)                     { notImpl(that); }
    @Override public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that)                     { notImpl(that); }
    @Override public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that)                     { notImpl(that); }
    @Override public void visitJmlModelProgramStatement(JmlModelProgramStatement that)                     { notImpl(that); }
    @Override public void visitJmlGroupName(JmlGroupName that)               { notImpl(that); }
    @Override public void visitJmlTypeClauseIn(JmlTypeClauseIn that)         { notImpl(that); }
    @Override public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that)     { notImpl(that); }
    @Override public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that)     { notImpl(that); }
    @Override public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that)     { notImpl(that); }
    @Override public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) { notImpl(that); }
    @Override public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) { notImpl(that); }
    @Override public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) { notImpl(that); }
    @Override public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) { notImpl(that); }
    @Override public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) { notImpl(that); }
    @Override public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) { notImpl(that); }
    @Override public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) { notImpl(that); }
    @Override public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) { notImpl(that); }
    @Override public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) { notImpl(that); }
    @Override public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) { notImpl(that); }
    @Override public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) { notImpl(that); }
    @Override public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) { notImpl(that); }
    @Override public void visitJmlSpecificationCase(JmlSpecificationCase that){ notImpl(that); }
    @Override public void visitJmlMethodSpecs(JmlMethodSpecs that)           { notImpl(that); }
    @Override public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that){ notImpl(that); }
    @Override public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that)   { notImpl(that); }
    @Override public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that){ notImpl(that); }

    // These should all be translated away prior to calling the basic blocker
    @Override public void visitJmlBinary(JmlBinary that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlLblExpression(JmlLblExpression that) { shouldNotBeCalled(that); }    
    @Override public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) { shouldNotBeCalled(that); }

    // These do not need to be implemented
    @Override public void visitTopLevel(JCCompilationUnit that)    { shouldNotBeCalled(that); }
    @Override public void visitImport(JCImport that)               { shouldNotBeCalled(that); }
    @Override public void visitJmlCompilationUnit(JmlCompilationUnit that)   { shouldNotBeCalled(that); }
    @Override public void visitJmlImport(JmlImport that)                     { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodDecl(JmlMethodDecl that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlStatement(JmlStatement that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementSpec(JmlStatementSpec that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementDecls(JmlStatementDecls that) { shouldNotBeCalled(that); }
    @Override public void visitMethodDef(JCMethodDecl that)        { shouldNotBeCalled(that); }
    

    // OK
    @Override public void visitBinary(JCBinary that) {
        scan(that.lhs);
        that.lhs = result;
        scan(that.rhs);
        that.rhs = result;
        result = that; 
    }
    
    // OK
    @Override public void visitUnary(JCUnary that) { 
        scan(that.arg);
        that.arg = result;
        result = that; 
    }
    
    // OK
    @Override public void visitParens(JCParens that) { 
        scan(that.expr);
        that.expr = result;
        result = that; 
    }
    
    // OK
    @Override public void visitConditional(JCConditional that) { 
        scan(that.cond);
        that.cond = result;
        scan(that.truepart);
        that.truepart = result;
        scan(that.falsepart);
        that.falsepart = result;
        result = that; 
    }

    // OK // FIXME - does this expression type appear?
    @Override public void visitTypeTest(JCInstanceOf that) { 
        scan(that.expr);
        scan(that.clazz); // FIXME - do we scan type names?
        result = that; 
    }

    // OK // FIXME - does this expression type appear? in REF case it should be a noop
    @Override public void visitTypeCast(JCTypeCast that) { 
        scan(that.clazz); // FIXME - do we scan type names?
        scan(that.expr);
        result = that; 
    }

// Do not need to override these methods
//  @Override public void visitSkip(JCSkip that) { super.visitSkip(that); }
        
    public void visitJmlStatementLoop(JmlStatementLoop that) { 
        shouldNotBeCalled(that); // These are the specs for loops - they are handled in the loop visitors
    }
    
    // FIXME - what about Indexed, TypeCast, TypeTest, AssignOp, NewClass, NewArray

    /** This class is a tree walker that finds any references to classes in the
     * tree being walked: types of anything, explicit type literals
     * 
     * @author David Cok
     *
     */
//    public static class ClassFinder extends JmlTreeScanner {
//        
//        private Set<Type> types;
//        
//        public ClassFinder() {}
//        
//        public static Set<Type> findS(List<? extends JCTree> that, Set<Type> v) {
//            ClassFinder vf = new ClassFinder();
//            return vf.find(that,v);
//        }
//        
//        public static Set<Type> findS(JCTree that, Set<Type> v) {
//            ClassFinder vf = new ClassFinder();
//            return vf.find(that,v);
//        }
//        
//        public Set<Type> find(List<? extends JCTree> that, Set<Type> v) {
//            if (v == null) types = new HashSet<Type>();
//            else types = v;
//            for (JCTree t: that) t.accept(this);
//            return types;
//        }
//        
//        public Set<Type> find(JCTree that, Set<Type> v) {
//            if (v == null) types = new HashSet<Type>();
//            else types = v;
//            that.accept(this);
//            return types;
//        }
//        
//        // visitAnnotation  - FIXME
//
//        // visitApply - expression: just scan the component expressions
//        // visitAssert - statement: just scan the component expressions
//        // visitAssign - no new types - just scan the component expressions
//        // visitAssignOp - no new types - just scan the component expressions
//        // visitBinary - only primitive types
//        // visitBlock - statement: just scan the component expressions
//        // visitBreak - statement: just scan the component expressions
//        // visitCase - statement: just scan the component expressions
//        // visitCatch - statement: just scan the component expressions - FIXME - make sure to get the declaration
//        // visitClassDef - FIXME ???
//        // visitConditional - no new types - just scan the component expressions
//        // visitContinue - statement: just scan the component expressions
//        // visitDoLoop - statement: just scan the component expressions
//        // visitErroneous - statement: just scan the component expressions
//        // visitExec - statement: just scan the component expressions
//        // visitForEachLoop - statement: just scan the component expressions - FIXME - implied iterator?
//        // visitForLoop - statement: just scan the component expressions
//
//        public void visitIdent(JCIdent that) {
//            if (!that.type.isPrimitive()) types.add(that.type);
//            super.visitIdent(that);
//        }
//        
//        // visitIf - statement: just scan the component expressions
//        // visitImport - statement: just scan the component expressions
//        // visitIndexed - FIXME
//        // visitLabelled - statement: just scan the component expressions
//        // visitLetExpr - FIXME
//        // visitLiteral - FIXME
//        // visitMethodDef - FIXME
//        // visitModifiers - no new types
//        // visitNewArray - FIXME
//
//        public void visitNewClass(JCNewClass that) {
//            types.add(that.type);
//        }
//        
//        // visitParens - no new types - just scan the component expressions
//        // visitReturn - statement: just scan the component expressions
//        // visitSelect - FIXME
//        // visitSkip - statement: just scan the component expressions
//        // visitSwitch - statement: just scan the component expressions (FIXME _ might be an Enum)
//        // visitSynchronized - statement: just scan the component expressions
//        // visitThrow - statement: just scan the component expressions
//        // visitTopLevel - statement: just scan the component expressions
//        // visitTree
//        // visitTry - statement: just scan the component expressions
//        // visitTypeApply - FIXME ??
//        // visitTypeArray - FIXME ??
//        // visitTypeBoundKind - FIXME ??
//        // visitTypeCast - FIXME ??
//
//        public void visitTypeIdent(JCPrimitiveTypeTree that) {
//            types.add(that.type);
//            super.visitTypeIdent(that);
//        }
//        
//        // visitTypeParameter - FIXME ??
//        // visitTypeTest (instanceof) - scans the expression and the type
//        // visitUnary - only primitive types
//        // visitVarDef - FIXME ??
//        // visitWhileLoop - statement: just scan the component expressions
//        // visitWildcard - FIXME ??
//        
//        // visitJmlBBArrayAccess - FIXME ?
//        // visitJmlBBArrayAssignment - FIXME ?
//        // visitJmlBBFieldAccess - FIXME ?
//        // visitJmlBBFieldAssignment - FIXME ?
//        // visitJmlBinary - no new types - FIXME - subtype?
//        // visitJmlClassDecl - FIXME - do specs also
//        // visitJmlCompilationUnit - just scan internal components
//        // visitJmlConstraintMethodSig - FIXME ?
//        // visitJmlDoWhileLoop - FIXME - scan specs
//        // visitJmlEnhancedForLoop - FIXME - scan specs
//        // visitJmlForLoop - FIXME - scan specs
//        // visitJmlGroupName - FIXME??
//        // visitJmlImport - no types
//        // visitLblExpression - no new types - scan component expressions
//        // visitJmlMethodClause... - scan all component expressions - FIXME : watch Decls, Signals, SigOnly
//        // visitJmlMethodDecl - FIXME?? - do specs also
//        // visitJmlMethodSpecs - FIXME??
//        // visitJmlPrimitiveTypeTree - FIXME??
//        // visitJmlQuantifiedExpr - FIXME??
//        // visitJmlRefines - FIXME??
//        // visitJmlSetComprehension - FIXME??
//        // visitJmlSingleton - FIXME??
//        // visitJmlSpecificationCase - FIXME?? - FIXME??
//        // visitJmlStatement - FIXME??
//        // visitJmlStatementDecls - FIXME??
//        // visitJmlStatementExpr - FIXME??
//        // visitJmlStatementLoop - FIXME??
//        // visitJmlStatementSpec - FIXME??
//        // visitJmlStoreRefArrayRange - FIXME??
//        // visitJmlStoreRefKeyword - FIXME??
//        // visitJmlStoreRefListExpression - FIXME??
//        // visitJmlTypeClause... - scan all components - FIXME - is there more to do?
//        // visitJmlVariableDecl - FIXME??
//        // visitJmlWhileLoop - FIXME - be sure to scan specs
//        
//        // FIXME - some things that can probably always be counted on: Object, String, Class
//        // FIXME - closure of super types and super interfaces 
//    } 
    

//    /** A Map that caches class info for a given class symbol */
//    @NonNull protected Map<Symbol,JmlClassInfo> classInfoMap = new HashMap<Symbol,JmlClassInfo>();
//
//    /** Returns the jmlClassInfo structure for a class, computing and caching 
//     * it if necessary.
//     * @param cls the declaration whose info is desired
//     * @return the corresponding JmlClassInfo structure; may be null if the
//     *   argument has no associated symbol
//     */
//    //@ modifies (* contents of the classInfoMap *);
//    //@ ensures cls.sym != null <==> \result != null;
//    @Nullable JmlClassInfo getClassInfo(@NonNull JCClassDecl cls) {
//        JmlClassInfo mi = classInfoMap.get(cls.sym);
//        if (mi == null) {
//            mi = computeClassInfo(cls.sym);
//            classInfoMap.put(cls.sym,mi);
//        }
//        return mi;
//    }
//    
//    /** Returns the JmlClassInfo structure for the given Class Symbol,
//     * computing and caching it if necessary
//     * @param sym the Symbol for the class whose JmlClassInfo is wanted
//     * @return the corresponding JmlClassInfo structure, null if sym is null
//     */
//    @Nullable JmlClassInfo getClassInfo(@NonNull Symbol sym) {
//        if (sym == null) return null;
//        ClassSymbol csym = (ClassSymbol)sym;
//        JmlClassInfo mi = classInfoMap.get(sym);
//        if (mi == null) {
//            mi = computeClassInfo(csym);
//            classInfoMap.put(sym,mi);
//        }
//        return mi;
//    }
//    
//    // FIXME - what about nested classes ($-separated ?)
//    /** Returns the JmlClassInfo structure for the given dot-separated,
//     * fully-qualified class name,
//     * computing and caching it if necessary
//     * @param qualifiedName the fully-qualified name of the class
//     * @return the corresponding JmlClassInfo structure, null if sym is null
//     */
//    @Nullable JmlClassInfo getClassInfo(@NonNull String qualifiedName) {
//        Name n = Names.instance(context).fromString(qualifiedName);
//        Symbol sym = Symtab.instance(context).classes.get(n);
//        return getClassInfo(sym);
//    }
    
//    // TODO - review this
//    /** Computes the class information for a given class declaration.
//     * @param csym the ClassSymbol for which to get JmlClassInfo
//     * @return the corresponding JmlClassInfo
//     */
//    protected @Nullable JmlClassInfo computeClassInfo(@NonNull ClassSymbol csym) {
//        TypeSpecs typeSpecs = specs.get(csym);
//        if (typeSpecs == null) {  
//            if (csym == syms.arrayClass) {
//                // This one is special
//                JmlClassInfo classInfo = new JmlClassInfo(null);
//                classInfo.typeSpecs = new TypeSpecs();
//                classInfo.csym = csym;
//                
//                Type type = syms.objectType;
//                classInfo.superclassInfo = getClassInfo(type.tsym);
//
//                return classInfo;
//            }
//            // This should not happen - every class referenced is loaded, 
//            // even binary files.  If there is no source and no specs, then
//            // the typespecs will have essentially null
//            // innards, but the object should be there.
//            // If this point is reached, some class somehow escaped being loaded.
//            log.error("jml.internal","No typespecs for class " + csym);
//            return null;
//        }
//        JCClassDecl tree = typeSpecs.decl;
//            // 'tree' may be null if there is a binary class with no specs.
//            // So we have to be sure there are default specs, which for
//            // a class is essentially empty.
//
//        JmlClassInfo classInfo = new JmlClassInfo(tree);
//        classInfo.typeSpecs = typeSpecs;
//        classInfo.csym = csym;
//        
//        Type type = csym.getSuperclass();
//        classInfo.superclassInfo = (csym == syms.objectType.tsym || csym.isInterface() ) ? null : getClassInfo(type.tsym);
//
//        // Divide up the various type specification clauses into the various types
//        ListBuffer<JmlTypeClauseRepresents> represents = new ListBuffer<JmlTypeClauseRepresents>();
//        ListBuffer<JCVariableDecl> modelFields = new ListBuffer<JCVariableDecl>();
//
//        for (JmlTypeClause c: typeSpecs.clauses) {
//            boolean isStatic = c.modifiers != null && (c.modifiers.flags & Flags.STATIC) != 0;
//            if (c instanceof JmlTypeClauseDecl) {
//                JCTree tt = ((JmlTypeClauseDecl)c).decl;
//                if (tt instanceof JCVariableDecl && ((JmlAttr)Attr.instance(context)).isModel(((JCVariableDecl)tt).mods)) {
//                    // model field - find represents or make into abstract method
//                    modelFields.append((JCVariableDecl)tt);
//                } else {
//                    // ghost fields, model methods, model classes are used as is
//                    //newlist.append(tt);
//                }
//            } else {
//                JmlToken token = c.token;
//                if (token == JmlToken.INVARIANT) {
//                    JmlTypeClauseExpr copy = (JmlTypeClauseExpr)c.clone();
//                    copy.expression = treetrans.translate(copy.expression);
//                    if (isStatic) classInfo.staticinvariants.add(copy);
//                    else          classInfo.invariants.add(copy);
//                } else if (token == JmlToken.REPRESENTS) {
//                    JmlTypeClauseRepresents r = (JmlTypeClauseRepresents)c;
//                    represents.append(r);
//                } else if (token == JmlToken.CONSTRAINT) {
//                    if (isStatic) classInfo.staticconstraints.add((JmlTypeClauseConstraint)c);
//                    else          classInfo.constraints.add((JmlTypeClauseConstraint)c);
//                } else if (token == JmlToken.INITIALLY) {
//                    classInfo.initiallys.add((JmlTypeClauseExpr)c);
//                } else if (token == JmlToken.AXIOM) {
//                    JmlTypeClauseExpr copy = (JmlTypeClauseExpr)c.clone();
//                    copy.expression = treetrans.translate(copy.expression);
//                    classInfo.axioms.add(copy);
//                } else {
//                    log.warning("esc.not.implemented","JmlEsc does not yet implement (and ignores) " + token.internedName());
//                    // FIXME - readable if, writable if, monitors for, in, maps, initializer, static_initializer, (model/ghost declaration?)
//                }
//            }
//        }
//        return classInfo;
//    }

//    // FIXME - Review
//    /** This class converts a counterexample into more readable information */
//    public static class Tracer extends JmlTreeScanner {
//        
//        /** The compilation context */
//        @NonNull Context context;
//        
//        /** The counterexample information */
//        @NonNull ICounterexample ce;
//        
//        /** The log for output */
//        @NonNull Log log;
//        
//        @NonNull Writer w;
//        
//        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
//        private static class ReturnException extends RuntimeException {
//            private static final long serialVersionUID = -3475328526478936978L;}
//        
//        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
//        private static class ExException extends RuntimeException {
//            private static final long serialVersionUID = -5610207201211221750L;}
//        
//        /** Outputs the counterexample information in more readable form
//         * @param context the compilation context
//         * @param decl the method declaration 
//         * @param s the counterexample information to translate
//         */
//        public String trace(@NonNull Context context, @NonNull JCMethodDecl decl, @NonNull ICounterexample s) {
//            Tracer t = new Tracer(context,s);
//            try {
//                try {
//                    decl.accept(t);
//                } catch (ReturnException e) {
//                    // ignore
//                } catch (ExException e) {
//                    // ignore
//                } catch (RuntimeException e) {
//                    t.w.append("FAILED : " + e + "\n");
//                }
//                t.w.append("END\n");
//                return t.w.toString();
//            } catch (IOException e) {
//                log.noticeWriter.println("IOException");
//                return "";
//            }
//        }
//
//        /** Translates the given position information into source, line and column information 
//         * @param pos the position information to translate
//         * @return A String containing human-readable source location information
//         */
//        public String getPosition(int pos) { // TODO - check about the second argument of getColumnNumber
//            return log.currentSourceFile().getName() + ":" + log.currentSource().getLineNumber(pos) + " (col " + log.currentSource().getColumnNumber(pos,false) + "): ";
//        }
//        
//        /** The constructor for this class
//         * @param context the compilation context
//         * @param s the counterexample information
//         */
//        protected Tracer(@NonNull Context context, @NonNull ICounterexample s) {
//            this.context = context;
//            ce = s;
//            log = Log.instance(context);
//            w = new StringWriter();
//        }
//        
//        // CAUTION: The Strings in use in these visit methods correspond to the
//        // encoding used in the BasicBlocker methods.  The BasicBlocker encodes
//        // variables using combinations of variable name, declaration position,
//        // and incarnation position.  These are reflected in the counterexample 
//        // information and we need to match that as we interpret the counterexample
//        // information in these methods.
//        
//        // FIXME - this implementation needs fleshing out
//        
//        public void visitMethodDef(JCMethodDecl that) {
//            try {
//                w.append("START METHOD " + that.sym + "\n");
//                for (JCVariableDecl param: that.params) {
//                    String s = param.name + "$" + param.pos + "$0";
//                    String value = ce.get(s);
//                    w.append("Parameter value: " + param.name + " = " + (value == null ? "<unused>" : value) + "\n");
//                }
//            } catch (IOException e) {
//                // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
//            super.visitMethodDef(that);
//        }
//        
//        public void visitIf(JCIf that) {
//            String s = "branchCondition_" + that.pos + "_" + 0;
//            String value = ce.get(s);
//            try {
//                if (value == null) w.append(getPosition(that.pos) + "!!!  Could not find value for branch ("+s+")\n");
//                else {
//                    w.append(getPosition(that.pos) + "Branch condition value: " + value + "\n");
//                    if (value.equals("true")) {
//                        if (that.thenpart != null) that.thenpart.accept(this);
//                    } else if (value.equals("false")) {
//                        if (that.elsepart != null) that.elsepart.accept(this);
//                    } else {
//                        w.append("!!! Unknown value: " + value + "\n");
//                    }
//                }
//            } catch (IOException e) {
//                // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
//        }
//        
//        public void visitAssign(JCAssign that) {
//            try {
//                if (that.lhs instanceof JCIdent) {
//                    JCIdent id = (JCIdent)that.lhs;
//                    String s = id.name + "$" + ((VarSymbol)id.sym).pos + "$" + that.pos;
//                    String value = ce.get(s);
//                    if (value == null) w.append(getPosition(that.pos) + "!!!  Could not find value for variable ("+s+")\n");
//                    else w.append(getPosition(that.pos) + "Assignment: " + id.name + " = " + value + "\n");
//                }
//            } catch (IOException e) {
//                // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
//        }
//        
//        public void visitTry(JCTry that) {
//            try {
//                try {
//                    that.body.accept(this);
//                } catch (ReturnException e) {
//                    // do the finally block
//                    if (that.finalizer != null) {
//                        w.append(getPosition(that.finalizer.pos) + "Executing finally block\n");
//                        that.finalizer.accept(this);
//                    }
//                    throw e;
//                } catch (ExException e) {
//                    // FIXME
//                }
//            } catch (IOException e) {
//                // FIXME
//            }
//        }
//        
//        public void visitReturn(JCReturn that) {
//            String s = "RESULT_";  // FIXME - should replace with defined constnat, but this is missing the final $
//            String value = ce.get(s);
//            try {
//                if (that.expr != null) {
//                    if (value == null) w.append(getPosition(that.pos) + "!!!  Could not find return value ("+s+")\n");
//                    else w.append(getPosition(that.pos) + "Executed return: value = " + value + "\n");
//                } else {
//                    w.append(getPosition(that.pos) + "Executed return\n");
//                }
//            } catch (IOException e) {
//                // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
//            throw new ReturnException();
//        }
//    } 
    

//    /** A runtime exception used to jump up to a finally block in the visitor calling stack */
//    private static class ReturnException extends RuntimeException {
//        private static final long serialVersionUID = -3475328526478936978L;}
//
//    /** A runtime exception used to jump up to a finally block in the visitor calling stack */
//    private static class ExException extends RuntimeException {
//        private static final long serialVersionUID = -5610207201211221750L;}
    
    /** Outputs the counterexample information in more readable form
     * @param context the compilation context
     * @param program the program whose counterexample information is to be printed 
     * @param ce the counterexample information to translate
     * @param prover the prover from which the counterexample information came
     */
//    public static String trace(@NonNull Context context, @NonNull BasicProgram program, @NonNull ICounterexample ce, IProver prover) {
//        String s = null;
//        try {
//            s = (new TracerBB(context)).trace(program,ce,prover);
//        } catch (ReturnException e) {
//            // ignore
//        } catch (ExException e) {
//            // ignore
//        } catch (IOException e) {
//            log.noticeWriter.println("ABORTED");
//        } catch (RuntimeException e) {
//            log.noticeWriter.println("ABORTED");
//            throw e;
//        } 
//        return s;
//    }
//    
    
//    // FIXME - Review
//    /** This class converts a counterexample into more readable information;
//     * it uses the basic program form rather than using the Java AST. */
//    public static class TracerBB extends JmlTreeScanner {
//        
//        /** The counterexample information */
//        ICounterexample ce;
//        
//        boolean showSubexpressions;
//        
//        /** The log for output */
//        @NonNull Log log;
//        
//        /** The program being traced */
//        BasicProgram program;
//        
//        /** The compilation context */
//        @NonNull Context context;
//        
//        Map<String,String> values;
//        
//        Writer w;
//        
//        /** The prover that was used to create the counterexample */
//        IProver prover;
//        
//        Symtab syms;
//        
//        List<IProverResult.Span> path = null;
//        
//        /** Translates the given position information into source, line and column information 
//         * @param pos the position information to translate
//         * @return A String containing human-readable source location information
//         */
//        public String getPosition(int pos) {  // TODO - check about the second argument of getColumnNumber
//            return log.currentSourceFile().getName() + ":" + log.currentSource().getLineNumber(pos) + " (col " + log.currentSource().getColumnNumber(pos,false) + "): \t";
//        }
//        
//        /** The constructor for this class
//         * @param context the compilation context
//         */
//        public TracerBB(@NonNull Context context) {
//            this.context = context;
//            log = Log.instance(context);
//            syms = Symtab.instance(context);
//            w = new StringWriter();
//            showSubexpressions = JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS) || true;
//        }
//        
//        // FIXME - DOCUMENT
//        public static String trace(@NonNull Context context, @NonNull BasicProgram program, ICounterexample ce, IProver prover) {
//            try {
//                return new TracerBB(context).trace(program,ce,prover);
//            } catch (IOException e) {
//                return "<IOException: " + e + ">";
//            }
//        }
//        
//        //@ ensures this.program != null && this.ce != null;
//        //@ ensures this.program != program && this.ce != ce;
//        public String trace(@NonNull BasicProgram program, ICounterexample ce, IProver prover) throws IOException {
//            this.ce = ce;
//            this.program = program;
//            this.prover = prover;
//            w = new StringWriter();
//            w.append("COUNTEREXAMPLE TRACE \n\n");
//            values = ce.getMap();
//            this.subexp = new Subexpressor(context,prover,values,w);
//            this.path = new LinkedList<IProverResult.Span>();
//            
//            for (JCVariableDecl vd: program.methodDecl.params) {
//                String n = vd.name + "$" + vd.pos + "$0";
//                String value = ce.get(n);
//                w.append(getPosition(vd.pos) + "Parameter \t" +  n + " \t= " + (value==null?"?":value) + "\n");
//            }
//            
//            if (showSubexpressions) prover.reassertCounterexample(ce);
////            for (Map.Entry<JCTree,String> entry: ((Counterexample)ce).mapv.entrySet()) { // FIXME - hacked to get at map - fix this
////              values.put(entry.getKey(),entry.getValue());
////            }
//            BasicBlock block = program.startBlock();
//            outer: while (traceBlockStatements(block,ce)) {
//                for (BasicBlock next: block.succeeding()) {
//                    String s = next.id().toString();
//                    String value = ce.get(s);
//                    if (value.equals("false")) {
//                        block = next;
//                        continue outer;
//                    }
//                }
//                break;
//            }
//            w.append("END\n");
//            ce.putMap(values);
//            ce.putPath(path);
//            return w.toString();
//        }
//        
//
//        
//        // CAUTION: The Strings in use in these visit methods correspond to the
//        // encoding used in the BasicBlocker methods.  The BasicBlocker encodes
//        // variables using combinations of variable name, declaration position,
//        // and incarnation position.  These are reflected in the counterexample 
//        // information and we need to match that as we interpret the counterexample
//        // information in these methods.
//        
//        // FIXME - Review
//        protected boolean traceBlockStatements(BasicBlock b, ICounterexample ce) throws IOException {
//            w.append(" [ block " + b.id() + " ]\n");
//            boolean sawFalseAssert = false;
//            String pos=null, lastpos;
//            for (JCStatement statement: b.statements) {
//                if (!(statement instanceof JmlStatementExpr)) {
//                    log.error(statement.pos,"esc.internal.error","Incorrect statement type in traceBlockStatements: " + statement.getClass());
//                    continue;
//                }
//                JmlStatementExpr s = (JmlStatementExpr)statement;
//                JCExpression expr = s.expression;
//                if (expr instanceof JCIdent) {
//                    Name nm = ((JCIdent)expr).name;
//                    if (nm.toString().startsWith(BasicBlocker.ASSUMPTION_PREFIX)) {
//                        for (BasicProgram.Definition def : program.definitions) {
//                            if (def.id.name.equals(nm)) {
//                                expr = def.value;
//                                break;
//                            }
//                        }
////                        for (JCExpression e : program.pdefinitions) {
////                            if (e instanceof JCBinary && ((JCBinary)e).lhs instanceof JCIdent && ((JCIdent)((JCBinary)e).lhs).name.equals(nm)) {
////                                expr = ((JCBinary)e).rhs;
////                            }
////                        }
//                    }
//                }
//                lastpos = pos;
//                pos = getPosition(s.pos);
//                Label label = s.label;
//                if (label == Label.ASSUME_CHECK) {
//                    // skip
//                } else if (s.token == JmlToken.ASSUME) {
//                    if (label == Label.ASSIGNMENT) {
//                        // FIXME - array, field assignments
//                        if (expr instanceof JCBinary) {
//                            JCBinary bin = (JCBinary)expr;
//                            if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                            Name n = ((JCIdent)bin.lhs).name;
//                            String v = value((JCIdent)bin.lhs);
//                            w.append(pos + "Assignment " + n + " = " + v
//                                    + "  [" + bin.rhs + "]\n");
//                            record(bin.lhs,v);
//                            showSubexpressions(bin.rhs);
//
//                        } else if (expr instanceof JmlBBArrayAssignment){
//                            JmlBBArrayAssignment asg = (JmlBBArrayAssignment)expr;
//                            JCExpression array = asg.args.get(2);
//                            JCExpression index = asg.args.get(3);
//                            JCExpression value = asg.args.get(4);
//                            
//                            List<String> results = subexp.getValues(array,index,value);
//                            if (results != null) {
//                            w.append(pos + "ArrayAssignment " 
//                                    + results.get(0) + "[" + results.get(1) + "] = " + results.get(2)
//                                    + "  [ (" + array + ")[" + index + "] = " + value + " ]\n");
//                            }
//                            showSubexpressions(array);
//                            showSubexpressions(index);
//                            showSubexpressions(value);
//                        } else if (expr instanceof JmlBBFieldAssignment){
//                            JmlBBFieldAssignment asg = (JmlBBFieldAssignment)expr;
//                            JCExpression obj = asg.args.get(2);
//                            JCIdent field = (JCIdent)asg.args.get(0);
//                            JCExpression value = asg.args.get(3);
//                            
//                            List<String> results = subexp.getValues(obj,value);
//                            w.append(pos + "FieldAssignment " 
//                                    + results.get(0) + "." + field + " = " + results.get(1)
//                                    + "  [ (" + obj + ")." + field + " = " + value + " ]\n");
//                            showSubexpressions(obj);
//                            showSubexpressions(value);
//
//                        } else {
//                            failure(label,expr);
//                        }
//                    } else if (label == Label.ARGUMENT) {
//                        // Called methods and new object (called constructor) calls
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        Name n = ((JCIdent)bin.lhs).name;
//                        String v = value((JCIdent)bin.lhs);
//                        w.append(pos + "ArgumentEvaluation " + n + " = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(bin.lhs,v);
//                        showSubexpressions(bin.rhs);
//
//                    } else if (label == Label.RECEIVER) {
//                        // Called methods and new object (called constructor) calls
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        Name n = ((JCIdent)bin.lhs).name;
//                        String v = value((JCIdent)bin.lhs);
//                        w.append(pos + "ReceiverEvaluation " + n + " = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(bin.lhs,v);
//                        showSubexpressions(bin.rhs);
//                    
//                    } else if (label == Label.BRANCHC) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        String v = value((JCIdent)bin.lhs);
//                        w.append(pos + label + " = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(bin.lhs,v);
//                        showSubexpressions(bin.rhs);
//                        
//                    } else if (label == Label.LBL) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        JCIdent id = (JCIdent)bin.lhs;
//                        String lbl = id.toString();
//                        int k = lbl.lastIndexOf('$');
//                        lbl = lbl.substring(k+1);
//                        String v = value(id);
//                        w.append(pos + label + ": " + lbl + " = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(id,v);
//                        showSubexpressions(bin.rhs);
//                        
//                    } else if (label == Label.SWITCH_VALUE) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        String v = value((JCIdent)bin.lhs);
//                        w.append(pos + "switch value = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(bin.lhs,v);
//                        showSubexpressions(bin.rhs);
//                        
//                    } else if (label == Label.SYN) {  // FIXME - rename the SYN types that are wanted
//                        if (expr instanceof JCBinary) {
//                            JCExpression lhs = ((JCBinary)expr).lhs;
//                            if (lhs instanceof JCIdent) {
//                                String value = ce.get(((JCIdent)lhs).name.toString());
//                                w.append(pos + "Syn " + lhs + " = " + value + "\n");
//                            } else {
//                                w.append(pos + "Syn " + expr + "\n");
//                            }
//                        } else {
//                            w.append(pos + "Syn " + expr + "\n");
//                        }
//                    } else if (label == Label.EXPLICIT_ASSUME) {
//                        if (expr instanceof JCIdent) {
//                            // This will happen for tracked assumptions
//                            Name n = ((JCIdent)expr).name;
//                            String value = ce.get(n.toString());
//                            w.append(pos + label + " " + n + " = " + value + "\n");
//                            JCExpression e = findDefinition(n);
//                            record(expr,value);
//                            if (e != null) showSubexpressions(e);
//                        } else {
//                            w.append(pos + label + " " + expr + "\n");
//                            showSubexpressions(expr);
//                        }
//                    } else if (label == Label.DSA) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        if (!(bin.rhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        w.append(lastpos + label + " = " + value((JCIdent)bin.lhs)
//                                + "  [" + bin.rhs + "]\n");
//                        // no subexpressions
//                    } else if (label == Label.RETURN) {
//                        w.append(pos + "Executing return statement\n");
//                    } else if (label == Label.TERMINATION) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCBinary)) { failure(label,expr); continue; }
//                        bin = (JCBinary)bin.lhs;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        String v = value((JCIdent)bin.lhs);
//                        if (v.equals("0")) {
//                            String rv = bin.lhs.toString().replace("terminationVar","result");
//                            String vv = valueNull(rv);
//                            w.append(pos + "Called method returned normally [" + bin.lhs + "=" + v +"]"+ (vv==null?"":", return value = " + vv + " ["+rv+"]\n"));
//                        } else {
//                            String rv = bin.lhs.toString().replace("terminationVar","exception");
//                            String vv = subexp.getType(rv);
//                            w.append(pos + "Called method exited with an exception [" + bin.lhs + "=" + v +"]"
//                                    + (vv==null?"":", exception type = "+vv) + "\n");
//                        }
//                    } else if (label == Label.METHODAXIOM) {
//                        // Just print the axiom - don't try to evaluate it
//                        w.append(pos + label + " " + expr + "\n");
//                    } else if (label == Label.ARRAY_INIT) {
//                        // Just print the expression - don't try to evaluate it
//                        w.append(pos + label + " " + expr + "\n");
//                    } else if (label == Label.BRANCHT || label == Label.HAVOC) {
//                        // skip
//                    } else if (label == Label.BRANCHE) {
//                        if (expr instanceof JCUnary) {
//                            JCExpression e = ((JCUnary)expr).getExpression();
//                            if (e instanceof JCIdent) {
//                                String value = value((JCIdent)e);
//                                record(expr,value);
//                            }
//                        }
//                    } else {
//                        w.append(pos + label + " " + expr + "\n");
//                        showSubexpressions(expr);
//                    }
//                } else if (s.token == JmlToken.ASSERT) {
//                    String value = null;
//                    String name = null;
//                    if (expr instanceof JCIdent) {
//                        name = ((JCIdent)expr).toString();
//                        value = ce.get(name);
//                        JCExpression e = findDefinition(((JCIdent)expr).name);
//                        if (e != null) expr = e;
//                    }
//                    w.append(pos + "Assert [" + label + "] "
//                            + (value == null? "" : value)
//                            + "   [" + expr + "]\n");
//                    showSubexpressions(expr);
//                    if ("false".equals(value)) {
//                        sawFalseAssert = true;
//                    }
//                } else if (s.token == JmlToken.COMMENT) {
//                    w.append(pos);
//                    w.append("Comment: // ");
//                    w.append(((JCLiteral)s.expression).value.toString());
//                    w.append("\n");
//                } else {
//                    log.error(pos,"esc.internal.error","Incorrect token type in traceBlockStatements: " + s.token.internedName());
//                }
//                if (label == Label.PRECONDITION) {
////                    int sp = TreeInfo.getStartPos(expr);
////                    int ep = TreeInfo.getEndPos(expr,log.currentSource().getEndPosTable());
////                    int type = IProverResult.Span.NORMAL;
////                    String result = values.get(expr.toString());
////                    type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
////                    if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                    doLogicalSubExprs(expr);
//                } else if (label == Label.ASSIGNMENT || label == Label.EXPLICIT_ASSERT || label == Label.EXPLICIT_ASSUME
//                        || label == Label.BRANCHT || label == Label.BRANCHE
//                        || label == Label.SWITCH_VALUE) { 
//                    int sp = TreeInfo.getStartPos(s);
//                    int ep = TreeInfo.getEndPos(s,log.currentSource().getEndPosTable());
//                    int type = IProverResult.Span.NORMAL;
//                    if (label != Label.ASSIGNMENT) {
//                        String result = values.get(expr.toString());
//                        type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//                    }
//                    if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                } else if (label == Label.CATCH_CONDITION) {
//                    int sp = TreeInfo.getStartPos(s);
//                    int ep = TreeInfo.getEndPos(s,log.currentSource().getEndPosTable());
//                    int type = IProverResult.Span.NORMAL;
//                    type = IProverResult.Span.NORMAL; 
//                    if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                } else if (label == Label.POSTCONDITION || label == Label.SIGNALS) {
//                    JCExpression texpr = expr;
//                    if (label == Label.SIGNALS) {// FIXME - a NPE thrown from here does not produce any visible error
//                        texpr = (texpr instanceof JmlBinary && ((JmlBinary)texpr).op == JmlToken.IMPLIES) ? ((JmlBinary)texpr).rhs : null;
//                        texpr = (texpr instanceof JCBinary && ((JCBinary)texpr).getTag() == JCTree.AND) ? ((JCBinary)texpr).rhs : null;
//                        if (texpr instanceof JmlBinary && ((JmlBinary)texpr).op == JmlToken.IMPLIES) {
//                            JCExpression tt = ((JmlBinary)texpr).rhs;
//                            if (tt instanceof JmlBinary && ((JmlBinary)tt).op == JmlToken.IMPLIES) {
//                                texpr = (JmlBinary)tt;
//                            }
//                        } else {
//                            texpr = null;
//                        }
//                    } else {
//                        texpr = (texpr instanceof JmlBinary && ((JmlBinary)texpr).op == JmlToken.IMPLIES) ? ((JmlBinary)texpr).rhs : null;
//                        texpr = (texpr instanceof JmlBinary && ((JmlBinary)texpr).op == JmlToken.IMPLIES) ? texpr : null;
//                    }
//                    if (texpr instanceof JmlBinary) {
//                        JmlBinary rexpr = (JmlBinary)texpr;
//                        JCExpression lhs = rexpr.lhs;
//                        JCExpression rhs = rexpr.rhs;
//                        int sp = TreeInfo.getStartPos(lhs);
//                        int ep = TreeInfo.getEndPos(lhs,log.currentSource().getEndPosTable());
//                        int type = IProverResult.Span.NORMAL;
//                        String result = values.get(lhs.toString());
//                        type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//                        if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                        if (type != IProverResult.Span.FALSE) {
//                            sp = TreeInfo.getStartPos(rhs);
//                            ep = TreeInfo.getEndPos(rhs,log.currentSource().getEndPosTable());
//                            type = IProverResult.Span.NORMAL;
//                            result = values.get(rhs.toString());
//                            type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//                            if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                        }
//                    } else {
//                        int sp = TreeInfo.getStartPos(s);
//                        int ep = TreeInfo.getEndPos(s,log.currentSource().getEndPosTable());
//                        int type = IProverResult.Span.NORMAL;
//                        String result = values.get(expr.toString());
//                        type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//                        if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                    }
//                } else if (label == Label.TERMINATION) {
//                    int sp = TreeInfo.getStartPos(s);
//                    int ep = TreeInfo.getEndPos(s,log.currentSource().getEndPosTable());
//                    int type = IProverResult.Span.NORMAL;
//                    {
//                        JCExpression e = ((JCBinary)((JCBinary)expr).lhs).lhs;
//                        String result = values.get(e.toString());
//                        int k = result == null ? 0 : Integer.valueOf(result);
//                        type = k < 0 ? IProverResult.Span.EXCEPTION : IProverResult.Span.NORMAL; 
//                    }
//                    if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                }
//                if (sawFalseAssert) break;// Stop reporting the trace if we encounter a false assertion
//            }
//            return !sawFalseAssert;
//        }
//        
//        public int doExpr(JCExpression expr, boolean show) {
//            int sp = TreeInfo.getStartPos(expr);
//            int ep = TreeInfo.getEndPos(expr,log.currentSource().getEndPosTable());
//            int type = IProverResult.Span.NORMAL;
//            String result = values.get(expr.toString());
//            type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//            if (show && sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//            return type;
//        }
//        
//        public int doLogicalSubExprs(JCExpression expr) {
//            int r = -10;
//            if (expr instanceof JCBinary) {
//                int op = expr.getTag();
//                JCBinary bin = (JCBinary)expr;
//                if (op == JCTree.OR) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    if (r != IProverResult.Span.TRUE) {
//                        r = doLogicalSubExprs(bin.rhs);
//                    }
//                } else if (op == JCTree.AND) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    if (r != IProverResult.Span.FALSE) {
//                        r = doLogicalSubExprs(bin.rhs);
//                    }
//                } else if (op == JCTree.BITOR) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    int rr = doLogicalSubExprs(bin.rhs);
//                    r = (rr==IProverResult.Span.TRUE) ? rr : r;
//                } else {
//                    r = doExpr(expr,true);
//                }
//            } else if (expr instanceof JmlBinary) {
//                JmlBinary bin = (JmlBinary)expr;
//                JmlToken op = bin.op;
//                if (op == JmlToken.IMPLIES) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    if (r != IProverResult.Span.FALSE) {
//                        r = doLogicalSubExprs(bin.rhs);
//                    }
//                } else if (op == JmlToken.REVERSE_IMPLIES) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    if (r != IProverResult.Span.TRUE) {
//                        r = doLogicalSubExprs(bin.rhs);
//                    }
//                } else {
//                    r = doLogicalSubExprs(bin.rhs);
//                    r = doExpr(expr,false);
//                }
//            } else {
//                r = doExpr(expr,true);
//            }
//
//            // FIXME - also do NOT, conditional expression, boolean ==, EQUIVALENCE, INEQUIVALENCE
//            return r;
//        }
//        
//        public JCExpression findDefinition(Name name) {
//            for (BasicProgram.Definition def: program.definitions()) {
//                JCIdent id = def.id;
//                if (id.name != name) continue;
//                return def.value;
//            }
////            for (JCExpression e: program.pdefinitions) {
////                if (!(e instanceof JCBinary)) continue;
////                JCBinary bin = (JCBinary)e;
////                if (!(bin.lhs instanceof JCIdent)) continue;
////                JCIdent id = (JCIdent)bin.lhs;
////                if (id.name != name) continue;
////                return bin.rhs;
////            }
//            return null;
//        }
//        
//        public String value(JCIdent id) {
//            String v = ce.get(id.name.toString());
//            if (v == null) v = "?";
//            return v;
//        }
//        
//        public String valueNull(JCIdent id) {
//            return ce.get(id.name.toString());
//        }
//        
//        public String valueNull(String id) {
//            return ce.get(id);
//        }
//        
//        public void failure(Label label, JCExpression expr) {
//            log.warning("jml.internal.notsobad","Unable to interpret counterexample trace.  A " + label + " statement has unexpected structure: " + expr);
//        }
//        
//        Subexpressor subexp;
//        
//        public String showSubexpressions(JCExpression expr) {
//            if (showSubexpressions) try { 
//                subexp.walk(expr);
//                return w.toString();
//            } catch (IOException e) {
//                return "<IOException>";
//            }
//            return "";
//        }
//        
//        public void record(JCExpression expr, String value) {
//            subexp.values.put(expr.toString(),value);
//        }
//    }
//    
//    static int count = 1000000;
//
//    /** This class requests values of subexpressions from the prover */
//    public static class Subexpressor extends JmlTreeScanner {
//        
//        Context context;
//        IProver prover;
//        JmlTree.Maker factory;
//        Names names;
//        Symtab syms;
//        Writer w;
//        final String prefix = "X$$$";
//        List<JCBinary> exprs = new LinkedList<JCBinary>();
//        Map<String,JCExpression> requests = new HashMap<String,JCExpression>();
//        Map<String,String> values = null;
//        
//        /** Top-level call for the class - puts requests to the prover for each
//         * subexpression of the argument, returning the results in 'requests'.
//         * This method can be reused, but is not thread-safe.
//         */
//        public void walk(JCExpression expr) throws IOException {
//            exprs.clear();
//            requests.clear();
//            scan(expr);
//            IProverResult res = null;
//            try {
//                for (JCExpression e: exprs) {
//                    prover.assume(e);
//                }
//                res = prover.check(true);
//            } catch (ProverException ex) {
//                w.append(ex.toString());  // FIXME - clean up the error reporting here and in the RUntimeExceptions just below.
//                w.append("\n");
//                return;
//            }
//            if (res == null) {
//                throw new RuntimeException("ERROR: no additional information available");
//            } else if (!res.isSat()) {
//                throw new RuntimeException("ERROR: no longer satisfiable");
//            } else {
//                ICounterexample nce = res.counterexample();
//                for (JCBinary bin: exprs) {
//                    JCIdent id = (JCIdent)bin.lhs;
//                    String value = nce.get(id.toString());
//                    if (value != null && id.type.tag == TypeTags.CHAR) {
//                        value = ((Character)(char)Integer.parseInt(value)).toString() + " (" + value + ")";
//                    }
//                    if (value == null) value = "?";
//                    w.append("                                " + value + "\t = " + bin.rhs + "\n");
//                    values.put(bin.rhs.toString(), value);
//                }
//            }
//        }
//        
//        /** Top-level call that returns a list of values (as Strings) corresponding to the list of 
//         * expressions in the argument */
//        public List<String> getValues(JCExpression... exprlist) throws IOException {
//            IProverResult res = null;
//            List<JCIdent> ids = new LinkedList<JCIdent>();
//            try {
//                for (JCExpression e: exprlist) {
//                    JCIdent id = newIdent(e);
//                    JCExpression ex = factory.at(Position.NOPOS).Binary(JCTree.EQ,id,e);
//                    ex.type = syms.booleanType;
//                    ids.add(id);
//                    prover.assume(ex);
//                }
//                res = prover.check(true);
//            } catch (ProverException ex) {
//                w.append(ex.toString()); w.append("\n"); // FIXME - better error response here and below
//                return null;
//            }
//            if (res == null) {
//                w.append("ERROR: no additional information available\n");
//            } else if (!res.isSat()) {
//                w.append("ERROR: no longer satisfiable\n");
//            } else {
//                ICounterexample nce = res.counterexample();
//                List<String> out = new LinkedList<String>();
//                int k = 0;
//                for (JCIdent id: ids) {
//                    String value = nce.get(id.name.toString());
//                    if (value == null) value = "?";
//                    out.add(value);
//                    if (values != null) {
//                        JCExpression ee = exprlist[k];
//                        String e = ee.toString();
//                        if (ee.type.tag == TypeTags.CHAR) {
//                            e = ((Character)(char)Integer.parseInt(e)).toString();
//                        }
//                        values.put(e,value);
//                        //System.out.println("MAPPING: " + e + " " + value);
//                        k++; // FIXME - increment inside or outside the if statement
//                    }
//                }
//                prover.reassertCounterexample(nce);
//                return out;
//            }
//            return null;
//        }
//
//        /** Returns the dynamic type of the variable given in the argument */
//        public String getType(String eid) {
//            try {
//                factory.at(Position.NOPOS);
//                JCIdent expr = factory.Ident(Names.instance(context).fromString(eid));
//                expr.type = syms.objectType;
//                JCExpression e = factory.JmlMethodInvocation(JmlToken.BSTYPEOF,expr);
//                e.type = syms.classType;
//                JCIdent id = newIdent(e);
//                JCExpression ex = factory.at(Position.NOPOS).Binary(JCTree.EQ,id,e);
//                ex.type = syms.booleanType;
//                prover.assume(ex);
//                IProverResult res = prover.check(true);
//                if (res == null) {
//                    w.append("ERROR: no additional information available\n");
//                } else if (!res.isSat()) {
//                    w.append("ERROR: no longer satisfiable\n");
//                } else {
//                    ICounterexample nce = res.counterexample();
//                    String value = nce.get(id.name.toString());
//                    return value;
//                }
//            } catch (IOException e) {
//                Log.instance(context).noticeWriter.println(e.toString());
//
//            } catch (ProverException e) {
//                Log.instance(context).noticeWriter.println(e.toString());
//            }
//            return null;
//        }
//        
//        public Subexpressor(Context context, IProver prover, Map<String,String> values, Writer w) {
//            this.context = context;
//            this.prover = prover;
//            this.factory = JmlTree.Maker.instance(context);
//            this.names = Names.instance(context);
//            this.syms = Symtab.instance(context);
//            this.w = w;
//            this.values = values;
//        }
//        
//        public void request(JCExpression expr) {
//            JCIdent id = newIdent(expr);
//            requests.put(id.name.toString(),expr);
//            JCBinary bin = factory.Binary(JCTree.EQ,id,expr);
//            bin.type = syms.booleanType;
//            bin.pos = Position.NOPOS;
//            exprs.add(bin);
//        }
//        
//        /** Creates a unique identifier with the type of the given expression */
//        public JCIdent newIdent(JCExpression expr)  {
//            Type t = expr.type;
//            Name n = names.fromString(prefix + (++count));
//            JCIdent id = factory.Ident(n);
//            id.type = t;
//            return id;
//        }
//        
//        /** Scan the given JCTree, issuing a request() call for each subexpression encountered */
//        public void scan(JCTree that) {
//            super.scan(that);
//            if (that instanceof JCExpression &&
//                    !(that instanceof JCParens) &&
//                    !(that instanceof JCLiteral)) request((JCExpression)that);
//        }
//
//        /** Scan the given JCTree, issuing a request() call for each subexpression encountered,
//         * but not for the argument itself */
//        public void scanNoRequest(JCTree that) {
//            super.scan(that);
//        }
//        
//        public void visitLiteral(JCLiteral tree) {
//            String r = tree.toString();
//            values.put(r,r);
//        }
//
//        /** Overridden so that we request the arguments but not the method call itself.*/
//        public void visitApply(JCMethodInvocation tree) {
//            scanNoRequest(tree.meth);
//            scan(tree.args);
//        }
//        
//        /** Don't request values for quantified expressions */
//        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree) {
//            // do not scan the subexpressions of a quantified expression
//        }
//        
//        public void visitCatch(JCCatch tree) {
//            super.visitCatch(tree);
//        }
//    }
//    
//    /** This class computes metrics over a BasicBlock */
//    public static class Counter extends JmlTreeScanner {
//        
//        int nodes = 0;  // nodes
//        int assumes = 0;
//        int asserts = 0;
//        int blocks = 0;
//        int statements = 0;
//        int paths = 0;
//        int maxBlockNodes = 0;
//        
//        public void count(BasicBlock b) {
//            for (JCTree t: b.statements()) t.accept(this);
//            nodes += b.statements().size();
//        }
//        
//        public static int counts(BasicBlock b) {
//            return counts(b.statements());
//        }
//        
//        public static int counts(List<JCStatement> sts) {
//            Counter c = new Counter();
//            for (JCTree t: sts) t.accept(c);
//            return c.nodes + sts.size();
//        }
//        
//        static public Counter count(BasicProgram b) {
//            Counter c = new Counter();
//            int max = 0;
//            for (BasicBlock bb: b.blocks()) {
//                int c1 = c.nodes;
//                c.count(bb);
//                if (c.nodes - c1 > max) max = c.nodes - c1;
//            }
//            c.maxBlockNodes = max;
//            for (BasicProgram.Definition t: b.definitions()) { t.id.accept(c); t.value.accept(c); }
//            for (JCTree t: b.pdefinitions) t.accept(c);
//            for (JCTree t: b.background()) t.accept(c);
//            c.blocks = b.blocks().size();
//            return c;
//        }
//        
//        static public int countx(BasicProgram b) {
//            Counter c = new Counter();
//            for (BasicProgram.Definition t: b.definitions()) { t.id.accept(c); t.value.accept(c); }
//            for (JCTree t: b.pdefinitions) t.accept(c);
//            for (JCTree t: b.background()) t.accept(c);
//            return c.nodes;
//        }
//        
//        static public int countAST(JCTree node) {
//            Counter c = new Counter();
//            node.accept(c);
//            if (node instanceof JCBlock) c.nodes++;
//            return c.nodes;
//        }
//        
//        static public int countASTStatements(JCTree node) {
//            Counter c = new Counter();
//            node.accept(c);
//            if (node instanceof JCBlock) c.statements++;
//            return c.statements;
//        }
//        
//        public Counter() {
//        }
//        
//        public void add(Counter c) {
//            nodes += c.nodes;
//            assumes += c.assumes;
//            asserts += c.asserts;
//            blocks += c.blocks;
//            statements += c.statements;
//            maxBlockNodes = maxBlockNodes < c.maxBlockNodes ? c.maxBlockNodes : maxBlockNodes;
//        }
//        
//        public void scan(JCTree that) {
//            nodes++;
//            if (that instanceof JCStatement) statements++;
//            super.scan(that);
//        }
//        
//        public void visitJmlStatementExpr(JmlStatementExpr that) {
//            if (that.token == JmlToken.ASSUME) assumes++;
//            if (that.token == JmlToken.ASSERT) asserts++;
//            super.visitJmlStatementExpr(that);
//        }
//        
//        public String toString() {
//            return "    " + blocks + " blocks; " + nodes + " nodes; " + maxBlockNodes + " max; " + assumes + " assumes; " + asserts + " asserts; " ;
//        }
//    }

}
