package org.jmlspecs.openjml.esc;

import static com.sun.tools.javac.code.TypeTags.CLASS;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
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
import org.jmlspecs.openjml.JmlTree.JmlBBArrayHavoc;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
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
import org.jmlspecs.openjml.JmlTree.JmlPrimitiveTypeTree;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSetComprehension;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementDecls;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
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
import org.jmlspecs.openjml.proverinterface.Counterexample;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.proverinterface.ProverException;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeMaker;
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
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

/**
 * This class converts a Java AST into basic block form (including DSA and
 * passification).
 * <P>
 * Basic block form contains only this subset of AST nodes:
 * <UL>
 * <LI>JCLiteral - numeric (all of them? FIXME), null, boolean, class (String?,
 * character?)
 * <LI>JCIdent
 * <LI>JCParens
 * <LI>JCUnary
 * <LI>JCBinary
 * <LI>JmlBinary
 * <LI>JCConditional
 * <LI>JmlBBFieldAccess
 * <LI>JmlBBArrayAccess
 * <LI>JmlBBFieldAssign
 * <LI>JmlBBArrayAssign
 * <LI>JCMethodInvocation - only pure methods within specifications
 * <LI>JmlMethodInvocation - old, typeof
 * <LI>JmlQuantifiedExpr - only forall and exists
 * <LI>JCTypeCast - but the clazz element now has a JCLiteral (which is a type
 * literal)
 * <LI>[JCInstanceOf - not present - use a typeof and a subtype operation]
 * </UL>
 * 
 * @author David Cok
 */
public class BasicBlocker extends JmlTreeScanner {

    // /** The context key for the tree factory. */
    // protected static final Context.Key<BasicBlocker> bbKey =
    // new Context.Key<BasicBlocker>();
    //
    // /////// To have a unique BasicBlocker instance for each method translated
    // // In the initialization of tools, call
    // BasicBlocker.Factory.preRegister(context);
    // // Obtain a new BasicBlocker when desired with
    // context.get(BasicBlocker.class);
    //
    // /** Register a BasicBlocker Factory, if nothing is registered yet */
    // public static void preRegister(final Context context) {
    // if (context.get(bbKey) != null) return;
    // context.put(bbKey, new Context.Factory<BasicBlocker>() {
    // @Override
    // public BasicBlocker make(Context context) {
    // return new BasicBlocker(context);
    // }
    // });
    // }
    //
    // /////// To have one BasicBlocker instance per context use this method
    // without the pre-registration
    // // Don't need pre-registration since we are not replacing any tool and
    // not using a factory
    // // To obtain a reference to the instance of BasicBlocker for the current
    // context
    // // BasicBlocker.instance(context);
    //
    // /** Get the instance for this context.
    // *
    // * @param context the compilation context
    // * @return a (unique for the context) BasicBlocker instance
    // */
    // public static BasicBlocker instance(@NonNull Context context) {
    // BasicBlocker instance = context.get(bbKey);
    // // This is lazily initialized so that a derived class can preRegister to
    // // replace this BasicBlocker
    // if (instance == null) {
    // instance = new BasicBlocker(context);
    // }
    // return instance;
    // }

    // Options

    // TODO - document
    static boolean                              useAssertDefinitions      = true;

    // This implements checking of assumption feasibility. After an
    // assumption that is to be checked, we add the assertion
    // assert assumeCheck$<uniqueint>$<label>
    // and the definition
    // assume assumeCheck$<uniqueint>$<label> == <assumecheckvar> != <uniqueint>
    // where <uniqueint> is a positive integer not used elsewhere for
    // this purpose. Here we use the source code location so that it
    // can be used as well to generate error messages.
    // Then we also add to the VC the assumption
    // assume <assumecheckvar> == 0
    // That way all the inserted assertions above are true. However, we
    // can change any one of them to false by replacing the assumption
    // above with
    // assume <assumecheckvar> == <uniqueid>
    // using the specific <uniqueint> of the assumption we want to test

    // FIXME - review and document
    static public boolean                       insertAssumptionChecks    = true;

    // FIXME - review and document
    static boolean                              useCountedAssumeCheck     = true;

    // FIXME - review and document
    static JCExpression                         booleanAssumeCheck;

    // FIXME - review and document
    JCExpression                                assumeCheck               = null;

    /**
     * This static field controls whether (user) assume statements are turned
     * into assumptions tracked with the assume count variable; if so, then
     * there is an easy mechanism to test whether the assumptions are feasible.
     */
    public static boolean                       useAssumeDefinitions      = true;

    // THE FOLLOWING ARE ALL FIXED STRINGS

    // -----------------------------------------------------------------
    // Names for a bunch of synthetic variables
    /** Standard name for the variable that tracks termination */
    public static final @NonNull
    String                                      TERMINATION_VAR           = "_terminationVar$$";

    /**
     * Standard name for the variable that represents the heap (which excludes
     * local variables)
     */
    public static final @NonNull
    String                                      HEAP_VAR                  = "_heap$$";

    /** Standard name for the variable that tracks allocations */
    public static final @NonNull
    String                                      ALLOC_VAR                 = "_alloc$$";

    /** Prefix for assumptions defined in the basic block */
    public static final String                  ASSUMPTION_PREFIX         = "$assumption";

    /** Prefix for variables designating results of method calls */
    public static final String                  RESULT_PREFIX             = "$$result$";

    /** Name of the encoded method result variable */
    public static final String                  RESULT                    = "$$result";

    /** Name of the variable representing an exception thrown from the method */
    public static final String                  EXCEPTION                 = "$$exception";

    /** Name of the encoded this variable */
    public static final String                  THIS                      = "this$";

    /** The prefix of the variables used in checking assumptions */
    public static final String                  ASSUME_CHECK_PREFIX       = "assumeCheck$";

    /** A variable name used in checking assumptions */
    public static final String                  ASSUME_CHECK_COUNT        = "__assumeCheckCount";

    /** Name of length field */
    public static final String                  LENGTH                    = "length";

    /** Suffix for the name of a basic block for a finally block */
    public static final String                  FINALLY                   = "$finally";

    /** Suffix for the name of a 'catchrest' basic block */
    public static final String                  CATCHREST                 = "$catchrest";

    /** Suffix for the name of a basic block holding the body of a loop */
    public static final String                  LOOPBODY                  = "$LoopBody";

    /** Suffix for the name of a basic block holding the code after a loop */
    public static final String                  LOOPAFTER                 = "$LoopAfter";

    /**
     * Suffix for the name of a basic block holding the code where continue
     * statements go
     */
    public static final String                  LOOPCONTINUE              = "$LoopContinue";

    /**
     * Suffix for the name of a basic block holding the code where break
     * statements go
     */
    public static final String                  LOOPBREAK                 = "$LoopBreak";

    /**
     * Suffix for the name of a basic block to which control transfers if the
     * loop condition fails
     */
    public static final String                  LOOPEND                   = "$LoopEnd";

    /**
     * Suffix for the name of a basic block for the then branch of an if
     * statement
     */
    public static final String                  THENSUFFIX                = "$then";

    /**
     * Suffix for the name of a basic block for the else branch of an if
     * statement
     */
    public static final String                  ELSESUFFIX                = "$else";

    /** Suffix for the name of a basic block after an if statement */
    public static final String                  AFTERIF                   = "$afterIf";

    /** Prefix for branch condition variables */
    public static final String                  BRANCHCONDITION_PREFIX    = "branchCondition$";

    // -----------------------------------------------------------------
    // Names for various basic blocks

    /** The prefix used for names of blocks */
    public static final @NonNull
    String                                      blockPrefix               = "BL$_$";

    /** Standard name for the block that starts the body */
    public static final @NonNull
    String                                      BODY_BLOCK_NAME           = blockPrefix
                                                                                  + "bodyBegin";

    /**
     * Standard name for the starting block of the program (just has the
     * preconditions)
     */
    public static final @NonNull
    String                                      START_BLOCK_NAME          = blockPrefix
                                                                                  + "Start";

    /** Standard name for the return block, whether or not a value is returned */
    public static final @NonNull
    String                                      RETURN_BLOCK_NAME         = blockPrefix
                                                                                  + "return";

    /**
     * Standard name for the postcondition block, whether or not a value is
     * returned
     */
    public static final @NonNull
    String                                      COND_RETURN_BLOCK_NAME    = blockPrefix
                                                                                  + "condReturn";

    /** Standard name for the exception block */
    public static final @NonNull
    String                                      EXCEPTION_BLOCK_NAME      = blockPrefix
                                                                                  + "exception";

    /** Standard name for the conditional exception block */
    public static final @NonNull
    String                                      COND_EXCEPTION_BLOCK_NAME = blockPrefix
                                                                                  + "condException";

    // THE FOLLOWING FIELDS ARE EXPECTED TO BE CONSTANT FOR THE LIFE OF THE
    // OBJECT
    // They are either initialized in the constructor or initialized on first
    // use

    /** The compilation context */
    @NonNull
    protected Context                           context;

    /** The log to which to send error, warning and notice messages */
    @NonNull
    protected Log                               log;

    /**
     * The specifications database for this compilation context, initialized in
     * the constructor
     */
    @NonNull
    protected JmlSpecs                          specs;

    /**
     * The symbol table from the compilation context, initialized in the
     * constructor
     */
    @NonNull
    protected Symtab                            syms;

    /**
     * The Names table from the compilation context, initialized in the
     * constructor
     */
    @NonNull
    protected Names                             names;

    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    @NonNull
    protected JmlTreeUtils                      treeutils;

    /** The object that desugars JML */
    @NonNull
    protected JmlTranslator                     treetrans;

    /** General utilities */
    @NonNull
    protected Utils                             utils;

    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull
    protected JmlTree.Maker                     factory;

    // Caution - the following are handy, but they are shared, so they won't
    // have proper position information

    /**
     * Holds an AST node for a boolean true literal, initialized in the
     * constructor
     */
    @NonNull
    final protected JCLiteral                   trueLiteral;

    /**
     * Holds an AST node for a boolean false literal, initialized in the
     * constructor
     */
    @NonNull
    final protected JCLiteral                   falseLiteral;

    /** Holds an AST node for a null literal, initialized in the constructor */
    @NonNull
    final protected JCLiteral                   nullLiteral;

    /** Holds an AST node for a null literal, initialized in the constructor */
    @NonNull
    final protected JCLiteral                   zeroLiteral;

    /**
     * Identifier of a synthesized object field holding the allocation time of
     * the object, initialized in the constructor
     */
    @NonNull
    protected JCIdent                           allocIdent;

    /** A counter to ensure unique instances of alloc identifiers */
    protected int                               allocCount                = 0;

    /**
     * Symbol of a synthesized object field holding the allocation time of the
     * object, initialized in the constructor
     */
    @NonNull
    protected VarSymbol                         allocSym;

    /**
     * Symbol of a synthesized object field holding the allocation time of the
     * object, initialized in the constructor
     */
    @NonNull
    protected VarSymbol                         terminationSym;

    /**
     * Identifier of a synthesized object field holding the length of an array
     * object, initialized in the constructor
     */
    @NonNull
    protected JCIdent                           lengthIdent;

    /**
     * Symbol of a synthesized object field holding the length of an array
     * object, initialized in the constructor
     */
    @NonNull
    protected VarSymbol                         lengthSym;

    /**
     * A fixed id for 'this' of the method being translated (see currentThisId
     * for the 'this' of called methods).
     */
    @NonNull
    protected JCIdent                           thisId;

    // These are initialized on beginning the translation of a given
    // method

    /**
     * A holding spot for the conditional return block of a program under normal
     * termination
     */
    protected BasicBlock                        condReturnBlock;

    /**
     * A holding spot for the return block of a program under normal termination
     */
    protected BasicBlock                        returnBlock;

    /** A holding spot for the conditional exception block (after try-finally) */
    protected BasicBlock                        condExceptionBlock;

    /**
     * A holding spot for the last block of a program when there is an exception
     */
    protected BasicBlock                        exceptionBlock;

    // THE FOLLOWING FIELDS ARE USED IN THE COURSE OF DOING THE WORK OF
    // CONVERTING
    // TO BASIC BLOCKS. They are fields of the class because they need to be
    // shared across the visitor methods.

    /** visit methods that emit statements put them here */
    protected List<JCStatement>                 newstatements;                                                     // FIXME
                                                                                                                    // -
                                                                                                                    // just
                                                                                                                    // use
                                                                                                                    // currentBlock.statements
                                                                                                                    // ???

    /**
     * Place to put new definitions, such as the equalities defining auxiliary
     * variables
     */
    protected List<BasicProgram.Definition>     newdefs;

    // FIXME - fold into background???
    protected List<JCExpression>                newpdefs;

    /** Place to put new background assertions, such as class predicates */
    protected List<JCExpression>                background;

    /**
     * List of blocks yet to be processed, that is, translated from conventional
     * program to basic program state)
     */
    protected java.util.List<BasicBlock>        blocksToDo;

    /** List of blocks completed processing - in basic state */
    protected java.util.List<BasicBlock>        blocksCompleted;

    /** A map of names to blocks */
    protected java.util.Map<String, BasicBlock> blockLookup;

    /** A variable to hold the block currently being processed */
    protected BasicBlock                        currentBlock;

    /** The variable name that is currently the 'this' variable */
    protected JCIdent                           currentThisId;

    /**
     * Ordered list of statements from the current block that are yet to be
     * processed into basic program form
     */
    protected List<JCStatement>                 remainingStatements;

    /** The guarding condition so far in processing an expression */
    protected JCExpression                      condition;

    /**
     * true when translating a spec expression, which has particular effect on
     * the translation of method calls
     */
    protected boolean                           inSpecExpression;

    /** The program being constructed */
    protected BasicProgram                      program                   = null;

    // Characteristics of the method under study
    /** The declaration of the method under conversion */
    protected JmlMethodDecl                     methodDecl;

    /** True if the method being converted is a constructor */
    protected boolean                           isConstructor;

    /** True if the method being converted is static */
    protected boolean                           isStatic;

    /** True if the method being converted is a helper method */
    protected boolean                           isHelper;

    // FIXME - document the following; check when initialized

    protected JCExpression                      resultVar                 = null;

    protected JCIdent                           exceptionVar              = null;

    protected JCIdent                           signalsVar                = null;                                  // Used
                                                                                                                    // when
                                                                                                                    // translating
                                                                                                                    // a
                                                                                                                    // signals
                                                                                                                    // clause

    protected JCIdent                           heapVar;

    protected JCIdent                           terminationVar;                                                    // 0=no
                                                                                                                    // termination
                                                                                                                    // requested;
                                                                                                                    // 1=return
                                                                                                                    // executed;
                                                                                                                    // 2
                                                                                                                    // =
                                                                                                                    // exception
                                                                                                                    // happening

    protected JCIdent                           assumeCheckCountVar;                                               // FIXME
                                                                                                                    // -
                                                                                                                    // initialized?

    protected int                               assumeCheckCount;                                                  // FIXME
                                                                                                                    // -
                                                                                                                    // initialized?

    /**
     * This is an integer that rises monotonically on each use and is used to
     * make sure new identifiers are unique.
     */
    protected int                               unique;

    /**
     * Holds the result of any of the visit methods that produce JCExpressions,
     * since the visitor template used here does not have a return value. [We
     * could have used the templated visitor, but other methods do not need to
     * return anything, we don't need the additional parameter, and that visitor
     * is complicated by the use of interfaces for the formal parameters.]
     */
    private JCExpression                        result;

    /**
     * A mapping from BasicBlock to the sym->incarnation map giving the map that
     * corresponds to the state at the exit of the BasicBlock.
     */
    @NonNull
    protected Map<BasicBlock, VarMap>           blockmaps                 = new HashMap<BasicBlock, VarMap>();

    /**
     * A mapping from labels to the sym->incarnation map operative at the
     * position of the label.
     */
    @NonNull
    protected Map<Name, VarMap>                 labelmaps                 = new HashMap<Name, VarMap>();

    /**
     * A mapping from labels to the statement that is labelled.
     */
    @NonNull
    protected Map<Name, JCTree>                 labelmapStatement         = new HashMap<Name, JCTree>();

    /** The map from symbol to incarnation number in current use */
    @NonNull
    protected VarMap                            currentMap;

    /**
     * The mapping of variables to incarnations to use when in the scope of an
     * \old
     */
    @NonNull
    protected VarMap                            oldMap                    = new VarMap();

    /** The class info block when walking underneath a given class. */
    protected JmlClassInfo                      classInfo;

    /**
     * The jfoMap and jfoArray keep track of a mapping between JavaFileObjects
     * and unique Integers. When position information in an encoded identifier
     * refers to a file that is not the file containing the implementation of
     * the method being translated and verified, then we have to indicate which
     * file contains the source for the position reference. This indication is
     * an @ followed by an integer included in the identifier, where the integer
     * is a unique positive integer associated with the file. Since these
     * mappings are static, the associations remain constant across different
     * methods and different compilation contexts. <BR>
     * jfoMap is a mapping from JavaFileObject to Integer
     */
    // FIXME - should reconsider whether this mapping is static
    static Map<JavaFileObject, Integer>         jfoMap                    = new HashMap<JavaFileObject, Integer>();

    /** Maps integers to JavaFileObject, the reverse of the mapping in jfoMap */
    static ArrayList<JavaFileObject>            jfoArray                  = new ArrayList<JavaFileObject>();
    static {
        jfoArray.add(0, null);
    }

    /** Returns the int associated with a file, creating it if necessary */
    public static int getIntForFile(JavaFileObject jfo) {
        Integer i = jfoMap.get(jfo);
        int k;
        if (i == null) {
            k = jfoArray.size();
            jfoArray.add(k, jfo);
            jfoMap.put(jfo, k);
        } else {
            k = i;
        }
        return k;
    }

    /** Returns the file associated with an int */
    public static JavaFileObject getFileForInt(int i) {
        return jfoArray.get(i);
    }

    /**
     * The constructor, but use the instance() method to get a new instance, in
     * order to support extension. This constructor should only be invoked by a
     * derived class constructor.
     * 
     * @param context
     *            the compilation context
     */
    protected BasicBlocker(@NonNull Context context) {
        // context.put(bbKey, this);
        this.context = context;
        this.log = Log.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.treetrans = JmlTranslator.instance(context);
        this.utils = Utils.instance(context);
        this.scanMode = AST_JAVA_MODE;

        unique = 0;

        trueLiteral = factory.Literal(TypeTags.BOOLEAN, 1);
        trueLiteral.type = syms.booleanType;
        falseLiteral = factory.Literal(TypeTags.BOOLEAN, 0);
        falseLiteral.type = syms.booleanType;
        nullLiteral = factory.at(0).Literal(TypeTags.BOT, 0);
        nullLiteral.type = syms.objectType;
        zeroLiteral = treeutils.makeIntLiteral(0, 0);
        zeroLiteral.type = syms.intType;

        // This is the field name used to access the allocation time of an
        // object
        allocSym = newVarSymbol(0, ALLOC_VAR, syms.intType, 0);
        allocIdent = newAuxIdent(allocSym, 0);

        terminationSym = newVarSymbol(0, TERMINATION_VAR, syms.intType, 0);

        /** This is the symbol to access the length of an array */
        lengthSym = syms.lengthVar;
        lengthIdent = newAuxIdent(lengthSym, 0);

    }

    /**
     * This class implements a map from variable (as a Symbol) to a unique name
     * as used in Single-Assignment form. At any given point in the program
     * there is a current mapping from symbols to names, giving the name that
     * holds the value for the symbol at that location. When a variable is
     * assigned a new value, it gets a new current Single-Assignment name and
     * the map is updated.
     * <P>
     * Each Symbol also has an incarnation number. The number is incremented as
     * new incarnations happen. The number is used to form the variables SA
     * name.
     */
    public class VarMap {
        // The maps allow VarSymbol or TypeSymbol (for TypeVar)
        private Map<VarSymbol, Integer>  map                   = new HashMap<VarSymbol, Integer>();

        private Map<TypeSymbol, Integer> maptypename           = new HashMap<TypeSymbol, Integer>();

        private Map<Symbol, Name>        mapn                  = new HashMap<Symbol, Name>();

        int                              everythingIncarnation = 0;

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
        public/* @Nullable */Name getName(VarSymbol vsym) {
            Name s = mapn.get(vsym);
            return s;
        }

        /**
         * Returns the name for a variable symbol as stored in this map,
         * creating (and storing) one if it is not present.
         */
        public/* @NonNull */Name getCurrentName(VarSymbol vsym) {
            Name s = mapn.get(vsym);
            if (s == null) {
                s = encodedName(vsym, everythingIncarnation);
                put(vsym, everythingIncarnation, s);
            }
            return s;
        }

        /** Returns the name for a class symbol as stored in this map */
        public Name getName(TypeSymbol vsym) {
            Name s = mapn.get(vsym);
            return s;
        }

        /**
         * Returns the name for a type symbol as stored in this map, creating
         * (and storing) one if it is not present.
         */
        public/* @NonNull */Name getCurrentName(TypeSymbol vsym) {
            Name s = mapn.get(vsym);
            if (s == null) {
                s = encodedName(vsym, everythingIncarnation);
                put(vsym, everythingIncarnation, s);
            }
            return s;
        }

        /** Returns the incarnation number for the symbol */
        public Integer get(VarSymbol vsym) {
            Integer i = map.get(vsym);
            if (i == null) {
                i = everythingIncarnation;
                map.put(vsym, i);
            }
            return i;
        }

        /** Returns the incarnation number for the type symbol */
        public Integer get(TypeSymbol vsym) {
            Integer i = maptypename.get(vsym);
            if (i == null) {
                i = everythingIncarnation;
                maptypename.put(vsym, i);
            }
            return i;
        }

        /** Stores a new incarnation of a symbol */
        public void put(VarSymbol vsym, Integer i, Name s) {
            map.put(vsym, i);
            mapn.put(vsym, s);
        }

        /** Stores a new incarnation of a symbol */
        public void put(TypeSymbol vsym, Integer i, Name s) {
            maptypename.put(vsym, i);
            mapn.put(vsym, s);
        }

        /** Adds everything in the argument map into the receiver's map */
        public void putAll(VarMap m) {
            map.putAll(m.map);
            maptypename.putAll(m.maptypename);
            mapn.putAll(m.mapn);
            everythingIncarnation = m.everythingIncarnation;
        }

        /**
         * Removes a symbol from the map, as when it goes out of scope or when a
         * temporary variable is no longer needed.
         */
        public Integer remove(Symbol v) {
            mapn.remove(v);
            return map.remove(v);
        }

        /**
         * Returns the Set of all variable Symbols that are in the map; note
         * that variables that are in scope but have not been used will not
         * necessarily be present in the map.
         */
        public Set<VarSymbol> keySet() {
            return map.keySet();
        }

        /** Returns a debug representation of the map */
        public String toString() {
            StringBuilder s = new StringBuilder();
            s.append("[");
            Iterator<Map.Entry<VarSymbol, Integer>> entries = map.entrySet()
                    .iterator();
            while (entries.hasNext()) {
                Map.Entry<VarSymbol, Integer> entry = entries.next();
                s.append(entry.getKey());
                s.append("=");
                s.append(entry.getValue());
                s.append(",");
            }
            Iterator<Map.Entry<TypeSymbol, Integer>> entriest = maptypename
                    .entrySet().iterator();
            while (entries.hasNext()) {
                Map.Entry<TypeSymbol, Integer> entry = entriest.next();
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

    /** Should not need this when everything is implemented */
    protected void notImpl(JCTree that) {
        log.noticeWriter.println("NOT IMPLEMENTED: BasicBlocker - "
                + that.getClass());
        result = trueLiteral;
    }

    /** Called by visit methods that should never be called. */
    protected void shouldNotBeCalled(JCTree that) {
        Log.instance(context).error(
                "esc.internal.error",
                "Did not expect to be calling a " + that.getClass()
                        + " within BasicBlocker");
        throw new JmlInternalError();
    }

    /**
     * Creates a translated expression whose value is the given type; the result
     * is a JML type, e.g. a representation of an instantiated generic.
     */
    protected JCExpression makeTypeLiteral(Type type, int pos) {
        return treeutils.trType(pos, type);
    }

    /**
     * This creates an (unprocessed) assignment and adds it to the given block.
     * This is appropriate for blocks that are being added to the todo list.
     * 
     * @param b
     *            block to which to add the new statement
     * @param pos
     *            the source position to use for the new expressions
     * @param lhs
     *            target of the assignment
     * @param rhs
     *            value of the assignment
     */
    protected void addAssignmentStatement(BasicBlock b, int pos,
            JCExpression lhs, JCExpression rhs) {
        JCAssign asg = factory.at(pos).Assign(lhs, rhs);
        asg.type = lhs.type;
        JCExpressionStatement exec = factory.at(pos).Exec(asg);
        exec.type = exec.expr.type; // This is probably not needed
        b.statements.add(exec);
    }

    /**
     * Creates an encoded name from a symbol and an incarnation position of the
     * form <symbol name>$<declaration position>$<use position>$<unique-id> If
     * the symbol has a negative declaration position, that value is not
     * included in the string
     * 
     * @param sym
     *            the symbol being given a logical name
     * @param incarnationPosition
     *            the incarnation position for which to give a new name
     * @return the new name
     */
    protected Name encodedName(VarSymbol sym, int incarnationPosition) {
        return names.fromString(sym.getQualifiedName()
                + (sym.pos < 0 ? "$" : ("$" + sym.pos + "$"))
                + incarnationPosition + "$" + (unique++));
    }

    // FIXME - review and document
    protected Name encodedName(TypeSymbol tp, int incarnationPosition) {
        return names.fromString(tp.name + "$" + incarnationPosition);
    }

    // FIXME - review and document
    protected Name encodedNameNoUnique(VarSymbol sym, int incarnationPosition) {
        return names.fromString(sym.getQualifiedName()
                + (sym.pos < 0 ? "$" : ("$" + sym.pos + "$"))
                + incarnationPosition);
    }

    /**
     * Creates an encoded name for a Type variable. There is no incarnation
     * position because type variables are not assigned after initialization.
     * 
     * @param sym
     * @param declarationPosition
     * @return a name for the given TypeSymbol
     */
    protected Name encodedTypeName(TypeSymbol sym, int declarationPosition) {
        return names.fromString(sym.flatName() + "$" + declarationPosition);
    }

    /**
     * Creates an encoded name from a symbol and an incarnation position of the
     * form <symbol name>$<declaration position>$<use position> Does not include
     * a unique id If the symbol has a negative declaration position, that value
     * is not included in the string
     * 
     * @param sym
     *            the symbol being given a logical name
     * @param incarnationPosition
     *            the incarnation position for which to give a new name
     * @return the new name
     */
    protected Name encodedName(MethodSymbol sym, int declpos,
            int incarnationPosition) {
        if (sym.name.toString().startsWith("makeTYPE")) return sym.name;
        return names.fromString(sym.getQualifiedName()
                + (declpos < 0 ? "$" : ("$" + declpos + "$"))
                + incarnationPosition);
    }

    /**
     * Creates an identifier nodes for a new incarnation of the variable, that
     * is, when the variable is assigned to.
     * 
     * @param id
     *            the old identifier, giving the root name, symbol and type
     * @param incarnationPosition
     *            the position (and incarnation number) of the new variable
     * @return the new identifier
     */
    protected JCIdent newIdentIncarnation(JCIdent id, int incarnationPosition) {
        return newIdentIncarnation((VarSymbol) id.sym, incarnationPosition);
    }

    /** Creates a new incarnation of a variable, with unique id added */
    protected JCIdent newIdentIncarnation(VarSymbol vsym,
            int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(
                encodedName(vsym, incarnationPosition));
        n.type = vsym.type;
        n.sym = vsym;
        currentMap.put(vsym, incarnationPosition, n.name);
        return n;
    }

    /**
     * Creates a new Ident node, but in this case we are not using the name from
     * the current incarnation map - so we supply the name. This is just used
     * for DSA assignments.
     */
    protected JCIdent newIdentUse(VarSymbol sym, Name name, int useposition) {
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }

    // FIXME - review and document
    protected JCIdent newIdentUse(VarMap map, VarSymbol sym, int useposition) {
        Name name = map.getCurrentName(sym); // Creates a name if ther has not
                                             // been one created yet
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }

    /**
     * Creates an identifier node for a use of a variable at a given source code
     * position; the current incarnation value is used
     * 
     * @param sym
     *            the underlying symbol (which gives the declaration location)
     * @param useposition
     *            the source position of its use
     * @return the new identifier
     */
    protected JCIdent newIdentUse(VarSymbol sym, int useposition) {
        Name name = currentMap.getCurrentName(sym);
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }

    // FIXME - review and document
    protected JCIdent newTypeIdentUse(TypeSymbol sym, int useposition) {
        Name name = currentMap.getCurrentName(sym);
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }

    /**
     * Creates a newly incarnated variable corresponding to the given
     * declaration. The incarnation number will be the position of the
     * declaration for some declarations, but not, for example, for a formal
     * argument of a method call - then it would be the position of the actual
     * parameter expression.
     * 
     * @param id
     *            the original declaration
     * @param incarnation
     *            the incarnation number to use
     * @return the new variable node
     */
    protected JCIdent newIdentIncarnation(JCVariableDecl id, int incarnation) {
        JCIdent n = factory.at(incarnation).Ident(
                encodedName(id.sym, incarnation));
        n.sym = id.sym;
        n.type = id.type;
        // FIXME - end information?
        currentMap.put(id.sym, incarnation, n.name);
        return n;
    }

    // FIXME - review and document
    protected JCIdent newIdentIncarnation(TypeSymbol id, int incarnation) {
        JCIdent n = factory.at(incarnation).Ident(encodedName(id, incarnation));
        n.sym = id;
        n.type = id.type;
        // FIXME - end information?
        currentMap.put(id, incarnation, n.name);
        return n;
    }

    // FIXME - review and document
    protected JCIdent newTypeVarIncarnation(TypeSymbol vsym,
            int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(
                encodedTypeName(vsym, incarnationPosition));
        n.type = JmlTypes.instance(context).TYPE;
        n.sym = vsym;
        currentMap.put(vsym, incarnationPosition, n.name);
        return n;
    }

    // FIXME - document
    protected JCIdent newArrayIncarnation(Type componentType, int usePosition) {
        JCIdent id = getArrayIdent(componentType);
        id = newIdentIncarnation((VarSymbol) id.sym, usePosition);
        // currentMap.put((VarSymbol)id.sym,Integer.valueOf(usePosition),id.name);
        return id;
    }

    /**
     * Creates an attributed, untranslated JCIdent and accompanying VarSymbol
     * using the given name and type; the given pos is used as the textual
     * position of the JCIdent node; also, if incarnations is true, pos is used
     * as the declaration position of the new identifier, with the implication
     * that additional incarnations will be defined later. The new Symbol has no
     * modifiers and no owner.
     * 
     * @param name
     *            the Name to use for the new symbol
     * @param type
     *            the type of the new symbol
     * @param pos
     *            the declaration position of the new symbol, if incarnations is
     *            true
     * @param incarnations
     *            whether there will be multiple incarnations of this symbol
     * @return a JCIdent tree node representing a use of the new symbol
     */
    protected JCIdent newAuxIdent(@NonNull String name, @NonNull Type type,
            int pos, boolean incarnations) {
        return newAuxIdent(names.fromString(name), type, pos, incarnations);
    }

    /**
     * Creates an attributed, untranslated JCIdent and accompanying VarSymbol
     * using the given name and type; the given pos is used as the textual
     * position of the JCIdent node; also, if incarnations is true, pos is used
     * as the declaration position of the new identifier, with the implication
     * that additional incarnations will be defined later. The new Symbol has no
     * modifiers and no owner.
     * 
     * @param name
     *            the Name to use for the new symbol
     * @param type
     *            the type of the new symbol
     * @param pos
     *            the declaration position of the new symbol, if incarnations is
     *            true
     * @param incarnations
     *            whether there will be multiple incarnations of this symbol
     * @return a JCIdent tree node representing a use of the new symbol
     */
    protected JCIdent newAuxIdent(@NonNull Name name, @NonNull Type type,
            int pos, boolean incarnations) {
        VarSymbol s = new VarSymbol(0, name, type, null);
        s.pos = incarnations ? pos : Position.NOPOS;
        return newAuxIdent(s, pos);
    }

    /**
     * Creates an attributed, untranslated JCIdent from the given VarSymbol; the
     * given pos is used as the textual position of the JCIdent node;
     * 
     * @param sym
     *            a VarSymbbol for which to generate a JCIdent AST node
     * @param pos
     *            the use position of the new tree node
     * @return a JCIdent tree node representing a use of the new symbol
     */
    protected JCIdent newAuxIdent(VarSymbol sym, int pos) {
        JCIdent id = factory.at(pos).Ident(sym.name);
        id.sym = sym;
        id.type = sym.type;
        return id;
    }

    /**
     * Creates a new VarSymbol with the given name and type and modifier flags
     * (and no owner); the declaration position is 'pos'.
     */
    protected VarSymbol newVarSymbol(long flags, @NonNull String name,
            @NonNull Type type, int pos) {
        // We leave the symbol's declaration position as Position.NOPOS (-1).
        VarSymbol v = new VarSymbol(flags, names.fromString(name), type, null);
        v.pos = pos;
        return v;
    }

    /**
     * Start the processing of the given block
     * 
     * @param b
     *            the block for which to initialize processing
     */
    protected void startBlock(@NonNull BasicBlock b) {
        // Check that all preceding blocks are actually completed
        // This is defensive programming and should not actually be needed
        // log.noticeWriter.println("Checking block " + b.id());
        loop: while (true) {
            for (BasicBlock pb : b.preceders) {
                // log.noticeWriter.println("   " + b.id() + " follows " +
                // pb.id());
                if (!blocksCompleted.contains(pb)) {
                    log.noticeWriter.println("Internal Error: block "
                            + pb.id.name + " precedes block " + b.id.name
                            + " , but was not processed before it");
                    processBlock(pb);
                    continue loop; // the list of preceding blocks might have
                                   // changed - check it over again
                }
            }
            break; // all preceding blocks were processed
        }
        // FIXME - replace this with some anonymous classes in OO fashion
        String nm = b.id.toString();
        if (nm.endsWith(FINALLY)) {
            // Once we are processing a finally block, all returns and throws
            // exit the finally block and go to whatever enclosing catch blocks
            // or try-return blocks there are.
            catchListStack.remove(0);
            tryreturnStack.remove(0);
        } else if (nm.endsWith(CATCHREST)) {
            // Once we are processing the catchrest block then all throws go
            // to the finally block, not to the catch blocks. So we adjust
            // the content of the top of the catchList stack, which visitThrow
            // uses to set the following blocks to the throw statement
            BasicBlock finallyBlock = tryreturnStack.get(0).followers().get(0);
            catchListStack.get(0).clear();
            catchListStack.get(0).add(finallyBlock);
        } else if (nm.endsWith(LOOPAFTER)) {
            loopStack.remove(0);
        }
        // log.noticeWriter.println("Starting block " + b.id);
        currentBlock = b;
        remainingStatements = currentBlock.statements;
        newstatements = currentBlock.statements = new ArrayList<JCStatement>();
        currentMap = initMap(currentBlock);
    }

    /**
     * Files away a completed block, adding it to the blocksCompleted list and
     * to the lookup Map.
     * 
     * @param b
     *            the completed block
     */
    protected void completed(@NonNull BasicBlock b) {
        if (b == null) return;
        blocksCompleted.add(b);
        blockmaps.put(b, currentMap);
        blockLookup.put(b.id.name.toString(), b);
        currentMap = null; // Defensive - so no inadvertent assignments
        // log.noticeWriter.println("Completed block " + b.id);
    }

    /**
     * Updates the data structures to indicate that the after block follows the
     * before block
     * 
     * @param before
     *            block that precedes after
     * @param after
     *            block that follows before
     */
    protected void follows(@NonNull BasicBlock before, @NonNull BasicBlock after) {
        before.followers.add(after);
        after.preceders.add(before);
    }

    /**
     * Updates the data structures to indicate that all the after blocks follow
     * the before block
     * 
     * @param before
     *            block that precedes after
     * @param after
     *            block that follows before
     */
    protected void follows(@NonNull BasicBlock before,
            @NonNull List<BasicBlock> after) {
        for (BasicBlock b : after) {
            before.followers.add(b);
            b.preceders.add(before);
        }
    }

    /**
     * Inserts the after block after the before block, replacing anything that
     * used to follow the before block
     * 
     * @param before
     * @param after
     */
    protected void replaceFollows(@NonNull BasicBlock before,
            @NonNull BasicBlock after) {
        for (BasicBlock b : before.followers) {
            b.preceders.remove(before);
        }
        before.followers.clear();
        follows(before, after);
    }

    /**
     * Inserts the after blocks after the before block, replacing anything that
     * used to follow the before block
     * 
     * @param before
     * @param after
     */
    protected void replaceFollows(@NonNull BasicBlock before,
            @NonNull List<BasicBlock> after) {
        for (BasicBlock b : before.followers) {
            b.preceders.remove(before);
        }
        before.followers.clear();
        for (BasicBlock b : after) {
            follows(before, b);
        }
    }

    /**
     * This utility method converts an expression from AST to BasicProgram form;
     * the method may have side-effects in creating new statements (in
     * newstatements). The returned expression node is expected to have
     * position, type and symbol information set.
     * 
     * @param expr
     *            the expression to convert
     * @return the converted expression
     */
    protected JCExpression trExpr(JCExpression expr) {
        if (expr == null) return null;
        expr.accept(this);
        return result;
    }

    /**
     * This utility method converts an expression from AST to BasicProgram form;
     * the argument is expected to be a spec-expression; the method may have
     * side-effects in creating new statements (in newstatements). The returned
     * expression node is expected to have position, type and symbol information
     * set.
     * 
     * @param expr
     *            the expression to convert
     * @param source
     *            the file containing the spec expression, since it might be
     *            different than the Java source
     * @return the converted expression
     */
    protected JCExpression trSpecExpr(JCExpression expr, JavaFileObject source) {
        if (expr == null) return null;
        if (inSpecExpression) {
            return trExpr(expr);
        } else {
            specMethodCalls.clear();
            boolean prevInSpecExpression = inSpecExpression;
            inSpecExpression = true;
            JavaFileObject prev = log.currentSourceFile();
            try {
                log.useSource(source);
                JCExpression result = trExpr(expr);
                return result;
            } finally {
                inSpecExpression = prevInSpecExpression;
                specMethodCalls.clear();
                log.useSource(prev);
            }
        }
    }

    // FIXME - comment - this is used to avoid recursive axiomatization of the
    // same method
    // it also serves to avoid repeated axiomatization of the same method within
    // one spec experession
    private Map<MethodSymbol, Name> specMethodCalls = new HashMap<MethodSymbol, Name>();

    // FIXME - review and document
    protected JCExpression trJavaExpr(JCExpression expr) {
        return trExpr(expr);
    }

    /**
     * Static entry point that converts an AST (the block of a method) into
     * basic block form
     * 
     * @param context
     *            the compilation context
     * @param tree
     *            the block of a method
     * @param denestedSpecs
     *            the specs of the method
     * @param classDecl
     *            the enclosing class
     * @return the resulting BasicProgram
     */
    public static @NonNull
    BasicProgram convertToBasicBlocks(@NonNull Context context,
            @NonNull JCMethodDecl tree, JmlMethodSpecs denestedSpecs,
            JCClassDecl classDecl) {
        BasicBlocker blocker = new BasicBlocker(context);
        return blocker.convertMethodBody(tree, denestedSpecs, classDecl);
    }

    /**
     * Returns a new, empty BasicBlock
     * 
     * @param name
     *            the name to give the block
     * @param pos
     *            a position to associate with the JCIdent for the block
     * @return the new block
     */
    protected @NonNull
    BasicBlock newBlock(@NonNull String name, int pos) {
        JCIdent id = newAuxIdent(name, syms.booleanType, pos, false);
        BasicBlock bb = new BasicBlock(id);
        blockLookup.put(id.name.toString(), bb);
        return bb;
    }

    /**
     * Returns a new, empty BasicBlock, but the new block takes all of the
     * followers of the given block; the previousBlock will then have no
     * followers.
     * 
     * @param name
     *            the name to give the block
     * @param pos
     *            a position to associate with the JCIdent for the block
     * @param previousBlock
     *            the block that is giving up its followers
     * @return the new block
     */
    protected @NonNull
    BasicBlock newBlock(@NonNull String name, int pos,
            @NonNull BasicBlock previousBlock) {
        JCIdent id = newAuxIdent(name, syms.booleanType, pos, false);
        BasicBlock bb = newBlock(id, previousBlock);
        blockLookup.put(id.name.toString(), bb);
        return bb;
    }
    
    public BasicBlock newBlock(JCIdent id, BasicBlock previousBlock) {
        BasicBlock nb = new BasicBlock(id);
        List<BasicBlock> s = nb.followers(); // empty, just don't create a new empty list
        nb.followers = previousBlock.followers();
        previousBlock.followers = s;
        for (BasicBlock f: nb.followers()) {
            f.preceders().remove(previousBlock);
            f.preceders().add(nb);
        }
        return nb;
    }


    /**
     * Converts the top-level block of a method into the elements of a
     * BasicProgram
     * 
     * @param methodDecl
     *            the method to convert to to a BasicProgram
     * @param denestedSpecs
     *            the specs of the method
     * @param classDecl
     *            the declaration of the containing class
     * @return the completed BasicProgram
     */
    protected @NonNull
    BasicProgram convertMethodBody(@NonNull JCMethodDecl methodDecl,
            JmlMethodSpecs denestedSpecs, @NonNull JCClassDecl classDecl) {
        this.methodDecl = (JmlMethodDecl) methodDecl;
        program = new BasicProgram(context);
        unique = 0;
        isConstructor = methodDecl.sym.isConstructor(); // FIXME - careful if
                                                        // there is nesting???
        isStatic = methodDecl.sym.isStatic();
        isHelper = utils.isHelper(methodDecl.sym);
        typesAdded = new HashSet<TypeSymbol>();
        int pos = methodDecl.pos;
        inSpecExpression = false;
        if (classDecl.sym == null) {
            log.error(
                    "jml.internal",
                    "The class declaration in BasicBlocker.convertMethodBody appears not to be typechecked");
            return null;
        }
        JmlClassInfo classInfo = getClassInfo(classDecl.sym);
        if (classInfo == null) {
            log.error("jml.internal", "There is no class information for "
                    + classDecl.sym);
            return null;
        }
        this.classInfo = classInfo;
        newdefs = new LinkedList<BasicProgram.Definition>();
        newpdefs = new LinkedList<JCExpression>();
        background = new LinkedList<JCExpression>();
        blocksToDo = new LinkedList<BasicBlock>();
        blocksCompleted = new ArrayList<BasicBlock>();
        blockLookup = new java.util.HashMap<String, BasicBlock>();

        thisId = newAuxIdent(THIS, methodDecl.sym.owner.type, pos, false);
        currentThisId = thisId;

        if (methodDecl.getReturnType() != null) {
            resultVar = newAuxIdent(RESULT, methodDecl.getReturnType().type, 0,
                    true);
        }
        terminationVar = newAuxIdent(terminationSym, 0);
        exceptionVar = newAuxIdent(EXCEPTION, syms.exceptionType, 0, true);
        heapVar = newAuxIdent(HEAP_VAR, syms.intType, 0, true); // FIXME - would
                                                                // this be
                                                                // better as its
                                                                // own
                                                                // uninterpreted
                                                                // type?
        assumeCheckCountVar = newAuxIdent(ASSUME_CHECK_COUNT, syms.intType, 0,
                false);
        assumeCheckCount = 0;

        JCBlock block = methodDecl.getBody();

        // Define the conditional return block
        condReturnBlock = newBlock(COND_RETURN_BLOCK_NAME, pos);
        JCExpression e = treeutils.makeBinary(pos, JCTree.GT, terminationVar,
                zeroLiteral);
        addUntranslatedAssume(0, Label.SYN, e, condReturnBlock.statements);

        // Define the return block
        returnBlock = newBlock(RETURN_BLOCK_NAME, pos);
        follows(condReturnBlock, returnBlock);

        // Define the conditional exception block
        condExceptionBlock = newBlock(COND_EXCEPTION_BLOCK_NAME, pos);
        e = treeutils.makeBinary(pos, JCTree.LT, terminationVar, zeroLiteral);
        // e will be translated when the assumption statement (incl.
        // terminationVar) is processed
        addUntranslatedAssume(0, Label.SYN, e, condExceptionBlock.statements);

        // Define the exception block
        exceptionBlock = newBlock(EXCEPTION_BLOCK_NAME, pos);
        follows(condExceptionBlock, exceptionBlock);

        // Define the start block
        BasicBlock startBlock = newBlock(START_BLOCK_NAME, pos);

        // Define the body block
        // Put all the program statements in the Body Block
        BasicBlock bodyBlock = newBlock(BODY_BLOCK_NAME, methodDecl.body.pos);
        e = treeutils.makeBinary(methodDecl.body.pos, JCTree.EQ,
                terminationVar, zeroLiteral);
        // e will be translated when the assumption statement (incl.
        // terminationVar) is processed
        addUntranslatedAssume(methodDecl.body.pos, Label.SYN, e,
                bodyBlock.statements);

        // Then the program
        bodyBlock.statements.addAll(block.getStatements());
        follows(startBlock, bodyBlock);
        follows(bodyBlock, returnBlock); // implicit, unconditional return

        // Put the blocks in the todo list (reverse order)
        blocksToDo.add(0, exceptionBlock);
        blocksToDo.add(0, condExceptionBlock);
        blocksToDo.add(0, returnBlock);
        blocksToDo.add(0, condReturnBlock);
        blocksToDo.add(0, bodyBlock);
        condition = trueLiteral;

        // Handle the start block a little specially
        // It does not have any statements in it
        startBlock(startBlock); // Start it so the currentMap is defined
        newIdentIncarnation(heapVar, 0);
        newIdentIncarnation(terminationSym, 0);
        newIdentIncarnation(exceptionVar, 0);
        newIdentIncarnation(allocSym, allocCount);
        currentMap.put(syms.lengthVar, 0, names.fromString(LENGTH)); // TODO:
                                                                     // Some
                                                                     // places
                                                                     // use
                                                                     // 'length'
                                                                     // without
                                                                     // encoding,
                                                                     // so we
                                                                     // store an
                                                                     // unencoded
                                                                     // name

        // FIXME - have to do static vars of super types also
        // FIXME - and all the model fields
        // FIXME - and all the fields of referenced classes
        // We have to create and store incarnations of class fields so that
        // there is a record of
        // them in the oldMap. Otherwise, if the variables are used within \old
        // later on, a new
        // identifier will be created, with a new unique number.
        for (JCTree tree : classInfo.decl.defs) {
            if (tree instanceof JCVariableDecl) {
                JCVariableDecl d = (JCVariableDecl) tree;
                newIdentIncarnation(d.sym, 0);
            }
        }
        if (!isStatic) {
            // TODO: thisId is not being translated here - will it be translated
            // in later uses?
            e = treeutils.makeNeqObject(methodDecl.body.pos, thisId,
                    nullLiteral);
            addAssume(methodDecl.body.pos, Label.SYN, e, startBlock.statements);
        }
//        addGlobalPreconditions(startBlock, (JmlMethodDecl) methodDecl,
//                (JmlClassDecl) classDecl);
        currentBlock = startBlock;
        for (JCVariableDecl decl : methodDecl.params) {
            toLogicalForm.put(decl, newIdentIncarnation(decl, decl.pos));
        }
        addPreconditions(methodDecl, denestedSpecs);
        checkAssumption(methodDecl.pos, Label.PRECONDITION);
        oldMap = currentMap.copy();
        completed(currentBlock);

        // Pick a block to do and process it
        while (!blocksToDo.isEmpty()) {
            processBlock(blocksToDo.remove(0));
        }
        addPostconditions(returnBlock, methodDecl, denestedSpecs);
        addExPostconditions(exceptionBlock, methodDecl, denestedSpecs);

        // Make the BasicProgram
        program.methodDecl = methodDecl;
        program.startId = startBlock.id;
        program.blocks.addAll(blocksCompleted);
        if (assumeCheck != null) booleanAssumeCheck = assumeCheck;
        program.definitions = newdefs;
        program.pdefinitions = newpdefs;
        program.background = background;
        program.assumeCheckVar = assumeCheckCountVar;

        // Find all the variables so they can be declared if necessary
        Set<JCIdent> vars = new HashSet<JCIdent>();
        for (BasicBlock bb : blocksCompleted) {
            VarFinder.findVars(bb.statements, vars);
        }
        for (BasicProgram.Definition def : newdefs) {
            VarFinder.findVars(def.id, vars);
            VarFinder.findVars(def.value, vars);
        }
        for (JCExpression ex : newpdefs) {
            VarFinder.findVars(ex, vars);
        }
        for (JCExpression ex : background) {
            VarFinder.findVars(ex, vars);
        }
        // Collection<JCIdent> decls = program.declarations;
        // Set<Name> varnames = new HashSet<Name>();
        // for (JCIdent id: vars) {
        // if (varnames.add(id.getName())) decls.add(id);
        // }
        program.toLogicalForm = toLogicalForm;
        return program;
    }

    /**
     * Does the conversion of a block with Java statements into basic program
     * form, possibly creating new blocks on the todo list
     * 
     * @param block
     *            the block to process
     */
    protected void processBlock(@NonNull BasicBlock block) {
        if (block.preceders.isEmpty()) {
            // Delete any blocks that do not follow anything
            for (BasicBlock b : block.followers) {
                b.preceders.remove(block);
            }
            return;// Don't add it to the completed blocks
        }
        startBlock(block);
        processBlockStatements(true);
    }

    /**
     * Iterates through the statements on the remainingStatements list,
     * processing them
     * 
     * @param complete
     *            call 'completed' on the currentBlock, if true
     */
    protected void processBlockStatements(boolean complete) {
        while (!remainingStatements.isEmpty()) {
            JCStatement s = remainingStatements.remove(0);
            condition = trueLiteral;
            if (s != null) s.accept(this); // A defensive check - statements in
                                           // the list should not be null
        }
        if (complete) completed(currentBlock);
    }

//    // FIXME - needs review and content and documentation!
//    protected void addGlobalPreconditions(@NonNull BasicBlock b,
//            @NonNull JmlMethodDecl tree, @NonNull JmlClassDecl classDecl) {
//        ClassCollector collector = ClassCollector.collect(classDecl, tree);
//        int d = 0;
//        // MethodSymbol distinct =
//        // makeFunction(names.fromString("distinct"),syms.intType,syms.classType);
//        // for (ClassSymbol csym : collector.classes) {
//        // // each class symbol is distinct
//        // JCLiteral id = makeTypeLiteral(csym.type,0);
//        // JCExpression e = makeFunctionApply(0,distinct,id);
//        // e = treeutils.makeBinary(JCTree.EQ,e,treeutils.makeLiteral(++d,0),0);
//        // addAssume(Label.IMPLICIT_ASSUME,trExpr(e),b.statements,false); //
//        // FIXME - track?
//        // }
//
//    }

    /**
     * Inserts assumptions corresponding to the preconditions into the given
     * block. Uses classInfo to get the class-level preconditions.
     * 
     * @param tree
     *            the method being translated
     * @param denestedSpecs
     *            the denested specs for that method
     */
    // FIXME - REVIEW and document
    protected void addPreconditions(@NonNull JCMethodDecl tree,
            @NonNull JmlMethodSpecs denestedSpecs) {

        JmlClassInfo utilsInfo = getClassInfo("org.jmlspecs.utils.Utils");
        if (utilsInfo != null) addClassPreconditions(utilsInfo, currentBlock); // FIXME
                                                                               // -
                                                                               // need
                                                                               // to
                                                                               // get
                                                                               // this
                                                                               // -
                                                                               // should
                                                                               // not
                                                                               // be
                                                                               // null
        JmlClassInfo info = getClassInfo("java.lang.Long"); // TODO - this
                                                            // should happen
                                                            // with the
                                                            // accumulated
                                                            // referenced
                                                            // classes
        if (info != null) addClassPreconditions(info, currentBlock);

        addClassPreconditions(classInfo, currentBlock);

        if (!tree.sym.isStatic()) {
            // \typeof(this) <: <currenttype>
            int pos = tree.pos;
            JCExpression e = makeThis(pos);
            e = makeTypeof(e);
            JCExpression lit = treeutils.trType(pos, classInfo.csym.type); // FIXME
                                                                           // -
                                                                           // not
                                                                           // necessarily
                                                                           // a
                                                                           // literal
            e = treeutils.makeJmlBinary(pos, JmlToken.SUBTYPE_OF, e, lit);
            e = trSpecExpr(e, log.currentSourceFile());
            addAssume(e.pos, Label.IMPLICIT_ASSUME, e, currentBlock.statements);
        }

        JCExpression expr = falseLiteral;
        MethodSymbol msym = tree.sym;
        JmlMethodInfo mi = getMethodInfo(msym);
        if (mi.requiresPredicates.size() == 0)
            expr = trueLiteral;
        else
            for (JmlMethodClauseExpr pre : mi.requiresPredicates) {
                JCExpression pexpr = trSpecExpr(pre.expression, pre.source());
                if (expr == falseLiteral)
                    expr = pexpr;
                else {
                    expr = treeutils.makeBinary(expr.pos, JCTree.BITOR, expr,
                            pexpr);
                }
            }
        expr.pos = expr.getStartPosition();

        addClassPredicate(classInfo.csym.type);

        JCIdent alloc = newIdentUse(allocSym, tree.pos);
        Iterator<JCVariableDecl> baseParams = tree.params.iterator();
        while (baseParams.hasNext()) {
            JCVariableDecl base = baseParams.next();
            if (!base.type.isPrimitive()) {
                int pos = base.pos;
                // for each reference parameter p: assume (p == null) || ((
                // \typeof(p) <: <statictype> ) && p.alloc < allocVar )
                // also add the class predicate for the argument type
                Type transType = trType(base.type); // Translated in case it is
                                                    // a type variable
                addClassPredicate(transType);
                JCIdent baseId = newIdentUse(base.sym, pos);
                // FIXME - set startpos
                JCExpression t = factory.at(pos)
                        .JmlMethodInvocation(
                                JmlToken.BSTYPEOF,
                                com.sun.tools.javac.util.List
                                        .<JCExpression> of(baseId));
                t.type = syms.classType;
                JCExpression lit = makeTypeLiteral(transType, pos);
                // FIXME - need subtypes for all of a parameters bounds
                JCExpression eq = treeutils.makeJmlBinary(pos,
                        JmlToken.SUBTYPE_OF, t, lit);

                // <newid>.alloc < <alloc>
                JCExpression ee = new JmlBBFieldAccess(allocIdent, baseId);
                ee.pos = pos;
                ee.type = syms.intType;
                ee = treeutils.makeBinary(pos, JCTree.LT, ee, alloc);

                eq = treeutils.makeBinary(pos, JCTree.AND, eq, ee);
                eq = treeutils.makeBinary(pos, JCTree.OR,
                        treeutils.makeEqObject(pos, baseId, nullLiteral), eq);

                eq = trSpecExpr(eq, null);
                addAssume(pos, Label.SYN, eq, currentBlock.statements);
            }
        }

        { // this is defined before the call
            JCExpression ee = new JmlBBFieldAccess(allocIdent, thisId);
            ee.pos = tree.pos;
            ee.type = syms.intType;
            ee = treeutils.makeBinary(tree.pos, JCTree.LT, ee, alloc);
            addAssume(ee.pos, Label.SYN, ee, currentBlock.statements);
        }

        // Need definedness checks? FIXME
        if (!isConstructor && !isStatic) {
            for (MethodSymbol m : getMethodInfo(msym).overrides) {
                expr = addMethodPreconditions(currentBlock, m, tree, tree.pos,
                        expr);
            }
        }

        if (mi.requiresPredicates.size() == 1) {
            JmlMethodClauseExpr pre = mi.requiresPredicates.get(0);
            addAssume(pre.pos, pre, Label.PRECONDITION, expr,
                    currentBlock.statements);
        } else {
            // FIXME - figure out how to highlight when there are multiple
            // preconditions
            addAssume(tree.pos, tree, Label.PRECONDITION, expr,
                    currentBlock.statements);
        }

    }

    // FIXME - REVIEW and document
    protected JCExpression addMethodPreconditions(@NonNull BasicBlock b,
            @NonNull MethodSymbol msym, @NonNull JCMethodDecl baseMethod,
            int pos, JCExpression expr) {

        // Note: msym, the MethodSymbol of an overridden method, always exists,
        // but if the super class it is in is only binary then msym.params is
        // null.
        // So instead we use mi.decl; it however is null if there are no specs.
        // However if there are no specs, there is nothing to do anyway. Also,
        // mi.decl will contain the parameter names used in the specs.

        // FIXME - argument names??? Will the pre and post names be different?
        JmlMethodInfo mi = getMethodInfo(msym);
        if (mi.decl == null) return trueLiteral;

        if (msym != baseMethod.sym) {
            addParameterMappings(baseMethod, mi.decl, pos, b);
        }

        for (JmlMethodClauseExpr req : mi.requiresPredicates) {
            JCExpression pre = req.expression;
            int p = (expr == null || expr.pos == 0) ? pre.getStartPosition()
                    : expr.pos;
            pre = trSpecExpr(pre, req.source());
            if (expr == null)
                expr = pre;
            else {
                expr = treeutils.makeBitOr(p, expr, pre);
                copyEndPosition(expr, pre);
            }
        }
        return expr;
    }

    // FIXME - REVIEW and document
    protected void addClassPreconditions(JmlClassInfo cInfo, BasicBlock b) {
        if (cInfo.superclassInfo != null) {
            addClassPreconditions(cInfo.superclassInfo, b);
        }
        JmlClassInfo prevClassInfo = classInfo;
        classInfo = cInfo; // Set the global value so trExpr calls have access
                           // to it
        try {
            // The axioms should perhaps be part of a class predicate? // FIXME
            for (JmlTypeClauseExpr ax : cInfo.axioms) {
                b.statements.add(comment(ax));
                JCExpression e = ax.expression;
                e = trSpecExpr(e, ax.source());
                addAssume(ax.pos, Label.INVARIANT, e, b.statements);
            }

            // For each type parameter T we need T != null and any bounds
            // expressions
            if (classInfo.decl != null) {
                for (JCTypeParameter t : classInfo.decl.typarams) {
                    b.statements.add(comment(t.pos,
                            "Type parameter " + t.getName()));
                    b.statements.add(comment(t.pos, t.type.tsym + " != null"));
                    JCIdent typeId = newTypeVarIncarnation(t.type.tsym, t.pos);
                    JCExpression e = treeutils.makeNeqObject(t.pos, typeId,
                            nullLiteral);
                    JmlStatementExpr asm = factory.JmlExpressionStatement(
                            JmlToken.ASSUME, Label.SYN,
                            trSpecExpr(e, classInfo.decl.sym.sourcefile));
                    asm.pos = t.pos;
                    b.statements.add(asm);

                    for (JCExpression ee : t.getBounds()) {
                        b.statements.add(comment(ee.pos, t.type.tsym + " <: "
                                + ee.type));
                        JCIdent id = newTypeIdentUse(t.type.tsym, t.pos);
                        JCExpression subtype = treeutils.makeJmlBinary(ee.pos,
                                JmlToken.SUBTYPE_OF, id,
                                treeutils.trType(ee.pos, ee.type));
                        JmlStatementExpr asmm = factory.JmlExpressionStatement(
                                JmlToken.ASSUME,
                                Label.SYN,
                                trSpecExpr(subtype,
                                        classInfo.decl.sym.sourcefile));
                        asmm.pos = t.pos;
                        b.statements.add(asmm);

                    }
                }
            }

            // For each field we need a type predicate: f == null || f.alloc <
            // allocVar
            for (Symbol d : cInfo.csym.members().getElements()) {
                if ((d instanceof VarSymbol) && !d.type.isPrimitive()) {
                    VarSymbol v = (VarSymbol) d;
                    if (utils.isJMLStatic(v)) {
                        declareAllocated(v, v.pos);
                    } else {
                        JCIdent id = newIdentUse(v, v.pos);
                        JCExpression e = new JmlBBFieldAccess(id, currentThisId);
                        e.pos = v.pos;
                        declareAllocated(e, v.pos);
                    }
                }
            }

            if (!isConstructor && !isHelper) {
                for (JmlTypeClauseExpr inv : cInfo.staticinvariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e, inv.source());
                    JmlStatementExpr asm = factory.JmlExpressionStatement(
                            JmlToken.ASSUME, Label.INVARIANT, e);
                    asm.pos = inv.getStartPosition();
                    copyEndPosition(asm, inv);
                    asm.source = inv.source;
                    b.statements.add(asm);
                }
                if (!isStatic) {
                    for (JmlTypeClauseExpr inv : cInfo.invariants) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e, inv.source());
                        JmlStatementExpr asm = factory.JmlExpressionStatement(
                                JmlToken.ASSUME, Label.INVARIANT, e);
                        asm.pos = inv.getStartPosition();
                        copyEndPosition(asm, inv);
                        asm.source = inv.source;
                        b.statements.add(asm);
                    }
                }
            }
        } finally {
            classInfo = prevClassInfo;
        }
    }

    // FIXME - REVIEW and document
    protected void addAssert(Label label, JCExpression that, int declpos,
            List<JCStatement> statements, int usepos, JavaFileObject source,
            JCTree statement) {
        if (Nowarns.instance(context)
                .suppress(source, usepos, label.toString())) return;
        if (useAssertDefinitions && label != Label.ASSUME_CHECK) {
            // if (extraEnv) { usepos++; declpos++; }
            String n;
            if (source == log.currentSourceFile()) {
                n = "assert$" + usepos + "$" + declpos + "$" + label + "$"
                        + (unique++);
            } else {
                Integer i = getIntForFile(source);
                n = "assert$" + usepos + "$" + declpos + "@" + i + "$" + label
                        + "$" + (unique++);
            }

            JCIdent id = newAuxIdent(n, syms.booleanType,
                    that.getStartPosition(), false);
            copyEndPosition(id, that); // FIXME - merge into the call above

            // JCExpression expr =
            // treeutils.makeBinary(that.pos,JCTree.EQ,id,that);
            // FIXME - start and end?
            BasicProgram.Definition stat = new BasicProgram.Definition(
                    statement.pos, id, that); // FIXME - if we keep this, should
                                              // use a factory
            newdefs.add(stat);
            that = id;
        }
        JmlTree.JmlStatementExpr st = factory.at(statement.pos)
                .JmlExpressionStatement(JmlToken.ASSERT, label, that);
        st.optionalExpression = null;
        st.source = source;
        st.associatedPos = declpos;
        st.type = null; // no type for a statement
        copyEndPosition(st, statement);
        statements.add(st);
    }

    public void copyEndPosition(JCTree newnode, JCTree srcnode) {
        Map<JCTree, Integer> z = log.currentSource().getEndPosTable();
        if (z != null && srcnode != null) { // srcnode can be null when
                                            // processing a switch statement
            int end = srcnode.getEndPosition(z);
            if (end != Position.NOPOS) z.put(newnode, end);
        }
    }

    /**
     * Adds an assertion with an untranslated expression to the given statement
     * list; it is presumed the statement will be translated later
     */
    protected void addUntranslatedAssert(Label label, JCExpression that,
            int declpos, List<JCStatement> statements, int usepos, /* @Nullable */
            JavaFileObject source) {
        JmlStatementExpr st;
        st = factory.at(usepos).JmlExpressionStatement(JmlToken.ASSERT, label,
                that);
        st.optionalExpression = null;
        st.source = source;
        st.associatedPos = declpos;
        st.type = null; // no type for a statement
        statements.add(st);
    }

    // FIXME - REVIEW and document
    /**
     * Adds an assertion to the given statement list; the expression is presumed
     * translated
     */
    protected void addAssertNoTrack(Label label, JCExpression that,
            List<JCStatement> statements, int usepos, /* @Nullable */
            JavaFileObject source) {
        JmlStatementExpr st;
        st = factory.at(usepos).JmlExpressionStatement(JmlToken.ASSERT, label,
                that);
        st.optionalExpression = null;
        st.type = null; // no type for a statement
        st.source = source;
        st.associatedPos = usepos;// FIXME - what should this be set to?
        statements.add(st);
    }

    /**
     * Adds a new assume statement to the end of the currentBlock; the assume
     * statement is given the declaration pos and label from the arguments; it
     * is presumed the input expression is translated, as is the produced assume
     * statement.
     * 
     * @param pos
     *            the declaration position of the assumption
     * @param label
     *            the kind of assumption
     * @param that
     *            the (translated) expression being assumed
     */
    protected void addAssume(int pos, Label label, JCExpression that) {
        addAssume(pos, label, that, currentBlock.statements);
    }

    /**
     * Adds a new assume statement to the end of the given statements list; the
     * assume statement is given the declaration pos and label from the
     * arguments; it is presumed the input expression is translated, as is the
     * produced assume statement.
     * 
     * @param pos
     *            the declaration position of the assumption
     * @param label
     *            the kind of assumption
     * @param that
     *            the (translated) expression being assumed
     * @param statements
     *            the list to add the new assume statement to
     */
    protected JmlStatementExpr addAssume(int pos, Label label,
            JCExpression that, List<JCStatement> statements) {
        factory.at(pos);
        JmlStatementExpr st;
        if (useAssumeDefinitions) {
            JCIdent id = factory.Ident(names.fromString(ASSUMPTION_PREFIX
                    + (unique++)));
            id.type = syms.booleanType;
            newdefs.add(new BasicProgram.Definition(that.pos, id, that)); // FIXME-
                                                                          // end
                                                                          // position?
            st = factory.JmlExpressionStatement(JmlToken.ASSUME, label, id);
        } else {
            st = factory.JmlExpressionStatement(JmlToken.ASSUME, label, that);
        }
        copyEndPosition(st, that);
        st.type = null; // statements do not have a type
        statements.add(st);
        return st;
    }

    protected JmlStatementExpr addAssume(int startpos, JCTree endpos,
            Label label, JCExpression that, List<JCStatement> statements) {
        if (startpos < 0) startpos = that.pos; // FIXME - temp
        factory.at(startpos);
        JmlStatementExpr st;
        if (useAssumeDefinitions) {
            JCIdent id = factory.Ident(names.fromString(ASSUMPTION_PREFIX
                    + (unique++)));
            id.type = syms.booleanType;
            newdefs.add(new BasicProgram.Definition(that.pos, id, that)); // FIXME-
                                                                          // start,
                                                                          // end
                                                                          // position?
            st = factory.JmlExpressionStatement(JmlToken.ASSUME, label, id);
        } else {
            st = factory.JmlExpressionStatement(JmlToken.ASSUME, label, that);
        }
        copyEndPosition(st, endpos);
        st.type = null; // statements do not have a type
        statements.add(st);
        return st;
    }

    /**
     * Adds a new UNTRANSLATED assume statement to the end of the given
     * statements list; the statements list should be a list of statements that
     * will be processed (and translated) at some later time; the assume
     * statement is given the declaration pos and label from the arguments; it
     * is presumed the input expression is untranslated, as is the produced
     * assume statement.
     * 
     * @param pos
     *            the declaration position of the assumption
     * @param label
     *            the kind of assumption
     * @param that
     *            the (untranslated) expression being assumed
     * @param statements
     *            the list to add the new assume statement to
     */
    protected JmlStatementExpr addUntranslatedAssume(int pos, Label label,
            JCExpression that, List<JCStatement> statements) {
        JmlStatementExpr st = factory.at(pos).JmlExpressionStatement(
                JmlToken.ASSUME, label, that);
        st.type = null; // statements do not have a type
        copyEndPosition(st, that);
        statements.add(st);
        return st;
    }

    protected JmlStatementExpr addUntranslatedAssume(int pos, JCTree posend,
            Label label, JCExpression that, List<JCStatement> statements) {
        JmlStatementExpr st = factory.at(pos).JmlExpressionStatement(
                JmlToken.ASSUME, label, that);
        st.type = null; // statements do not have a type
        copyEndPosition(st, posend);
        statements.add(st);
        return st;
    }

    /** Adds an axiom to the axiom set */
    protected void addAxiom(int pos, Label label, JCExpression that,
            List<JCStatement> statements) {
        newpdefs.add(that);
    }

    static public String encodeType(Type t) { // FIXME String? char? void?
                                              // unsigned?
        if (t instanceof ArrayType) {
            return "refA$" + encodeType(((ArrayType) t).getComponentType());
        } else if (!t.isPrimitive()) {
            return "REF";
        } else if (t.tag == TypeTags.INT || t.tag == TypeTags.SHORT
                || t.tag == TypeTags.LONG || t.tag == TypeTags.BYTE) {
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
    private Map<String, JCIdent> arrayIdMap = new HashMap<String, JCIdent>();

    // FIXME - review and document
    protected JCIdent getArrayIdent(Type componentType) {
        String s = "arrays$" + encodeType(componentType);
        JCIdent id = arrayIdMap.get(s);
        if (id == null) {
            id = factory.Ident(names.fromString(s));
            id.pos = 0;
            id.type = componentType;
            VarSymbol sym = new VarSymbol(0, id.name, id.type, null);
            sym.pos = 0;
            id.sym = sym;
            arrayIdMap.put(s, id);
        }
        id = newIdentUse((VarSymbol) id.sym, 0);
        return id;
    }

    /**
     * Creates a auxiliary variable and inserts an assumption about its value.
     * Any new generated statements are added into the currentBlock
     * 
     * @param name
     *            the name of the auxiliary variable, including any label and
     *            position encoding
     * @param type
     *            the type of the variable (e.g. syms.booleanType)
     * @param expr
     *            the (untranslated) value of the variable
     * @param makeDefinition
     * @param saveInMap
     * @return the variable corresponding the the given String argument
     */
    // FIXME - REVIEW and document
    // FIXME - modifies the content of currentBlock.statements
    protected @NonNull
    JCIdent addAuxVariable(@NonNull String name, @NonNull Type type,
            @NonNull JCExpression expr, boolean makeDefinition,
            boolean saveInMap) {
        JCExpression newexpr = trExpr(expr);
        int pos = expr.getPreferredPosition();
        JCIdent vd = newAuxIdent(name, type, pos, false);
        if (saveInMap) {
            currentMap.put((VarSymbol) vd.sym, pos, vd.name);
        }
        // FIXME - use a definition?
        if (makeDefinition) {
            // newdefs.add(treeutils.makeEquality(newexpr.pos,vd,newexpr));
            newdefs.add(new BasicProgram.Definition(newexpr.pos, vd, newexpr));
        } else {
            JmlTree.JmlStatementExpr asm = factory.at(pos)
                    .JmlExpressionStatement(JmlToken.ASSUME, Label.SYN,
                            treeutils.makeEquality(newexpr.pos, vd, newexpr));
            currentBlock.statements.add(asm);
        }
        return vd;
    }

    // FIXME - REVIEW and document
    protected void addPostconditions(BasicBlock b, JCMethodDecl decl,
            JmlMethodSpecs denestedSpecs) {
        int pos = decl.pos;
        currentBlock = b;
        currentMap = blockmaps.get(b);
        if (currentMap == null) return; // no normal return

        // checkAssumption(pos,Label.RETURN);

        JCIdent id = newIdentUse(terminationSym, 0);
        addAssume(0, Label.SYN,
                treeutils.makeBinary(0, JCTree.EQ, terminationVar, id));

        addMethodPostconditions(decl.sym, b, pos, decl);

        if (!isConstructor && !isStatic) {
            MethodSymbol msym = decl.sym;
            for (MethodSymbol m : getMethodInfo(msym).overrides) {
                addMethodPostconditions(m, b, pos, decl);
            }
        }

        // FIXME - reevaluate the last argument: this is the location that the
        // error message
        // indicates as where the assertion failed - it could be the return
        // statement, or the
        // ending close paren. But the only information we have at this point is
        // the preferred
        // location of the method declaration (unless we could get the ending
        // information).
        addClassPostconditions(classInfo, b, pos);

        // FIXME - this is wrong - we assume th OR of everything
    }

    // FIXME - REVIEW and document
    protected void addMethodPostconditions(MethodSymbol msym, BasicBlock b,
            int pos, JCMethodDecl baseMethod) {
        List<JCStatement> statements = b.statements;
        // Note: msym, the MethodSymbol of an overridden method, always exists,
        // but if the super class it is in is only binary then msym.params is
        // null.
        // So instead we use mi.decl; it however is null if there are no specs.
        // However if there are no specs, there is nothing to do anyway. Also,
        // mi.decl will contain the parameter names used in the specs.

        // FIXME - argument names??? Will the pre and post names be different?
        JmlMethodInfo mi = getMethodInfo(msym);
        if (mi.decl == null) return;
        if (msym != baseMethod.sym) {
            addParameterMappings(baseMethod, mi.decl, pos, b);
        }
        for (JmlMethodClauseExpr post : mi.ensuresPredicates) {
            addAssert(Label.POSTCONDITION,
                    trSpecExpr(post.expression, post.source()),
                    post.getStartPosition(), statements, pos, post.source(),
                    post);
        }
    }

    // FIXME - REVIEW and document
    protected void addExPostconditions(BasicBlock b, JCMethodDecl decl,
            JmlMethodSpecs denestedSpecs) {
        currentBlock = b;
        currentMap = blockmaps.get(b);
        if (currentMap == null) return; // no exceptions ever thrown

        JCIdent id = newIdentUse(terminationSym, 0);
        addAssume(0, Label.SYN,
                treeutils.makeBinary(0, JCTree.EQ, terminationVar, id));

        addMethodExPostconditions(decl.sym, b, decl.pos, decl);

        if (!isConstructor && !isStatic) {
            MethodSymbol msym = decl.sym;
            for (MethodSymbol m : getMethodInfo(msym).overrides) {
                addMethodExPostconditions(m, b, decl.pos, decl);
            }
        }
    }

    // FIXME - REVIEW and document
    protected void addMethodExPostconditions(MethodSymbol msym, BasicBlock b,
            int pos, JCMethodDecl baseMethod) {
        List<JCStatement> statements = b.statements;
        // Note: msym, the MethodSymbol of an overridden method, always exists,
        // but if the super class it is in is only binary then msym.params is
        // null.
        // So instead we use mi.decl; it however is null if there are no specs.
        // However if there are no specs, there is nothing to do anyway. Also,
        // mi.decl will contain the parameter names used in the specs.

        // FIXME - argument names??? Will the pre and post names be different?
        JmlMethodInfo mi = getMethodInfo(msym);
        if (mi.decl == null) return;
        if (msym != baseMethod.sym) {
            addParameterMappings(baseMethod, mi.decl, pos, b);
        }
        // signals/exsures predicates
        for (JmlMethodClauseExpr post : mi.exPredicates) {
            JCExpression ex = ((JmlBinary) post.expression).lhs;
            ex = ex instanceof JmlBinary ? ((JmlBinary) ex).lhs : null;
            ex = ex instanceof JmlMethodInvocation ? ((JmlMethodInvocation) ex).args
                    .get(0) : null;
            signalsVar = ex instanceof JCIdent ? (JCIdent) ex : null;
            addAssert(Label.SIGNALS,
                    trSpecExpr(post.expression, post.source()),
                    post.getStartPosition(), statements, post.pos,
                    post.source(), post);
            signalsVar = null;
        }
        // signals_only predicates
        for (JmlMethodClauseExpr post : mi.sigPredicates) {
            addAssert(Label.SIGNALS,
                    trSpecExpr(post.expression, post.source()),
                    post.getStartPosition(), statements, pos, post.source(),
                    post);
        }
    }

    // FIXME - REVIEW and document
    protected void addClassPostconditions(JmlClassInfo cInfo, BasicBlock b,
            int usepos) {
        if (cInfo.superclassInfo != null) {
            addClassPostconditions(cInfo.superclassInfo, b, usepos);
        }

        currentBlock = b;
        currentMap = blockmaps.get(b);
        List<JCStatement> statements = b.statements; // FIXME - also assign
                                                     // newstatements?
        if (!isHelper) {
            for (JmlTypeClauseExpr inv : cInfo.staticinvariants) {
                JCExpression e = inv.expression;
                e = trSpecExpr(e, inv.source());
                addAssert(Label.INVARIANT, e,
                        inv.expression.getStartPosition(), statements, usepos,
                        inv.source(), inv);
            }
            if (!isStatic) {
                for (JmlTypeClauseExpr inv : cInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e, inv.source());
                    addAssert(Label.INVARIANT, e,
                            inv.expression.getStartPosition(), statements,
                            usepos, inv.source(), inv);
                }
            }
            if (!isConstructor) {
                for (JmlTypeClauseConstraint inv : cInfo.staticconstraints) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e, inv.source());
                    addAssert(Label.CONSTRAINT, e,
                            inv.expression.getStartPosition(), statements,
                            usepos, inv.source(), inv);
                }
                if (!isStatic) {
                    for (JmlTypeClauseConstraint inv : cInfo.constraints) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e, inv.source());
                        addAssert(Label.CONSTRAINT, e,
                                inv.expression.getStartPosition(), statements,
                                usepos, inv.source(), inv);
                    }
                }
            } else {
                for (JmlTypeClauseExpr inv : cInfo.initiallys) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e, inv.source());
                    addAssert(Label.INITIALLY, e,
                            inv.expression.getStartPosition(), statements,
                            usepos, inv.source(), inv);
                }
            }
        }
    }

    Set<TypeSymbol> typesAdded = new HashSet<TypeSymbol>();

    // FIXME - REVIEW and document
    protected void addClassPredicate(Type type) {
        // FIXME - this appears to add the class predicate only once for a
        // generic type - is that OK?
        if (typesAdded.contains(type.tsym)) return;
        typesAdded.add(type.tsym);
        pushTypeArgs(type);
        // FIXME _ type can be a TypeVar and type.tsym a TypeSymbol that is not
        // a class Symbol
        if (type.tsym instanceof ClassSymbol) {
            TypeSymbol ts = ((ClassSymbol) type.tsym).getSuperclass().tsym;
            if (ts != null && ts.type.tag != TypeTags.NONE) {
                Type t = trType(ts.type);
                addClassPredicate(t);

                JCExpression lit0 = treeutils.makeDotClass(0, type);
                JCExpression e = treeutils.makeNeqObject(0, lit0, nullLiteral);
                background.add(trSpecExpr(e, null));

                JCExpression supertype = treeutils.makeDotClass(0, t);

                e = treeutils.makeJmlBinary(0, JmlToken.JSUBTYPE_OF, lit0,
                        supertype);
                background.add(trSpecExpr(e, null));

                e = treeutils.makeNeqObject(0, lit0, supertype);
                background.add(trSpecExpr(e, null));
                // FIXME - we need to state that all type literals are distinct
                // FIXME - need to have literals for generic types

                JCExpression lit1 = makeTypeLiteral(type, 0);
                JCExpression lit2 = makeTypeLiteral(t, 0);
                e = treeutils.makeJmlBinary(0, JmlToken.SUBTYPE_OF, lit1, lit2);
                if (lit1 != null && lit2 != null) e = trSpecExpr(e, null); // FIXME
                                                                           // -
                                                                           // guards
                                                                           // are
                                                                           // just
                                                                           // while
                                                                           // we
                                                                           // don't
                                                                           // have
                                                                           // all
                                                                           // literals
                                                                           // implemented
                background.add(e);
                e = treeutils.makeNeqObject(0, lit1, lit2);
                if (lit1 != null && lit2 != null) e = trSpecExpr(e, null); // FIXME
                                                                           // -
                                                                           // guards
                                                                           // are
                                                                           // just
                                                                           // while
                                                                           // we
                                                                           // don't
                                                                           // have
                                                                           // all
                                                                           // literals
                                                                           // implemented
                background.add(e);
                e = treeutils.makeJmlBinary(0, JmlToken.SUBTYPE_OF, lit2, lit1);
                e = treeutils.makeNot(0, e);
                if (lit1 != null && lit2 != null) e = trSpecExpr(e, null); // FIXME
                                                                           // -
                                                                           // guards
                                                                           // are
                                                                           // just
                                                                           // while
                                                                           // we
                                                                           // don't
                                                                           // have
                                                                           // all
                                                                           // literals
                                                                           // implemented
                background.add(e);

                // FIXME - we need to state that all type literals are distinct

                // FIXME - need to add everything else - e.g. invariants

            }
        } else {
            log.noticeWriter.println("adddClassPredicate not implemented for "
                    + type + " " + type.getClass());
        }
        popTypeArgs(type);
    }

    /**
     * This method returns the method symbol of the method in some superclass
     * that the argument overrides. It does not check interfaces.
     * 
     * @param msym
     *            the overriding method
     * @return the overridden method, or null if none
     */
    @Nullable
    protected MethodSymbol getOverrided(@NonNull MethodSymbol msym) {
        Types types = Types.instance(context);
        for (Type t = types.supertype(msym.owner.type); t.tag == CLASS; t = types
                .supertype(t)) {
            TypeSymbol c = t.tsym;
            Scope.Entry e = c.members().lookup(msym.name);
            while (e.scope != null) {
                if (msym.overrides(e.sym, (TypeSymbol) msym.owner, types, false)) {
                    return (MethodSymbol) e.sym;
                }
                e = e.next();
            }
        }
        return null;
    }

    /**
     * Adds assumptions to equate parameters of a overridden method with those
     * of an overriding method.
     * 
     * @param baseMethod
     *            the overriding method
     * @param otherMethod
     *            the overridden method
     * @param pos
     *            a position to use in creating new variable locations
     * @param b
     *            the block into which to add the assumptions
     */
    // FIXME - check that the names are different when a method is used in
    // multiple locations
    protected void addParameterMappings(@NonNull JCMethodDecl baseMethod,
            @NonNull JCMethodDecl otherMethod, int pos, BasicBlock b) {
        if (baseMethod == null) return; // FIXME - this happens on
                                        // <array>.clone() - any other time?
        Iterator<JCVariableDecl> baseParams = baseMethod.params.iterator();
        Iterator<JCVariableDecl> newParams = otherMethod.params.iterator();
        while (baseParams.hasNext()) {
            JCVariableDecl base = baseParams.next();
            JCVariableDecl newp = newParams.next();
            JCIdent baseId = newIdentUse(base.sym, pos);
            JCIdent newId = newIdentIncarnation(newp, 0);
            JCExpression eq = trSpecExpr(
                    treeutils.makeBinary(pos, JCTree.EQ, newId, baseId),
                    ((ClassSymbol) baseMethod.sym.owner).sourcefile);
            addAssume(pos, Label.SYN, eq, b.statements);
        }
    }

    // FIXME - REVIEW and document
    // FIXME - change to this use everywhere - sort out positions
    protected void addParameterMappings(@NonNull MethodSymbol baseMethod,
            @NonNull JCMethodDecl otherMethod, int pos, BasicBlock b) {
        Iterator<VarSymbol> baseParams = baseMethod.params.iterator();
        Iterator<JCVariableDecl> newParams = otherMethod.params.iterator();
        while (baseParams.hasNext()) {
            VarSymbol base = baseParams.next();
            JCVariableDecl newp = newParams.next();
            JCIdent baseId = newIdentUse(base, pos);
            JCIdent newId = newIdentIncarnation(newp, 0);
            JCExpression eq = trSpecExpr(
                    treeutils.makeEquality(pos, newId, baseId),
                    ((ClassSymbol) baseMethod.owner).sourcefile);
            addAssume(pos, Label.SYN, eq, b.statements);
        }
    }

    /**
     * This generates a comment statement (not in any statement list) whose
     * content is the given String.
     */
    public JmlStatementExpr comment(int pos, String s) {
        return factory.at(pos).JmlExpressionStatement(JmlToken.COMMENT, null,
                factory.Literal(s));
    }

    /**
     * This generates a comment statement (not in any statement list) whose
     * content is the given JCTree, pretty-printed.
     */
    public JmlStatementExpr comment(JCTree t) {
        return comment(t.pos, JmlPretty.write(t, false));
    }

    /**
     * Returns the initial VarMap of the given block; the returned map is a
     * combination of the maps from all preceding blocks, with appropriate DSA
     * assignments added.
     * 
     * @param block
     * @return the VarMap for the given block
     */
    protected VarMap initMap(BasicBlock block) {
        VarMap newMap = new VarMap();
        if (block.preceders.size() == 0) {
            // keep the empty one
        } else if (block.preceders.size() == 1) {
            newMap.putAll(blockmaps.get(block.preceders.get(0)));
        } else {
            // Here we do the DSA step of combining the results of the blocks
            // that precede
            // the block we are about to process. The situation is this: a
            // particular symbol,
            // sym say, may have been modified in any of the preceding blocks.
            // In each case
            // a new incarnation and a new identifier Name will have been
            // assigned. A record
            // of that current Identifer Name is in the VarMap for the block.
            // But we need a single
            // Name to use in this new block. SO we pick a Name (e.g. sym$k$nnn)
            // to use for the new block,
            // and for each preceding block we add an assumption of the form
            // sym$k$mmm = sym$k$nnn.
            // This assumption is added to the end of the preceding block.
            // We pick the name for the new block as the one with the maximum
            // incarnation number.
            // TODO: Note that it is not clear where to declare the identifier
            // for the new block.
            List<VarMap> all = new LinkedList<VarMap>();
            VarMap combined = new VarMap();
            int maxe = -1;
            for (BasicBlock b : block.preceders) {
                VarMap m = blockmaps.get(b);
                all.add(m);
                combined.putAll(m);
                if (maxe < m.everythingIncarnation)
                    maxe = m.everythingIncarnation;
            }
            combined.everythingIncarnation = maxe;
            for (VarSymbol sym : combined.keySet()) {
                Name maxName = null;
                int max = -1;
                for (VarMap m : all) {
                    Integer i = m.get(sym);
                    if (i > max) {
                        max = i;
                        maxName = m.getName(sym);
                    }
                }
                newMap.put(sym, max, maxName);

                for (BasicBlock b : block.preceders) {
                    VarMap m = blockmaps.get(b);
                    Integer i = m.get(sym);
                    if (i < max) {
                        // No position information for these nodes
                        // Type information put in, though I don't know that we
                        // need it
                        JCIdent pold = newIdentUse(m, sym, 0);
                        JCIdent pnew = newIdentUse(newMap, sym, 0);
                        JCBinary eq = treeutils.makeEquality(0, pnew, pold);
                        addUntranslatedAssume(0, Label.DSA, eq, b.statements);
                    }
                }
            }
        }
        return newMap;
    }

    /**
     * This class holds a summary of specification and other useful data about a
     * method. It is only used during BasicBlock, but it is computed and cached
     * on first request (within the compilation context). The
     * 'computeMethodInfo' call fills in the details.
     */
    static public class JmlMethodInfo {
        /** Creates an unitialized instance from a method declaration */
        public JmlMethodInfo(JCMethodDecl d, Context context) {
            this.decl = d;
            this.owner = d.sym;
            this.source = ((JmlMethodDecl) d).sourcefile;
            findOverrides(owner, context);
        }

        /** Creates an uninitialized instance from a method symbol */
        public JmlMethodInfo(MethodSymbol msym, Context context) {
            this.decl = null;
            this.owner = msym;
            this.source = null;
            findOverrides(owner, context);
        }

        /** The symbol for this method */
        MethodSymbol                        owner;

        /** The declaration for this method, if there is one */
        /* @Nullable */JCMethodDecl         decl;

        /** The JmlClassInfo stucture for the containing class */
        JmlClassInfo                        classInfo;

        /** The file in which the method is declared and implemented */
        JavaFileObject                      source;

        /**
         * The name used as the result of the method - filled in during
         * translation
         */
        String                              resultName;

        /** Whether the result is used - filled in during translation */
        boolean                             resultUsed         = false;

        // FIXME
        JCExpression                        exceptionDecl;

        VarSymbol                           exceptionLocal;

        /** A list of all the forall predicates */
        // FIXME - how interacts with spec cases
        java.util.List<JCVariableDecl>      foralls            = new LinkedList<JCVariableDecl>();

        /** A list of all the old predicates */
        // FIXME - how interacts with spec cases
        ListBuffer<JCVariableDecl>          olds               = new ListBuffer<JCVariableDecl>();

        /** A list of the one combined requires predicate */
        // FIXME - combined across inheritance?
        java.util.List<JmlMethodClauseExpr> requiresPredicates = new LinkedList<JmlMethodClauseExpr>();

        /**
         * A list of desugared ensures predicates (i.e. in the form
         * \old(precondition) ==> postcondition )
         */
        java.util.List<JmlMethodClauseExpr> ensuresPredicates  = new LinkedList<JmlMethodClauseExpr>();

        /**
         * A list of desugared signals predicates (i.e. in the form
         * \old(precondition) ==> postcondition )
         */
        java.util.List<JmlMethodClauseExpr> exPredicates       = new LinkedList<JmlMethodClauseExpr>();

        /**
         * A list of desugared signals_only predicates (i.e. in the form
         * \old(precondition) ==> postcondition )
         */
        java.util.List<JmlMethodClauseExpr> sigPredicates      = new LinkedList<JmlMethodClauseExpr>();

        /**
         * A list of desugared diverges predicates (i.e. in the form
         * \old(precondition) ==> postcondition )
         */
        java.util.List<JmlMethodClauseExpr> divergesPredicates = new LinkedList<JmlMethodClauseExpr>();

        /** A structure holding information about desugared assignable clauses */
        public static class Entry {
            public Entry(JCExpression pre, java.util.List<JCExpression> list) {
                this.pre = pre;
                this.storerefs = list;
            }

            /** The precondition guarding this list of assignables */
            // FIXME - with \old?
            public JCExpression                 pre;

            /** A list of storerefs for a particular spec case */
            public java.util.List<JCExpression> storerefs;
        }

        /** A list of assignable clause information */
        java.util.List<Entry>        assignables        = new LinkedList<Entry>();

        /** A list of overridden methods from super classes */
        java.util.List<MethodSymbol> overrides          = new LinkedList<MethodSymbol>();

        /** A list of overridden methods from super interfaces */
        java.util.List<MethodSymbol> interfaceOverrides = new LinkedList<MethodSymbol>();

        protected void findOverrides(MethodSymbol sym, Context context) {
            MethodSymbol msym = sym;
            Types types = Types.instance(context);
            for (Type t = types.supertype(msym.owner.type); t.tag == CLASS; t = types
                    .supertype(t)) {
                TypeSymbol c = t.tsym;
                Scope.Entry e = c.members().lookup(msym.name);
                while (e.scope != null) {
                    if (msym.overrides(e.sym, (TypeSymbol) msym.owner, types,
                            false)) {
                        msym = (MethodSymbol) e.sym;
                        if (msym != null) overrides.add(msym);
                        break;
                    }
                    e = e.next();
                }
            }

        }

    }

    // FIXME - meethodInfo objects are going to be recomputed for every instance
    // of BasicBlocker

    // FIXME - review and document
    Map<Symbol, JmlMethodInfo> methodInfoMap = new HashMap<Symbol, JmlMethodInfo>();

    // FIXME - review and document
    JmlMethodInfo getMethodInfo(MethodSymbol msym) {
        JmlMethodInfo mi = methodInfoMap.get(msym);
        if (mi == null) {
            mi = computeMethodInfo(msym);
            methodInfoMap.put(msym, mi);
        }
        return mi;
    }

    // FIXME - when run standalone (not in Eclipse), this method is called with
    // the Object constructor
    // as its argument, but with method.sym == null - is this because it is
    // Binary? is it not seeing the specs?
    protected JmlMethodInfo computeMethodInfo(MethodSymbol msym) {
        JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(msym);
        if (mspecs == null) {
            // The specs may be null because none were ever written (and there
            // was not even a declaration of the method to which an empty spec
            // was attached).
            mspecs = JmlSpecs.defaultSpecs(context,msym,0); // FIXME - review - argument was
                                               // null and used to work
        }
        // Note: The mspecs.decl may be null if the original class is only
        // binary and no specs file was written (so there is no source code
        // declaration anywhere).

        JmlMethodInfo mi = mspecs.cases.decl == null ? new JmlMethodInfo(msym,
                context) : new JmlMethodInfo(mspecs.cases.decl, context);
        JmlMethodSpecs denestedSpecs = msym == null ? null : specs
                .getDenestedSpecs(msym);
        if (JmlEsc.escdebug)
            log.noticeWriter.println("SPECS FOR " + msym.owner + " " + msym
                    + " " + (denestedSpecs != null));
        if (JmlEsc.escdebug)
            log.noticeWriter
                    .println(denestedSpecs == null ? "     No denested Specs"
                            : ("   " + denestedSpecs.toString())); // FIXME -
                                                                   // bad
                                                                   // indenting

        List<JCStatement> prev = newstatements;
        newstatements = new LinkedList<JCStatement>();
        if (denestedSpecs != null) {
            // preconditions
            JCExpression pre = denestedSpecs.cases.size() == 0 ? treeutils
                    .makeBooleanLiteral(mspecs.cases.decl == null ? 0
                            : mspecs.cases.decl.pos, true) : null;
            int num = 0;
            JavaFileObject source = null;
            for (JmlSpecificationCase spc : denestedSpecs.cases) {
                treetrans.pushSource(spc.sourcefile);
                if (source == null) source = spc.sourcefile;

                for (JmlMethodClause c : spc.clauses) {
                    if (c.token == JmlToken.FORALL) {
                        JmlMethodClauseDecl d = (JmlMethodClauseDecl) c;
                        for (JCVariableDecl stat : d.decls) {
                            JCVariableDecl newstat = treetrans.translate(stat);
                            mi.foralls.add(newstat);
                        }
                    } else if (c.token == JmlToken.OLD) {
                        JmlMethodClauseDecl d = (JmlMethodClauseDecl) c;
                        for (JCVariableDecl stat : d.decls) {
                            JCVariableDecl newstat = treetrans.translate(stat);
                            mi.olds.append(newstat);
                        }
                    }
                }
                JCExpression spre = null;
                for (JmlMethodClause c : spc.clauses) {
                    if (c.token == JmlToken.REQUIRES) {
                        num++;
                        JCExpression e = treetrans
                                .translate((((JmlMethodClauseExpr) c).expression));
                        e.pos = c.pos;
                        copyEndPosition(e, c); // FIXME - these lines should be
                                               // part of translate
                        if (spre == null) {
                            spre = e;
                        } else {
                            spre = treeutils.makeBinary(spre.pos, JCTree.AND,
                                    spre, e);
                            copyEndPosition(spre, e);
                        }
                    }
                }
                if (spre == null) {
                    spre = treeutils.makeBooleanLiteral(spc.pos, true);
                    copyEndPosition(spre, spc);
                }
                if (pre == null)
                    pre = spre;
                else {
                    pre = treeutils
                            .makeBinary(pre.pos, JCTree.BITOR, pre, spre);
                    copyEndPosition(pre, spre);
                }
                treetrans.popSource();
            }
            {
                JmlMethodClauseExpr p = factory.at(pre.pos)
                        .JmlMethodClauseExpr(JmlToken.REQUIRES, pre);
                p.sourcefile = source != null ? source : log
                        .currentSourceFile();
                if (num == 1) copyEndPosition(p, pre);
                mi.requiresPredicates.add(p); // Just one composite precondition
                                              // for all of the spec cases
            }

            // postconditions
            for (JmlSpecificationCase spc : denestedSpecs.cases) {
                JCExpression spre = null;
                for (JmlMethodClause c : spc.clauses) {
                    if (c.token == JmlToken.REQUIRES) {
                        if (spre == null) {
                            JCExpression cexpr = ((JmlMethodClauseExpr) c).expression;
                            spre = treetrans.translate((cexpr));
                            copyEndPosition(spre, cexpr); // FIXME _ included in
                                                          // translate?
                        } else {
                            int pos = spre.getStartPosition();
                            JCExpression cexpr = ((JmlMethodClauseExpr) c).expression;
                            spre = treeutils.makeBinary(pos, JCTree.AND, spre,
                                    treetrans.translate((cexpr)));
                            copyEndPosition(spre, cexpr);
                        }
                    }
                }
                if (spre == null) {
                    spre = treeutils.makeBooleanLiteral(Position.NOPOS, true);
                    // FIXME - fix position?
                }
                // FIXME - set startpos for JmlMethodInvocation
                JCExpression nspre = factory.at(spre.getStartPosition())
                        .JmlMethodInvocation(JmlToken.BSOLD,
                                com.sun.tools.javac.util.List.of(spre));
                copyEndPosition(nspre, spre);
                nspre.type = spre.type;
                spre = nspre;
                for (JmlMethodClause c : spc.clauses) {
                    if (c.token == JmlToken.ENSURES) {
                        JCExpression e = treetrans
                                .translate(((JmlMethodClauseExpr) c).expression);
                        copyEndPosition(e, ((JmlMethodClauseExpr) c).expression); // FIXME
                                                                                  // -
                                                                                  // fold
                                                                                  // into
                                                                                  // translate
                        JCExpression post = treeutils
                                .makeJmlBinary(e.getStartPosition(),
                                        JmlToken.IMPLIES, spre, e);
                        copyEndPosition(post, e);// FIXME - fold into translate;
                                                 // wathc out for different
                                                 // source files
                        JmlMethodClauseExpr p = factory.at(c.pos)
                                .JmlMethodClauseExpr(JmlToken.ENSURES, post);
                        p.sourcefile = c.source();
                        copyEndPosition(p, c);
                        int sp1 = post.getStartPosition();
                        int ep1 = post.getEndPosition(log.currentSource()
                                .getEndPosTable());
                        int sp2 = spre.getStartPosition();
                        int ep2 = spre.getEndPosition(log.currentSource()
                                .getEndPosTable());
                        int sp3 = e.getStartPosition();
                        int ep3 = e.getEndPosition(log.currentSource()
                                .getEndPosTable());
                        mi.ensuresPredicates.add(p);
                    } else if (c.token == JmlToken.ASSIGNABLE) {
                        JmlMethodClauseStoreRef mod = (JmlMethodClauseStoreRef) c;
                        // spre is the precondition under which the store-refs
                        // are modified
                        List<JCExpression> list = mod.list; // store-ref
                                                            // expressions
                        mi.assignables.add(new JmlMethodInfo.Entry(spre, list));
                    } else if (c.token == JmlToken.SIGNALS) {
                        // FIXME - what if there is no variable? - is there one
                        // already inserted or is it null?
                        JmlMethodClauseSignals mod = (JmlMethodClauseSignals) c;
                        JCExpression e = treetrans.translate(mod.expression);
                        copyEndPosition(e, mod.expression); // FIXME - fold into
                                                            // translate
                        boolean isFalse = (e instanceof JCLiteral)
                                && ((JCLiteral) e).value.equals(0);
                        // If vardef is null, then there is no declaration in
                        // the signals clause (e.g. it is just false).
                        // We use the internal \exception token instead; we
                        // presume the type is java.lang.Exception
                        JCExpression post = treeutils
                                .makeJmlBinary(e.getStartPosition(),
                                        JmlToken.IMPLIES, spre, e);
                        copyEndPosition(post, e);// FIXME - fold into translate;
                                                 // wathc out for different
                                                 // source files
                        if (!isFalse) {
                            if (mod.vardef != null) {
                                JCIdent id = treeutils.makeIdent(
                                        mod.vardef.pos, mod.vardef.sym);
                                e = makeNNInstanceof(id, c.pos,
                                        mod.vardef.type, mod.vardef.pos);
                                post = treeutils.makeJmlBinary(c.pos,
                                        JmlToken.IMPLIES, e, post);
                            } else {
                                JCExpression id = factory.at(c.pos)
                                        .JmlSingleton(JmlToken.BSEXCEPTION);
                                e = makeNNInstanceof(id, c.pos,
                                        syms.exceptionType, c.pos);
                                post = treeutils.makeJmlBinary(c.pos,
                                        JmlToken.IMPLIES, e, post);
                            }
                            copyEndPosition(post, mod.expression);
                        }
                        JmlMethodClauseExpr p = factory.at(c.pos)
                                .JmlMethodClauseExpr(JmlToken.SIGNALS, post);
                        copyEndPosition(p, c);
                        p.sourcefile = c.source();
                        // expression is pre ==> post
                        // or (\typeof(exVar) <: ExTYPE) ==> (pre ==> post)
                        mi.exPredicates.add(p);
                    } else if (c.token == JmlToken.DIVERGES) {
                        JCExpression e = treetrans
                                .translate(((JmlMethodClauseExpr) c).expression);
                        JCExpression post = treeutils
                                .makeJmlBinary(e.getStartPosition(),
                                        JmlToken.IMPLIES, spre, e);
                        JmlMethodClauseExpr p = factory.at(post.pos)
                                .JmlMethodClauseExpr(JmlToken.DIVERGES, post);
                        p.sourcefile = c.source();
                        mi.divergesPredicates.add(p);
                    } else if (c.token == JmlToken.SIGNALS_ONLY) {
                        JCExpression post = makeSignalsOnly((JmlMethodClauseSignalsOnly) c);
                        post = treeutils
                                .makeJmlBinary(post.getPreferredPosition(),
                                        JmlToken.IMPLIES, spre, post);
                        JmlMethodClauseExpr p = factory.at(post.pos)
                                .JmlMethodClauseExpr(JmlToken.SIGNALS, post);
                        p.sourcefile = c.source();
                        mi.sigPredicates.add(p);
                    }
                    // FIXME - is signals_only desugared or handled here?
                    // FIXME - we are ignoring forall old when duration
                    // working_space callable accessible measured_by captures
                }
            }
        }
        newstatements = prev;
        return mi;
    }

    // FIXME - review and document
    protected JCExpression makeTypeof(JCExpression e) {
        JCExpression typeof = factory.at(e.pos).JmlMethodInvocation(
                JmlToken.BSTYPEOF, e);
        typeof.type = syms.classType;
        return typeof;
    }

    // FIXME - review and document
    /** Makes a Java this parse tree node (attributed) */
    protected JCIdent makeThis(int pos) {
        return treeutils.makeIdent(pos, methodDecl._this);
    }

    // FIXME - review and document
    /**
     * Makes the equivalent of an instanceof operation: \typeof(e) <:
     * \type(type)
     */
    protected JCExpression makeNNInstanceof(JCExpression e, int epos,
            Type type, int typepos) {
        JCExpression e1 = makeTypeof(e);
        JCExpression e2 = makeTypeLiteral(type, typepos);
        if (inSpecExpression) e2 = trSpecExpr(e2, null);
        JCExpression ee = treeutils.makeJmlBinary(epos, JmlToken.SUBTYPE_OF,
                e1, e2);
        return ee;
    }

    // FIXME - review and document
    /**
     * Makes the equivalent of an instanceof operation: e !=null && \typeof(e)
     * <: \type(type)
     */
    protected JCExpression makeInstanceof(JCExpression e, int epos, Type type,
            int typepos) {
        JCExpression e1 = treeutils.makeNeqObject(epos, e, nullLiteral);
        JCExpression e2 = treeutils.makeJmlBinary(epos, JmlToken.SUBTYPE_OF,
                makeTypeof(e), makeTypeLiteral(type, typepos));
        if (inSpecExpression) e2 = trSpecExpr(e2, null);
        JCExpression ee = treeutils.makeBinary(epos, JCTree.AND, e1, e2);
        return ee;
    }

    // FIXME - review and document
    protected MethodSymbol makeFunction(Name name, Type resultType,
            Type... argTypes) {
        ListBuffer<Type> args = new ListBuffer<Type>().appendArray(argTypes);
        MethodType methodType = new MethodType(args.toList(), resultType,
                com.sun.tools.javac.util.List.<Type> nil(), syms.methodClass);
        MethodSymbol meth = new MethodSymbol(Flags.STATIC, name, methodType,
                null); // no owner
        return meth;
    }

    // FIXME - review and document
    protected JCExpression makeFunctionApply(int pos, MethodSymbol meth,
            JCExpression... args) {
        JCIdent methid = factory.at(pos).Ident(meth);
        JCExpression e = factory.at(pos).Apply(null, methid,
                new ListBuffer<JCExpression>().appendArray(args).toList());
        e.type = meth.getReturnType();
        return e;
    }

    // FIXME - review and document
    protected JCExpression makeSignalsOnly(JmlMethodClauseSignalsOnly clause) {
        JCExpression e = treeutils.makeBooleanLiteral(clause.pos, false);
        JCExpression id = factory.at(0).JmlSingleton(JmlToken.BSEXCEPTION);
        for (JCExpression typetree : clause.list) {
            int pos = typetree.getStartPosition();
            e = treeutils.makeBinary(pos, JCTree.OR,
                    makeNNInstanceof(id, pos, typetree.type, pos), e);
        }
        return e;
    }

    // STATEMENT NODES

    // Just process all the statements in the block prior to any other
    // remaining statements
    public void visitBlock(JCBlock that) {
        List<JCStatement> s = that.getStatements();
        if (s != null) remainingStatements.addAll(0, s);
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        currentBlock.statements.add(comment(that.pos, "while..."));
        visitLoopWithSpecs(that, null, that.cond, null, that.body,
                that.loopSpecs);
    }

    public void visitWhileLoop(JCWhileLoop that) {
        currentBlock.statements.add(comment(that.pos, "while..."));
        visitLoopWithSpecs(that, null, that.cond, null, that.body, null);
    }

    public void visitJmlForLoop(JmlForLoop that) {
        currentBlock.statements.add(comment(that.pos, "for..."));
        visitLoopWithSpecs(that, that.init, that.cond, that.step, that.body,
                that.loopSpecs);
    }

    public void visitForLoop(JCForLoop that) {
        currentBlock.statements.add(comment(that.pos, "for..."));
        visitLoopWithSpecs(that, that.init, that.cond, that.step, that.body,
                null);
    }

    // FIXME - review and document
    List<JCTree> loopStack = new LinkedList<JCTree>();

    /*
     * for (Init; Test; Update) S becomes LoopStart: - is actually the end of
     * the current Block Init; assert loop invariants [ goto LoopDo <<< if a do
     * while loop ] IF UNROLLING: compute loop condition goto LoopUnroll0,
     * LoopEnd LoopUnroll0: assume loop condition compute decreasing, check that
     * it is >= 0 S Update assert loop invariant check that decreasing has
     * decreased [ compute loop condition goto LoopUnroll1, LoopEnd LoopUnroll1:
     * assume loop condition compute decreasing, check that it is >= 0 S Update
     * assert loop invariant check that decreasing has decreased ] havoc any
     * loop modified variables assume loop invariants compute loop condition
     * (which may have side effects creating other statements) goto LoopBody,
     * LoopEnd LoopBody: assume loop condition value compute decreasing, check
     * that it is >= 0 S [ break -> LoopBreak; continue -> LoopContinue ] goto
     * LoopContinue LoopContinue: <-- all continues go here Update; assert loop
     * invariants check that decreasing is less LoopEnd: assume !(loop condition
     * value) goto LoopBreak LoopBreak: <-- all breaks go here //assert loop
     * invariants goto rest...
     */// FIXME - allow for unrolling

    protected void visitLoopWithSpecs(JCTree that, List<JCStatement> init,
            JCExpression test, List<JCExpressionStatement> update,
            JCStatement body, List<JmlStatementLoop> loopSpecs) {
        loopStack.add(0, that);
        int pos = that.pos;
        BasicBlock bloopBody = newBlock(blockPrefix + pos + LOOPBODY, pos);
        BasicBlock bloopContinue = newBlock(blockPrefix + pos + LOOPCONTINUE,
                pos);
        BasicBlock bloopEnd = newBlock(blockPrefix + pos + LOOPEND, pos);
        BasicBlock bloopBreak = newBlock(blockPrefix + pos + LOOPBREAK, pos);
        String restName = blockPrefix + pos + LOOPAFTER;
        blockLookup.put(bloopContinue.id.name.toString(), bloopContinue);
        blockLookup.put(bloopBreak.id.name.toString(), bloopBreak);

        // Now create an (unprocessed) block for everything that follows the
        // loop statement
        BasicBlock brest = newBlock(restName, pos, currentBlock);// it gets all
                                                                 // the
                                                                 // followers of
                                                                 // the current
                                                                 // block
        List<JCStatement> temp = brest.statements; // an empty list
        brest.statements = remainingStatements; // it gets all of the remaining
                                                // statements
        remainingStatements = temp;
        blocksToDo.add(0, brest); // push it on the front of the to do list

        // Finish out the current block with the loop initialization
        if (init != null) remainingStatements.addAll(init);
        processBlockStatements(false);

        // check the loop invariants (translated)
        addLoopInvariants(JmlToken.ASSERT, loopSpecs, that.getStartPosition(),
                currentBlock, Label.LOOP_INVARIANT_PRELOOP);

        // Now havoc any variables changed in the loop body
        {
            List<JCExpression> targets = TargetFinder.findVars(body, null);
            TargetFinder.findVars(test, targets);
            if (update != null) TargetFinder.findVars(update, targets);
            // synthesize a modifies list
            int wpos = body.pos + 1;
            // log.noticeWriter.println("HEAP WAS " + currentMap.get((VarSymbol)
            // heapVar.sym));
            newIdentIncarnation(heapVar, wpos);
            // log.noticeWriter.println("HEAP NOW " + currentMap.get((VarSymbol)
            // heapVar.sym) + " " + (wpos+1));
            for (JCExpression e : targets) {
                if (e instanceof JCIdent) {
                    newIdentIncarnation((JCIdent) e, wpos);
                    // } else if (e instanceof JCFieldAccess) {
                    // } else if (e instanceof JCArrayAccess) {

                } else {
                    // FIXME - havoc in loops
                    log.noticeWriter.println("UNIMPLEMENTED HAVOC IN LOOP "
                            + e.getClass());
                    // log.noticeWriter.flush();
                    throw new Utils.JmlNotImplementedException(null,
                            "UNIMPLEMENTED HAVOC IN LOOP " + e.getClass());
                }
            }
        }

        // assume the loop invariants (translated)
        addLoopInvariants(JmlToken.ASSUME, loopSpecs, that.getStartPosition(),
                currentBlock, Label.LOOP_INVARIANT);

        // compute the loop variants
        if (loopSpecs != null)
            for (JmlStatementLoop loopspec : loopSpecs) {
                if (loopspec.token == JmlToken.DECREASES) {
                    String dec = "$$decreases" + "$"
                            + loopspec.getStartPosition();
                    JCIdent id = addAuxVariable(
                            dec,
                            syms.longType,
                            trSpecExpr(loopspec.expression,
                                    log.currentSourceFile()), false, true);
                    loopspec.sym = (VarSymbol) id.sym;
                }
            }

        // compute the loop condition
        int testPos = test == null ? that.pos : test.getStartPosition();
        String loopTestVarName = "loopCondition" + "$" + testPos + "$"
                + testPos; // FIXME - end position?
        JCIdent loopTest = addAuxVariable(loopTestVarName, syms.booleanType,
                test == null ? trueLiteral : trJavaExpr(test), false, false);
        completed(currentBlock);
        BasicBlock bloopStart = currentBlock;
        follows(bloopStart, bloopBody);
        follows(bloopStart, bloopEnd);

        // Create and process the loop body block
        startBlock(bloopBody);

        // assume the loop condition (translated)
        addAssume(loopTest.pos, Label.LOOP, loopTest, bloopBody.statements);

        // check that the loop variants are not negative (translated)
        if (loopSpecs != null)
            for (JmlStatementLoop loopspec : loopSpecs) {
                if (loopspec.token == JmlToken.DECREASES) {
                    int p = loopspec.getStartPosition();
                    JCIdent v = newIdentUse(loopspec.sym, p); // FIXME -
                                                              // probably not
                                                              // the right use
                                                              // position
                    JCExpression e = treeutils.makeBinary(
                            p,
                            JCTree.GT,
                            v,
                            trSpecExpr(treeutils.makeIntLiteral(p, 0),
                                    log.currentSourceFile()));
                    addAssert(Label.LOOP_DECREASES_NEGATIVE, e, p,
                            currentBlock.statements, body.getStartPosition(),
                            log.currentSourceFile(), loopspec);
                }
            }

        // do the loop body - the loop body will continue to be processed after
        // we setup the remaining blocks for later processing
        remainingStatements.add(body);
        follows(bloopBody, bloopContinue);

        // Create an unprocessed loop continue block (untranslated)
        // do the update
        if (update != null) bloopContinue.statements.addAll(update);

        int end = endPos(body);
        if (end <= 0) {
            log.noticeWriter.println("BAD EBND");
        }
        // Check that loop invariants are still established
        addUntranslatedLoopInvariants(JmlToken.ASSERT, loopSpecs, end,
                bloopContinue, Label.LOOP_INVARIANT);
        // Check that loop variants are decreasing
        if (loopSpecs != null)
            for (JmlStatementLoop loopspec : loopSpecs) {
                if (loopspec.token == JmlToken.DECREASES) {
                    int p = loopspec.getPreferredPosition();
                    JCIdent v = newIdentUse(loopspec.sym, p); // FIXME -
                                                              // probably not
                                                              // the right use
                                                              // position
                    JCExpression newexpr = loopspec.expression;
                    JCExpression e = treeutils.makeBinary(
                            newexpr.getStartPosition(), JCTree.LT,
                            trSpecExpr(newexpr, log.currentSourceFile()), v);
                    addUntranslatedAssert(Label.LOOP_DECREASES, e,
                            loopspec.getStartPosition(),
                            bloopContinue.statements, end,
                            log.currentSourceFile()); // FIXME - track which
                                                      // continue is causing a
                                                      // problem?
                }
            }

        // Create the LoopEnd block (untranslated)
        follows(bloopEnd, bloopBreak);
        JCExpression neg = treeutils.makeUnary(loopTest.pos, JCTree.NOT,
                loopTest); // loopTest is already processed - but that is OK
                           // since it is just an auxiliary ident
        addUntranslatedAssume(neg.pos, Label.LOOP, neg, bloopEnd.statements);

        // Create the LoopBreak block (untranslated)
        follows(bloopBreak, brest);
        addUntranslatedLoopInvariants(JmlToken.ASSERT, loopSpecs, end + 1,
                bloopBreak, Label.LOOP_INVARIANT_ENDLOOP);

        // Push the blocks at the beginning of the todo list (in appropriate
        // order)
        blocksToDo.add(0, bloopBreak);
        blocksToDo.add(0, bloopEnd);
        blocksToDo.add(0, bloopContinue);

        // Go on to process the loopBody block
    }

    int endPos(JCTree t) {
        if (t instanceof JCBlock) {
            return ((JCBlock) t).endpos;
        } else if (t instanceof JCMethodDecl) {
            return endPos(((JCMethodDecl) t).body);
        } else {
            // FIXME - fix this sometime - we don't know the end position of
            // statements that are not blocks
            if (JmlEsc.escdebug) log.noticeWriter.println("UNKNOWN END POS");
            return t.pos;
        }
    }

    // FIXME - REVIEW and document
    protected void addLoopInvariants(JmlToken t,
            java.util.List<JmlStatementLoop> loopSpecs, int usepos,
            BasicBlock block, Label label) {
        if (loopSpecs == null) return;
        for (JmlStatementLoop loopspec : loopSpecs) {
            if (loopspec.token == JmlToken.LOOP_INVARIANT) {
                block.statements.add(comment(loopspec));
                JCExpression e = trSpecExpr(loopspec.expression,
                        log.currentSourceFile());
                if (t == JmlToken.ASSUME)
                    addAssume(e.pos, label, e, block.statements);
                else
                    addAssert(label, e, loopspec.getStartPosition(),
                            block.statements, usepos, log.currentSourceFile(),
                            loopspec);
            }
        }
    }

    // FIXME - REVIEW and document
    protected void addUntranslatedLoopInvariants(JmlToken t,
            java.util.List<JmlStatementLoop> loopSpecs, int usepos,
            BasicBlock block, Label label) {
        if (loopSpecs == null) return;
        for (JmlStatementLoop loopspec : loopSpecs) {
            if (loopspec.token == JmlToken.LOOP_INVARIANT) {
                block.statements.add(comment(loopspec));
                JCExpression e = loopspec.expression;
                if (t == JmlToken.ASSUME)
                    addUntranslatedAssume(usepos, label, e, block.statements);
                else
                    addUntranslatedAssert(label, e,
                            loopspec.getStartPosition(), block.statements,
                            usepos, log.currentSourceFile());
            }
        }
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        currentBlock.statements.add(comment(that.pos, "for..."));
        visitForeachLoopWithSpecs(that, that.loopSpecs);
    }

    public void visitForeachLoop(JCEnhancedForLoop that) {
        currentBlock.statements.add(comment(that.pos, "for..."));
        visitForeachLoopWithSpecs(that, null);
    }

    protected void visitForeachLoopWithSpecs(JCEnhancedForLoop that,
            com.sun.tools.javac.util.List<JmlStatementLoop> loopSpecs) {
        int pos = that.pos;
        if (that.expr.type.tag == TypeTags.ARRAY) {
            // for (T v; arr) S
            // becomes
            // for (int $$index=0; $$index<arr.length; $$index++) { v =
            // arr[$$index]; S }

            // make int $$index = 0; as the initialization
            // Name name = names.fromString("$$index$"+that.pos);
            // JCVariableDecl decl =
            // makeVariableDecl(name,syms.intType,treeutils.makeIntLiteral(0,pos),pos);
            JCVariableDecl decl = ((JmlEnhancedForLoop) that).indexDecl;
            JCVariableDecl vdecl = ((JmlEnhancedForLoop) that).indexDecl;
            com.sun.tools.javac.util.List<JCStatement> initList = com.sun.tools.javac.util.List
                    .<JCStatement> of(decl, vdecl);

            // make assume \values.size() == 0

            // make $$index < <expr>.length as the loop test
            JCIdent id = (JCIdent) factory.at(pos).Ident(decl);
            id.type = decl.type;
            JCExpression fa = factory.at(pos).Select(that.getExpression(),
                    syms.lengthVar);
            fa.type = syms.intType;
            JCExpression test = treeutils.makeBinary(pos, JCTree.LT, id, fa);

            // make $$index = $$index + 1 as the update list
            JCIdent idd = (JCIdent) factory.at(pos + 1).Ident(decl);
            id.type = decl.type;
            JCAssign asg = factory.at(idd.pos).Assign(
                    idd,
                    treeutils.makeBinary(idd.pos, JCTree.PLUS, id,
                            treeutils.makeIntLiteral(pos, 1)));
            asg.type = syms.intType;
            JCExpressionStatement update = factory.at(idd.pos).Exec(asg);
            com.sun.tools.javac.util.List<JCExpressionStatement> updateList = com.sun.tools.javac.util.List
                    .<JCExpressionStatement> of(update);

            // make <var> = <expr>[$$index] as the initialization of the target
            // and prepend it to the body
            JCArrayAccess aa = factory.at(pos)
                    .Indexed(that.getExpression(), id);
            aa.type = that.getVariable().type;
            JCIdent v = (JCIdent) factory.at(pos).Ident(that.getVariable());
            v.type = aa.type;
            asg = factory.at(pos).Assign(v, aa);
            asg.type = v.type;
            ListBuffer<JCStatement> newbody = new ListBuffer<JCStatement>();
            newbody.append(factory.at(pos).Exec(asg));
            newbody.append(that.body);

            // add 0 <= $$index && $$index <= <expr>.length
            // as an additional loop invariant
            JCExpression e1 = treeutils.makeBinary(pos, JCTree.LE,
                    treeutils.makeIntLiteral(pos, 0), id);
            JCExpression e2 = treeutils.makeBinary(pos, JCTree.LE, id, fa);
            JCExpression e3 = treeutils.makeBinary(pos, JCTree.AND, e1, e2);
            JmlStatementLoop inv = factory.at(pos).JmlStatementLoop(
                    JmlToken.LOOP_INVARIANT, e3);
            if (loopSpecs == null) {
                loopSpecs = com.sun.tools.javac.util.List
                        .<JmlStatementLoop> of(inv);
            } else {
                ListBuffer<JmlStatementLoop> buf = new ListBuffer<JmlStatementLoop>();
                buf.appendList(loopSpecs);
                buf.append(inv);
                loopSpecs = buf.toList();
            }
            visitLoopWithSpecs(that, initList, test, updateList,
                    factory.at(that.body.pos).Block(0, newbody.toList()),
                    loopSpecs);
        } else {
            notImpl(that); // FIXME
        }
    }

    public void visitDoLoop(JCDoWhileLoop that) {
        currentBlock.statements.add(comment(that.pos, "do..."));
        visitDoLoopWithSpecs(that, null);
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        currentBlock.statements.add(comment(that.pos, "do..."));
        visitDoLoopWithSpecs(that, that.loopSpecs);
    }

    // FIXME - rewview this
    /*
     * FOR A DO-WHILE LOOP do { S; } while (Test) becomes
     * 
     * LoopStart: - is actually the end of the current Block assert loop
     * invariants havoc any loop modified variables assume loop invariants
     * compute decreasing, check that it is >= 0 S [ break -> LoopBreak;
     * continue -> LoopContinue ] goto LoopContinue LoopContinue: <-- all
     * continues go here compute loop condition (which may have side effects
     * creating other statements) assert loop invariants check that decreasing
     * is less goto LoopEnd LoopEnd: assume !(loop condition value) goto
     * LoopBreak LoopBreak: <-- all breaks go here goto rest...
     */// FIXME - allow for unrolling
    protected void visitDoLoopWithSpecs(JCDoWhileLoop that,
            List<JmlStatementLoop> loopSpecs) {
        JCExpression test = that.getCondition();
        JCStatement body = that.getStatement();
        loopStack.add(0, that);
        int pos = that.pos;
        BasicBlock bloopStart = currentBlock;
        BasicBlock bloopContinue = newBlock(blockPrefix + pos + LOOPCONTINUE,
                pos);
        BasicBlock bloopEnd = newBlock(blockPrefix + pos + LOOPEND, pos);
        BasicBlock bloopBreak = newBlock(blockPrefix + pos + LOOPBREAK, pos);
        String restName = blockPrefix + pos + LOOPAFTER;

        // Create an (unprocessed) block for everything that follows the
        // loop statement
        BasicBlock brest = newBlock(restName, pos, currentBlock);// it gets all
                                                                 // the
                                                                 // followers of
                                                                 // the current
                                                                 // block
        List<JCStatement> temp = brest.statements;
        brest.statements = remainingStatements; // it gets all of the remaining
                                                // statements
        remainingStatements = temp;
        blocksToDo.add(0, brest); // push it on the front of the to do list

        // Back to the current block
        // test the loop invariants
        addLoopInvariants(JmlToken.ASSERT, loopSpecs, that.getStartPosition(),
                currentBlock, Label.LOOP_INVARIANT_PRELOOP);

        // Now havoc any variables changed in the loop
        {
            List<JCExpression> targets = TargetFinder.findVars(body, null);
            TargetFinder.findVars(test, targets);
            // synthesize a modifies list
            int wpos = body.pos;
            for (JCExpression e : targets) {
                if (e instanceof JCIdent) {
                    newIdentIncarnation((JCIdent) e, wpos);
                } else {
                    // FIXME - havoc in loops
                    log.noticeWriter.println("UNIMPLEMENTED HAVOC IN LOOP "
                            + e.getClass());
                    throw new JmlInternalError();
                }
            }
        }

        // assume the loop invariant
        addLoopInvariants(JmlToken.ASSUME, loopSpecs, that.getStartPosition(),
                currentBlock, Label.LOOP_INVARIANT);

        // Compute the loop variant and Check that the variant is not negative
        if (loopSpecs != null)
            for (JmlStatementLoop loopspec : loopSpecs) {
                if (loopspec.token == JmlToken.DECREASES) {
                    int p = loopspec.getStartPosition();
                    JCIdent v = newIdentUse(loopspec.sym, p);
                    JCExpression e = treeutils.makeBinary(p, JCTree.GE, v,
                            treeutils.makeIntLiteral(p, 0));
                    addAssert(Label.LOOP_DECREASES_NEGATIVE, e, p,
                            currentBlock.statements, body.getStartPosition(),
                            log.currentSourceFile(), loopspec); // FIXME - track
                                                                // which
                                                                // continue is
                                                                // causing a
                                                                // problem?
                }
            }
        // do the loop body
        remainingStatements.add(that.body);
        processBlockStatements(true);
        follows(bloopStart, bloopContinue);

        // Create a loop continue block
        startBlock(bloopContinue);
        processBlockStatements(false);
        // Compute the loop condition, with any side-effect
        String loopTestVarName = "forCondition" + "$" + test.getStartPosition()
                + "$" + test.getStartPosition(); // FIXME - end position?
        JCIdent loopTest = addAuxVariable(loopTestVarName, syms.booleanType,
                trJavaExpr(test), false, false);

        // Check that loop invariants are still established
        addLoopInvariants(JmlToken.ASSERT, loopSpecs, endPos(body),
                currentBlock, Label.LOOP_INVARIANT); // FIXME - use end
                                                     // position?

        // Check that loop variants are decreasing
        if (loopSpecs != null)
            for (JmlStatementLoop loopspec : loopSpecs) {
                if (loopspec.token == JmlToken.DECREASES) {
                    int p = loopspec.getPreferredPosition();
                    JCIdent id = newIdentUse(loopspec.sym, p);
                    JCExpression newexpr = trSpecExpr(loopspec.expression,
                            log.currentSourceFile());
                    JCExpression e = treeutils.makeBinary(
                            newexpr.getStartPosition(), JCTree.LT, newexpr, id);
                    addAssert(Label.LOOP_DECREASES, e,
                            loopspec.getStartPosition(),
                            currentBlock.statements, body.getStartPosition(),
                            log.currentSourceFile(), loopspec); // FIXME - track
                                                                // which
                                                                // continue is
                                                                // causing a
                                                                // problem?
                }
            }
        follows(bloopContinue, bloopEnd);
        completed(bloopContinue);

        // Create the LoopEnd block
        startBlock(bloopEnd);
        follows(bloopEnd, bloopBreak);
        JCExpression neg = treeutils.makeUnary(loopTest.pos, JCTree.NOT,
                loopTest);
        addUntranslatedAssume(loopTest.pos, Label.LOOP, neg,
                currentBlock.statements);
        completed(bloopEnd);

        // fill in the LoopBreak block
        startBlock(bloopBreak);
        follows(bloopBreak, brest);
        addLoopInvariants(JmlToken.ASSERT, loopSpecs, endPos(body),
                currentBlock, Label.LOOP_INVARIANT_ENDLOOP);
        completed(bloopBreak);

        currentBlock = null;
        newstatements = null;
        loopStack.remove(0);
    }

    public void visitLabelled(JCLabeledStatement that) {
        currentBlock.statements.add(comment(that.pos, that.label + ": ..."));
        JCTree target = that.getStatement();
        VarMap map = currentMap.copy();
        labelmaps.put(that.label, map);
        labelmapStatement.put(that.label, target);
        that.getStatement().accept(this);
        toLogicalForm.put(that, result);
    }

    // Translation of a switch statement
    // switch (swexpr) {
    // case A:
    // SA;
    // break;
    // case B:
    // SB;
    // // fall through
    // case C:
    // SC;
    // break;
    // default:
    // SD;
    // }
    // translates to
    // -- continuation of current block:
    // assume $$switchExpression$<pos>$<pos> == swexpr;
    // goto $$case$<A>,$$case$<B>,$$case$<C>
    // $$case$<A>:
    // assume $$switchExpression$<pos>$<pos> == A;
    // SA
    // goto $$BL$<pos>$switchEnd
    // $$case$<B>:
    // assume $$switchExpression$<pos>$<pos> == B;
    // SB
    // goto $$caseBody$<C>
    // $$case$<C>:
    // assume $$switchExpression$<pos>$<pos> == C;
    // goto $$caseBody$<C>
    // $$caseBody$<C>: // Need this block because B fallsthrough to C
    // SC
    // goto $$BL$<pos>$switchEnd
    // $$defaultcase$<C>:
    // assume !($$switchExpression$<pos>$<pos> == A && ...);
    // SD
    // goto $$BL$<pos>$switchEnd
    // $$BL$<pos>$switchEnd:
    // ....
    //
    // FIXME - review
    public void visitSwitch(JCSwitch that) {
        currentBlock.statements.add(comment(that.pos, "switch ..."));
        int pos = that.pos;
        JCExpression switchExpression = that.selector;
        int swpos = switchExpression.getStartPosition();
        List<JCCase> cases = that.cases;

        // Create the ending block name
        String endBlock = blockPrefix + pos + "$switchEnd";

        try {
            breakStack.add(0, that);

            // We create a new auxiliary variable to hold the switch value, so
            // we can track its value and so the subexpression does not get
            // replicated. We add an assumption about its value and add it to
            // list of new variables
            String switchName = "$switchExpression$" + pos;
            JCIdent vd = newAuxIdent(switchName, switchExpression.type, swpos,
                    false);
            JCExpression newexpr = treeutils.makeBinary(swpos, JCTree.EQ, vd,
                    switchExpression);
            copyEndPosition(newexpr, switchExpression);
            addAssume(swpos, switchExpression, Label.SWITCH_VALUE,
                    trJavaExpr(newexpr), currentBlock.statements);
            BasicBlock switchStart = currentBlock;

            // Now create an (unprocessed) block for everything that follows the
            // switch statement
            BasicBlock b = newBlock(endBlock, pos, currentBlock);// it gets all
                                                                 // the
                                                                 // followers of
                                                                 // the current
                                                                 // block
            List<JCStatement> temp = b.statements;
            b.statements = remainingStatements; // it gets all of the remaining
                                                // statements
            remainingStatements = temp;
            blocksToDo.add(0, b); // push it on the front of the to do list
            BasicBlock brest = b;

            // Now we need to make unprocessed blocks for all of the case
            // statements,
            // adding them to the todo list at the end
            // Note that there might be nesting of other switch statements etc.
            java.util.LinkedList<BasicBlock> blocks = new java.util.LinkedList<BasicBlock>();
            BasicBlock prev = null;
            JCExpression defaultCond = falseLiteral;
            JmlTree.JmlStatementExpr defaultAsm = null;
            for (JCCase caseStatement : cases) {
                JCExpression caseValue = caseStatement.getExpression();
                List<JCStatement> stats = caseStatement.getStatements();
                int casepos = caseStatement.getStartPosition();

                // create a block for this case test
                String caseName = blockPrefix
                        + caseStatement.getStartPosition() + "$case";
                if (caseValue == null)
                    caseName = blockPrefix + casepos + "$default";
                BasicBlock blockForTest = newBlock(caseName, casepos);
                blocks.add(blockForTest);
                follows(switchStart, blockForTest);

                // create the case test, or null if this is the default case
                JCBinary eq = caseValue == null ? null : treeutils.makeBinary(
                        caseValue.getStartPosition(), JCTree.EQ, vd,
                        trJavaExpr(caseValue));
                JmlStatementExpr asm = addUntranslatedAssume(caseStatement.pos,
                        Label.CASECONDITION, eq, blockForTest.statements);
                checkAssumption(caseStatement.pos, Label.CASECONDITION,
                        blockForTest.statements);

                // continue to build up the default case test
                if (caseValue == null)
                    defaultAsm = asm; // remember the assumption for the default
                                      // case
                else
                    defaultCond = treeutils.makeBinary(
                            caseValue.getStartPosition(), JCTree.OR, eq,
                            defaultCond);

                // determine whether this case falls through to the next
                boolean fallthrough = stats.isEmpty()
                        || !(stats.get(stats.size() - 1) instanceof JCBreak);

                if (prev == null) {
                    // statements can go in the same block
                    blockForTest.statements.addAll(stats);
                    if (!fallthrough) follows(blockForTest, brest);
                    prev = fallthrough ? blockForTest : null;
                } else {
                    // falling through from the previous case
                    // since there is fall-through, the statements need to go in
                    // their own block
                    String caseStats = "$caseBody$"
                            + caseStatement.getStartPosition(); // FIXME - is
                                                                // there certain
                                                                // to be a case
                                                                // statement
                    BasicBlock blockForStats = newBlock(caseStats,
                            caseStatement.getStartPosition());
                    blockForStats.statements.addAll(stats);
                    follows(blockForTest, blockForStats);
                    replaceFollows(prev, blockForStats);
                    follows(blockForStats, brest);
                    blocks.add(blockForStats);
                    prev = fallthrough ? blockForStats : null;
                }
            }
            if (prev != null) {
                // The last case statement did not appear to have a break
                // statement
                // Add a break, even if it does not necessarily need it (e.g. it
                // returns) // FIXME - test this
                follows(prev, brest);
            }
            int dpos = defaultAsm == null ? pos : defaultAsm.pos;
            JCExpression eq = treeutils
                    .makeUnary(dpos, JCTree.NOT, defaultCond);
            if (defaultAsm != null) {
                // There was a default case already made, but at the time we
                // just
                // put in null for the case condition, since we did not know it
                // yet (and we wanted to process the statements in textual
                // order).
                // So here we violate encapsulation a bit and poke it in.
                defaultAsm.expression = eq;
            } else {
                // There was no default - we need to construct an empty one
                // create a block for this case test
                String caseName = "$defaultcase$" + pos;
                BasicBlock blockForTest = newBlock(caseName, pos);
                blocks.add(blockForTest);
                follows(switchStart, blockForTest);
                follows(blockForTest, brest);

                addUntranslatedAssume(pos, Label.CASECONDITION, eq,
                        blockForTest.statements);
            }
            // push all of the blocks onto the to do list
            while (!blocks.isEmpty()) {
                blocksToDo.add(0, blocks.removeLast());
            }
            // continue on to complete the current block
        } finally {
            breakStack.remove(0); // FIXME - this is not going to work for
                                  // embedded breaks
        }

    }

    // Should never get here because case statements are handled in switch
    public void visitCase(JCCase that) {
        shouldNotBeCalled(that);
    }

    // FIXME - review and document
    protected java.util.List<BasicBlock>                 tryreturnStack = new java.util.LinkedList<BasicBlock>();

    // FIXME - review and document
    protected java.util.List<java.util.List<BasicBlock>> catchListStack = new java.util.LinkedList<java.util.List<BasicBlock>>();

    // This sets up a complicated arrangement of blocks
    //
    // currentBlock: try statement
    // rest of statements
    //
    // becomes
    //
    // currentBlock: try statement block
    // throw - goto catchBlocks
    // return - goto tryreturnBlock
    // goto finallyBlock
    //
    // tryreturnBlock: assume terminationVar > 0
    // goto finallyBlock
    //
    // catchBlocks: assume terminationVar < 0
    // assume condition on exception
    // reset terminationVar to 0
    // catch block statements
    // goto finallyBlock
    //
    // finallyBlock: any finally block statements
    // goto afterTryBlock, condExceptionBlock, condReturnBlock
    // [ if the try block is nested then instead we
    // goto afterTryBlock, catchBlocks of outer try, tryreturnBlock of outer
    // try]
    //
    // afterTryBlock: assume terminationVar == 0
    // rest of statements
    //
    //
    // FIXME - the catch blocks should use Java not JML subtype tests
    // FIXME - review
    public void visitTry(JCTry that) {
        currentBlock.statements.add(comment(that.pos, "try..."));

        // Create an (unprocessed) block for everything that follows the
        // try statement
        int pos = that.pos;
        BasicBlock brest = newBlock(blockPrefix + pos + "$afterTry", pos,
                currentBlock);// it gets all the followers of the current block

        // Add an initial assumption to the rest of the statements that the
        // program
        // is still executing normally (no return or throw has happened)
        JCExpression e = treeutils.makeBinary(pos, JCTree.EQ, terminationVar,
                zeroLiteral);
        addUntranslatedAssume(pos, Label.SYN, e, brest.statements);
        brest.statements.addAll(remainingStatements); // it gets all of the
                                                      // remaining statements
        blocksToDo.add(0, brest);
        remainingStatements.clear();
        remainingStatements.add(that.getBlock());

        // We make an empty finally block if the try statement does not
        // have one, just to simplify things
        String finallyBlockName = blockPrefix + pos + "$finally";
        BasicBlock finallyBlock = newBlock(finallyBlockName, pos);
        JCBlock finallyStat = that.getFinallyBlock();
        if (finallyStat != null) finallyBlock.statements.add(finallyStat); // it
                                                                           // gets
                                                                           // the
                                                                           // statements
                                                                           // of
                                                                           // the
                                                                           // finally
                                                                           // statement
        blocksToDo.add(0, finallyBlock); // push it on the front of the to do
                                         // list
        follows(currentBlock, finallyBlock);
        follows(finallyBlock, brest);
        if (tryreturnStack.isEmpty()) {
            follows(finallyBlock, condReturnBlock);
            follows(finallyBlock, condExceptionBlock);
        } else {
            follows(finallyBlock, tryreturnStack.get(0));
            follows(finallyBlock, catchListStack.get(0));
        }

        // We need a conditional finally block as the target of nested finally
        // blocks, to distinguish returns from exceptions from continued
        // execution

        String returnBlockName = blockPrefix + pos + "$tryreturn";
        BasicBlock tryreturnBlock = newBlock(returnBlockName, pos);
        // JCIdent tv = newIdentUse((VarSymbol)terminationVar.sym,pos);
        addUntranslatedAssume(pos, Label.SYN, treeutils.makeBinary(pos,
                JCTree.GT, terminationVar, zeroLiteral),
                tryreturnBlock.statements);
        tryreturnStack.add(0, tryreturnBlock);
        blocksToDo.add(0, tryreturnBlock); // push it on the front of the to do
                                           // list
        follows(tryreturnBlock, finallyBlock);

        // Now all the catch blocks
        // The expressions and assumptinos used here are prior to DSA processing
        List<BasicBlock> catchList = new LinkedList<BasicBlock>();
        int i = 0;
        // JCIdent ev = newIdentUse((VarSymbol)exceptionVar.sym,pos);
        JCExpression condtv = treeutils.makeBinary(pos, JCTree.AND, treeutils
                .makeBinary(pos, JCTree.LT, terminationVar, zeroLiteral),
                treeutils.makeNeqObject(pos, exceptionVar, nullLiteral));
        JCExpression cond = trueLiteral;
        for (JCCatch catcher : that.catchers) {
            // A catch block has these statements
            // assume <exception condition>
            // assume <catchVar> = <exceptionVar>
            // assign <terminationVar> = 0 -- once the exception is caught we
            // proceed normally
            // statements of the catch block
            int cpos = catcher.pos;
            String catchBlockName = blockPrefix + cpos + "$catch";
            BasicBlock catchBlock = newBlock(catchBlockName, cpos);

            addClassPredicate(catcher.param.vartype.type);
            JCExpression inst = makeNNInstanceof(exceptionVar, cpos,
                    catcher.param.type, cpos);
            addUntranslatedAssume(
                    catcher.param.getStartPosition(),
                    catcher.param,
                    Label.CATCH_CONDITION,
                    treeutils.makeBinary(cpos, JCTree.AND, condtv,
                            treeutils.makeBinary(cpos, JCTree.AND, cond, inst)),
                    catchBlock.statements);

            cond = treeutils.makeBinary(cpos, JCTree.AND, cond,
                    treeutils.makeUnary(cpos, JCTree.NOT, inst));

            // JCIdent id = newIdentUse(catcher.param.sym,cpos);
            JCIdent id = treeutils.makeIdent(cpos, catcher.param.sym);
            addAssignmentStatement(catchBlock, cpos, id, exceptionVar);

            id = newIdentUse((VarSymbol) terminationVar.sym, cpos);
            addAssignmentStatement(catchBlock, cpos, id, zeroLiteral);

            catchBlock.statements.add(catcher.getBlock()); // it gets all of the
                                                           // remaining
                                                           // statements
            follows(catchBlock, finallyBlock);
            catchList.add(catchBlock);
            blocksToDo.add(i++, catchBlock); // push it on the to do list
        }
        // If there are any catch blocks then we need one final catch block for
        // the
        // case that no other blocks have caught the exception. This block may
        // not be feasible.
        // We also make the block even if there are no catch blocks so that we
        // know
        // when the catch blocks have been processed. This is a bit tricky.
        {
            String catchBlockName = blockPrefix + that.pos + "$catchrest";
            BasicBlock catchBlock = newBlock(catchBlockName, that.pos);
            addUntranslatedAssume(pos, Label.SYN,
                    treeutils.makeBinary(pos, JCTree.AND, condtv, cond),
                    catchBlock.statements); // Do not track
            follows(catchBlock, finallyBlock);
            blocksToDo.add(0, catchBlock); // push it on the to do list, before
                                           // the others
            catchList.add(catchBlock);
        }
        catchListStack.add(0, catchList);

        // Finish the processing of the current block
        processBlockStatements(false);
    }

    // Should not get here because catch statements are handled with the try
    // statement
    public void visitCatch(JCCatch that) {
        shouldNotBeCalled(that);
    }

    public void visitIf(JCIf that) {
        currentBlock.statements.add(comment(that.pos, "if..."));
        int pos = that.pos;
        // Create a bunch of block names
        String thenName = blockPrefix + pos + THENSUFFIX;
        String elseName = blockPrefix + pos + ELSESUFFIX;
        String restName = blockPrefix + pos + AFTERIF;

        // We create a new auxiliary variable to hold the branch condition, so
        // we can track its value and so the subexpression does not get
        // replicated. We add an assumption about its value and add it to
        // list of new variables
        String condName = BRANCHCONDITION_PREFIX + pos;
        JCIdent vd = newAuxIdent(condName, syms.booleanType, pos, true);
        currentMap.put((VarSymbol) vd.sym, pos, vd.sym.name); // FIXME - fold
                                                              // this into a
                                                              // newAuxIdent
                                                              // call?
        JCExpression newexpr = treeutils.makeBinary(that.cond.pos, JCTree.EQ,
                vd, that.cond);
        addAssume(pos, that, Label.BRANCHC, trJavaExpr(newexpr),
                currentBlock.statements);

        // Now create an (unprocessed) block for everything that follows the
        // if statement
        BasicBlock b = newBlock(restName, pos, currentBlock);// it gets all the
                                                             // followers of the
                                                             // current block
        List<JCStatement> temp = b.statements;
        b.statements = remainingStatements; // it gets all of the remaining
                                            // statements
        remainingStatements = temp;
        blocksToDo.add(0, b); // push it on the front of the to do list
        BasicBlock brest = b;

        // Now make the else block, also unprocessed
        b = newBlock(elseName, pos);
        JCExpression c = treeutils.makeUnary(pos, JCTree.NOT, vd);
        JmlTree.JmlStatementExpr t = factory.at(that.cond.pos + 1)
                .JmlExpressionStatement(JmlToken.ASSUME, Label.BRANCHE, c);
        copyEndPosition(t, that.cond);
        b.statements.add(t);
        if (that.elsepart != null) b.statements.add(that.elsepart);
        blocksToDo.add(0, b);
        follows(b, brest);
        follows(currentBlock, b);

        // Now make the then block, also still unprocessed
        b = newBlock(thenName, pos);
        c = vd;
        t = factory.at(that.cond.pos).JmlExpressionStatement(JmlToken.ASSUME,
                Label.BRANCHT, c);
        copyEndPosition(t, that.cond);
        b.statements.add(t);
        b.statements.add(that.thenpart);
        blocksToDo.add(0, b);
        follows(b, brest);
        follows(currentBlock, b);
    }

    public void visitExec(JCExpressionStatement that) {
        currentBlock.statements.add(comment(that));
        // This includes assignments and stand-alone method invocations
        that.expr.accept(this);
        // ignore the result; any statements are already added
    }

    // FIXME - review and document
    protected java.util.List<JCStatement> breakStack = new java.util.LinkedList<JCStatement>();

    // FIXME - needs review
    public void visitBreak(JCBreak that) {
        currentBlock.statements.add(comment(that));
        if (breakStack.isEmpty()) {
            // ERROR - FIXME
        } else if (breakStack.get(0) instanceof JCSwitch) {
            // Don't need to do anything. If the break is not at the end of a
            // block,
            // the compiler would not have passed this. If it is at the end of a
            // block
            // the logic in handling JCSwitch has taken care of everything.

            // FIXME - for safety, check and warn if there are any remaining
            // statements in the block
        } else if (that.label == null) {
            JCTree t = loopStack.get(0);
            String s = blockPrefix + t.pos + "$LoopBreak";
            BasicBlock b = blockLookup.get(s);
            if (b == null)
                log.noticeWriter.println("NO BREAK BLOCK: " + s);
            else
                replaceFollows(currentBlock, b);
        } else {
            Log.instance(context).error("esc.not.implemented",
                    "break statements with labels in BasicBlocker");
        }
    }

    // FIXME - review with loops
    public void visitContinue(JCContinue that) {
        currentBlock.statements.add(comment(that));
        if (that.label == null) {
            JCTree t = loopStack.get(0);
            String blockName = blockPrefix + t.pos + LOOPCONTINUE;
            BasicBlock b = blockLookup.get(blockName);
            if (b == null)
                log.noticeWriter.println("NO CONTINUE BLOCK: " + blockName);
            else
                replaceFollows(currentBlock, b);
        } else {
            Log.instance(context).warning("esc.not.implemented",
                    "continue statements with labels in BasicBlocker");
        }
    }

    // FIXME - review
    public void visitReturn(JCReturn that) {
        currentBlock.statements.add(comment(that));
        if (that.getExpression() != null) {
            int p = that.getExpression().getStartPosition();
            JCExpression res = treeutils.makeEquality(p, resultVar,
                    trJavaExpr(that.getExpression())); // resultVar is not
                                                       // translated - shoudl be
                                                       // incase there are
                                                       // multiple returns
                                                       // executed FIXME
            addAssume(TreeInfo.getStartPos(that), that, Label.ASSIGNMENT, res,
                    currentBlock.statements);
        }
        int pos = that.getStartPosition();
        JCIdent id = newIdentIncarnation(terminationVar, pos);
        JCLiteral lit = treeutils.makeIntLiteral(pos, pos);
        JCExpression e = treeutils.makeBinary(pos, JCTree.EQ, id, lit);
        addAssume(pos, that, Label.RETURN, e, currentBlock.statements);
        if (tryreturnStack.isEmpty()) {
            replaceFollows(currentBlock, returnBlock);
        } else {
            BasicBlock finallyBlock = tryreturnStack.get(0);
            replaceFollows(currentBlock, finallyBlock);
        }
        if (!remainingStatements.isEmpty()) {
            // Not fatal
            Log.instance(context).warning("esc.internal.error",
                    "Unexpected statements following a return statement");
        }
    }

    // FIXME - review
    public void visitThrow(JCThrow that) {
        currentBlock.statements.add(comment(that));

        // Capture the exception expression
        int p = that.getExpression().getStartPosition();
        JCExpression res = trJavaExpr(that.getExpression());
        JCIdent idex = newIdentIncarnation(exceptionVar, p);
        JCExpression now = treeutils.makeEqObject(p, idex, res);
        addAssume(TreeInfo.getStartPos(that), Label.ASSIGNMENT, now); // <exceptionVar>
                                                                      // =
                                                                      // <throw-expression>

        int pos = that.getStartPosition();
        JCIdent id = newIdentIncarnation(terminationVar, pos);
        JCLiteral lit = treeutils.makeIntLiteral(pos, -pos);
        JCExpression expr = treeutils.makeBinary(pos, JCTree.EQ, id, lit);
        addAssume(TreeInfo.getStartPos(that), Label.SYN, expr); // <terminationVar>
                                                                // = -pos

        // FIXME - if we are already in a catch block we keep the finally block
        // as our follower.

        if (catchListStack.isEmpty()) {
            replaceFollows(currentBlock, exceptionBlock);
        } else {
            List<BasicBlock> catchList = catchListStack.get(0);
            if (catchList.isEmpty()) {
                replaceFollows(currentBlock, tryreturnStack.get(0)); // followed
                                                                     // by the
                                                                     // finally
                                                                     // block
            } else {
                replaceFollows(currentBlock, catchList); // followed by all the
                                                         // catch blocks
            }
        }
        // If the tryStack is not empty, the following blocks have already
        // been setup in visitTry, to go to either the set of catch blocks
        // (if there are any) or to the finally block

        if (!remainingStatements.isEmpty()) {
            // Not fatal
            Log.instance(context).warning("esc.internal.error",
                    "Unexpected statements following a throw statement");
        }
    }

    public void visitAssert(JCAssert that) { // This is a Java assert statement
        currentBlock.statements.add(comment(that));
        JCExpression cond = trJavaExpr(that.cond);
        JCExpression detail = trJavaExpr(that.detail);
        // FIXME - what to do with detail
        // FIXME - for now turn cond into a JML assertion
        // FIXME - need a label for the assert statement
        // FIXME - set line and source
        addAssert(Label.EXPLICIT_ASSERT, cond, that.cond.getStartPosition(),
                newstatements, that.cond.getStartPosition(),
                log.currentSourceFile(), that);
    }

    // FIXME - needs review
    public void visitApply(JCMethodInvocation that) {
        // This is an expression so we just use trExpr
        JCExpression now;
        JCExpression obj;
        MethodSymbol msym;
        Type.ForAll tfa = null;
        if (that.meth instanceof JCIdent) {
            now = trExpr(that.meth);
            if (((JCIdent) now).sym instanceof MethodSymbol) {

                msym = (MethodSymbol) ((JCIdent) now).sym;
                if (msym.isStatic())
                    obj = null;
                else
                    obj = currentThisId;

            } else {
                msym = null;
                obj = null;
            } // FIXME - this shouldn't really happen - there is a mis
              // translation in creating makeTYPE expressions

        } else if (that.meth instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess) that.meth;
            msym = (MethodSymbol) (fa.sym);
            if (msym.isStatic())
                obj = null;
            else {
                obj = trExpr(fa.selected);
                // FIXME - should do better than converting to String
                if (!fa.selected.type.toString().endsWith("JMLTYPE"))
                    checkForNull(obj, fa.pos, trueLiteral, null);
            }
        } else {
            // FIXME - not implemented
            log.warning("esc.not.implemented", "BasicBlocker.visitApply for "
                    + that.meth.getClass());
            msym = null;
            obj = null;
            result = trueLiteral;
            return;
        }
        if (msym.type instanceof Type.ForAll) tfa = (Type.ForAll) msym.type;

        // FIXME - what does this translation mean?
        // ListBuffer<JCExpression> newtypeargs = new
        // ListBuffer<JCExpression>();
        // for (JCExpression arg: that.typeargs) {
        // JCExpression n = trExpr(arg);
        // newtypeargs.append(n);
        // }

        ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
        for (JCExpression arg : that.args) {
            JCExpression n = trExpr(arg);
            newargs.append(n);
        }

        pushTypeArgs();
        if (tfa != null) {
            // tfa is the declaration of a parameterized method
            // that is the actual call, which may not have explicit parameters
            Iterator<Type> tv = tfa.tvars.iterator();
            Iterator<JCExpression> e = that.typeargs.iterator();
            if (e.hasNext()) {
                while (tv.hasNext()) {
                    typeargs.put(tv.next().tsym, e.next().type);
                }
            } else {
                log.noticeWriter
                        .println("NOT IMPLEMENTED - parameterized method call with implicit type parameters");
            }
        }

        // FIXME - concerned that the position here is not after the
        // positions of all of the arguments
        if (inSpecExpression) {
            result = insertSpecMethodCall(that.pos, msym, obj, that.typeargs,
                    newargs.toList());
        } else {
            result = insertMethodCall(that, msym, obj, that.getTypeArguments(),
                    newargs.toList()); // typeargs ? FIXME
        }

        popTypeArgs();
        toLogicalForm.put(that, result);
        return;
    }

    // FIXME - review this
    // boolean extraEnv = false;
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        // This is an expression so we just use trExpr
        // log.noticeWriter.println("NO CHECK OF APPLY"); FIXME
        // that.meth.accept(this);
        // for (JCExpression arg: that.args) {
        // arg.accept(this);
        // }

        JmlToken token = that.token;
        JCExpression arg;

        if (token == null) {

            // Presuming this is the checkfor null method
            // that.meth.sym == ???
            JCExpression e = that.meth;
            if (e instanceof JCFieldAccess) {
                Name n = ((JCFieldAccess) e).sym.name;
                if (n.toString().equals("nonNullCheck")) {
                    arg = trExpr(that.args.get(1));
                    checkForNull(arg, that.pos, trueLiteral, that.label);
                    result = arg;
                } else if (n.toString().equals("zeroIntCheck")) {
                    arg = trExpr(that.args.get(1));
                    checkForZero(arg, that.pos, trueLiteral, that.label);
                    result = arg;
                } else if (n.toString().equals("trueCheck")) {
                    JCExpression cond = trExpr(that.args.get(1));
                    arg = trExpr(that.args.get(2));
                    checkTrue(that.pos, cond, that.label);
                    result = arg;
                } else if (n.toString().equals("eqCheck")) {
                    JCExpression obj = trExpr(that.args.get(1));
                    arg = trExpr(that.args.get(2));
                    JCExpression cond = treeutils.makeEquality(that.pos, arg,
                            obj);
                    checkTrue(that.pos, cond, that.label);
                    result = arg;
                } else if (n.toString().equals("intRangeCheck")) {
                    // JCExpression cond = trExpr(that.args.get(1));
                    // arg = trExpr(that.args.get(2));
                    // checkTrue(that.pos,cond,that.label);
                    // result = arg;
                } else {
                    System.out.println("NAME " + n); // FIXME
                }
            } else {
                System.out.println("INTENRAL ERROR ");
                // FIXME
            }

        } else {

            switch (token) {
                case BSPAST:
                case BSOLD:
                case BSPRE:
                    // FIXME - there is a problem if the argument includes an
                    // identifier that
                    // is the quantified variable of a quantifier statement
                    VarMap prev = currentMap;
                    JCIdent label = that.args.size() > 1 ? (JCIdent) (that.args
                            .get(1)) : null;
                    currentMap = oldMap;
                    try {
                        if (label != null) {
                            VarMap lmap = labelmaps.get(label.name);
                            if (lmap != null)
                                currentMap = lmap;
                            else {
                                log.noticeWriter.println("BAD LABEL: " + label);
                            }
                        }
                        result = trExpr(that.args.get(0));
                    } finally {
                        currentMap = prev;
                    }
                    toLogicalForm.put(that, result);
                    return;

                case BSTYPEOF:
                    arg = trExpr(that.args.get(0));
                    checkForNull(arg, that.pos, trueLiteral, null);
                    ListBuffer<JCExpression> lb = new ListBuffer<JCExpression>();
                    lb.append(arg);
                    result = factory.at(that.pos).JmlMethodInvocation(token,
                            lb.toList());
                    ((JmlMethodInvocation) result).startpos = that.startpos;
                    result.type = syms.classType;
                    toLogicalForm.put(that, result);
                    return;

                case BSTYPELC:
                    // Type type = that.args.get(0).type;
                    // type = trType(type);
                    // addClassPredicate(type);
                    // result = makeTypeLiteral(type,that.pos);
                    visitApply(that);
                    return;

                case BSELEMTYPE:
                    // FIXME - shutting up the warning, but not really
                    // implementing this
                    // Also need a check that the argument is non-null
                    arg = trExpr(that.args.get(0));
                    checkForNull(arg, that.pos, trueLiteral, null);
                    result = arg;// FIXME - wrong
                    return;

                case BSMAX:
                case BSREACH:
                case BSSPACE:
                case BSWORKINGSPACE:
                case BSDURATION:
                    Log.instance(context).warning(
                            "esc.not.implemented",
                            "Not yet implemented token in BasicBlocker: "
                                    + that.token.internedName());
                    result = trueLiteral; // FIXME - may not even be a boolean
                                          // typed result
                    break;

                case BSFRESH: { // FIXME - define this to include being non-null
                                // - is that the JML definition?
                    int pos = that.pos;
                    JCExpression e = trExpr(that.args.get(0));
                    // checkForNull(e,that.pos,trueLiteral);
                    JCIdent alloc = newIdentUse(allocSym, pos);
                    // assume <newid>.alloc = <newalloc>
                    JCExpression ee = new JmlBBFieldAccess(allocIdent, e);
                    ee.pos = pos;
                    ee.type = syms.intType;
                    result = treeutils.makeBinary(pos, JCTree.AND,
                            treeutils.makeNeqObject(pos, e, nullLiteral),
                            treeutils.makeBinary(pos, JCTree.EQ, ee, alloc));

                }
                    break;

                // case BSNOTMODIFIED:
                // // Allows multiple arguments; they may be store-refs with
                // wildcards (FIXME)
                // JCExpression combined = null;
                // for (JCExpression a : that.args){
                // // FIXME - there is an issue with condition - how do we
                // evaluate if old(e) is well-defined?
                // // defined as arg == \old(arg)
                // int pos = that.pos;
                // JCExpression e = trExpr(a);
                // VarMap prevMap = currentMap;
                // currentMap = oldMap;
                // try {
                // // FIXME - what happens if not_modifieds are nested, or
                // within an old
                // //extraEnv = true;
                // JCExpression ee = trExpr(a);
                // ee = treeutils.makeBinary(JCTree.EQ,e,ee,pos);
                // if (combined == null) combined = ee;
                // else combined =
                // treeutils.makeBinary(JCTree.AND,combined,ee,pos);
                // } finally {
                // currentMap = prevMap;
                // //extraEnv = false;
                // }
                // }
                // result = combined;
                // break;

                case BSNONNULLELEMENTS: {
                    int pos = that.pos;
                    arg = trExpr(that.args.get(0));
                    // checkForNull(arg,pos,trueLiteral);
                    Name fcnname = names.fromString("nnelement$"
                            + encodeType(arg.type));
                    MethodSymbol msym = makeFunction(fcnname, syms.booleanType,
                            arg.type);
                    result = makeFunctionApply(pos, msym, arg);

                    // also need an axiom: (\forall a, int i; i in range; a[i]
                    // != null)
                    Name index = names.fromString("index$");
                    JCIdent indexId = newAuxIdent(index, syms.intType, pos,
                            false);
                    // JCIdent arrayId = newAuxIdent(array,arg.type,pos,false);
                    Type elemType = ((ArrayType) arg.type).elemtype;
                    JCIdent arrays = getArrayIdent(elemType);
                    JCExpression len = new JmlBBFieldAccess(lengthIdent, arg);
                    len.type = syms.intType;
                    len.pos = pos;
                    JCExpression range = treeutils.makeBinary(pos, JCTree.AND,
                            treeutils.makeBinary(pos, JCTree.LE, zeroLiteral,
                                    indexId), treeutils.makeBinary(pos,
                                    JCTree.LT, indexId, len));
                    JCExpression acc = new JmlBBArrayAccess(arrays, arg,
                            indexId, pos, elemType);
                    JCExpression predicate = treeutils.makeNeqObject(pos, acc,
                            nullLiteral);
                    JCExpression intTypeTree = factory.at(pos).TypeIdent(
                            TypeTags.INT);
                    intTypeTree.type = syms.intType;
                    JCExpression e = factory.at(pos).JmlQuantifiedExpr(
                            JmlToken.BSFORALL,
                            com.sun.tools.javac.util.List
                                    .<JCVariableDecl> of(treeutils
                                            .makeVariableDecl(index,
                                                    syms.intType, null, pos)),
                            range, predicate);
                    e.type = syms.booleanType;
                    e = treeutils.makeBinary(pos, JCTree.AND,
                            treeutils.makeNeqObject(pos, arg, nullLiteral), e);
                    e = treeutils.makeBinary(pos, JCTree.EQ,
                            makeFunctionApply(pos, msym, arg), e);
                    // e =
                    // factory.at(pos).JmlQuantifiedExpr(JmlToken.BSFORALL,null,
                    // new
                    // ListBuffer<JCExpression>().append(factory.Type(arg.type)),
                    // new ListBuffer<Name>().append(array),
                    // null,e);
                    background.add(e);
                    // Log.instance(context).warning("esc.not.implemented","Not yet implemented token in BasicBlocker: "
                    // + that.token.internedName());
                    // result = trueLiteral; // FIXME
                }
                    break;

                case BSISINITIALIZED:
                case BSINVARIANTFOR:
                    Log.instance(context).warning(
                            "esc.not.implemented",
                            "Not yet implemented token in BasicBlocker: "
                                    + that.token.internedName());
                    result = treeutils.trueLit; // FIXME
                    break;

                case BSNOWARN:
                case BSNOWARNOP:
                case BSWARN:
                case BSWARNOP:
                case BSBIGINT_MATH:
                case BSSAFEMATH:
                case BSJAVAMATH:
                    Log.instance(context).warning(
                            "esc.not.implemented",
                            "Not yet implemented token in BasicBlocker: "
                                    + that.token.internedName());
                    result = trExpr(that.args.get(0)); // FIXME - just pass
                                                       // through for now
                    break;

                default:
                    Log.instance(context).error(
                            "esc.internal.error",
                            "Unknown token in BasicBlocker: "
                                    + that.token.internedName());
                    result = trueLiteral; // FIXME - may not even be a boolean
                                          // typed result
                    break;
            }
        }
        toLogicalForm.put(that, result);

    }

    /**
     * This is not a tree walker visitor, but just a helper method called when
     * there is a (pure) method invocation inside a specification expression.
     * The translation here is to keep the call (modified) but add an assumption
     * that implies values for the method.
     * 
     * @param pos
     * @param sym
     * @param obj
     *            already translated method receiver, or null if static
     * @param args
     *            already translated method arguments
     * @return TODO
     */
    // FIXME - review and document
    protected JCExpression insertSpecMethodCall(int pos, MethodSymbol sym,
            JCExpression obj,
            com.sun.tools.javac.util.List<JCExpression> typeargs,
            com.sun.tools.javac.util.List<JCExpression> args) {
        VarMap prevOldMap = oldMap;
        JCIdent prevThisId = thisId;
        JCExpression prevResultVar = resultVar;

        // FIXME - need to do a definedness check that the called method is
        // guaranteed to normally terminate

        try {
            JmlMethodSpecs mspecs = specs.getDenestedSpecs(sym);
            JCExpression newapply = null;
            JmlMethodInfo mi = getMethodInfo(sym);
            JmlMethodDecl decl = null;
            if (mspecs == null) {
                // This happens if the owner is a binary class with no specs.
                // If there is no declaration of the method in the spec file,
                // then an empty JmlMethodSpecs structure will have been put
                // in the specs database.
                mspecs = JmlSpecs.defaultSpecs(context,sym,0).cases;
            } else {
                decl = mspecs.decl;
            }

            Name newMethod = specMethodCalls.get(sym);
            boolean notYetAxiomatized = newMethod == null;
            if (notYetAxiomatized) {
                // get the heap incarnation number
                Integer heapNum = currentMap.get((VarSymbol) heapVar.sym);
                newMethod = encodedName(sym, mspecs.pos, heapNum);
                specMethodCalls.put(sym, newMethod);
            }
            JCIdent newMethodName = newAuxIdent(newMethod, sym.getReturnType(),
                    pos, false); // FIXME - string to name to string to name

            if (obj == null && args.size() == 0) {
                // Static and no arguments, so we just use the new method name
                // as a constant
                newapply = newMethodName;
                if (notYetAxiomatized) {
                    resultVar = newMethodName; // FIXME - what about typeargs
                    for (JmlMethodClauseExpr post : mi.ensuresPredicates) {
                        JCExpression expr = trExpr(post.expression);
                        addAssume(expr.pos, Label.METHODAXIOM, expr,
                                newstatements);
                    }
                }
            } else {
                newMethodName.sym = sym;
                newMethodName.type = sym.type;

                // Need precondition check - FIXME

                // Construct what we are going to replace \result with
                ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
                if (obj != null) newargs.append(obj);
                for (JCExpression e : args)
                    newargs.append(e);
                newapply = factory.at(pos).Apply(typeargs, newMethodName,
                        newargs.toList());
                newapply.type = sym.getReturnType();
                // FIXME - needs type - is this right

                // Construct the axioms from the postconditions
                ListBuffer<JCExpression> margs = new ListBuffer<JCExpression>();

                ListBuffer<JCVariableDecl> decls = ListBuffer
                        .<JCVariableDecl> lb();
                if (obj != null) {
                    margs.append(currentThisId);
                    decls.append(treeutils.makeVariableDecl(thisId.name,
                            syms.objectType, null, 0)); // FIXME _ object type?
                                                        // // FIXME pos
                }
                if (decl != null) {
                    for (JCVariableDecl e : decl.params) {
                        JCIdent p = newIdentUse(e.sym, 0);
                        margs.append(p);
                        decls.append(treeutils.makeVariableDecl(p.name, e.type,
                                null, 0)); // FIXME - position
                    }
                } else {
                    // FIXME - I'm not sure when sym.params is null and when it
                    // is an empty list - got my first null with: assert
                    // \values.size() == \index
                    if (sym.params != null)
                        for (VarSymbol e : sym.params) {
                            JCIdent p = newIdentUse(e, 0);
                            margs.append(p);
                            decls.append(treeutils.makeVariableDecl(p.name,
                                    e.type, null, 0)); // FIXME - position
                    }
                }

                JCExpression mapply = factory.at(pos).Apply(null,
                        newMethodName, margs.toList()); // FIXME - what about
                                                        // typeargs
                mapply.type = sym.getReturnType();

                // ListBuffer<Name> single = new ListBuffer<Name>();
                // single.append(thisId.name);
                if (notYetAxiomatized) {
                    resultVar = mapply;
                    VarMap savedOldMap = oldMap;
                    oldMap = currentMap;
                    try {
                        for (JmlMethodClauseExpr post : mi.ensuresPredicates) {
                            JCExpression predicate = trExpr(post.expression);
                            JmlQuantifiedExpr expr = factory.at(pos)
                                    .JmlQuantifiedExpr(JmlToken.BSFORALL,
                                            decls.toList(), null, predicate);
                            expr.type = syms.booleanType;
                            // addAssume(Label.METHODAXIOM,expr,newstatements,false);
                            addAxiom(post.pos, Label.METHODAXIOM, expr,
                                    newstatements);
                            // Need inherited specs, also interfaces - FIXME
                            // FIXME - use condition?
                        }
                    } finally {
                        oldMap = savedOldMap;
                    }
                }
            }
            return newapply;
        } finally {
            oldMap = prevOldMap;
            thisId = prevThisId;
            resultVar = prevResultVar;
        }
    }

    // Note - obj and the args are already translated
    // pos is the preferred position of the method call (e.g. the left
    // parenthesis)
    // FIXME - review and document
    protected JCIdent insertMethodCall(JCMethodInvocation tree,
            MethodSymbol methodSym, JCExpression obj,
            List<JCExpression> typeargs, List<JCExpression> args) {
        int pos = tree.pos;
        MethodSymbol baseMethodSym = methodSym;
        VarMap prevOldMap = oldMap;
        JCIdent prevThisId = thisId;
        JCIdent retId = methodSym.type == null ? null : newAuxIdent(
                RESULT_PREFIX + pos, methodSym.getReturnType(), pos, true);
        JCIdent exceptionId = methodSym.type == null ? null
                : newIdentIncarnation(this.exceptionVar, pos);
        JCExpression prevResultVar = resultVar;
        JCIdent prevExceptionVar = exceptionVar;

        try {
            JmlClassInfo calledClassInfo = getClassInfo(methodSym.owner);
            JmlMethodSpecs mspecs = specs.getDenestedSpecs(methodSym);
            if (mspecs == null) {
                // This happens for a binary class with no specs for the given
                // method.
                // log.noticeWriter.println("NO SPECS FOR METHOD CALL(A) " +
                // sym.owner + "." + sym);
                mspecs = JmlSpecs.defaultSpecs(context,methodSym,pos).cases;
            } // else
            {
                boolean isStaticCalled = methodSym.isStatic();
                boolean isConstructorCalled = methodSym.isConstructor();
                boolean isHelperCalled = utils.isHelper(methodSym);

                JCExpression expr;
                // all expressions are already translated, so we can now create
                // a new 'this' - the specs of the called method are translated
                // with 'this' being the receiver object

                // Assign the receiver to a new variable. If the method called
                // is static, obj is null.
                if (obj != null) {
                    currentThisId = newAuxIdent("this$" + pos,
                            methodSym.owner.type, pos, false);
                    addAssume(obj.pos, Label.RECEIVER,
                            treeutils.makeEqObject(obj.pos, currentThisId, obj));
                }

                // Assign each of the arguments to a new variable
                JmlMethodDecl decl = mspecs.decl;

                // FIXME - change this loop to use JmlMethodInfo.overrides - and
                // what about interfaceOverrides?
                while (decl == null && methodSym.params == null) {
                    if (isConstructorCalled || isStaticCalled) break;
                    methodSym = getOverrided(methodSym);
                    if (methodSym == null) break;
                    mspecs = specs.getDenestedSpecs(methodSym);
                    if (mspecs != null) decl = mspecs.decl;
                }

                boolean hasArgs = methodSym != null;

                if (hasArgs) {
                    int i = 0;
                    if (decl != null) {
                        JavaFileObject source = ((ClassSymbol) decl.sym.owner).sourcefile;
                        if (obj == null) {
                            // static
                            List<JCExpression> argtypes = typeargs;
                            List<JCTypeParameter> ptypes = decl.typarams;
                            if (argtypes != null && ptypes != null) {
                                Iterator<JCExpression> argiter = argtypes
                                        .iterator();
                                Iterator<JCTypeParameter> piter = ptypes
                                        .iterator();
                                while (argiter.hasNext() && piter.hasNext()) {
                                    Type argtype = argiter.next().type;
                                    Type ptype = piter.next().type;
                                    // for each type argument T (number i)
                                    // assume \type(T) ==
                                    // \typeof(receiver).getArg(i);
                                    JCIdent id = newIdentIncarnation(
                                            ptype.tsym, pos);
                                    JCExpression e = makeTypeLiteral(argtype,
                                            pos);
                                    e = treeutils.makeEqObject(pos, id, e);
                                    addAssume(pos, Label.ARGUMENT,
                                            trSpecExpr(e, source));
                                }
                            } else if (ptypes == null) {
                                List<Type> pptypes = decl.sym.owner.type
                                        .getTypeArguments();
                                if (argtypes != null && pptypes != null) {
                                    Iterator<JCExpression> argiter = argtypes
                                            .iterator();
                                    Iterator<Type> piter = pptypes.iterator();
                                    while (argiter.hasNext() && piter.hasNext()) {
                                        Type argtype = argiter.next().type;
                                        Type ptype = piter.next();
                                        // for each type argument T (number i)
                                        // assume \type(T) ==
                                        // \typeof(receiver).getArg(i);
                                        JCIdent id = newIdentIncarnation(
                                                ptype.tsym, pos);
                                        JCExpression e = makeTypeLiteral(
                                                argtype, pos);
                                        e = treeutils.makeEqObject(pos, id, e);
                                        addAssume(pos, Label.ARGUMENT,
                                                trSpecExpr(e, source));
                                    }
                                }

                            }
                        } else {
                            List<Type> argtypes = obj.type.getTypeArguments();
                            if (obj.type.getEnclosingType() != Type.noType)
                                argtypes = allTypeArgs(obj.type);
                            List<Type> ptypes = decl.sym.owner.type
                                    .getTypeArguments();
                            if (decl.sym.owner.type.getEnclosingType() != Type.noType)
                                ptypes = allTypeArgs(decl.sym.owner.type);
                            if (argtypes != null && ptypes != null) {
                                Iterator<Type> argiter = argtypes.iterator();
                                Iterator<Type> piter = ptypes.iterator();
                                while (argiter.hasNext() && piter.hasNext()) {
                                    Type argtype = argiter.next();
                                    Type ptype = piter.next();
                                    // for each type argument T (number i)
                                    // assume \type(T) ==
                                    // \typeof(receiver).getArg(i);
                                    JCIdent id = newIdentIncarnation(
                                            ptype.tsym, pos);
                                    JCExpression e = makeTypeLiteral(argtype,
                                            pos);
                                    e = treeutils.makeEqObject(pos, id, e);
                                    addAssume(pos, Label.ARGUMENT,
                                            trSpecExpr(e, source));
                                }
                            }
                        }
                        for (JCVariableDecl vd : decl.params) {
                            expr = args.get(i++);
                            // expr = trSpecExpr(expr,source);
                            JCIdent id = newIdentIncarnation(vd, pos);
                            addAssume(expr.getStartPosition(), Label.ARGUMENT,
                                    treeutils.makeEquality(expr.pos, id, expr));
                        }
                    } else if (methodSym.params != null) {
                        for (VarSymbol vd : methodSym.params) {
                            expr = args.get(i++);
                            JCIdent id = newIdentIncarnation(vd, pos);
                            addAssume(expr.getStartPosition(), Label.ARGUMENT,
                                    treeutils.makeEquality(expr.pos, id, expr));
                        }
                    } else {
                        // No specifications for a binary method

                        // FIXME - but there might be specs for a super method
                        // and we need to have parameter mappings for them
                    }
                }

                if (isConstructorCalled) {
                    // Presuming that isConstructor
                    // We are calling a this or super constructor
                    // static invariants have to hold
                    if (!isHelperCalled && calledClassInfo != null) {
                        for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e, inv.source());
                            addAssert(Label.INVARIANT, e,
                                    inv.getStartPosition(), newstatements, pos,
                                    inv.source(), inv);
                        }
                    }
                } else if (!isConstructor && !isHelper) {
                    for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e, inv.source());
                        addAssert(Label.INVARIANT, e, inv.getStartPosition(),
                                newstatements, pos, inv.source(), inv);
                    }
                    if (!isStatic) {
                        for (JmlTypeClauseExpr inv : calledClassInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e, inv.source());
                            addAssert(Label.INVARIANT, e,
                                    inv.getStartPosition(), newstatements, pos,
                                    inv.source(), inv);
                        }
                    }
                }

                JmlMethodInfo mi = null;
                if (hasArgs) {
                    JCExpression exprr = null;
                    mi = getMethodInfo(methodSym);
                    int dpos = mi.decl == null ? pos : mi.decl.pos;
                    JavaFileObject source = null;
                    boolean multipleSource = false;
                    for (JmlMethodClauseExpr pre : mi.requiresPredicates) {
                        JCExpression pexpr = trSpecExpr(pre.expression,
                                pre.source());
                        if (exprr == null)
                            exprr = pexpr;
                        else {
                            exprr = treeutils.makeBinary(exprr.pos,
                                    JCTree.BITOR, exprr, pexpr);
                            copyEndPosition(exprr, pexpr);
                        }
                        source = pre.source();
                    }

                    if (!isConstructorCalled && !isStaticCalled) {
                        MethodSymbol msym = methodSym;
                        // FIXME - do this for interfaces as well
                        for (MethodSymbol m : mi.overrides) {
                            exprr = addMethodPreconditions(currentBlock, m,
                                    mi.decl, dpos, exprr); // FIXME - what
                                                           // position to use?
                            if (getMethodInfo(m).requiresPredicates.size() > 0) {
                                if (source == null)
                                    source = getMethodInfo(m).requiresPredicates
                                            .get(0).source();
                                else
                                    multipleSource = true;
                            }
                        }
                    }
                    if (exprr == null)
                        exprr = treeutils.makeBooleanLiteral(dpos, true);
                    JCTree first = mi.requiresPredicates.size() > 0 ? mi.requiresPredicates
                            .get(0) : exprr;

                    addAssert(Label.PRECONDITION, exprr,
                            exprr.getStartPosition(), newstatements, pos,
                            source, first);

                    // Grap a copy of the map before we introduce havoced
                    // variables
                    oldMap = currentMap.copy();

                    // FIXME - I think there is a problem if the modifies list
                    // uses expressions
                    // that are also being havoced
                    havocAssignables(pos, mi); // expressions are evaluated in
                                               // the pre-state
                }

                // Bump up the version of the heap
                // FIXME - does a class get pure from its container?
                boolean isPure = utils.isPure(methodSym)
                        || utils.isPure(methodSym.enclClass());
                if (!isPure) newIdentIncarnation(heapVar, pos);

                // Bump up the allocation, in case there are any fresh
                // declarations

                JCIdent oldalloc = newIdentUse(allocSym, pos);
                JCIdent alloc = newIdentIncarnation(allocSym, allocCount);
                alloc.pos = pos;

                // assume <oldalloc> < <newalloc>
                JCExpression ee = treeutils.makeBinary(pos, JCTree.LT,
                        oldalloc, alloc);
                addAssume(pos, Label.SYN, ee);

                // Take care of termination options

                resultVar = retId;
                exceptionVar = exceptionId;
                JCIdent termVar = newIdentIncarnation(terminationSym, pos);
                JCExpression termExp = treeutils.makeBinary(pos, JCTree.OR,
                        treeutils.makeBinary(pos, JCTree.EQ, termVar,
                                zeroLiteral), treeutils.makeBinary(
                                pos,
                                JCTree.AND,
                                treeutils.makeBinary(pos, JCTree.EQ, termVar,
                                        treeutils.makeBinary(pos, JCTree.MINUS,
                                                zeroLiteral, treeutils
                                                        .makeIntLiteral(pos,
                                                                pos))),
                                makeInstanceof(exceptionVar, pos,
                                        syms.exceptionType, pos)));
                termExp = trSpecExpr(termExp, null);
                addAssume(tree.getStartPosition(), tree, Label.TERMINATION,
                        termExp, currentBlock.statements);

                // If there is a non-primitive result, we need to say that it is
                // allocated (if not null)
                if (!baseMethodSym.isConstructor()
                        && !baseMethodSym.getReturnType().isPrimitive()) {
                    declareAllocated(resultVar, pos);
                    // JCExpression eee = new
                    // JmlBBFieldAccess(allocIdent,resultVar);
                    // eee.pos = pos;
                    // eee.type = syms.intType;
                    // eee =
                    // treeutils.makeBinary(JCTree.LT,eee,newIdentUse(allocSym,pos),pos);
                    // eee =
                    // treeutils.makeBinary(JCTree.OR,eee,treeutils.makeBinary(JCTree.EQ,resultVar,nullLiteral,pos),pos);
                    // addAssume(Label.SYN,eee,currentBlock.statements,false);
                }

                if (hasArgs) {
                    JCExpression prevCondition2 = condition;
                    JCBinary nn = treeutils.makeNeqObject(pos, exceptionVar,
                            nullLiteral);
                    try {
                        JCBinary normalTerm = treeutils.makeBinary(pos,
                                JCTree.LE, zeroLiteral, termVar);
                        condition = treeutils.makeBinary(pos, JCTree.AND,
                                condition, normalTerm);
                        for (JmlMethodClauseExpr post : mi.ensuresPredicates) {
                            // (termVar >= 0) ==> <ensures condition>
                            addAssume(pos, Label.POSTCONDITION,
                                    treeutils.makeJmlBinary(
                                            pos,
                                            JmlToken.IMPLIES,
                                            normalTerm,
                                            trSpecExpr(post.expression,
                                                    post.source())),
                                    newstatements);
                        }
                        JCBinary excTerm = treeutils.makeBinary(pos, JCTree.GT,
                                zeroLiteral, termVar);
                        condition = treeutils.makeBinary(pos, JCTree.AND,
                                prevCondition2, excTerm);
                        // NOW: condition is prevCondition2 && (0 > termVar)
                        for (JmlMethodClauseExpr post : mi.exPredicates) {
                            JCExpression ex = ((JmlBinary) post.expression).lhs;
                            signalsVar = null;
                            if (ex instanceof JmlBinary) {
                                ex = ((JmlBinary) ex).lhs;
                                ex = ((JmlMethodInvocation) ex).args.get(0);
                                signalsVar = ex instanceof JCIdent ? (JCIdent) ex
                                        : null;
                            }
                            // (termVar < 0) ==> ( exceptionVar != null &&
                            // <signals condition> )
                            addAssume(pos, Label.SIGNALS,
                                    treeutils.makeJmlBinary(
                                            pos,
                                            JmlToken.IMPLIES,
                                            excTerm,
                                            trSpecExpr(treeutils.makeBinary(
                                                    pos, JCTree.AND, nn,
                                                    post.expression), post
                                                    .source())), newstatements);
                            signalsVar = null;
                        }
                        for (JmlMethodClauseExpr post : mi.sigPredicates) {
                            // (termVar < 0) ==> <signals condition>
                            addAssume(pos, Label.SIGNALS_ONLY,
                                    treeutils.makeJmlBinary(
                                            pos,
                                            JmlToken.IMPLIES,
                                            excTerm,
                                            trSpecExpr(treeutils.makeBinary(
                                                    pos, JCTree.AND, nn,
                                                    post.expression), post
                                                    .source())), newstatements);
                        }
                    } finally {
                        condition = prevCondition2;
                    }
                    if (!isConstructorCalled && !isStaticCalled) {
                        // FIXME - do this for interfaces as well
                        for (MethodSymbol msym : getMethodInfo(methodSym).overrides) {
                            mi = getMethodInfo(msym);
                            addParameterMappings(mspecs.decl, mi.decl, pos,
                                    currentBlock);
                            for (JmlMethodClauseExpr post : mi.ensuresPredicates) {
                                addAssume(
                                        post.getStartPosition(),
                                        Label.POSTCONDITION,
                                        treeutils.makeJmlBinary(
                                                pos,
                                                JmlToken.IMPLIES,
                                                treeutils.makeBinary(pos,
                                                        JCTree.LE, zeroLiteral,
                                                        termVar),
                                                trSpecExpr(
                                                        treeutils
                                                                .makeBinary(
                                                                        pos,
                                                                        JCTree.AND,
                                                                        nn,
                                                                        post.expression),
                                                        post.source())));
                            }
                            for (JmlMethodClauseExpr post : mi.exPredicates) {
                                JCExpression ex = ((JmlBinary) post.expression).lhs;
                                ex = ex instanceof JmlBinary ? ((JmlBinary) ex).lhs
                                        : null;
                                ex = ex instanceof JmlMethodInvocation ? ((JmlMethodInvocation) ex).args
                                        .get(0) : null;
                                signalsVar = ex instanceof JCIdent ? (JCIdent) ex
                                        : null;
                                addAssume(
                                        post.getStartPosition(),
                                        Label.SIGNALS,
                                        treeutils.makeJmlBinary(
                                                pos,
                                                JmlToken.IMPLIES,
                                                treeutils.makeBinary(pos,
                                                        JCTree.GT, zeroLiteral,
                                                        termVar),
                                                trSpecExpr(
                                                        treeutils
                                                                .makeBinary(
                                                                        pos,
                                                                        JCTree.AND,
                                                                        nn,
                                                                        post.expression),
                                                        post.source())));
                                signalsVar = null;
                            }
                            for (JmlMethodClauseExpr post : mi.sigPredicates) {
                                // (termVar < 0) ==> <signals condition>
                                addAssume(
                                        post.getStartPosition(),
                                        Label.SIGNALS_ONLY,
                                        treeutils.makeJmlBinary(
                                                pos,
                                                JmlToken.IMPLIES,
                                                treeutils.makeBinary(pos,
                                                        JCTree.GT, zeroLiteral,
                                                        termVar),
                                                trSpecExpr(
                                                        treeutils
                                                                .makeBinary(
                                                                        pos,
                                                                        JCTree.AND,
                                                                        nn,
                                                                        post.expression),
                                                        post.source())));
                            }
                        }
                    }
                }

                if (isConstructorCalled) {
                    // Presuming that isConstructor
                    // Calling a super or this constructor
                    if (!isHelperCalled && calledClassInfo != null) {
                        for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e, inv.source());
                            addAssume(e.pos, Label.INVARIANT, e, newstatements);
                        }
                        for (JmlTypeClauseExpr inv : calledClassInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e, inv.source());
                            addAssume(e.pos, Label.INVARIANT, e, newstatements);
                        }
                        for (JmlTypeClauseConstraint inv : calledClassInfo.staticconstraints) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e, inv.source());
                            addAssume(e.pos, Label.CONSTRAINT, e, newstatements);
                        }
                    }
                } else if (!isHelper) {
                    for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e, inv.source());
                        addAssume(e.pos, Label.INVARIANT, e, newstatements);
                    }
                    if (!isStatic) {
                        for (JmlTypeClauseExpr inv : calledClassInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e, inv.source());
                            addAssume(e.pos, Label.INVARIANT, e, newstatements);
                        }
                    }
                    for (JmlTypeClauseConstraint inv : calledClassInfo.staticconstraints) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e, inv.source());
                        addAssume(e.pos, Label.CONSTRAINT, e, newstatements);
                    }
                    if (!isConstructor) {
                        if (!isStatic) {
                            for (JmlTypeClauseConstraint inv : calledClassInfo.constraints) {
                                JCExpression e = inv.expression;
                                e = trSpecExpr(e, inv.source());
                                addAssume(e.pos, Label.CONSTRAINT, e,
                                        newstatements);
                            }
                        }
                    }
                }
                // Take out the temporary variables for the arguments
                if (decl != null && decl.params != null)
                    for (JCVariableDecl vd : decl.params) {
                        currentMap.remove(vd.sym);
                    }

                // Now create an (unprocessed) block for everything that follows
                // the
                // method call
                String restName = blockPrefix + pos + "$afterCall$"
                        + (unique++);
                BasicBlock brest = newBlock(restName, pos, currentBlock);// it
                                                                         // gets
                                                                         // all
                                                                         // the
                                                                         // followers
                                                                         // of
                                                                         // the
                                                                         // current
                                                                         // block
                List<JCStatement> temp = brest.statements; // Empty - swapping
                                                           // lists to avoid
                                                           // copying
                brest.statements = remainingStatements; // it gets all of the
                                                        // remaining statements
                remainingStatements = temp;
                // Don't because we are going to begin it below
                // blocksToDo.add(0,brest); // push it on the front of the to do
                // list
                follows(currentBlock, brest);

                // We also need an empty block for the exception to go to. We
                // cannot
                // go directly to the exception block because some DSA variable
                // renaming may need to be done.
                BasicBlock bexc = newBlock(blockPrefix + pos + "$afterCallExc$"
                        + (unique++), pos);
                blocksToDo.add(0, bexc); // push it on the front of the to do
                                         // list
                follows(currentBlock, bexc);
                addUntranslatedAssume(pos, Label.SYN, treeutils.makeBinary(pos,
                        JCTree.LT, terminationVar, zeroLiteral),
                        bexc.statements);

                if (tryreturnStack.isEmpty()) {
                    follows(bexc, exceptionBlock);
                } else {
                    List<BasicBlock> catchList = catchListStack.get(0);
                    for (BasicBlock b : catchList) {
                        follows(bexc, b);
                    }
                }

                // Now we have to complete the currentBlock and start brest
                // because we may be in the middle of translating an
                // expression and any statement after this point has to go
                // into the next (the non-exception) block

                completed(currentBlock);
                startBlock(brest);
                addAssume(pos, Label.SYN, treeutils.makeBinary(pos, JCTree.EQ,
                        termVar, zeroLiteral), brest.statements);
            }
        } finally {
            oldMap = prevOldMap;
            currentThisId = prevThisId;
            resultVar = prevResultVar;
            exceptionVar = prevExceptionVar;
            result = retId;
        }
        return retId;
    }

    // FIXME - REVIEW and document
    protected List<Type> allTypeArgs(Type type) {
        ListBuffer<Type> list = new ListBuffer<Type>();
        allTypeArgs(list, type);
        return list.toList();
    }

    // FIXME - REVIEW and document
    protected void allTypeArgs(ListBuffer<Type> list, Type type) {
        if (type == Type.noType) return;
        allTypeArgs(list, type.getEnclosingType());
        list.appendList(type.getTypeArguments());
    }

    // FIXME - REVIEW and document
    // Generate a (translated) allocation predicate // FIXME - check this out
    // and use it
    protected void declareAllocated(VarSymbol vsym, int pos) {
        JCIdent var = newIdentUse(vsym, pos);
        declareAllocated(var, pos);
    }

    // Generate a (translated) allocation predicate // FIXME - check this out
    // and use it
    protected void declareAllocated(JCExpression e, int pos) {
        currentBlock.statements.add(comment(pos, e + " != null || " + e
                + " .alloc < " + allocSym));
        JCExpression eee = new JmlBBFieldAccess(allocIdent, e);
        eee.pos = pos;
        eee.type = syms.intType;
        eee = treeutils.makeBinary(pos, JCTree.LE, eee,
                newIdentUse(allocSym, pos));
        eee = treeutils.makeBinary(pos, JCTree.OR,
                treeutils.makeEqObject(pos, e, nullLiteral), eee);
        addAssume(pos, Label.SYN, eee, currentBlock.statements);
    }

    // Generate a (translated) alloc comparison // FIXME - check this out and
    // use it and docuiment
    protected JCExpression allocCompare(int pos, JCExpression e) {
        JCExpression eee = new JmlBBFieldAccess(allocIdent, e);
        eee.pos = pos;
        eee.type = syms.intType;
        eee = treeutils.makeBinary(pos, JCTree.LE, eee,
                newIdentUse(allocSym, pos));
        return eee;
    }

    // Generate a (translated) alloc selection // FIXME - check this out and use
    // it and document
    protected JCExpression allocSelect(int pos, JCExpression e) {
        JCExpression eee = new JmlBBFieldAccess(allocIdent, e);
        eee.pos = pos;
        eee.type = syms.intType;
        return eee;
    }

    // FIXME - review and document
    protected void havocAssignables(int pos, JmlMethodInfo mi) {
        // * a store-ref
        // * is a JCIdent, a JCSelect (potentially with a null field), or a
        // JmlStoreRefArrayRange;
        // * there may be more than one use of a JmlStoreRefArrayRange, e.g.
        // a[2..3][4..5] or
        // * a.f[4..5].g[6..7]
        for (JmlMethodInfo.Entry entry : mi.assignables) {
            JCExpression preCondition = trSpecExpr(entry.pre,
                    log.currentSourceFile()); // FIXME - fix this
            for (JCTree sr : entry.storerefs) {
                if (sr == null) {
                    Log.instance(context)
                            .error(pos, "jml.internal",
                                    "Unexpected null store-ref in BasicBlocker.havocAssignables");
                    continue;
                }
                int npos = pos * 100000 + sr.pos;
                JCExpression prevCondition = condition;
                if (sr instanceof JCIdent) {
                    JCIdent id = (JCIdent) sr;
                    if (utils.isJMLStatic(id.sym)) {
                        JCExpression oldid = trSpecExpr(id,
                                log.currentSourceFile()); // FIXME
                        JCIdent newid = newIdentIncarnation(id, npos); // new
                                                                       // incarnation
                        // newid == precondition ? newid : oldid
                        JCExpression e = factory.at(pos).Conditional(
                                preCondition, newid, oldid);
                        e.type = newid.type;
                        e = treeutils.makeBinary(pos, JCTree.EQ, newid, e);
                        addAssume(pos, Label.HAVOC, e, currentBlock.statements);
                    } else {
                        // Same as for JCFieldAccess except that fa.selected is
                        // always 'this' (currentThisId)
                        Type type = id.type;
                        checkForNull(currentThisId, id.pos, preCondition, null);

                        JCIdent oldid = newIdentUse((VarSymbol) id.sym, id.pos);
                        JCFieldAccess oldaccess = new JmlBBFieldAccess(oldid,
                                currentThisId);
                        oldaccess.pos = id.pos;
                        oldaccess.type = type;

                        JCIdent newid = newIdentIncarnation(oldid, npos);
                        JCFieldAccess newaccess = new JmlBBFieldAccess(newid,
                                currentThisId);
                        newaccess.pos = id.pos;
                        newaccess.type = type;

                        JCExpression right = factory.at(id.pos).Conditional(
                                preCondition, newaccess, oldaccess);
                        right.type = type;

                        JCExpression expr = new JmlBBFieldAssignment(newid,
                                oldid, currentThisId, right);
                        expr.pos = pos;
                        expr.type = type;

                        addAssume(pos, Label.HAVOC, expr,
                                currentBlock.statements);
                    }
                } else if (sr instanceof JCFieldAccess) {
                    // FIXME - this duplicates logic in visitSelect and
                    // doAssignment
                    // s.f' = precondition ? s.f' : s.f
                    JCFieldAccess fa = (JCFieldAccess) sr;
                    JCExpression selected = fa.selected;
                    boolean isType = true;
                    if ((selected instanceof JCIdent)
                            && ((JCIdent) selected).sym instanceof ClassSymbol) {
                        // do nothing
                    } else if ((selected instanceof JCFieldAccess)
                            && ((JCFieldAccess) selected).sym instanceof ClassSymbol) {
                        // do nothing
                    } else {
                        selected = trSpecExpr(fa.selected,
                                log.currentSourceFile()); // FIXME
                        isType = false;
                    }

                    try {
                        if (!isType)
                            checkForNull(selected, sr.pos, preCondition, null);

                        if (fa.sym == null) {
                            Symbol ownerSym = fa.selected.type.tsym;
                            if (ownerSym instanceof ClassSymbol) {
                                ClassSymbol csym = (ClassSymbol) ownerSym;
                                Scope.Entry symentry = csym.members().elems;
                                while (symentry != null) {
                                    Symbol sym = symentry.sym;
                                    symentry = symentry.sibling;
                                    if (sym instanceof VarSymbol) {
                                        if (utils.isJMLStatic(sym)) {
                                            JCIdent newid = newIdentIncarnation(
                                                    (VarSymbol) sym, npos);
                                            JCExpression e = treeutils
                                                    .makeEquality(npos, newid,
                                                            newid);
                                            addAssume(sr.pos, Label.HAVOC, e,
                                                    currentBlock.statements);

                                        } else if (!isType) {
                                            havocField((VarSymbol) sym,
                                                    selected, fa.pos, npos,
                                                    sym.type, preCondition);
                                        }
                                    }
                                }
                            } else {
                                log.noticeWriter.println("FOUND "
                                        + ownerSym.getClass());
                            }

                        } else {
                            VarSymbol vsym = (VarSymbol) fa.sym;
                            havocField(vsym, selected, fa.pos, npos, fa.type,
                                    preCondition);
                        }
                    } finally {
                        condition = prevCondition;
                    }

                } else if (sr instanceof JmlStoreRefArrayRange) {
                    JmlStoreRefArrayRange ar = (JmlStoreRefArrayRange) sr;

                    ListBuffer<Name> ns = new ListBuffer<Name>();
                    JCExpression array = extractQuantifiers(ar.expression, ns);

                    condition = treeutils.makeBinary(sr.pos, JCTree.AND,
                            condition, preCondition);
                    try {
                        if (ar.hi != ar.lo || ar.lo == null) {
                            // wildcard at the top level
                            if (ns.size() > 0) {
                                // and wildcards within
                            } else {
                                // no wildcards within

                                JCIdent arrayId = getArrayIdent(sr.type);

                                array = trSpecExpr(array,
                                        log.currentSourceFile()); // FIXME
                                checkForNull(array, sr.pos, trueLiteral, null);

                                JCExpression indexlo = trSpecExpr(ar.lo,
                                        log.currentSourceFile()); // FIXME
                                if (indexlo != null)
                                    checkArrayAccess(array, indexlo, sr.pos);
                                else
                                    indexlo = zeroLiteral;

                                JCExpression indexhi = trSpecExpr(ar.hi,
                                        log.currentSourceFile()); // FIXME
                                boolean above = false;
                                if (indexhi != null)
                                    checkArrayAccess(array, indexhi, sr.pos);
                                else {
                                    // indexhi =
                                    // factory.at(sr.pos).Select(array,lengthSym);
                                    indexhi = new JmlBBFieldAccess(lengthIdent,
                                            array);
                                    indexhi.pos = sr.pos;
                                    indexhi.type = syms.intType;
                                    above = true;
                                }

                                JCIdent nid = newArrayIncarnation(sr.type, pos);
                                JCExpression e = new JmlBBArrayHavoc(nid,
                                        arrayId, array, indexlo, indexhi,
                                        preCondition, above);

                                addAssume(pos, Label.HAVOC, e,
                                        currentBlock.statements);

                            }
                        } else {
                            // single element at the top level

                            if (ns.size() > 0) {
                                // FIXME - this is all wrong
                                // But wild-cards within the ar.expression

                                // JCIdent label =
                                // newAuxIdent("havoclabel$"+npos,syms.intType,npos,false);
                                // labelmaps.put(label.name,currentMap.copy());
                                // JCExpression oldaccess =
                                // factory.at(npos).JmlMethodInvocation(JmlToken.BSOLD,access,label);
                                //
                                // JCArrayAccess newaccess =
                                // factory.at(access.pos).Indexed(access.indexed,access.index);
                                // newaccess.type = access.type;
                                //
                                // // JCIdent meth =
                                // newAuxIdent("arbitrary$",syms.intType,npos);
                                // // ListBuffer<JCExpression> args = new
                                // ListBuffer<JCExpression>();
                                // // for (Name n: ns) {
                                // // JCIdent id = factory.at(npos).Ident(n);
                                // // id.type = syms.intType;
                                // // args.append(id);
                                // // }
                                // // JCMethodInvocation app =
                                // factory.at(npos).Apply(null,meth,args.toList());
                                // // app.type = ar.type;
                                //
                                // JCConditional cond =
                                // factory.at(sr.pos).Conditional(
                                // treeutils.makeBinary(JCTree.AND,entry.pre,accumRange,npos),newaccess,oldaccess);
                                // cond.type = access.type;
                                //
                                // JCExpression assign =
                                // treeutils.makeBinary(JCTree.EQ,newaccess,cond,npos);
                                //
                                // JmlQuantifiedExpr quant =
                                // factory.at(sr.pos).JmlQuantifiedExpr(JmlToken.BSFORALL,null,factory.Type(syms.intType),ns,fullRange,assign);
                                //
                                // JCIdent nid =
                                // newArrayIncarnation(sr.type,npos);
                                // JmlQuantifiedExpr trQuant =
                                // (JmlQuantifiedExpr)trSpecExpr(quant,log.currentSourceFile());
                                // // FIXME
                                // // Now we fix up the expression
                                // JCExpression predicate = trQuant.predicate;
                                // JCBinary bin = (JCBinary)predicate;
                                // cond = (JCConditional)bin.rhs;
                                // JmlBBArrayAccess newaa =
                                // (JmlBBArrayAccess)cond.truepart;
                                // JmlBBArrayAccess oldaa =
                                // (JmlBBArrayAccess)cond.falsepart;
                                //
                                // JCExpression expr = new
                                // JmlBBArrayAssignment(nid,oldaa.arraysId,oldaa.indexed,oldaa.index,cond);
                                // expr.pos = sr.pos;
                                // expr.type = cond.type;
                                //
                                // trQuant.predicate = expr;
                                //
                                // addAssume(pos,Label.HAVOC,trQuant,currentBlock.statements,false);

                            } else {
                                // single element
                                // a'[i] = preCondition ? a'[i] : a[i];

                                array = trSpecExpr(array,
                                        log.currentSourceFile()); // FIXME
                                checkForNull(array, sr.pos, trueLiteral, null);

                                JCExpression index = trSpecExpr(ar.lo,
                                        log.currentSourceFile()); // FIXME
                                checkArrayAccess(array, index, sr.pos);

                                JCIdent arrayID = getArrayIdent(sr.type);
                                JCExpression oldvalue = new JmlBBArrayAccess(
                                        arrayID, array, index, sr.pos, sr.type);

                                JCIdent nid = newArrayIncarnation(sr.type, pos);
                                JCExpression newvalue = new JmlBBArrayAccess(
                                        nid, array, index, sr.pos, sr.type);

                                JCExpression condValue = factory.at(sr.pos)
                                        .Conditional(preCondition, newvalue,
                                                oldvalue);
                                condValue.type = oldvalue.type;

                                JCExpression expr = new JmlBBArrayAssignment(
                                        nid, arrayID, array, index, condValue);
                                expr.pos = sr.pos;
                                expr.type = oldvalue.type;
                                addAssume(pos, Label.HAVOC, expr,
                                        currentBlock.statements);
                            }
                        }
                    } finally {
                        condition = prevCondition;
                    }

                } else if (sr instanceof JmlStoreRefKeyword) {
                    if (((JmlStoreRefKeyword) sr).token == JmlToken.BSNOTHING) {
                        // OK
                    } else {
                        havocEverything(preCondition, sr.pos);
                    }
                } else if (sr instanceof JmlSingleton) { // FIXME - why do we
                                                         // get JmlSingleton as
                                                         // a store-ref? -
                                                         // should not this
                                                         // should be an error
                    if (((JmlSingleton) sr).token == JmlToken.BSNOTHING) {
                        // OK
                    } else {
                        havocEverything(preCondition, sr.pos);
                    }
                } else {
                    Log.instance(context).error(
                            sr.pos,
                            "jml.internal",
                            "Unexpected kind of store-ref in BasicBlocker.havocAssignables: "
                                    + sr.getClass());
                }
            }
        }
    }

    // FIXME - review and document
    private JCExpression fullRange;

    private JCExpression accumRange;

    protected JCExpression extractQuantifiers(JCExpression expr,
            ListBuffer<Name> ns) {
        if (expr instanceof JCIdent) {
            accumRange = trueLiteral;
            fullRange = trueLiteral;
            return expr;
        } else if (expr instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange a = (JmlStoreRefArrayRange) expr;
            JCExpression e = extractQuantifiers(a.expression, ns);
            JCExpression id;
            if (a.lo == a.hi && a.lo != null) {
                id = a.lo;
            } else {
                Name n = names.fromString("i" + (ns.size() + 1));
                id = factory.at(expr.pos).Ident(n); // No symbol - FIXME ???
                id.type = syms.intType;
                ns.append(n);
                fullRange = treeutils
                        .makeBinary(a.pos, JCTree.AND, fullRange, treeutils
                                .makeBinary(a.pos, JCTree.LE, zeroLiteral, id));
                // JCExpression len =
                // factory.at(a.pos).Select(a.expression,lengthSym);
                JCExpression len = new JmlBBFieldAccess(lengthIdent,
                        a.expression);
                len.pos = a.pos;
                len.type = syms.intType;
                fullRange = treeutils.makeBinary(a.pos, JCTree.AND, fullRange,
                        treeutils.makeBinary(a.pos, JCTree.LT, id, len));
                if (a.lo != null)
                    accumRange = treeutils
                            .makeBinary(a.lo.pos, JCTree.AND, accumRange,
                                    treeutils.makeBinary(a.lo.pos, JCTree.LE,
                                            a.lo, id));
                if (a.hi != null)
                    accumRange = treeutils
                            .makeBinary(a.hi.pos, JCTree.AND, accumRange,
                                    treeutils.makeBinary(a.hi.pos, JCTree.LE,
                                            id, a.hi));
            }
            e = factory.at(expr.pos).Indexed(e, id);
            e.type = expr.type;
            return e;
        } else if (expr instanceof JCFieldAccess) {
            JCFieldAccess a = (JCFieldAccess) expr;
            JCExpression e = extractQuantifiers(a.selected, ns);
            if (e == a.selected) return e;
            e = factory.at(expr.pos).Select(e, a.sym);
            e.type = a.type;
            return e;
        } else {
            return expr;
        }
    }

    // FIXME - review and document
    protected void havocField(VarSymbol vsym, JCExpression selected, int pos,
            int npos, Type type, JCExpression preCondition) {
        JCIdent oldid = newIdentUse(vsym, pos);
        JCFieldAccess oldaccess = new JmlBBFieldAccess(oldid, selected);
        oldaccess.pos = pos;
        oldaccess.type = type;

        JCIdent newid = newIdentIncarnation(oldid, npos);
        JCFieldAccess newaccess = new JmlBBFieldAccess(newid, selected);
        newaccess.pos = pos;
        newaccess.type = type;

        JCExpression right = factory.at(pos).Conditional(preCondition,
                newaccess, oldaccess);
        right.type = type;

        JCExpression expr = new JmlBBFieldAssignment(newid, oldid, selected,
                right);
        expr.pos = pos;
        expr.type = type;

        addAssume(pos, Label.HAVOC, expr, currentBlock.statements);

    }

    // FIXME - review and document
    protected void havocEverything(JCExpression preCondition, int newpos) {
        // FIXME - if the precondition is true, then we do not need to add the
        // assumptions - we just need to call newIdentIncarnation to make a new
        // value in the map. This would shorten the VC. How often is this
        // really the case? Actually the preCondition does not need to be true,
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
            JCIdent oldid = newIdentUse(vsym, newpos);
            JCIdent newid = newIdentIncarnation(vsym, newpos);
            JCExpression e = factory.at(newpos).Conditional(preCondition,
                    newid, oldid);
            e.type = vsym.type;
            e = treeutils.makeEquality(newpos, newid, e);
            addAssume(newpos, Label.HAVOC, e, currentBlock.statements);
        }
        currentMap.everythingIncarnation = newpos; // FIXME - this now applies
                                                   // to every
                                                   // not-yet-referenced
                                                   // variable, independent of
                                                   // the preCondition
    }

    public void visitSkip(JCSkip that) {
        // do nothing
    }

    public void visitJmlStatement(JmlStatement that) {
        // These are the set and debug statements
        // Just do all the JML statements as if they were Java statements,
        // since they are part of specifications

        // FIXME _ should never reach this anymore
        log.noticeWriter
                .println("SHOULD NOT HAVE REACHED HERE - BasicBLocker.visitJmlStatment "
                        + that.token.internedName());
        boolean prevInSpecExpression = inSpecExpression;
        try {
            inSpecExpression = true;
            that.statement.accept(this);
        } finally {
            inSpecExpression = prevInSpecExpression;
        }
    }

    public void visitJmlStatementLoop(JmlStatementLoop that) {
        shouldNotBeCalled(that); // These are the specs for loops - they are
                                 // handled in the loop visitors
    }

    public void visitJmlStatementSpec(JmlStatementSpec that) {
        notImpl(that); // None of these are implemented as yet - FIXME
    }

    // FIXME - review
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        JmlStatementExpr now = null;
        if (that.token != JmlToken.COMMENT)
            currentBlock.statements.add(comment(that));
        if (that.token == JmlToken.ASSUME || that.token == JmlToken.ASSERT) {
            JCExpression expr = trSpecExpr(that.expression, that.source);
            JCExpression opt = trSpecExpr(that.optionalExpression, that.source);
            if (that.token == JmlToken.ASSUME) {
                // if (that.label == Label.EXPLICIT_ASSUME || that.label ==
                // Label.BRANCHT || that.label == Label.BRANCHE) {
                // now =
                // factory.at(that.pos).JmlExpressionStatement(that.token,that.label,expr);
                // now.optionalExpression = opt;
                // now.type = that.type;
                if (that.label == Label.LOOP) {
                    expr = that.expression; // FIXME - explain no translation
                }
                now = factory.at(that.pos).JmlExpressionStatement(that.token,
                        that.label, expr);
                copyEndPosition(now, that);
                now.optionalExpression = opt;
                now.type = that.type;
                currentBlock.statements.add(now);
                if (that.label == Label.EXPLICIT_ASSUME
                        || that.label == Label.BRANCHT
                        || that.label == Label.BRANCHE) {
                    checkAssumption(that.pos, that.label);
                }
            } else { // ASSERT
                if (that.label == Label.ASSUME_CHECK) {
                    expr = that.expression; // FIXME - explain no translation
                }
                addAssert(that.label, expr, that.associatedPos, newstatements,
                        that.pos, that.source, that);
            }

        } else if (that.token == JmlToken.UNREACHABLE) {
            JCExpression expr = treeutils.makeBooleanLiteral(
                    that.getStartPosition(), false);
            addAssert(Label.UNREACHABLE, expr, that.getStartPosition(),
                    currentBlock.statements, that.getStartPosition(),
                    log.currentSourceFile(), that);
        } else if (that.token == JmlToken.HENCE_BY) {
            log.error("esc.not.implemented", "hence_by in BasicBlocker");
        } else if (that.token == JmlToken.COMMENT) {
            // skip
        } else {
            log.error("esc.internal.error", "Unknown token in BasicBlocker: "
                    + that.token.internedName());
        }
    }

    // We introduce the name 'assumeCheck$<int>$<label>' in order to make
    // it easy to identify the places where assumptions are being checked.
    /**
     * Adds (translated) assertions/assumptions that do assumption feasibility
     * checking for an assumption that is just added to the currentBlock
     * 
     * @param pos
     *            a positive integer different than that used for any other
     *            checkAssumption call; it should also be the textual location
     *            of the assumption being tested
     * @param label
     *            a Label giving the kind of assumption being tested (in order
     *            to better interpret the implications of the assumptino not
     *            being feasible)
     */

    // FIXME - REVIEW and document
    protected void checkAssumption(int pos, /* @ non_null */Label label,
            List<JCStatement> statements) {
        if (!insertAssumptionChecks) return;
        JCExpression e;
        JCIdent id;
        String n = ASSUME_CHECK_PREFIX + pos + "$" + label.toString();
        if (useCountedAssumeCheck) {
            JCExpression count = treeutils.makeIntLiteral(pos, pos);
            e = treeutils
                    .makeBinary(pos, JCTree.NE, assumeCheckCountVar, count);
            id = newAuxIdent(n, syms.booleanType, pos, false);
            // e = treeutils.makeBinary(pos,JCTree.EQ,id,e);
            // assume assumeCheck$<int>$<label> == <assumeCheckCountVar> !=
            // <int>
            // To do the coreId method, we need to put this in the definitions
            // list
            // instead. And it does not hurt anyway.
            // addAssume(pos,Label.ASSUME_CHECK,e); // adds to the currentBlock
            BasicProgram.Definition def = new BasicProgram.Definition(pos, id,
                    e);
            newdefs.add(def);
            e = def.expr(context);
        } else {
            id = newAuxIdent(n, syms.booleanType, pos, false);
            e = id;
            if (assumeCheck == null)
                assumeCheck = e;
            else
                assumeCheck = treeutils.makeBinary(pos, JCTree.AND, e,
                        assumeCheck);
        }
        program.assumptionsToCheck.add(new Entry(e, n));
        // an assert without tracking
        // assert assumeCheck$<int>$<label>
        addAssertNoTrack(Label.ASSUME_CHECK, id, statements, pos, null); // FIXME
                                                                         // -
                                                                         // need
                                                                         // the
                                                                         // position
                                                                         // of
                                                                         // the
                                                                         // assume,
                                                                         // I
                                                                         // think
    }

    // FIXME - REVIEW and document
    protected void checkAssumption(int pos, /* @ non_null */Label label) {
        checkAssumption(pos, label, currentBlock.statements);
    }

    // FIXME - REVIEW and document
    public static class Entry implements Map.Entry<JCExpression, String> {
        JCExpression key;

        String       value;

        public Entry(JCExpression e, String s) {
            key = e;
            value = s;
        }

        public JCExpression getKey() {
            return key;
        }

        public String getValue() {
            return value;
        }

        public String setValue(String value) {
            String v = value;
            this.value = value;
            return v;
        }
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        currentBlock.statements.add(comment(that));
        // This wraps local declarations within the body of a method:
        // ghost local variables and model local classes
        // Just treat them like Java local declarations FIXME - check this - see
        // also JmlVariableDecl
        boolean prevInSpecExpression = inSpecExpression;
        try {
            inSpecExpression = true;
            for (JCTree t : that.list) {
                t.accept(this);
            }
        } finally {
            inSpecExpression = prevInSpecExpression;
        }
    }

    public void visitParens(JCParens that) {
        JCExpression expr = trExpr(that.expr);
        JCParens now = factory.Parens(expr);
        now.type = that.type;
        now.pos = that.pos;
        result = now;
        toLogicalForm.put(that, result);
    }

    // FIXME - what about embedded assignments within a conditional

    public void visitConditional(JCConditional that) {
        JCExpression cond = trExpr(that.cond);
        JCExpression truepart;
        JCExpression falsepart;
        JCExpression prev = condition;
        try {
            condition = treeutils.makeBinary(that.pos, JCTree.AND, prev, cond);
            truepart = trExpr(that.truepart);
            condition = treeutils.makeBinary(that.pos, JCTree.AND, prev,
                    treeutils.makeUnary(that.pos, JCTree.NOT, cond));
            falsepart = trExpr(that.falsepart);
        } finally {
            condition = prev;
        }
        JCConditional now = factory.Conditional(cond, truepart, falsepart);
        now.type = that.type;
        now.pos = that.pos;
        copyEndPosition(now, that);
        result = now;
        toLogicalForm.put(that, result);
    }

    public void visitUnary(JCUnary that) {
        JCExpression arg = trExpr(that.arg);
        int tag = that.getTag();
        if (tag == JCTree.POSTDEC || tag == JCTree.POSTINC
                || tag == JCTree.PREDEC || tag == JCTree.PREINC) {
            int op = tag == JCTree.PREDEC || tag == JCTree.POSTDEC ? JCTree.MINUS
                    : JCTree.PLUS;
            JCExpression e = treeutils.makeBinary(that.pos, op, arg,
                    treeutils.makeIntLiteral(that.pos, 1));
            result = doAssignment(that.type, arg, e, that.pos + 1, that);
            if (tag == JCTree.POSTDEC || tag == JCTree.POSTINC) result = arg;
            return;
        }
        if (arg == that.arg) {
            result = that;
            return;
        }
        JCUnary now = factory.at(that.pos).Unary(that.getTag(), arg);
        now.operator = that.operator;
        now.type = that.type;
        copyEndPosition(now, that);
        result = now;
        toLogicalForm.put(that, result);
    }

    // FIXME - what about embedded assignments within short-circuit operations

    public void visitBinary(JCBinary that) {
        JCExpression left = trExpr(that.lhs);
        JCExpression right;
        if (that.getTag() == JCTree.OR) {
            JCExpression prev = condition;
            try {
                condition = treeutils.makeBinary(that.lhs.pos, JCTree.AND,
                        condition,
                        treeutils.makeUnary(that.lhs.pos, JCTree.NOT, left));
                right = trExpr(that.rhs);
            } finally {
                condition = prev;
            }
        } else if (that.getTag() == JCTree.AND) {
            JCExpression prev = condition;
            try {
                condition = treeutils.makeBinary(that.lhs.pos, JCTree.AND,
                        condition, left);
                right = trExpr(that.rhs);
            } finally {
                condition = prev;
            }
        } else {
            right = trExpr(that.rhs);
        }
        if (that.getTag() == JCTree.PLUS && that.type == syms.stringType) {
            // FIXME - review the handling of strings
            JCIdent concat = newAuxIdent("concat$", syms.stringType, that.pos,
                    false);
            JCExpression nleft = left;
            JCExpression nright = right;
            // FIXME - we should actually use proper conversion methods here and
            // for other binary operators
            if (nleft.type != syms.stringType) {
                nleft = newAuxIdent("STRING$$" + (unique++), syms.stringType,
                        left.pos, false);
            }
            if (nright.type != syms.stringType) {
                nright = newAuxIdent("STRING$$" + (unique++), syms.stringType,
                        right.pos, false);
            }
            JCMethodInvocation now = factory.at(that.pos).Apply(
                    null,
                    concat,
                    com.sun.tools.javac.util.List.<JCExpression> of(nleft,
                            nright));
            now.type = syms.stringType;
            result = now;
            copyEndPosition(result, that);
            toLogicalForm.put(that, result);
            return;
        }
        result = treeutils.makeBinary(that.pos, that.getTag(), that.operator,
                left, right);
        if (that.getTag() == JCTree.DIV || that.getTag() == JCTree.MOD) {
            JCExpression e = treeutils.makeBinary(that.rhs.pos, JCTree.NE,
                    right, zeroLiteral);
            e = treeutils.makeJmlBinary(that.rhs.pos, JmlToken.IMPLIES,
                    condition, e);
            addAssert(inSpecExpression ? Label.UNDEFINED_DIV0
                    : Label.POSSIBLY_DIV0, e, that.pos,
                    currentBlock.statements, that.pos, log.currentSourceFile(),
                    that);
        }
        copyEndPosition(result, that);
        toLogicalForm.put(that, result);
    }

    // FIXME - review
    public void visitTypeCast(JCTypeCast that) {
        JCExpression e = trExpr(that.getExpression());
        if (that.type.isPrimitive()) {
            // FIXME - not implemented for numeric casts
            result = e;
        } else {
            Type type = trType(that.getType().type);
            JCExpression nnull = treeutils.makeEqObject(that.pos, e,
                    nullLiteral); // e == null
            JCExpression inst = makeNNInstanceof(e, e.pos, type, that.clazz.pos); // \typeof(e)
                                                                                  // <:
                                                                                  // \type(type)
            inst = treeutils.makeBinary(that.pos, JCTree.OR, nnull, inst);
            JCExpression test = treeutils.makeJmlBinary(e.getStartPosition(),
                    JmlToken.IMPLIES, condition, inst);
            addAssert(inSpecExpression ? Label.UNDEFINED_BADCAST
                    : Label.POSSIBLY_BADCAST, trSpecExpr(test, null), that.pos,
                    currentBlock.statements, that.pos, log.currentSourceFile(),
                    that);

            addClassPredicate(type);
            JCExpression lit = makeTypeLiteral(type, that.getType()
                    .getStartPosition());
            if (true || inSpecExpression) lit = trSpecExpr(lit, null); // FIXME
                                                                       // =
                                                                       // true?
            JCTypeCast now = factory.at(that.pos).TypeCast(lit, e);
            now.type = that.type;

            JCExpression nullcond = treeutils.makeJmlBinary(that.pos,
                    JmlToken.IMPLIES, condition, treeutils.makeJmlBinary(
                            that.pos, JmlToken.EQUIVALENCE,
                            treeutils.makeEqObject(that.pos, now, nullLiteral),
                            nnull));
            addAssume(e.getStartPosition(), Label.IMPLICIT_ASSUME, nullcond);

            result = now;
        }
        copyEndPosition(result, that);
        toLogicalForm.put(that, result);
    }

    // FIXME - review
    public void visitTypeTest(JCInstanceOf that) {
        JCExpression e = trExpr(that.getExpression());
        Type t = trType(that.getType().type);
        result = makeInstanceof(e, e.pos, t, that.getType().pos);
        copyEndPosition(result, that);
        toLogicalForm.put(that, result);
    }

    // FIXME - review this and callees
    public void visitIndexed(JCArrayAccess that) {
        JCExpression array = trExpr(that.getExpression());
        JCExpression index = trExpr(that.getIndex());
        checkArrayAccess(array, index, that.pos);

        JCIdent arrayID = getArrayIdent(that.type);
        result = new JmlBBArrayAccess(arrayID, array, index, that.pos,
                that.type);
        toLogicalForm.put(that, result);
    }

    // FIXME - REVIEW and document
    protected void checkForNull(JCExpression objTrans, int pos,
            JCExpression precondition, Label label) {
        // if (objTrans == thisId) return; // 'this' is always non-null
        JCExpression c = precondition == trueLiteral ? condition : treeutils
                .makeBinary(condition.pos, JCTree.AND, condition, precondition);
        JCExpression e = treeutils.makeNeqObject(pos, objTrans, nullLiteral);
        e = treeutils.makeJmlBinary(pos, JmlToken.IMPLIES, c, e);
        addAssert(
                label != null ? label : inSpecExpression ? Label.UNDEFINED_NULL_DEREFERENCE
                        : Label.POSSIBLY_NULL_DEREFERENCE, e, pos, currentBlock.statements,
                pos, log.currentSourceFile(), precondition); // FIXME -
                                                             // positions?
    }

    // FIXME - REVIEW and document
    protected void checkForZero(JCExpression objTrans, int pos,
            JCExpression precondition, Label label) {
        // if (objTrans == thisId) return; // 'this' is always non-null
        JCExpression c = precondition == trueLiteral ? condition : treeutils
                .makeBinary(condition.pos, JCTree.AND, condition, precondition);
        JCExpression e = treeutils.makeBinary(pos, JCTree.NE, objTrans,
                zeroLiteral);
        e = treeutils.makeJmlBinary(pos, JmlToken.IMPLIES, c, e);
        addAssert(
                label != null ? label : inSpecExpression ? Label.UNDEFINED_DIV0
                        : Label.POSSIBLY_DIV0, e, pos, currentBlock.statements,
                pos, log.currentSourceFile(), precondition); // FIXME -
                                                             // positions?
    }

    protected void checkForNegative(JCExpression objTrans, int pos,
            JCExpression precondition, Label label) {
        // if (objTrans == thisId) return; // 'this' is always non-null
        JCExpression c = precondition == trueLiteral ? condition : treeutils
                .makeBinary(condition.pos, JCTree.AND, condition, precondition);
        JCExpression e = treeutils.makeBinary(pos, JCTree.GE, objTrans,
                zeroLiteral);
        e = treeutils.makeJmlBinary(pos, JmlToken.IMPLIES, c, e);
        addAssert(label != null ? label
                : inSpecExpression ? Label.UNDEFINED_NEGATIVESIZE
                        : Label.POSSIBLY_NEGATIVESIZE, e, pos,
                currentBlock.statements, pos, log.currentSourceFile(),
                precondition); // FIXME - positions?
    }

    // FIXME - REVIEW and document
    protected void checkTrue(int pos, JCExpression assertion, Label label) {
        // if (objTrans == thisId) return; // 'this' is always non-null
        JCExpression e = treeutils.makeJmlBinary(pos, JmlToken.IMPLIES,
                condition, assertion);
        int p = pos;
        if (label == Label.ASSIGNABLE) p = assertion.pos; 
        addAssert(label, e, p, currentBlock.statements, pos,
                log.currentSourceFile(), assertion);
    }

    // FIXME - REVIEW and document
    protected void checkArrayAccess(JCExpression arrayTrans,
            JCExpression indexTrans, int pos) {

        JCExpression index = indexTrans;

        // Require that.index is not negative
        JCExpression e = treeutils.makeBinary(index.pos, JCTree.GE, index,
                zeroLiteral);
        e = treeutils.makeJmlBinary(e.pos, JmlToken.IMPLIES, condition, e);
        addAssert(inSpecExpression ? Label.UNDEFINED_NEGATIVEINDEX
                : Label.POSSIBLY_NEGATIVEINDEX, e, pos,
                currentBlock.statements, pos, log.currentSourceFile(),
                indexTrans); // FIXME _ untranslated index?

        // Require that.index is not too large
        e = new JmlBBFieldAccess(lengthIdent, arrayTrans);
        e.pos = pos;
        e.type = syms.intType;
        e = treeutils.makeBinary(index.pos, JCTree.LT, index, e);
        e = treeutils.makeJmlBinary(e.pos, JmlToken.IMPLIES, condition, e);
        addAssert(inSpecExpression ? Label.UNDEFINED_TOOLARGEINDEX
                : Label.POSSIBLY_TOOLARGEINDEX, e, pos,
                currentBlock.statements, pos, log.currentSourceFile(), index);
    }

    // FIXME - review
    public void visitSelect(JCFieldAccess that) {
        Symbol sym = that.sym;
        if (sym == null) {
            log.noticeWriter.println("NULL SYM IN SELECT: " + that.name); // FIXME
        } else if (sym.owner == null || sym.isStatic()) { // FIXME - isStatic is
                                                          // not correct for JML
                                                          // fields in
                                                          // interfaces
            // FIXME - is there something predefined to compare against?
            if (sym.toString().equals("class")) {
                // Class literal
                Type ty = trType(that.selected.type);
                addClassPredicate(ty);
                JCExpression now = factory.at(that.pos).Literal(TypeTags.CLASS,
                        ty);
                now.type = syms.classType;
                result = now;
            } else if (sym.toString().equals(ALLOC_VAR)) {
                // FIXME - the alloc field is not a static field. We get here
                // because
                // it is not created with an owner. The owner should be the
                // owning
                // class, but there is just one allocSym defined - there ought
                // to
                // be one per class, but that fix has not yet been made, hence
                // this hack here.
                JCExpression selected = trExpr(that.selected);

                // Require that.selected is not null - FIXME
                // checkForNull(selected,that.pos,trueLiteral,null);

                // JCFieldAccess now = factory.Select(selected,that.name);
                // now.pos = that.pos;
                // now.sym = that.sym;
                // now.type = that.type;
                result = allocSelect(that.pos, selected);
            } else {
                VarSymbol vsym = (VarSymbol) that.sym;
                JCIdent now = newIdentUse(vsym, that.pos);
                now.type = that.type;
                result = now;
            }
        } else if (sym instanceof VarSymbol) {
            JCExpression selected = trExpr(that.selected);

            // Require that.selected is not null
            checkForNull(selected, that.pos, trueLiteral, null);

            JCIdent id = newIdentUse((VarSymbol) sym, that.pos);
            JCFieldAccess now = new JmlBBFieldAccess(id, selected);
            now.pos = that.pos;
            now.type = that.type;
            result = now;
        } else if (sym instanceof MethodSymbol) {
            JCExpression selected = trExpr(that.selected);

            // Require that.selected is not null
            checkForNull(selected, that.pos, condition,
                    inSpecExpression ? Label.UNDEFINED_NULL_DEREFERENCE
                            : Label.POSSIBLY_NULL_DEREFERENCE);
            result = that;
        } else {
            // FIXME - don't know what this could be
            result = that;
        }
        toLogicalForm.put(that, result);
    }

    public Map<JCTree, JCTree> toLogicalForm = new HashMap<JCTree, JCTree>();

    public Map<JCTree, String> toValue       = new HashMap<JCTree, String>();

    // FIXME - review this
    public void visitIdent(JCIdent that) {
        if (that.sym instanceof VarSymbol) {
            VarSymbol vsym = (VarSymbol) that.sym;
            Symbol owner = that.sym.owner;
            if (owner != null && owner instanceof ClassSymbol
                    && !vsym.isStatic()
                    && // FIXME isStatic not correct forJML fields in interfaces
                    vsym.name != names._this
                    && !utils.isExprLocal(vsym.flags())) {
                // This is a field reference without the default this. prefix
                // We need to make it a JCFieldAccess with a 'this'

                // FIXME - is there a symbol for this?
                JCIdent thisIdX = factory.at(that.pos).Ident(names._this);
                VarSymbol v = new VarSymbol(0, thisIdX.name, owner.type, owner);
                v.pos = 0;
                thisIdX.sym = v;
                thisIdX.type = owner.type;
                JCFieldAccess now = factory.at(that.pos).Select(thisIdX, vsym.name);
                now.type = that.type;
                now.sym = vsym;
                result = trExpr(now);
            } else if (signalsVar != null && vsym == signalsVar.sym) {
                result = newIdentUse((VarSymbol) exceptionVar.sym, that.pos);
            } else if (vsym.name == names._this) {
                result = factory.at(that.pos).Ident(currentThisId.sym);
            } else if (owner == null
                    && vsym.name.toString().startsWith(RESULT_PREFIX)) {
                // If there are nested function calls, then the \result of the
                // inner
                // call is already translated into a $$result$pos identifier. We
                // don't want to further translate it by calling newIdentUse
                result = that;
            } else {
                result = newIdentUse(vsym, that.pos);
                copyEndPosition(result, that);
            }
        } else if (that.type instanceof TypeVar) {
            result = newTypeIdentUse((TypeSymbol) that.sym, that.pos);
        } else {
            // FIXME - what case is this?
            result = that;
        }
        toLogicalForm.put(that, result);
    }

    // FIXME -document
    private Map<String, Integer> strings = new HashMap<String, Integer>();

    public void visitLiteral(JCLiteral that) {
        // numeric, boolean, character, String, null
        // FIXME - not sure about characters or String or class literals
        result = that;
        if (that.typetag == TypeTags.CLASS) {
            if (that.value instanceof Type) {
                // Don't translate this type - it is treated like Java
                Type type = (Type) that.value;
                addClassPredicate(type);
            } else if (that.value instanceof String) {
                String s = that.value.toString();
                Integer i = strings.get(s);
                if (i == null) {
                    i = strings.size();
                    strings.put(s, i);
                }
                Name n = names.fromString("STRING" + i);
                result = factory.at(that.pos).Ident(n);
                result.type = that.type;
            }
        }
        toLogicalForm.put(that, result);
    }

    public void visitAssign(JCAssign that) {
        JCExpression left = trExpr(that.lhs);
        JCExpression right = trExpr(that.rhs);
        result = doAssignment(that.type, left, right, that.pos, that);
        copyEndPosition(result, that);
        toLogicalForm.put(that.lhs, result);
        toLogicalForm.put(that, result);
    }

    // FIXME - embedded assignments to array elements are not implemented; no
    // warning either
    // FIXME - is all implicit casting handled
    // Note that the left and right expressions are translated.
    protected JCExpression doAssignment(Type restype, JCExpression left,
            JCExpression right, int pos, JCExpression statement) {
        if (left instanceof JCIdent) {
            JCIdent id = (JCIdent) left;
            left = newIdentIncarnation(id, left.pos);
            JCBinary expr = treeutils.makeEquality(pos, left, right);
            copyEndPosition(expr, right);

            // FIXME - set line and source
            addAssume(TreeInfo.getStartPos(statement), statement,
                    Label.ASSIGNMENT, expr, newstatements);
            return left;
        } else if (left instanceof JCArrayAccess) {
            JCIdent arr = getArrayIdent(right.type);
            JCExpression ex = ((JCArrayAccess) left).indexed;
            JCIdent nid = newArrayIncarnation(right.type, left.pos);
            JCExpression expr = new JmlBBArrayAssignment(nid, arr, ex,
                    ((JCArrayAccess) left).index, right);
            expr.pos = pos;
            expr.type = restype;

            // FIXME - set line and source
            addAssume(TreeInfo.getStartPos(left), Label.ASSIGNMENT, expr,
                    newstatements);
            newIdentIncarnation(heapVar, pos);
            return left;
        } else if (left instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess) left;
            JCIdent oldfield = newIdentUse((VarSymbol) fa.sym, pos);
            JCIdent newfield = newIdentIncarnation(oldfield, pos);
            JCExpression expr = new JmlBBFieldAssignment(newfield, oldfield,
                    fa.selected, right);
            expr.pos = pos;
            expr.type = restype;

            // FIXME - set line and source
            addAssume(TreeInfo.getStartPos(left), Label.ASSIGNMENT, expr,
                    newstatements);
            newIdentIncarnation(heapVar, pos);
            return left;
        } else {
            log.error(
                    "jml.internal",
                    "Unexpected case in BasicBlocker.doAssignment: "
                            + left.getClass() + " " + left);
            return null;
        }
    }

    // FIXME - what about implicit type casts
    // += -= *= /= %= >>= <<= >>>= &= |= ^=
    public void visitAssignop(JCAssignOp that) {
        JCExpression left = trExpr(that.lhs);
        JCExpression right = trExpr(that.rhs);
        int op = that.getTag() - JCTree.ASGOffset;
        JCExpression e = treeutils.makeBinary(that.pos, op, left, right);
        if (that.getTag() == JCTree.DIV_ASG || that.getTag() == JCTree.MOD_ASG) {
            JCExpression ee = treeutils.makeBinary(that.rhs.pos, JCTree.NE,
                    right, zeroLiteral);
            ee = treeutils.makeJmlBinary(that.rhs.pos, JmlToken.IMPLIES,
                    condition, ee);
            addAssert(inSpecExpression ? Label.UNDEFINED_DIV0
                    : Label.POSSIBLY_DIV0, ee, that.pos,
                    currentBlock.statements, that.pos, log.currentSourceFile(),
                    that);
        }
        result = doAssignment(that.type, left, e, that.pos, that);
        toLogicalForm.put(that.lhs, result);
        toLogicalForm.put(that, result);
    }

    // FIXME - review
    public void visitVarDef(JCVariableDecl that) {
        currentBlock.statements.add(comment(that));
        JCIdent lhs = newIdentIncarnation(that, that.getPreferredPosition());
        if (that.init != null) {
            // Create and store the new lhs incarnation before translating the
            // initializer because the initializer is in the scope of the newly
            // declared variable. Actually if there is such a situation, it
            // will likely generate an error about use of an uninitialized
            // variable.
            JCExpression init = trJavaExpr(that.init);
            JCBinary expr = treeutils.makeBinary(that.pos, JCBinary.EQ, lhs,
                    init);
            addAssume(TreeInfo.getStartPos(that), Label.ASSIGNMENT, expr,
                    newstatements);
            // JmlStatementExpr assume =
            // factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
            // newstatements.add(assume);
        }
    }

    public void visitSynchronized(JCSynchronized that) {
        // FIXME - for now ignore any synchronization
        trExpr(that.getExpression()); // just in case there are side-effects
        that.body.accept(this);
    }

    // FIXME - review and document
    List<Map<Symbol, Type>> typeargsStack = new LinkedList<Map<Symbol, Type>>();

    // FIXME - review and document
    Map<Symbol, Type>       typeargs      = new HashMap<Symbol, Type>();

    // FIXME - review and document
    public void pushTypeArgs() {
        typeargsStack.add(0, typeargs);
        typeargs = new HashMap<Symbol, Type>();
    }

    // FIXME - review and document
    public void popTypeArgs() {
        typeargs = typeargsStack.remove(0);
    }

    // FIXME - review and document
    public void pushTypeArgs(Type type) {
        if (type.getTypeArguments() != null
                && type.getTypeArguments().size() != 0) {
            pushTypeArgs();
            Iterator<Type> args = type.getTypeArguments().iterator();
            Iterator<TypeSymbol> params = type.tsym.getTypeParameters()
                    .iterator();
            while (params.hasNext()) {
                typeargs.put(params.next(), args.next());
            }
        }
    }

    // FIXME - review and document
    public void popTypeArgs(Type type) {
        if (type.getTypeArguments() != null
                && type.getTypeArguments().size() != 0) {
            popTypeArgs();
        }
    }

    // FIXME - review and document
    public Type trType(Type type) {
        if (type instanceof Type.TypeVar) {
            Type t = typeargs.get(type.tsym);
            type = t != null ? t : ((Type.TypeVar) type).getUpperBound(); // FIXME
                                                                          // -
                                                                          // what
                                                                          // about
                                                                          // the
                                                                          // other
                                                                          // bounds?
        }
        return type;
    }

    // FIXME - review
    public void visitNewClass(JCNewClass that) {
        if (that.def != null) {
            // We take time out here to go check the anonymous class
            // Note that if the same BasicBlocker instance is used for different
            // translations, we will have recursive calls of convertMethodBody
            JmlEsc.instance(context).visitClassDef(that.def);
        }
        // FIXME - ignoring enclosing expressions

        boolean isHelper = false;
        JmlMethodInfo mi = null;
        JmlMethodDecl decl = null;
        int pos = that.pos;

        Type type = that.type;
        if (type instanceof Type.TypeVar) {
            Type tt = typeargs.get(type);
            type = tt != null ? tt : type.getUpperBound();
        }

        // This is the id of a new variable that represents the result of the
        // new operation.
        JCIdent id = newAuxIdent("$$new" + pos + "$", that.type, pos, false);
        JCIdent prevId = currentThisId;
        VarMap prevOldMap = oldMap;
        JCExpression prevResultVar = resultVar;

        try {
            pushTypeArgs();

            Symbol.MethodSymbol sym = (MethodSymbol) that.constructor;
            JmlSpecs.MethodSpecs mspecs = specs.getSpecs(sym);
            if (mspecs == null) {
                mspecs = JmlSpecs.defaultSpecs(context,methodDecl.sym,0); // FIXME - is this OK
                // Log.instance(context).error("jml.internal","Unexpected failure to find specifications (even an empty spec) for method "
                // + sym.owner + "." + sym);
                // throw new JmlInternalError();
            }

            if (sym.params == null && sym.erasure_field != null) {
                log.noticeWriter
                        .println("BINARY GENERIC NOT IMPLEMENTED - exiting "
                                + sym);
                throw new RuntimeException();
            }

            // Evaluate all of the arguments and assign them to new variables
            decl = mspecs.cases.decl;
            int dpos = decl == null ? pos : decl.pos;
            int i = 0;
            if (sym.params != null)
                for (VarSymbol vd : sym.params) {
                    JCExpression expr = that.args.get(i++);
                    JCIdent pid = newIdentIncarnation(vd, pos);
                    addAssume(expr.pos, Label.ARGUMENT,
                            treeutils.makeEquality(expr.pos, pid, trExpr(expr)));
                }

            if (sym.owner.type.getTypeArguments() != null) {
                Iterator<Type> arg = sym.owner.type.getTypeArguments()
                        .iterator();
                if (that.clazz instanceof JCTypeApply) {
                    Iterator<JCExpression> param = ((JCTypeApply) that.clazz)
                            .getTypeArguments().iterator();
                    while (arg.hasNext() && param.hasNext()) { // FIXME - look
                                                               // into this -
                                                               // for
                                                               // constructors
                                                               // at least there
                                                               // may not be any
                                                               // type arguments
                        TypeSymbol tsym = arg.next().tsym;
                        JCExpression value = param.next();
                        JCIdent typeId = newTypeVarIncarnation(tsym, value.pos);
                        JCExpression eq = treeutils.makeEqObject(value.pos,
                                typeId, treeutils.trType(value.pos, value));
                        addAssume(eq.pos, Label.ARGUMENT,
                                trSpecExpr(eq, decl.source()));
                        typeargs.put(tsym, value.type);
                    }
                }
            }

            // FIXME - observed that for the Object() constructor sym !=
            // mspecs.decl.sym ?????

            // Define a new thisId before translating the precondition
            currentThisId = id;
            resultVar = currentThisId;

            isHelper = utils.isHelper(sym);
            mi = getMethodInfo(sym);
            for (JmlMethodClauseExpr pre : mi.requiresPredicates) { // FIXME -
                                                                    // need to
                                                                    // put the
                                                                    // composite
                                                                    // precondition
                                                                    // here
                addAssert(Label.PRECONDITION,
                        trSpecExpr(pre.expression, pre.sourcefile), dpos,
                        newstatements, pos, pre.source(), pre);
            }

            // Save the current incarnation map, so that instances of \old in
            // the
            // postconditions of the called method are mapped to values just
            // before
            // the havoc of assigned variables (and not to the values at the
            // beginning
            // of the method being translated).
            oldMap = currentMap.copy();

            // Now make a new incarnation value for anything in the assignables
            // list,
            // effectively making its value something legal but undefined.
            // FIXME - if we do this, then we have to redo any field
            // initializations, etc.
            // FIXME - do we have the default right
            for (JmlMethodInfo.Entry entry : mi.assignables) {
                // What to do with preconditions? FIXME
                for (JCTree sr : entry.storerefs) {
                    if (sr instanceof JCIdent) {
                        JCIdent pid = (JCIdent) sr;
                        newIdentIncarnation(pid, pos + 1); // new incarnation
                    } else if (sr instanceof JmlSingleton) {
                        if (((JmlSingleton) sr).token == JmlToken.BSNOTHING) { // FIXME - should not have a JmlSingleton here
                            // OK
                        } else {
                            log.noticeWriter.println("UNIMPLEMENTED STORE REF "
                                    + sr.getClass());
                        }
                    } else if (sr instanceof JmlStoreRefKeyword) {
                        if (((JmlStoreRefKeyword) sr).token == JmlToken.BSNOTHING) {
                            // OK
                        } else {
                            log.noticeWriter.println("UNIMPLEMENTED STORE REF "
                                    + sr.getClass());
                        }
                    } else {
                        log.noticeWriter.println("UNIMPLEMENTED STORE REF "
                                + sr.getClass());
                    }
                }
            }

            Type typeToConstruct = that.clazz.type;
            // FIXME - should really only do this translation when in a
            // specification
            typeToConstruct = trType(typeToConstruct);
            addClassPredicate(typeToConstruct);

            JCIdent oldalloc = newIdentUse(allocSym, pos);
            JCIdent alloc = newIdentIncarnation(allocSym, allocCount);
            alloc.pos = pos;

            // assume <oldalloc> < <newalloc>
            JCExpression ee = treeutils.makeBinary(pos, JCTree.LT, oldalloc,
                    alloc);
            // ee = trSpecExpr(ee,null);
            addAssume(pos, Label.SYN, ee); // FIXME - translate?

            // assume <newid> != null;
            ee = treeutils.makeNeqObject(pos, id, nullLiteral); // FIXME -
                                                                // translate?
            // ee = trSpecExpr(ee,null);
            addAssume(pos, Label.SYN, ee);

            // assume \typeof(<newid>) == <declared type>
            ee = factory.at(pos).JmlMethodInvocation(JmlToken.BSTYPEOF,
                    com.sun.tools.javac.util.List.<JCExpression> of(id));
            ee.type = syms.classType;
            JCExpression lit = trSpecExpr(
                    makeTypeLiteral(typeToConstruct, pos), null);
            ee = treeutils.makeEqObject(pos, ee, lit);
            addAssume(pos, Label.SYN, ee);

            // assume <newid>.alloc = <newalloc>
            ee = new JmlBBFieldAccess(allocIdent, id); // FIXME pos, factory
            ee.pos = pos;
            ee.type = syms.intType;
            ee = treeutils.makeEquality(pos, ee, alloc);
            addAssume(pos, Label.SYN, ee);

            for (JmlMethodClauseExpr post : mi.ensuresPredicates) {
                addAssume(pos, Label.POSTCONDITION,
                        trSpecExpr(post.expression, post.source()));
            }
            if (!isHelper) {
                for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e, inv.source());
                    addAssume(pos, Label.INVARIANT, e);
                }
                for (JmlTypeClauseExpr inv : classInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e, inv.source());
                    addAssume(pos, Label.INVARIANT, e);
                }
            }
            // Take out the temporary variables for the arguments
            if (sym.params != null) for (VarSymbol vd : sym.params) {
                currentMap.remove(vd);
            }

            result = id;
        } finally {
            popTypeArgs();
            oldMap = prevOldMap;
            currentThisId = prevId;
            resultVar = prevResultVar;
        }
        toLogicalForm.put(that, result);
    }

    // FIXME - review
    public void visitNewArray(JCNewArray that) { // that.dims, elems, elemtype
        // that.dims - the array of explicit dimensions, if they exist; empty
        // list if the dimensions are implicit
        // that.elems - list of initializers
        // that.elemtype - the element type. This includes all implicit
        // dimensions
        // but not the explicit ones. So
        // new boolean[][] dims = empty list elems != null elemtype = boolean[]
        // type = boolean[][]
        // new boolean[3][] dims = {3}, elems = null elemtype = boolean[] type =
        // boolean[][]
        // new boolean[3][5] dims = {3,5} elems = null, elemtype = boolean type
        // = boolean[][]
        // This visit method is also called for the sub-initializers of an
        // initializer, in which case, for example for the components of { {1},
        // {2,3,4} }
        // dims = empty list elems != null elemtype = null type = int[]

        // First translate the initializer if it exists, since it makes
        // recursive calls
        List<JCExpression> newelems = null;
        if (that.elems != null) {
            newelems = new LinkedList<JCExpression>();
            for (JCExpression elem : that.elems) {
                newelems.add(trExpr(elem));
            }
        }

        int pos = that.pos;

        // assume <oldalloc> < <newalloc>
        JCIdent oldalloc = newIdentUse(allocSym, pos);
        JCIdent alloc = newIdentIncarnation(allocSym, allocCount);
        alloc.pos = pos;
        JCExpression e = treeutils.makeBinary(pos, JCTree.LT, oldalloc, alloc);
        addAssume(pos, Label.SYN, e);

        // assume <newarray> != null;
        JCIdent newarray = newAuxIdent("$$newarray$" + pos + "$", that.type,
                pos, false);
        e = treeutils.makeNeqObject(pos, newarray, nullLiteral);
        addAssume(pos, Label.ARRAY_INIT, e);

        // assume <newarray>.alloc = <newalloc>
        e = new JmlBBFieldAccess(allocIdent, newarray);
        e.pos = pos;
        e.type = syms.intType;
        e = treeutils.makeEquality(pos, e, alloc);
        addAssume(pos, Label.SYN, e);

        List<JCExpression> dims = that.dims;
        int ndims = dims.size();
        Type arrayType = that.type;

        ListBuffer<JCExpression> types = ListBuffer.<JCExpression> lb();
        JCExpression intTypeTree = factory.at(pos).TypeIdent(TypeTags.INT);
        intTypeTree.type = syms.intType;
        // ListBuffer<Name> inames = ListBuffer.<Name>lb();
        ListBuffer<JCVariableDecl> idecls = ListBuffer.<JCVariableDecl> lb();
        JCExpression range = trueLiteral;
        JCExpression access = null;

        if (newelems == null) {
            // no initializer, one or more dimensions given
            // FIXME - need to set the last elements to null

            int ind;
            JCExpression prevLen = null;
            for (ind = 0; ind < ndims; ind++) {

                JCExpression len = trExpr(that.dims.get(ind));
                // FIXME - need the precondition
                checkForNegative(len, len.pos, trueLiteral,
                        Label.POSSIBLY_NEGATIVESIZE);
                if (ind == 0) {
                    // <newarray>.length == <len>
                    e = new JmlBBFieldAccess(lengthIdent, newarray);
                    e.pos = pos;
                    e.type = syms.intType;
                    e = treeutils.makeEquality(pos, e, trExpr(len));
                    access = newarray;
                    prevLen = len;
                } else {
                    // (forall (i1::int ...) <range> => (...( <newarray> i1 ) i2
                    // ) ... in ).length == <len> )
                    types.append(intTypeTree);
                    Name nm = names.fromString("i" + ind);
                    JCIdent id = factory.at(pos).Ident(nm);
                    id.type = syms.intType;
                    // inames.append(nm);
                    idecls.append(treeutils.makeVariableDecl(id.name,
                            syms.intType, null, pos));
                    range = treeutils.makeBinary(pos, JCTree.AND, range,
                            treeutils.makeBinary(pos, JCTree.AND,
                                    treeutils.makeBinary(pos, JCTree.LE,
                                            zeroLiteral, id), treeutils
                                            .makeBinary(pos, JCTree.LT, id,
                                                    prevLen)));
                    arrayType = ((ArrayType) arrayType).elemtype;
                    JCIdent arraysID = getArrayIdent(arrayType);
                    access = new JmlBBArrayAccess(arraysID, access, id);
                    access.pos = pos;
                    access.type = arrayType;
                    JCExpression predicate = new JmlBBFieldAccess(lengthIdent,
                            access);
                    predicate.pos = pos;
                    predicate.type = syms.intType;
                    predicate = treeutils
                            .makeBinary(pos, JCTree.AND, treeutils
                                    .makeNeqObject(pos, access, nullLiteral),
                                    treeutils.makeEquality(pos, predicate,
                                            trExpr(len)));
                    e = factory.at(pos).JmlQuantifiedExpr(JmlToken.BSFORALL,
                            idecls.toList(), range, predicate);
                    e.type = syms.booleanType;
                }
                addAssume(pos, Label.ARRAY_INIT, e);
            }
            // (forall (i1::int ...) (...( <newarray> i1 ) i2 ) ... in ) != null
            // )
            arrayType = ((ArrayType) arrayType).elemtype;
            if (arrayType instanceof ArrayType) {
                types.append(intTypeTree);
                Name nm = names.fromString("i" + ind);
                JCIdent id = factory.at(pos).Ident(nm);
                id.type = syms.intType;
                // inames.append(nm);
                idecls.append(treeutils.makeVariableDecl(id.name, syms.intType,
                        null, pos));
                JCIdent arraysID = getArrayIdent(arrayType);
                access = new JmlBBArrayAccess(arraysID, access, id);
                access.pos = pos;
                access.type = arrayType;
                e = treeutils.makeEqObject(pos, access, nullLiteral);
                e = factory.at(pos).JmlQuantifiedExpr(JmlToken.BSFORALL,
                        idecls.toList(), trueLiteral, e);
                e.type = syms.booleanType;
                addAssume(pos, Label.ARRAY_INIT, e);
            }

        } else {
            // an initializer, but no dimensions given

            int num = newelems.size();
            JCExpression len = treeutils.makeIntLiteral(pos, num);

            // <newarray>.length == <len>
            e = new JmlBBFieldAccess(lengthIdent, newarray);
            e.pos = pos;
            e.type = syms.intType;
            e = treeutils.makeEquality(pos, e, trExpr(len));
            addAssume(pos, Label.ARRAY_INIT, e);

            int i = 0;
            for (JCExpression ee : newelems) {
                // create an assumption about each element of the new array,
                // given the initializer value (which might be a new array
                // itself)
                JCLiteral lit = treeutils.makeIntLiteral(ee.pos, i++);
                e = new JmlBBArrayAccess(getArrayIdent(ee.type), newarray, lit);
                e.pos = ee.pos;
                e.type = ee.type;
                e = treeutils.makeEquality(ee.pos, e, ee);
                addAssume(ee.pos, Label.ARRAY_INIT, e);
            }
        }
        result = newarray;
        toLogicalForm.put(that, result);
    }

    // FIXME
    public void visitTypeIdent(JCPrimitiveTypeTree that) {
        notImpl(that);
    }

    public void visitTypeArray(JCArrayTypeTree that) {
        notImpl(that);
    }

    public void visitTypeApply(JCTypeApply that) {
        notImpl(that);
    }

    public void visitTypeParameter(JCTypeParameter that) {
        notImpl(that);
    }

    public void visitWildcard(JCWildcard that) {
        notImpl(that);
    }

    public void visitTypeBoundKind(TypeBoundKind that) {
        notImpl(that);
    }

    public void visitAnnotation(JCAnnotation that) {
        notImpl(that);
    }

    public void visitModifiers(JCModifiers that) {
        notImpl(that);
    }

    public void visitErroneous(JCErroneous that) {
        notImpl(that);
    }

    public void visitLetExpr(LetExpr that) {
        notImpl(that);
    }

    // Adds specs to a Java Variable Declaration
    // FIXME - delegate to visitVarDef?
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        currentBlock.statements.add(comment(that));
        // FIXME - need to add various field specs tests
        JCIdent vd = newIdentIncarnation(that, that.pos);
        toLogicalForm.put(that, vd);
        if (that.init != null) {
            int p = that.init.pos;
            boolean prevInSpecExpression = inSpecExpression;
            try {
                if (Utils.instance(context).isJML(that.mods))
                    inSpecExpression = true;
                JCExpression ninit = trJavaExpr(that.init);
                addAssume(TreeInfo.getStartPos(that), Label.ASSIGNMENT,
                        treeutils.makeEquality(p, vd, ninit));
            } finally {
                inSpecExpression = prevInSpecExpression;
            }
        }
    }

    public void visitJmlSingleton(JmlSingleton that) {
        switch (that.token) {
            case BSRESULT:
                if (resultVar == null) {
                    throw new RuntimeException(); // FIXME - do something more
                                                  // informative - should not
                                                  // ever get here
                } else {
                    result = resultVar;
                }
                break;

            case INFORMAL_COMMENT:
                result = treeutils.makeBooleanLiteral(that.pos, true);
                break;

            case BSEXCEPTION:
                if (exceptionVar == null) {
                    // FIXME -error
                    log.noticeWriter.println("EXCEPTION VAR IS NULL");
                    result = null;
                } else {
                    result = newIdentUse((VarSymbol) exceptionVar.sym, that.pos);
                }
                break;

            case BSINDEX:
            case BSVALUES:
                if (that.info == null) {
                    log.error(
                            that.pos,
                            "esc.internal.error",
                            "No loop index found for this use of "
                                    + that.token.internedName());
                    result = null;
                } else {
                    result = newIdentUse((VarSymbol) that.info, that.pos);
                }
                break;

            case BSLOCKSET:
            case BSSAME:
            case BSNOTSPECIFIED:
            case BSNOTHING:
            case BSEVERYTHING:
                Log.instance(context).error(that.pos,
                        "jml.unimplemented.construct",
                        that.token.internedName(),
                        "BasicBlocker.visitJmlSingleton");
                // FIXME - recovery possible?
                break;

            default:
                Log.instance(context).error(that.pos, "jml.unknown.construct",
                        that.token.internedName(),
                        "BasicBlocker.visitJmlSingleton");
                // FIXME - recovery possible?
                break;
        }
        // result = that; // TODO - can all of these be present in a basic
        // block?
        toLogicalForm.put(that, result);
    }

    // public void visitJmlFunction(JmlFunction that) {
    // switch (that.token) {
    // case BSOLD :
    // case BSPRE :
    // // Handling of incarnation occurs later
    // result = that;
    // break;
    //
    // case BSTYPEOF :
    // case BSELEMTYPE :
    // case BSNONNULLELEMENTS :
    // case BSMAX :
    // case BSFRESH :
    // case BSREACH :
    // case BSSPACE :
    // case BSWORKINGSPACE :
    // case BSDURATION :
    // case BSISINITIALIZED :
    // case BSINVARIANTFOR :
    // case BSNOWARN:
    // case BSNOWARNOP:
    // case BSWARN:
    // case BSWARNOP:
    // case BSBIGINT_MATH:
    // case BSSAFEMATH:
    // case BSJAVAMATH:
    // case BSNOTMODIFIED:
    // case BSTYPELC:
    // Log.instance(context).error("esc.not.implemented","Not yet implemented token in BasicBlocker: "
    // + that.token.internedName());
    // result = trueLiteral; // FIXME - may not even be a boolean typed result
    // break;
    //
    // default:
    // Log.instance(context).error("esc.internal.error","Unknown token in BasicBlocker: "
    // + that.token.internedName());
    // result = trueLiteral; // FIXME - may not even be a boolean typed result
    // }
    // }

    public void visitJmlBinary(JmlBinary that) {
        JCExpression left = trExpr(that.lhs);
        JCExpression right;
        if (that.op == JmlToken.IMPLIES) {
            JCExpression prev = condition;
            try {
                condition = treeutils.makeBinary(that.lhs.pos, JCTree.AND,
                        condition, left);
                right = trExpr(that.rhs);
            } finally {
                condition = prev;
            }
        } else if (that.op == JmlToken.REVERSE_IMPLIES) {
            // This is rhs=>lhs, which is equivalent to lhs || !rhs
            // The short-circuit semantics is (lhs ? true : !rhs) [ instead of (
            // !rhs ? true : lhs) ]
            JCExpression prev = condition;
            try {
                condition = treeutils.makeBinary(that.lhs.pos, JCTree.AND,
                        condition,
                        treeutils.makeUnary(that.lhs.pos, JCTree.NOT, left));
                right = trExpr(that.rhs);
            } finally {
                condition = prev;
            }
        } else {
            right = trExpr(that.rhs);
        }

        result = treeutils.makeJmlBinary(that.pos, that.op, left, right);
        toLogicalForm.put(that, result);
    }

    // FIXME - how are these checked for definedness?
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        JmlToken op = that.op;
        if (op == JmlToken.BSFORALL || op == JmlToken.BSEXISTS) {
            JCExpression prevCondition = condition;
            try {
                ListBuffer<JCVariableDecl> decls = ListBuffer
                        .<JCVariableDecl> lb();
                for (JCVariableDecl d : that.decls) {
                    JCIdent id = newIdentUse(d.sym, 0);
                    JCVariableDecl dd = factory.at(d.pos).VarDef(d.mods,
                            id.name, d.vartype, null);
                    dd.type = d.type;
                    decls.append(dd);
                }
                JCExpression range = trExpr(that.range);
                condition = range == null ? condition : treeutils.makeBinary(
                        condition.pos, JCTree.AND, condition, range);
                JCExpression predicate = trExpr(that.value);
                JmlQuantifiedExpr now = factory.at(that.pos).JmlQuantifiedExpr(
                        op, decls.toList(), range, predicate);
                now.type = that.type;
                result = now;
            } finally {
                condition = prevCondition;
            }
        } else {
            result = trueLiteral;
            notImpl(that);
        }
        toLogicalForm.put(that, result);
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) {
        notImpl(that);
    }

    public void visitJmlLblExpression(JmlLblExpression that) {
        // The token is BSLBLANY, BSLBLPOS, BSLBLNEG. The substring(2) strips
        // off the BS.
        // The form of this string is parsed when the value is retrieved from
        // the prover context
        String n = "$$" + that.token.toString().substring(2) + "$" + that.pos
                + "$" + that.label;
        JCIdent id = newAuxIdent(n, that.type, that.pos, false);
        JCExpression e = treeutils.makeEquality(that.pos, id,
                trExpr(that.expression));
        addAssume(that.getStartPosition(), Label.LBL, e);
        result = id;
        toLogicalForm.put(that, result);
    }

    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        switch (that.token) {
            case BSNOTMODIFIED:
                // Allows multiple arguments; they may be store-refs with
                // wildcards (FIXME)
                JCExpression combined = null;
                for (JCExpression a : that.list) {
                    // FIXME - there is an issue with condition - how do we
                    // evaluate if old(e) is well-defined?
                    // defined as arg == \old(arg)
                    int pos = that.pos;
                    JCExpression e = trExpr(a);
                    VarMap prevMap = currentMap;
                    currentMap = oldMap;
                    try {
                        // FIXME - what happens if not_modifieds are nested, or
                        // within an old
                        // extraEnv = true;
                        JCExpression ee = trExpr(a);
                        ee = treeutils.makeEquality(pos, e, ee);
                        if (combined == null)
                            combined = ee;
                        else
                            combined = treeutils.makeBinary(pos, JCTree.AND,
                                    combined, ee);
                    } finally {
                        currentMap = prevMap;
                        // extraEnv = false;
                    }
                }
                result = combined;
                break;

            default:
                notImpl(that);
        }
    }

    public void visitJmlGroupName(JmlGroupName that) {
        notImpl(that);
    }

    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        notImpl(that);
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        notImpl(that);
    }

    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        notImpl(that);
    }

    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        notImpl(that);
    }

    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        notImpl(that);
    }

    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        notImpl(that);
    }

    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        notImpl(that);
    }

    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        notImpl(that);
    }

    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        notImpl(that);
    }

    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        notImpl(that);
    }

    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        notImpl(that);
    }

    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        notImpl(that);
    }

    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        notImpl(that);
    }

    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        notImpl(that);
    }

    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        notImpl(that);
    }

    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        notImpl(that);
    }

    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        notImpl(that);
    }

    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        notImpl(that);
    }

    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        notImpl(that);
    }

    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        notImpl(that);
    }

    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        notImpl(that);
    }

    // These do not need to be implemented
    public void visitTopLevel(JCCompilationUnit that) {
        shouldNotBeCalled(that);
    }

    public void visitImport(JCImport that) {
        shouldNotBeCalled(that);
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        shouldNotBeCalled(that);
    }

    public void visitJmlImport(JmlImport that) {
        shouldNotBeCalled(that);
    }

    /**
     * This method is not called for top-level classes, since the BasicBlocker
     * is invoked directly for each method.
     */
    // FIXME - what about for anonymous classes or local classes or nested
    // classes
    @Override
    public void visitClassDef(JCClassDecl that) {
        // Nested classes are found in JmlEsc. We get to this point if there is
        // a local
        // class declaration within method body.

        JmlEsc.instance(context).visitClassDef(that);
    }

    // Do not need to override this method
    // @Override
    // public void visitJmlClassDecl(JmlClassDecl that) {
    // super.visitJmlClassDecl(that);
    // }

    /** This method should never be called */
    @Override
    public void visitMethodDef(JCMethodDecl that) {
        shouldNotBeCalled(that);
    }

    /** This method should never be called */
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        shouldNotBeCalled(that);
    }

    // FIXME - this will go away
    public static class VarFinder extends JmlTreeScanner {

        private Set<JCIdent> vars; // FIXME - change to a collection?

        public VarFinder() {
        }

        public static Set<JCIdent> findVars(BasicProgram program) {
            VarFinder vf = new VarFinder();
            Set<JCIdent> v = new HashSet<JCIdent>();
            for (BasicProgram.Definition def : program.definitions()) {
                vf.find(def.id, v);
                vf.find(def.value, v);
            }
            for (JCExpression def : program.pdefinitions) {
                vf.find(def, v);
            }
            for (BasicBlock b : program.blocks()) {
                for (JCStatement st : b.statements()) {
                    vf.find(st, v);
                }
            }
            return v;
        }

        public static Set<JCIdent> findVars(List<? extends JCTree> that,
                Set<JCIdent> v) {
            VarFinder vf = new VarFinder();
            return vf.find(that, v);
        }

        public static Set<JCIdent> findVars(JCTree that, Set<JCIdent> v) {
            VarFinder vf = new VarFinder();
            return vf.find(that, v);
        }

        public Set<JCIdent> find(List<? extends JCTree> that, Set<JCIdent> v) {
            if (v == null)
                vars = new HashSet<JCIdent>();
            else
                vars = v;
            for (JCTree t : that)
                t.accept(this);
            return vars;
        }

        public Set<JCIdent> find(JCTree that, Set<JCIdent> v) {
            if (v == null)
                vars = new HashSet<JCIdent>();
            else
                vars = v;
            that.accept(this);
            return vars;
        }

        public void visitIdent(JCIdent that) {
            vars.add(that);
        }
    }

    /**
     * This class is a tree walker that finds any references to classes in the
     * tree being walked: types of anything, explicit type literals
     * 
     * @author David Cok
     * 
     */
    public static class ClassFinder extends JmlTreeScanner {

        private Set<Type> types;

        public ClassFinder() {
        }

        public static Set<Type> findS(List<? extends JCTree> that, Set<Type> v) {
            ClassFinder vf = new ClassFinder();
            return vf.find(that, v);
        }

        public static Set<Type> findS(JCTree that, Set<Type> v) {
            ClassFinder vf = new ClassFinder();
            return vf.find(that, v);
        }

        public Set<Type> find(List<? extends JCTree> that, Set<Type> v) {
            if (v == null)
                types = new HashSet<Type>();
            else
                types = v;
            for (JCTree t : that)
                t.accept(this);
            return types;
        }

        public Set<Type> find(JCTree that, Set<Type> v) {
            if (v == null)
                types = new HashSet<Type>();
            else
                types = v;
            that.accept(this);
            return types;
        }

        // visitAnnotation - FIXME

        // visitApply - expression: just scan the component expressions
        // visitAssert - statement: just scan the component expressions
        // visitAssign - no new types - just scan the component expressions
        // visitAssignOp - no new types - just scan the component expressions
        // visitBinary - only primitive types
        // visitBlock - statement: just scan the component expressions
        // visitBreak - statement: just scan the component expressions
        // visitCase - statement: just scan the component expressions
        // visitCatch - statement: just scan the component expressions - FIXME -
        // make sure to get the declaration
        // visitClassDef - FIXME ???
        // visitConditional - no new types - just scan the component expressions
        // visitContinue - statement: just scan the component expressions
        // visitDoLoop - statement: just scan the component expressions
        // visitErroneous - statement: just scan the component expressions
        // visitExec - statement: just scan the component expressions
        // visitForEachLoop - statement: just scan the component expressions -
        // FIXME - implied iterator?
        // visitForLoop - statement: just scan the component expressions

        public void visitIdent(JCIdent that) {
            if (!that.type.isPrimitive()) types.add(that.type);
            super.visitIdent(that);
        }

        // visitIf - statement: just scan the component expressions
        // visitImport - statement: just scan the component expressions
        // visitIndexed - FIXME
        // visitLabelled - statement: just scan the component expressions
        // visitLetExpr - FIXME
        // visitLiteral - FIXME
        // visitMethodDef - FIXME
        // visitModifiers - no new types
        // visitNewArray - FIXME

        public void visitNewClass(JCNewClass that) {
            types.add(that.type);
        }

        // visitParens - no new types - just scan the component expressions
        // visitReturn - statement: just scan the component expressions
        // visitSelect - FIXME
        // visitSkip - statement: just scan the component expressions
        // visitSwitch - statement: just scan the component expressions (FIXME _
        // might be an Enum)
        // visitSynchronized - statement: just scan the component expressions
        // visitThrow - statement: just scan the component expressions
        // visitTopLevel - statement: just scan the component expressions
        // visitTree
        // visitTry - statement: just scan the component expressions
        // visitTypeApply - FIXME ??
        // visitTypeArray - FIXME ??
        // visitTypeBoundKind - FIXME ??
        // visitTypeCast - FIXME ??

        public void visitTypeIdent(JCPrimitiveTypeTree that) {
            types.add(that.type);
            super.visitTypeIdent(that);
        }

        // visitTypeParameter - FIXME ??
        // visitTypeTest (instanceof) - scans the expression and the type
        // visitUnary - only primitive types
        // visitVarDef - FIXME ??
        // visitWhileLoop - statement: just scan the component expressions
        // visitWildcard - FIXME ??

        // visitJmlBBArrayAccess - FIXME ?
        // visitJmlBBArrayAssignment - FIXME ?
        // visitJmlBBFieldAccess - FIXME ?
        // visitJmlBBFieldAssignment - FIXME ?
        // visitJmlBinary - no new types - FIXME - subtype?
        // visitJmlClassDecl - FIXME - do specs also
        // visitJmlCompilationUnit - just scan internal components
        // visitJmlConstraintMethodSig - FIXME ?
        // visitJmlDoWhileLoop - FIXME - scan specs
        // visitJmlEnhancedForLoop - FIXME - scan specs
        // visitJmlForLoop - FIXME - scan specs
        // visitJmlGroupName - FIXME??
        // visitJmlImport - no types
        // visitLblExpression - no new types - scan component expressions
        // visitJmlMethodClause... - scan all component expressions - FIXME :
        // watch Decls, Signals, SigOnly
        // visitJmlMethodDecl - FIXME?? - do specs also
        // visitJmlMethodSpecs - FIXME??
        // visitJmlPrimitiveTypeTree - FIXME??
        // visitJmlQuantifiedExpr - FIXME??
        // visitJmlRefines - FIXME??
        // visitJmlSetComprehension - FIXME??
        // visitJmlSingleton - FIXME??
        // visitJmlSpecificationCase - FIXME?? - FIXME??
        // visitJmlStatement - FIXME??
        // visitJmlStatementDecls - FIXME??
        // visitJmlStatementExpr - FIXME??
        // visitJmlStatementLoop - FIXME??
        // visitJmlStatementSpec - FIXME??
        // visitJmlStoreRefArrayRange - FIXME??
        // visitJmlStoreRefKeyword - FIXME??
        // visitJmlStoreRefListExpression - FIXME??
        // visitJmlTypeClause... - scan all components - FIXME - is there more
        // to do?
        // visitJmlVariableDecl - FIXME??
        // visitJmlWhileLoop - FIXME - be sure to scan specs

        // FIXME - some things that can probably always be counted on: Object,
        // String, Class
        // FIXME - closure of super types and super interfaces
    }

    /**
     * This class is a tree walker that finds everything that is the target of a
     * modification in the tree being walked: assignments, assignment-ops,
     * increment and decrement operators, fields specified as modified by a
     * method call.
     */
    // FIXME - is the tree already in reduced BasicBlock form?
    public static class TargetFinder extends JmlTreeScanner {

        private List<JCExpression> vars;

        public TargetFinder() {
        }

        /**
         * Finds variables in the given JCTree, adding them to the list that is
         * the second argument; the second argument is returned.
         */
        public static/* @Nullable */List<JCExpression> findVars(JCTree that, /*
                                                                              * @
                                                                              * Nullable
                                                                              */
                List<JCExpression> v) {
            if (that == null) return v;
            TargetFinder vf = new TargetFinder();
            return vf.find(that, v);
        }

        /**
         * Finds variables in the given JCTrees, adding them to the list that is
         * the second argument; the second argument is returned.
         */
        public static List<JCExpression> findVars(
                Iterable<? extends JCTree> list, /* @Nullable */
                List<JCExpression> v) {
            TargetFinder vf = new TargetFinder();
            return vf.find(list, v);
        }

        /**
         * Finds variables in the given JCTrees, adding them to the list that is
         * the second argument; the second argument is returned.
         */
        public List<JCExpression> find(Iterable<? extends JCTree> list, /*
                                                                         * @Nullable
                                                                         */
                List<JCExpression> v) {
            if (v == null)
                vars = new ArrayList<JCExpression>();
            else
                vars = v;
            for (JCTree t : list)
                t.accept(this);
            return vars;
        }

        /**
         * Finds variables in the given JCTrees, adding them to the list that is
         * the second argument; the second argument is returned.
         */
        public List<JCExpression> find(JCTree that, List<JCExpression> v) {
            if (that == null) return v;
            if (v == null)
                vars = new ArrayList<JCExpression>();
            else
                vars = v;
            that.accept(this);
            return vars;
        }

        public void visitAssign(JCAssign that) {
            vars.add(that.lhs);
        }

        public void visitAssignOp(JCAssign that) {
            vars.add(that.lhs);
        }

        public void visitUnary(JCUnary that) {
            int op = that.getTag();
            if (op == JCTree.POSTDEC || op == JCTree.POSTINC
                    || op == JCTree.PREINC || op == JCTree.PREDEC)
                vars.add(that.getExpression());
        }

        // FIXME - also need targets of method calls, update statements of
        // loops,
        // initialization statements of loops, specs of method calls

    }

    /** A Map that caches class info for a given class symbol */
    @NonNull
    protected Map<Symbol, JmlClassInfo> classInfoMap = new HashMap<Symbol, JmlClassInfo>();

    /**
     * Returns the jmlClassInfo structure for a class, computing and caching it
     * if necessary.
     * 
     * @param cls
     *            the declaration whose info is desired
     * @return the corresponding JmlClassInfo structure; may be null if the
     *         argument has no associated symbol
     */
    // @ modifies (* contents of the classInfoMap *);
    // @ ensures cls.sym != null <==> \result != null;
    @Nullable
    JmlClassInfo getClassInfo(@NonNull JCClassDecl cls) {
        JmlClassInfo mi = classInfoMap.get(cls.sym);
        if (mi == null) {
            mi = computeClassInfo(cls.sym);
            classInfoMap.put(cls.sym, mi);
        }
        return mi;
    }

    /**
     * Returns the JmlClassInfo structure for the given Class Symbol, computing
     * and caching it if necessary
     * 
     * @param sym
     *            the Symbol for the class whose JmlClassInfo is wanted
     * @return the corresponding JmlClassInfo structure, null if sym is null
     */
    @Nullable
    JmlClassInfo getClassInfo(@NonNull Symbol sym) {
        if (sym == null) return null;
        ClassSymbol csym = (ClassSymbol) sym;
        JmlClassInfo mi = classInfoMap.get(sym);
        if (mi == null) {
            mi = computeClassInfo(csym);
            classInfoMap.put(sym, mi);
        }
        return mi;
    }

    // FIXME - what about nested classes ($-separated ?)
    /**
     * Returns the JmlClassInfo structure for the given dot-separated,
     * fully-qualified class name, computing and caching it if necessary
     * 
     * @param qualifiedName
     *            the fully-qualified name of the class
     * @return the corresponding JmlClassInfo structure, null if sym is null
     */
    @Nullable
    JmlClassInfo getClassInfo(@NonNull String qualifiedName) {
        Name n = Names.instance(context).fromString(qualifiedName);
        Symbol sym = Symtab.instance(context).classes.get(n);
        return getClassInfo(sym);
    }

    // TODO - review this
    /**
     * Computes the class information for a given class declaration.
     * 
     * @param csym
     *            the ClassSymbol for which to get JmlClassInfo
     * @return the corresponding JmlClassInfo
     */
    protected @Nullable
    JmlClassInfo computeClassInfo(@NonNull ClassSymbol csym) {
        TypeSpecs typeSpecs = specs.get(csym);
        if (typeSpecs == null) {
            if (csym == syms.arrayClass) {
                // This one is special
                JmlClassInfo classInfo = new JmlClassInfo(null);
                classInfo.typeSpecs = new TypeSpecs();
                classInfo.csym = csym;

                Type type = syms.objectType;
                classInfo.superclassInfo = getClassInfo(type.tsym);

                return classInfo;
            }
            // This should not happen - every class referenced is loaded,
            // even binary files. If there is no source and no specs, then
            // the typespecs will have essentially null
            // innards, but the object should be there.
            // If this point is reached, some class somehow escaped being
            // loaded.
            Log.instance(context).error("jml.internal",
                    "No typespecs for class " + csym);
            return null;
        }
        JCClassDecl tree = typeSpecs.decl;
        // 'tree' may be null if there is a binary class with no specs.
        // So we have to be sure there are default specs, which for
        // a class is essentially empty.

        JmlClassInfo classInfo = new JmlClassInfo(tree);
        classInfo.typeSpecs = typeSpecs;
        classInfo.csym = csym;

        Type type = csym.getSuperclass();
        classInfo.superclassInfo = (csym == syms.objectType.tsym || csym
                .isInterface()) ? null : getClassInfo(type.tsym);

        // Divide up the various type specification clauses into the various
        // types
        ListBuffer<JmlTypeClauseRepresents> represents = new ListBuffer<JmlTypeClauseRepresents>();
        ListBuffer<JCVariableDecl> modelFields = new ListBuffer<JCVariableDecl>();

        for (JmlTypeClause c : typeSpecs.clauses) {
            boolean isStatic = c.modifiers != null
                    && (c.modifiers.flags & Flags.STATIC) != 0;
            if (c instanceof JmlTypeClauseDecl) {
                JCTree tt = ((JmlTypeClauseDecl) c).decl;
                if (tt instanceof JCVariableDecl
                        && ((JmlAttr) Attr.instance(context))
                                .isModel(((JCVariableDecl) tt).mods)) {
                    // model field - find represents or make into abstract
                    // method
                    modelFields.append((JCVariableDecl) tt);
                } else {
                    // ghost fields, model methods, model classes are used as is
                    // newlist.append(tt);
                }
            } else {
                JmlToken token = c.token;
                if (token == JmlToken.INVARIANT) {
                    JmlTypeClauseExpr copy = (JmlTypeClauseExpr) c.clone();
                    copy.expression = treetrans.translate(copy.expression);
                    if (isStatic)
                        classInfo.staticinvariants.add(copy);
                    else
                        classInfo.invariants.add(copy);
                } else if (token == JmlToken.REPRESENTS) {
                    JmlTypeClauseRepresents r = (JmlTypeClauseRepresents) c;
                    represents.append(r);
                } else if (token == JmlToken.CONSTRAINT) {
                    if (isStatic)
                        classInfo.staticconstraints
                                .add((JmlTypeClauseConstraint) c);
                    else
                        classInfo.constraints.add((JmlTypeClauseConstraint) c);
                } else if (token == JmlToken.INITIALLY) {
                    classInfo.initiallys.add((JmlTypeClauseExpr) c);
                } else if (token == JmlToken.AXIOM) {
                    JmlTypeClauseExpr copy = (JmlTypeClauseExpr) c.clone();
                    copy.expression = treetrans.translate(copy.expression);
                    classInfo.axioms.add(copy);
                } else {
                    Log.instance(context).warning(
                            "esc.not.implemented",
                            "JmlEsc does not yet implement (and ignores) "
                                    + token.internedName());
                    // FIXME - readable if, writable if, monitors for, in, maps,
                    // initializer, static_initializer, (model/ghost
                    // declaration?)
                }
            }
        }
        return classInfo;
    }

    // FIXME - Review
    /** This class converts a counterexample into more readable information */
    public static class Tracer extends JmlTreeScanner {

        /** The compilation context */
        @NonNull
        Context         context;

        /** The counterexample information */
        @NonNull
        Counterexample ce;

        /** The log for output */
        @NonNull
        Log             log;

        @NonNull
        Writer          w;

        /**
         * A runtime exception used to jump up to a finally block in the visitor
         * calling stack
         */
        private static class ReturnException extends RuntimeException {
            private static final long serialVersionUID = -3475328526478936978L;
        }

        /**
         * A runtime exception used to jump up to a finally block in the visitor
         * calling stack
         */
        private static class ExException extends RuntimeException {
            private static final long serialVersionUID = -5610207201211221750L;
        }

        /**
         * Outputs the counterexample information in more readable form
         * 
         * @param context
         *            the compilation context
         * @param decl
         *            the method declaration
         * @param s
         *            the counterexample information to translate
         */
        public String trace(@NonNull Context context,
                @NonNull JCMethodDecl decl, @NonNull Counterexample s) {
            Tracer t = new Tracer(context, s);
            try {
                try {
                    decl.accept(t);
                } catch (ReturnException e) {
                    // ignore
                } catch (ExException e) {
                    // ignore
                } catch (RuntimeException e) {
                    t.w.append("FAILED : " + e + "\n");
                }
                t.w.append("END\n");
                return t.w.toString();
            } catch (IOException e) {
                Log.instance(context).noticeWriter.println("IOException");
                return "";
            }
        }

        /**
         * Translates the given position information into source, line and
         * column information
         * 
         * @param pos
         *            the position information to translate
         * @return A String containing human-readable source location
         *         information
         */
        public String getPosition(int pos) { // TODO - check about the second
                                             // argument of getColumnNumber
            return log.currentSourceFile().getName() + ":"
                    + log.currentSource().getLineNumber(pos) + " (col "
                    + log.currentSource().getColumnNumber(pos, false) + "): ";
        }

        /**
         * The constructor for this class
         * 
         * @param context
         *            the compilation context
         * @param s
         *            the counterexample information
         */
        protected Tracer(@NonNull Context context, @NonNull Counterexample s) {
            this.context = context;
            ce = s;
            log = Log.instance(context);
            w = new StringWriter();
        }

        // CAUTION: The Strings in use in these visit methods correspond to the
        // encoding used in the BasicBlocker methods. The BasicBlocker encodes
        // variables using combinations of variable name, declaration position,
        // and incarnation position. These are reflected in the counterexample
        // information and we need to match that as we interpret the
        // counterexample
        // information in these methods.

        // FIXME - this implementation needs fleshing out

        public void visitMethodDef(JCMethodDecl that) {
            try {
                w.append("START METHOD " + that.sym + "\n");
                for (JCVariableDecl param : that.params) {
                    String s = param.name + "$" + param.pos + "$0";
                    String value = ce.get(s);
                    w.append("Parameter value: " + param.name + " = "
                            + (value == null ? "<unused>" : value) + "\n");
                }
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            super.visitMethodDef(that);
        }

        public void visitIf(JCIf that) {
            String s = "branchCondition$" + that.pos + "$" + 0;
            String value = ce.get(s);
            try {
                if (value == null)
                    w.append(getPosition(that.pos)
                            + "!!!  Could not find value for branch (" + s
                            + ")\n");
                else {
                    w.append(getPosition(that.pos) + "Branch condition value: "
                            + value + "\n");
                    if (value.equals("true")) {
                        if (that.thenpart != null) that.thenpart.accept(this);
                    } else if (value.equals("false")) {
                        if (that.elsepart != null) that.elsepart.accept(this);
                    } else {
                        w.append("!!! Unknown value: " + value + "\n");
                    }
                }
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        public void visitAssign(JCAssign that) {
            try {
                if (that.lhs instanceof JCIdent) {
                    JCIdent id = (JCIdent) that.lhs;
                    String s = id.name + "$" + ((VarSymbol) id.sym).pos + "$"
                            + that.pos;
                    String value = ce.get(s);
                    if (value == null)
                        w.append(getPosition(that.pos)
                                + "!!!  Could not find value for variable ("
                                + s + ")\n");
                    else
                        w.append(getPosition(that.pos) + "Assignment: "
                                + id.name + " = " + value + "\n");
                }
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        public void visitTry(JCTry that) {
            try {
                try {
                    that.body.accept(this);
                } catch (ReturnException e) {
                    // do the finally block
                    if (that.finalizer != null) {
                        w.append(getPosition(that.finalizer.pos)
                                + "Executing finally block\n");
                        that.finalizer.accept(this);
                    }
                    throw e;
                } catch (ExException e) {
                    // FIXME
                }
            } catch (IOException e) {
                // FIXME
            }
        }

        public void visitReturn(JCReturn that) {
            String s = "$$result"; // FIXME - should replace with defined
                                   // constnat, but this is missing the final $
            String value = ce.get(s);
            try {
                if (that.expr != null) {
                    if (value == null)
                        w.append(getPosition(that.pos)
                                + "!!!  Could not find return value (" + s
                                + ")\n");
                    else
                        w.append(getPosition(that.pos)
                                + "Executed return: value = " + value + "\n");
                } else {
                    w.append(getPosition(that.pos) + "Executed return\n");
                }
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            throw new ReturnException();
        }
    }

    /**
     * A runtime exception used to jump up to a finally block in the visitor
     * calling stack
     */
    private static class ReturnException extends RuntimeException {
        private static final long serialVersionUID = -3475328526478936978L;
    }

    /**
     * A runtime exception used to jump up to a finally block in the visitor
     * calling stack
     */
    private static class ExException extends RuntimeException {
        private static final long serialVersionUID = -5610207201211221750L;
    }

    /**
     * Outputs the counterexample information in more readable form
     * 
     * @param context
     *            the compilation context
     * @param program
     *            the program whose counterexample information is to be printed
     * @param ce
     *            the counterexample information to translate
     * @param prover
     *            the prover from which the counterexample information came
     */
    public static String trace(@NonNull Context context,
            @NonNull BasicProgram program, @NonNull Counterexample ce,
            IProver prover) {
        String s = null;
        try {
            s = (new TracerBB(context)).trace(program, ce, prover);
        } catch (ReturnException e) {
            // ignore
        } catch (ExException e) {
            // ignore
        } catch (IOException e) {
            Log.instance(context).noticeWriter.println("ABORTED");
        } catch (RuntimeException e) {
            Log.instance(context).noticeWriter.println("ABORTED");
            throw e;
        }
        return s;
    }

    // FIXME - Review
    /**
     * This class converts a counterexample into more readable information; it
     * uses the basic program form rather than using the Java AST.
     */
    public static class TracerBB extends JmlTreeScanner {

        /** The counterexample information */
        Counterexample          ce;

        boolean                  showSubexpressions;

        /** The log for output */
        @NonNull
        Log                      log;

        /** The program being traced */
        BasicProgram             program;

        /** The compilation context */
        @NonNull
        Context                  context;

        Map<String, String>      values;

        Writer                   w;

        /** The prover that was used to create the counterexample */
        IProver                  prover;

        Symtab                   syms;

        List<IProverResult.Span> path = null;

        /**
         * Translates the given position information into source, line and
         * column information
         * 
         * @param pos
         *            the position information to translate
         * @return A String containing human-readable source location
         *         information
         */
        public String getPosition(int pos) { // TODO - check about the second
                                             // argument of getColumnNumber
            return log.currentSourceFile().getName() + ":"
                    + log.currentSource().getLineNumber(pos) + " (col "
                    + log.currentSource().getColumnNumber(pos, false) + "): \t";
        }

        /**
         * The constructor for this class
         * 
         * @param context
         *            the compilation context
         */
        public TracerBB(@NonNull Context context) {
            this.context = context;
            log = Log.instance(context);
            syms = Symtab.instance(context);
            w = new StringWriter();
            showSubexpressions = JmlOption.isOption(context,
                    JmlOption.SUBEXPRESSIONS) || true;
        }

        // FIXME - DOCUMENT
        public static String trace(@NonNull Context context,
                @NonNull BasicProgram program, Counterexample ce,
                IProver prover) {
            try {
                return new TracerBB(context).trace(program, ce, prover);
            } catch (IOException e) {
                return "<IOException: " + e + ">";
            }
        }

        // @ ensures this.program != null && this.ce != null;
        // @ ensures this.program != program && this.ce != ce;
        public String trace(@NonNull BasicProgram program, Counterexample ce,
                IProver prover) throws IOException {
            this.ce = ce;
            this.program = program;
            this.prover = prover;
            w = new StringWriter();
            w.append("COUNTEREXAMPLE TRACE \n\n");
            values = ce.getMap();
            this.subexp = new Subexpressor(context, prover, values, w);
            this.path = new LinkedList<IProverResult.Span>();

            for (JCVariableDecl vd : program.methodDecl.params) {
                String n = vd.name + "$" + vd.pos + "$0";
                String value = ce.get(n);
                w.append(getPosition(vd.pos) + "Parameter \t" + n + " \t= "
                        + (value == null ? "?" : value) + "\n");
            }

            if (showSubexpressions) prover.reassertCounterexample(ce);
            // for (Map.Entry<JCTree,String> entry:
            // ((Counterexample)ce).mapv.entrySet()) { // FIXME - hacked to get
            // at map - fix this
            // values.put(entry.getKey(),entry.getValue());
            // }
            BasicBlock block = program.startBlock();
            outer: while (traceBlockStatements(block, ce)) {
                for (BasicBlock next : block.followers()) {
                    String s = next.id().toString();
                    String value = ce.get(s);
                    if (value != null && value.equals("false")) {
                        block = next;
                        continue outer;
                    }
                }
                break;
            }
            w.append("END\n");
            ce.putMap(values);
            ce.putPath(path);
            return w.toString();
        }

        // CAUTION: The Strings in use in these visit methods correspond to the
        // encoding used in the BasicBlocker methods. The BasicBlocker encodes
        // variables using combinations of variable name, declaration position,
        // and incarnation position. These are reflected in the counterexample
        // information and we need to match that as we interpret the
        // counterexample
        // information in these methods.

        // FIXME - Review
        protected boolean traceBlockStatements(BasicBlock b, Counterexample ce)
                throws IOException {
            w.append(" [ block " + b.id() + " ]\n");
            boolean sawFalseAssert = false;
            String pos = null, lastpos;
            for (JCStatement statement : b.statements) {
                if (!(statement instanceof JmlStatementExpr)) {
                    log.error(statement.pos, "esc.internal.error",
                            "Incorrect statement type in traceBlockStatements: "
                                    + statement.getClass());
                    continue;
                }
                JmlStatementExpr s = (JmlStatementExpr) statement;
                JCExpression expr = s.expression;
                if (expr instanceof JCIdent) {
                    Name nm = ((JCIdent) expr).name;
                    if (nm.toString()
                            .startsWith(BasicBlocker.ASSUMPTION_PREFIX)) {
                        for (BasicProgram.Definition def : program.definitions) {
                            if (def.id.name.equals(nm)) {
                                expr = def.value;
                                break;
                            }
                        }
                        // for (JCExpression e : program.pdefinitions) {
                        // if (e instanceof JCBinary && ((JCBinary)e).lhs
                        // instanceof JCIdent &&
                        // ((JCIdent)((JCBinary)e).lhs).name.equals(nm)) {
                        // expr = ((JCBinary)e).rhs;
                        // }
                        // }
                    }
                }
                lastpos = pos;
                pos = getPosition(s.pos);
                Label label = s.label;
                if (label == Label.ASSUME_CHECK) {
                    // skip
                } else if (s.token == JmlToken.ASSUME) {
                    if (label == Label.ASSIGNMENT) {
                        // FIXME - array, field assignments
                        if (expr instanceof JCBinary) {
                            JCBinary bin = (JCBinary) expr;
                            if (!(bin.lhs instanceof JCIdent)) {
                                failure(label, expr);
                                continue;
                            }
                            Name n = ((JCIdent) bin.lhs).name;
                            String v = value((JCIdent) bin.lhs);
                            w.append(pos + "Assignment " + n + " = " + v
                                    + "  [" + bin.rhs + "]\n");
                            record(bin.lhs, v);
                            showSubexpressions(bin.rhs);

                        } else if (expr instanceof JmlBBArrayAssignment) {
                            JmlBBArrayAssignment asg = (JmlBBArrayAssignment) expr;
                            JCExpression array = asg.args.get(2);
                            JCExpression index = asg.args.get(3);
                            JCExpression value = asg.args.get(4);

                            List<String> results = subexp.getValues(array,
                                    index, value);
                            if (results != null) {
                                w.append(pos + "ArrayAssignment "
                                        + results.get(0) + "[" + results.get(1)
                                        + "] = " + results.get(2) + "  [ ("
                                        + array + ")[" + index + "] = " + value
                                        + " ]\n");
                            }
                            showSubexpressions(array);
                            showSubexpressions(index);
                            showSubexpressions(value);
                        } else if (expr instanceof JmlBBFieldAssignment) {
                            JmlBBFieldAssignment asg = (JmlBBFieldAssignment) expr;
                            JCExpression obj = asg.args.get(2);
                            JCIdent field = (JCIdent) asg.args.get(0);
                            JCExpression value = asg.args.get(3);

                            List<String> results = subexp.getValues(obj, value);
                            w.append(pos + "FieldAssignment " + results.get(0)
                                    + "." + field + " = " + results.get(1)
                                    + "  [ (" + obj + ")." + field + " = "
                                    + value + " ]\n");
                            showSubexpressions(obj);
                            showSubexpressions(value);

                        } else {
                            failure(label, expr);
                        }
                    } else if (label == Label.ARGUMENT) {
                        // Called methods and new object (called constructor)
                        // calls
                        if (!(expr instanceof JCBinary)) {
                            failure(label, expr);
                            continue;
                        }
                        JCBinary bin = (JCBinary) expr;
                        if (!(bin.lhs instanceof JCIdent)) {
                            failure(label, expr);
                            continue;
                        }
                        Name n = ((JCIdent) bin.lhs).name;
                        String v = value((JCIdent) bin.lhs);
                        w.append(pos + "ArgumentEvaluation " + n + " = " + v
                                + "  [" + bin.rhs + "]\n");
                        record(bin.lhs, v);
                        showSubexpressions(bin.rhs);

                    } else if (label == Label.RECEIVER) {
                        // Called methods and new object (called constructor)
                        // calls
                        if (!(expr instanceof JCBinary)) {
                            failure(label, expr);
                            continue;
                        }
                        JCBinary bin = (JCBinary) expr;
                        if (!(bin.lhs instanceof JCIdent)) {
                            failure(label, expr);
                            continue;
                        }
                        Name n = ((JCIdent) bin.lhs).name;
                        String v = value((JCIdent) bin.lhs);
                        w.append(pos + "ReceiverEvaluation " + n + " = " + v
                                + "  [" + bin.rhs + "]\n");
                        record(bin.lhs, v);
                        showSubexpressions(bin.rhs);

                    } else if (label == Label.BRANCHC) {
                        if (!(expr instanceof JCBinary)) {
                            failure(label, expr);
                            continue;
                        }
                        JCBinary bin = (JCBinary) expr;
                        if (!(bin.lhs instanceof JCIdent)) {
                            failure(label, expr);
                            continue;
                        }
                        String v = value((JCIdent) bin.lhs);
                        w.append(pos + label + " = " + v + "  [" + bin.rhs
                                + "]\n");
                        record(bin.lhs, v);
                        showSubexpressions(bin.rhs);

                    } else if (label == Label.LBL) {
                        if (!(expr instanceof JCBinary)) {
                            failure(label, expr);
                            continue;
                        }
                        JCBinary bin = (JCBinary) expr;
                        if (!(bin.lhs instanceof JCIdent)) {
                            failure(label, expr);
                            continue;
                        }
                        JCIdent id = (JCIdent) bin.lhs;
                        String lbl = id.toString();
                        int k = lbl.lastIndexOf('$');
                        lbl = lbl.substring(k + 1);
                        String v = value(id);
                        w.append(pos + label + ": " + lbl + " = " + v + "  ["
                                + bin.rhs + "]\n");
                        record(id, v);
                        showSubexpressions(bin.rhs);

                    } else if (label == Label.SWITCH_VALUE) {
                        if (!(expr instanceof JCBinary)) {
                            failure(label, expr);
                            continue;
                        }
                        JCBinary bin = (JCBinary) expr;
                        if (!(bin.lhs instanceof JCIdent)) {
                            failure(label, expr);
                            continue;
                        }
                        String v = value((JCIdent) bin.lhs);
                        w.append(pos + "switch value = " + v + "  [" + bin.rhs
                                + "]\n");
                        record(bin.lhs, v);
                        showSubexpressions(bin.rhs);

                    } else if (label == Label.SYN) { // FIXME - rename the SYN
                                                     // types that are wanted
                        if (expr instanceof JCBinary) {
                            JCExpression lhs = ((JCBinary) expr).lhs;
                            if (lhs instanceof JCIdent) {
                                String value = ce.get(((JCIdent) lhs).name
                                        .toString());
                                w.append(pos + "Syn " + lhs + " = " + value
                                        + "\n");
                            } else {
                                w.append(pos + "Syn " + expr + "\n");
                            }
                        } else {
                            w.append(pos + "Syn " + expr + "\n");
                        }
                    } else if (label == Label.EXPLICIT_ASSUME) {
                        if (expr instanceof JCIdent) {
                            // This will happen for tracked assumptions
                            Name n = ((JCIdent) expr).name;
                            String value = ce.get(n.toString());
                            w.append(pos + label + " " + n + " = " + value
                                    + "\n");
                            JCExpression e = findDefinition(n);
                            record(expr, value);
                            if (e != null) showSubexpressions(e);
                        } else {
                            w.append(pos + label + " " + expr + "\n");
                            showSubexpressions(expr);
                        }
                    } else if (label == Label.DSA) {
                        if (!(expr instanceof JCBinary)) {
                            failure(label, expr);
                            continue;
                        }
                        JCBinary bin = (JCBinary) expr;
                        if (!(bin.lhs instanceof JCIdent)) {
                            failure(label, expr);
                            continue;
                        }
                        if (!(bin.rhs instanceof JCIdent)) {
                            failure(label, expr);
                            continue;
                        }
                        w.append(lastpos + label + " = "
                                + value((JCIdent) bin.lhs) + "  [" + bin.rhs
                                + "]\n");
                        // no subexpressions
                    } else if (label == Label.RETURN) {
                        w.append(pos + "Executing return statement\n");
                    } else if (label == Label.TERMINATION) {
                        if (!(expr instanceof JCBinary)) {
                            failure(label, expr);
                            continue;
                        }
                        JCBinary bin = (JCBinary) expr;
                        if (!(bin.lhs instanceof JCBinary)) {
                            failure(label, expr);
                            continue;
                        }
                        bin = (JCBinary) bin.lhs;
                        if (!(bin.lhs instanceof JCIdent)) {
                            failure(label, expr);
                            continue;
                        }
                        String v = value((JCIdent) bin.lhs);
                        if (v.equals("0")) {
                            String rv = bin.lhs.toString().replace(
                                    "terminationVar", "result");
                            String vv = valueNull(rv);
                            w.append(pos
                                    + "Called method returned normally ["
                                    + bin.lhs
                                    + "="
                                    + v
                                    + "]"
                                    + (vv == null ? "" : ", return value = "
                                            + vv + " [" + rv + "]\n"));
                        } else {
                            String rv = bin.lhs.toString().replace(
                                    "terminationVar", "exception");
                            String vv = subexp.getType(rv);
                            w.append(pos
                                    + "Called method exited with an exception ["
                                    + bin.lhs
                                    + "="
                                    + v
                                    + "]"
                                    + (vv == null ? "" : ", exception type = "
                                            + vv) + "\n");
                        }
                    } else if (label == Label.METHODAXIOM) {
                        // Just print the axiom - don't try to evaluate it
                        w.append(pos + label + " " + expr + "\n");
                    } else if (label == Label.ARRAY_INIT) {
                        // Just print the expression - don't try to evaluate it
                        w.append(pos + label + " " + expr + "\n");
                    } else if (label == Label.BRANCHT || label == Label.HAVOC) {
                        // skip
                    } else if (label == Label.BRANCHE) {
                        if (expr instanceof JCUnary) {
                            JCExpression e = ((JCUnary) expr).getExpression();
                            if (e instanceof JCIdent) {
                                String value = value((JCIdent) e);
                                record(expr, value);
                            }
                        }
                    } else {
                        w.append(pos + label + " " + expr + "\n");
                        showSubexpressions(expr);
                    }
                } else if (s.token == JmlToken.ASSERT) {
                    String value = null;
                    String name = null;
                    if (expr instanceof JCIdent) {
                        name = ((JCIdent) expr).toString();
                        value = ce.get(name);
                        JCExpression e = findDefinition(((JCIdent) expr).name);
                        if (e != null) expr = e;
                    }
                    w.append(pos + "Assert [" + label + "] "
                            + (value == null ? "" : value) + "   [" + expr
                            + "]\n");
                    showSubexpressions(expr);
                    if ("false".equals(value)) {
                        sawFalseAssert = true;
                    }
                } else if (s.token == JmlToken.COMMENT) {
                    w.append(pos);
                    w.append("Comment: // ");
                    w.append(((JCLiteral) s.expression).value.toString());
                    w.append("\n");
                } else {
                    log.error(pos, "esc.internal.error",
                            "Incorrect token type in traceBlockStatements: "
                                    + s.token.internedName());
                }
                if (label == Label.PRECONDITION) {
                    // int sp = TreeInfo.getStartPos(expr);
                    // int ep =
                    // TreeInfo.getEndPos(expr,log.currentSource().getEndPosTable());
                    // int type = IProverResult.Span.NORMAL;
                    // String result = values.get(expr.toString());
                    // type = result == null ? IProverResult.Span.NORMAL :
                    // result.equals("true") ? IProverResult.Span.TRUE :
                    // result.equals("false") ? IProverResult.Span.FALSE :
                    // IProverResult.Span.NORMAL;
                    // if (sp >= 0 && ep >= sp) path.add(new
                    // IProverResult.Span(sp,ep,type)); // FIXME - don't think
                    // the end position is right for statements
                    doLogicalSubExprs(expr);
                } else if (label == Label.ASSIGNMENT
                        || label == Label.EXPLICIT_ASSERT
                        || label == Label.EXPLICIT_ASSUME
                        || label == Label.BRANCHT || label == Label.BRANCHE
                        || label == Label.SWITCH_VALUE) {
                    int sp = TreeInfo.getStartPos(s);
                    int ep = TreeInfo.getEndPos(s, log.currentSource()
                            .getEndPosTable());
                    int type = IProverResult.Span.NORMAL;
                    if (label != Label.ASSIGNMENT) {
                        String result = values.get(expr.toString());
                        type = result == null ? IProverResult.Span.NORMAL
                                : result.equals("true") ? IProverResult.Span.TRUE
                                        : result.equals("false") ? IProverResult.Span.FALSE
                                                : IProverResult.Span.NORMAL;
                    }
                    if (sp >= 0 && ep >= sp)
                        path.add(new IProverResult.Span(sp, ep, type)); // FIXME
                                                                        // -
                                                                        // don't
                                                                        // think
                                                                        // the
                                                                        // end
                                                                        // position
                                                                        // is
                                                                        // right
                                                                        // for
                                                                        // statements
                } else if (label == Label.CATCH_CONDITION) {
                    int sp = TreeInfo.getStartPos(s);
                    int ep = TreeInfo.getEndPos(s, log.currentSource()
                            .getEndPosTable());
                    int type = IProverResult.Span.NORMAL;
                    type = IProverResult.Span.NORMAL;
                    if (sp >= 0 && ep >= sp)
                        path.add(new IProverResult.Span(sp, ep, type)); // FIXME
                                                                        // -
                                                                        // don't
                                                                        // think
                                                                        // the
                                                                        // end
                                                                        // position
                                                                        // is
                                                                        // right
                                                                        // for
                                                                        // statements
                } else if (label == Label.POSTCONDITION
                        || label == Label.SIGNALS) {
                    JCExpression texpr = expr;
                    if (label == Label.SIGNALS) {// FIXME - a NPE thrown from
                                                 // here does not produce any
                                                 // visible error
                        texpr = (texpr instanceof JmlBinary && ((JmlBinary) texpr).op == JmlToken.IMPLIES) ? ((JmlBinary) texpr).rhs
                                : null;
                        texpr = (texpr instanceof JCBinary && ((JCBinary) texpr)
                                .getTag() == JCTree.AND) ? ((JCBinary) texpr).rhs
                                : null;
                        if (texpr instanceof JmlBinary
                                && ((JmlBinary) texpr).op == JmlToken.IMPLIES) {
                            JCExpression tt = ((JmlBinary) texpr).rhs;
                            if (tt instanceof JmlBinary
                                    && ((JmlBinary) tt).op == JmlToken.IMPLIES) {
                                texpr = (JmlBinary) tt;
                            }
                        } else {
                            texpr = null;
                        }
                    } else {
                        texpr = (texpr instanceof JmlBinary && ((JmlBinary) texpr).op == JmlToken.IMPLIES) ? ((JmlBinary) texpr).rhs
                                : null;
                        texpr = (texpr instanceof JmlBinary && ((JmlBinary) texpr).op == JmlToken.IMPLIES) ? texpr
                                : null;
                    }
                    if (texpr instanceof JmlBinary) {
                        JmlBinary rexpr = (JmlBinary) texpr;
                        JCExpression lhs = rexpr.lhs;
                        JCExpression rhs = rexpr.rhs;
                        int sp = TreeInfo.getStartPos(lhs);
                        int ep = TreeInfo.getEndPos(lhs, log.currentSource()
                                .getEndPosTable());
                        int type = IProverResult.Span.NORMAL;
                        String result = values.get(lhs.toString());
                        type = result == null ? IProverResult.Span.NORMAL
                                : result.equals("true") ? IProverResult.Span.TRUE
                                        : result.equals("false") ? IProverResult.Span.FALSE
                                                : IProverResult.Span.NORMAL;
                        if (sp >= 0 && ep >= sp)
                            path.add(new IProverResult.Span(sp, ep, type)); // FIXME
                                                                            // -
                                                                            // don't
                                                                            // think
                                                                            // the
                                                                            // end
                                                                            // position
                                                                            // is
                                                                            // right
                                                                            // for
                                                                            // statements
                        if (type != IProverResult.Span.FALSE) {
                            sp = TreeInfo.getStartPos(rhs);
                            ep = TreeInfo.getEndPos(rhs, log.currentSource()
                                    .getEndPosTable());
                            type = IProverResult.Span.NORMAL;
                            result = values.get(rhs.toString());
                            type = result == null ? IProverResult.Span.NORMAL
                                    : result.equals("true") ? IProverResult.Span.TRUE
                                            : result.equals("false") ? IProverResult.Span.FALSE
                                                    : IProverResult.Span.NORMAL;
                            if (sp >= 0 && ep >= sp)
                                path.add(new IProverResult.Span(sp, ep, type)); // FIXME
                                                                                // -
                                                                                // don't
                                                                                // think
                                                                                // the
                                                                                // end
                                                                                // position
                                                                                // is
                                                                                // right
                                                                                // for
                                                                                // statements
                        }
                    } else {
                        int sp = TreeInfo.getStartPos(s);
                        int ep = TreeInfo.getEndPos(s, log.currentSource()
                                .getEndPosTable());
                        int type = IProverResult.Span.NORMAL;
                        String result = values.get(expr.toString());
                        type = result == null ? IProverResult.Span.NORMAL
                                : result.equals("true") ? IProverResult.Span.TRUE
                                        : result.equals("false") ? IProverResult.Span.FALSE
                                                : IProverResult.Span.NORMAL;
                        if (sp >= 0 && ep >= sp)
                            path.add(new IProverResult.Span(sp, ep, type)); // FIXME
                                                                            // -
                                                                            // don't
                                                                            // think
                                                                            // the
                                                                            // end
                                                                            // position
                                                                            // is
                                                                            // right
                                                                            // for
                                                                            // statements
                    }
                } else if (label == Label.TERMINATION) {
                    int sp = TreeInfo.getStartPos(s);
                    int ep = TreeInfo.getEndPos(s, log.currentSource()
                            .getEndPosTable());
                    int type = IProverResult.Span.NORMAL;
                    {
                        JCExpression e = ((JCBinary) ((JCBinary) expr).lhs).lhs;
                        String result = values.get(e.toString());
                        int k = result == null ? 0 : Integer.valueOf(result);
                        type = k < 0 ? IProverResult.Span.EXCEPTION
                                : IProverResult.Span.NORMAL;
                    }
                    if (sp >= 0 && ep >= sp)
                        path.add(new IProverResult.Span(sp, ep, type)); // FIXME
                                                                        // -
                                                                        // don't
                                                                        // think
                                                                        // the
                                                                        // end
                                                                        // position
                                                                        // is
                                                                        // right
                                                                        // for
                                                                        // statements
                }
                if (sawFalseAssert) break;// Stop reporting the trace if we
                                          // encounter a false assertion
            }
            return !sawFalseAssert;
        }

        public int doExpr(JCExpression expr, boolean show) {
            int sp = TreeInfo.getStartPos(expr);
            int ep = TreeInfo.getEndPos(expr, log.currentSource().getEndPosTable());
            int type = IProverResult.Span.NORMAL;
            String result = values.get(expr.toString());
            type = result == null ? IProverResult.Span.NORMAL : result
                    .equals("true") ? IProverResult.Span.TRUE : result
                    .equals("false") ? IProverResult.Span.FALSE
                    : IProverResult.Span.NORMAL;
            if (show && sp >= 0 && ep >= sp) {
                //log.noticeWriter.println("SPAN " + sp + " " + ep + " " + result + " " + expr );
                path.add(new IProverResult.Span(sp, ep, type)); // FIXME - don't
                                                                // think the end
                                                                // position is
                                                                // right for
                                                                // statements
            }
            return type;
        }

        public int doLogicalSubExprs(JCExpression expr) {
            int r = -10;
            if (expr instanceof JCBinary) {
                int op = expr.getTag();
                JCBinary bin = (JCBinary) expr;
                if (op == JCTree.OR) {
                    r = doLogicalSubExprs(bin.lhs);
                    if (r != IProverResult.Span.TRUE) {
                        r = doLogicalSubExprs(bin.rhs);
                    }
                } else if (op == JCTree.AND) {
                    r = doLogicalSubExprs(bin.lhs);
                    if (r != IProverResult.Span.FALSE) {
                        r = doLogicalSubExprs(bin.rhs);
                    }
                } else if (op == JCTree.BITOR) {
                    r = doLogicalSubExprs(bin.lhs);
                    int rr = doLogicalSubExprs(bin.rhs);
                    r = (rr == IProverResult.Span.TRUE) ? rr : r;
                } else {
                    r = doExpr(expr, true);
                }
            } else if (expr instanceof JmlBinary) {
                JmlBinary bin = (JmlBinary) expr;
                JmlToken op = bin.op;
                if (op == JmlToken.IMPLIES) {
                    r = doLogicalSubExprs(bin.lhs);
                    if (r != IProverResult.Span.FALSE) {
                        r = doLogicalSubExprs(bin.rhs);
                    }
                } else if (op == JmlToken.REVERSE_IMPLIES) {
                    r = doLogicalSubExprs(bin.lhs);
                    if (r != IProverResult.Span.TRUE) {
                        r = doLogicalSubExprs(bin.rhs);
                    }
                } else {
                    r = doLogicalSubExprs(bin.rhs);
                    r = doExpr(expr, false);
                }
            } else {
                r = doExpr(expr, true);
            }

            // FIXME - also do NOT, conditional expression, boolean ==,
            // EQUIVALENCE, INEQUIVALENCE
            return r;
        }

        public JCExpression findDefinition(Name name) {
            for (BasicProgram.Definition def : program.definitions()) {
                JCIdent id = def.id;
                if (id.name != name) continue;
                return def.value;
            }
            // for (JCExpression e: program.pdefinitions) {
            // if (!(e instanceof JCBinary)) continue;
            // JCBinary bin = (JCBinary)e;
            // if (!(bin.lhs instanceof JCIdent)) continue;
            // JCIdent id = (JCIdent)bin.lhs;
            // if (id.name != name) continue;
            // return bin.rhs;
            // }
            return null;
        }

        public String value(JCIdent id) {
            String v = ce.get(id.name.toString());
            if (v == null) v = "?";
            return v;
        }

        public String valueNull(JCIdent id) {
            return ce.get(id.name.toString());
        }

        public String valueNull(String id) {
            return ce.get(id);
        }

        public void failure(Label label, JCExpression expr) {
            log.warning("jml.internal.notsobad",
                    "Unable to interpret counterexample trace.  A " + label
                            + " statement has unexpected structure: " + expr);
        }

        Subexpressor subexp;

        public String showSubexpressions(JCExpression expr) {
            if (showSubexpressions) try {
                subexp.walk(expr);
                return w.toString();
            } catch (IOException e) {
                return "<IOException>";
            }
            return "";
        }

        public void record(JCExpression expr, String value) {
            subexp.values.put(expr.toString(), value);
        }
    }

    static int count = 1000000;

    /** This class requests values of subexpressions from the prover */
    public static class Subexpressor extends JmlTreeScanner {

        Context                   context;

        IProver                   prover;

        JmlTree.Maker             factory;

        Names                     names;

        Symtab                    syms;

        Writer                    w;

        final String              prefix   = "X$$$";

        List<JCBinary>            exprs    = new LinkedList<JCBinary>();

        Map<String, JCExpression> requests = new HashMap<String, JCExpression>();

        Map<String, String>       values   = null;

        /**
         * Top-level call for the class - puts requests to the prover for each
         * subexpression of the argument, returning the results in 'requests'.
         * This method can be reused, but is not thread-safe.
         */
        public void walk(JCExpression expr) throws IOException {
            exprs.clear();
            requests.clear();
            scan(expr);
            IProverResult res = null;
            try {
                for (JCExpression e : exprs) {
                    prover.assume(e);
                }
                res = prover.check(true);
            } catch (ProverException ex) {
                w.append(ex.toString()); // FIXME - clean up the error reporting
                                         // here and in the RUntimeExceptions
                                         // just below.
                w.append("\n");
                return;
            }
            if (res == null) {
                throw new RuntimeException(
                        "ERROR: no additional information available");
            } else if (!res.isSat()) {
                throw new RuntimeException("ERROR: no longer satisfiable");
            } else {
                Counterexample nce = (Counterexample)res.counterexample();
                for (JCBinary bin : exprs) {
                    JCIdent id = (JCIdent) bin.lhs;
                    String value = nce.get(id.toString());
                    if (value != null && id.type.tag == TypeTags.CHAR) {
                        value = ((Character) (char) Integer.parseInt(value))
                                .toString() + " (" + value + ")";
                    }
                    if (value == null) value = "?";
                    w.append("                                " + value
                            + "\t = " + bin.rhs + "\n");
                    values.put(bin.rhs.toString(), value);
                }
            }
        }

        /**
         * Top-level call that returns a list of values (as Strings)
         * corresponding to the list of expressions in the argument
         */
        public List<String> getValues(JCExpression... exprlist)
                throws IOException {
            IProverResult res = null;
            List<JCIdent> ids = new LinkedList<JCIdent>();
            try {
                for (JCExpression e : exprlist) {
                    JCIdent id = newIdent(e);
                    JCExpression ex = factory.at(Position.NOPOS).Binary(
                            JCTree.EQ, id, e);
                    ex.type = syms.booleanType;
                    ids.add(id);
                    prover.assume(ex);
                }
                res = prover.check(true);
            } catch (ProverException ex) {
                w.append(ex.toString());
                w.append("\n"); // FIXME - better error response here and below
                return null;
            }
            if (res == null) {
                w.append("ERROR: no additional information available\n");
            } else if (!res.isSat()) {
                w.append("ERROR: no longer satisfiable\n");
            } else {
                Counterexample nce = (Counterexample)res.counterexample();
                List<String> out = new LinkedList<String>();
                int k = 0;
                for (JCIdent id : ids) {
                    String value = nce.get(id.name.toString());
                    if (value == null) value = "?";
                    out.add(value);
                    if (values != null) {
                        JCExpression ee = exprlist[k];
                        String e = ee.toString();
                        if (ee.type.tag == TypeTags.CHAR) {
                            e = ((Character) (char) Integer.parseInt(e))
                                    .toString();
                        }
                        values.put(e, value);
                        // System.out.println("MAPPING: " + e + " " + value);
                        k++; // FIXME - increment inside or outside the if
                             // statement
                    }
                }
                prover.reassertCounterexample(nce);
                return out;
            }
            return null;
        }

        /** Returns the dynamic type of the variable given in the argument */
        public String getType(String eid) {
            try {
                factory.at(Position.NOPOS);
                JCIdent expr = factory.Ident(Names.instance(context)
                        .fromString(eid));
                expr.type = syms.objectType;
                JCExpression e = factory.JmlMethodInvocation(JmlToken.BSTYPEOF,
                        expr);
                e.type = syms.classType;
                JCIdent id = newIdent(e);
                JCExpression ex = factory.at(Position.NOPOS).Binary(JCTree.EQ,
                        id, e);
                ex.type = syms.booleanType;
                prover.assume(ex);
                IProverResult res = prover.check(true);
                if (res == null) {
                    w.append("ERROR: no additional information available\n");
                } else if (!res.isSat()) {
                    w.append("ERROR: no longer satisfiable\n");
                } else {
                    Counterexample nce = (Counterexample)res.counterexample();
                    String value = nce.get(id.name.toString());
                    return value;
                }
            } catch (IOException e) {
                Log.instance(context).noticeWriter.println(e.toString());

            } catch (ProverException e) {
                Log.instance(context).noticeWriter.println(e.toString());
            }
            return null;
        }

        public Subexpressor(Context context, IProver prover,
                Map<String, String> values, Writer w) {
            this.context = context;
            this.prover = prover;
            this.factory = JmlTree.Maker.instance(context);
            this.names = Names.instance(context);
            this.syms = Symtab.instance(context);
            this.w = w;
            this.values = values;
        }

        public void request(JCExpression expr) {
            JCIdent id = newIdent(expr);
            requests.put(id.name.toString(), expr);
            JCBinary bin = factory.Binary(JCTree.EQ, id, expr);
            bin.type = syms.booleanType;
            bin.pos = Position.NOPOS;
            exprs.add(bin);
        }

        /** Creates a unique identifier with the type of the given expression */
        public JCIdent newIdent(JCExpression expr) {
            Type t = expr.type;
            Name n = names.fromString(prefix + (++count));
            JCIdent id = factory.Ident(n);
            id.type = t;
            return id;
        }

        /**
         * Scan the given JCTree, issuing a request() call for each
         * subexpression encountered
         */
        public void scan(JCTree that) {
            super.scan(that);
            if (that instanceof JCExpression && !(that instanceof JCParens)
                    && !(that instanceof JCLiteral))
                request((JCExpression) that);
        }

        /**
         * Scan the given JCTree, issuing a request() call for each
         * subexpression encountered, but not for the argument itself
         */
        public void scanNoRequest(JCTree that) {
            super.scan(that);
        }

        public void visitLiteral(JCLiteral tree) {
            String r = tree.toString();
            values.put(r, r);
        }

        /**
         * Overridden so that we request the arguments but not the method call
         * itself.
         */
        public void visitApply(JCMethodInvocation tree) {
            scanNoRequest(tree.meth);
            scan(tree.args);
        }

        /** Don't request values for quantified expressions */
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree) {
            // do not scan the subexpressions of a quantified expression
        }

        public void visitCatch(JCCatch tree) {
            super.visitCatch(tree);
        }
    }

    /** This class computes metrics over a BasicBlock */
    public static class Counter extends JmlTreeScanner {

        int nodes         = 0; // nodes

        int assumes       = 0;

        int asserts       = 0;

        int blocks        = 0;

        int statements    = 0;

        int paths         = 0;

        int maxBlockNodes = 0;

        public void count(BasicBlock b) {
            for (JCTree t : b.statements())
                t.accept(this);
            nodes += b.statements().size();
        }

        public static int counts(BasicBlock b) {
            return counts(b.statements());
        }

        public static int counts(List<JCStatement> sts) {
            Counter c = new Counter();
            for (JCTree t : sts)
                t.accept(c);
            return c.nodes + sts.size();
        }

        static public Counter count(BasicProgram b) {
            Counter c = new Counter();
            int max = 0;
            for (BasicBlock bb : b.blocks()) {
                int c1 = c.nodes;
                c.count(bb);
                if (c.nodes - c1 > max) max = c.nodes - c1;
            }
            c.maxBlockNodes = max;
            for (BasicProgram.Definition t : b.definitions()) {
                t.id.accept(c);
                t.value.accept(c);
            }
            for (JCTree t : b.pdefinitions)
                t.accept(c);
            for (JCTree t : b.background())
                t.accept(c);
            c.blocks = b.blocks().size();
            return c;
        }

        static public int countx(BasicProgram b) {
            Counter c = new Counter();
            for (BasicProgram.Definition t : b.definitions()) {
                t.id.accept(c);
                t.value.accept(c);
            }
            for (JCTree t : b.pdefinitions)
                t.accept(c);
            for (JCTree t : b.background())
                t.accept(c);
            return c.nodes;
        }

        static public int countAST(JCTree node) {
            Counter c = new Counter();
            node.accept(c);
            if (node instanceof JCBlock) c.nodes++;
            return c.nodes;
        }

        static public int countASTStatements(JCTree node) {
            Counter c = new Counter();
            node.accept(c);
            if (node instanceof JCBlock) c.statements++;
            return c.statements;
        }

        public Counter() {
        }

        public void add(Counter c) {
            nodes += c.nodes;
            assumes += c.assumes;
            asserts += c.asserts;
            blocks += c.blocks;
            statements += c.statements;
            maxBlockNodes = maxBlockNodes < c.maxBlockNodes ? c.maxBlockNodes
                    : maxBlockNodes;
        }

        public void scan(JCTree that) {
            nodes++;
            if (that instanceof JCStatement) statements++;
            super.scan(that);
        }

        public void visitJmlStatementExpr(JmlStatementExpr that) {
            if (that.token == JmlToken.ASSUME) assumes++;
            if (that.token == JmlToken.ASSERT) asserts++;
            super.visitJmlStatementExpr(that);
        }

        public String toString() {
            return "    " + blocks + " blocks; " + nodes + " nodes; "
                    + maxBlockNodes + " max; " + assumes + " assumes; "
                    + asserts + " asserts; ";
        }
    }

}

