/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.esc.BasicProgramParent.BlockParent;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.TypeTag;
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
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.tree.JCTree.TypeBoundKind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

/** This class is a base class for converting a Java AST into a basic block 
 * program. The methods here take care of converting control flow
 * into basic blocks, including adding assumptions at the beginning of blocks
 * to control feasible paths. For example, an if(b) ... statement is replaced by
 * two basic blocks, one for the then branch, beginning with 'assume b', and one
 * for the else block, beginning with 'assume !b'.
 * Derived classes are expected to handle tasks such as
 * converting to single-assignment form. 
 * <P>
 * These Java statements are handled: if, switch, loops (for, while, do, foreach),
 * return, throw, break continue.
 * <P>
 * Expression ASTs are used as is (without copying), so there may be some
 * structure sharing in the resulting basic block program.
 * <P>
 * The class expects a new object to be instantiated for each method to be
 * converted to a Basic Block program, including for methods in local
 * and anonymous classes.
 * 
 * @typeparam T basic block type
 * @typeparam P basic block program type
 * @author David Cok
 */
abstract public class BasicBlockerParent<T extends BlockParent<T>, P extends BasicProgramParent<T>> extends JmlTreeScanner {

    // THE FOLLOWING ARE ALL FIXED STRINGS
    
    //-----------------------------------------------------------------
    // Names for various basic blocks
    
    /** The prefix used for names of blocks */
    public static final @NonNull String blockPrefix = "BL_"; //$NON-NLS-1$
    
    /** Standard name for the block that starts the body */
    public static final @NonNull String BODY_BLOCK_NAME = "bodyBegin"; //$NON-NLS-1$
    
    /** Standard name for the starting block of the program (just has the preconditions) */
    public static final @NonNull String START_BLOCK_NAME = "Start"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block for a finally block */
    public static final String FINALLY = "_finally"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block which is the target for return and 
     * throw statements in the try statement body */
    public static final String TRYTARGET = "tryTarget"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block which is the no exception path
     * upon exit from the try statement body */
    public static final String TRYNOEXCEPTION = "noException"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block which is the normal exit path
     * after a finally block */
    public static final String TRYFINALLYNORMAL = "finallyNormal"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block which is the exit path after a
     * finally block when there is an outstanding return or exception */
    public static final String TRYFINALLYEXIT = "finallyExit"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block which holds the body of a catch clause */
    public static final String CATCH = "catch"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block representing the case where an
     * exception is not caught by any catch clause */
    public static final String NOCATCH = "nocatch"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block for a finally block */
    public static final String AFTERTRY = "_AfterTry"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block that comes after a switch statement */
    public static final String AFTERLABEL = "_AfterLabel"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block that comes after a switch statement */
    public static final String AFTERSWITCH = "_AfterSwitch"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block holding the body of a loop */
    public static final String LOOPBODY = "_LoopBody"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block holding the code after a loop */
    public static final String LOOPAFTER = "_LoopAfter"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block holding the code after a loop */
    public static final String LOOPAFTERDO = "_LoopAfterDo"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block holding the code where continue statements go */
    public static final String LOOPCONTINUE = "_LoopContinue"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block holding the code where break statements go */
    public static final String LOOPBREAK = "_LoopBreak"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block to which control transfers if the loop condition fails */
    public static final String LOOPEND = "_LoopEnd"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block for the then branch of an if statement */
    public static final String THENSUFFIX = "_then"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block for the else branch of an if statement */
    public static final String ELSESUFFIX = "_else"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block after an if statement */
    public static final String AFTERIF = "_afterIf"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block after a return statement */
    public static final String RETURN = "_return"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block after a throw statement */
    public static final String THROW = "_throw"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block for the body of a switch case */
    public static final String CASEBODY = "_caseBody_"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block for the case expression test */
    public static final String CASETEST = "_caseTest"; //$NON-NLS-1$
    
    /** Suffix for the name of a basic block for the switch default case */
    public static final String CASEDEFAULT = "_switchDefault"; //$NON-NLS-1$
    
    /** Part of the name for switch expressions */
    public static final String SWITCHEXPR = "_switchExpression_"; //$NON-NLS-1$
    
    // THE FOLLOWING FIELDS ARE EXPECTED TO BE CONSTANT FOR THE LIFE OF THE OBJECT
    // They are either initialized in the constructor or initialized on first use
    // Some are here for the benefit of derived classes and not used in this
    // class directly
    
    /** The compilation context */
    @NonNull final protected Context context;
    
    /** The log to which to send error, warning and notice messages */
    @NonNull final protected Log log;
    
    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull final protected Names names;
  
    /** The specifications database for this compilation context, initialized in the constructor */
    @NonNull final protected JmlSpecs specs;
    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull final protected Symtab syms;
    
    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    @NonNull final protected JmlTreeUtils treeutils;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    final protected JmlTree.@NonNull Maker M;

    // The following fields depend on the method being converted but
    // are otherwise fixed for the life of the object

    /** The declaration of the method under conversion */
    protected JmlMethodDecl methodDecl;
    
    /** True if the method being converted is a constructor */
    protected boolean isConstructor;
    
    /** True if the method being converted is static */
    protected boolean isStatic;
    
    /** The program being constructed */
    protected P program = null;
    
    /** The symbol used to hold the int location of the terminating statement. */
    protected VarSymbol terminationSym;
    
    /** The symbol used to designate the exception thrown by the method. */
    protected VarSymbol exceptionSym;

    // THE FOLLOWING FIELDS ARE USED IN THE COURSE OF DOING THE WORK OF CONVERTING
    // TO BASIC BLOCKS.  They are fields of the class because they need to be
    // shared across the visitor methods. Other such fields are declared close
    // to their points of use in the remainder of this file.
    
    /** A map of names to blocks */
    final protected java.util.Map<String,T> blockLookup = new java.util.HashMap<String,T>();
    
    /** A variable to hold the block currently being processed */
    protected T currentBlock;
    
    /** Ordered list of statements from the current block that are yet to be processed into basic program form */
    protected List<JCStatement> remainingStatements;
    
    /** A counter used to make sure that block names are unique */
    protected int blockCount = 0;
    
    /** Holds the result of any of the visit methods that produce JCExpressions, since the visitor
     * template used here does not have a return value.  [We could have used the templated visitor,
     * but other methods do not need to return anything, we don't need the additional parameter,
     * and that visitor is complicated by the use of interfaces for the formal parameters.]
     */
    protected JCExpression result;
    

    /** The constructor, but use the instance() method to get a new instance,
     * in order to support extension.  This constructor should only be
     * invoked by a derived class constructor.
     * @param context the compilation context
     */
    protected BasicBlockerParent(@NonNull Context context) {
        this.context = context;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.scanMode = AST_JAVA_MODE;
    }
    
    /** Instantiated by derived classes to create a new (empty) basic block program */
    abstract public P newProgram(Context context);
    
    /** Creates a new block of the appropriate type.
     */
    abstract public T newBlock(JCIdent id);
    
    /** Creates a block name - note that this format is presumed when 
     * proof failures are being traced and understood.
     * @param pos the character position of the statement for which the block is being generated
     * @param kind a suffix to indicate the reason for block
     * @return a composite name for a block
     */
    // The format of the block name is relied upon in JmlEsc.reportInvalidAssertion
    protected String blockName(int pos, String kind) {
        // The block count is appended to be sure that the id is unique. Blocks
        // can originate from the same DiagnosticPosition and so the pos and key
        // are not always enough to distinguish them. So the pos and the key
        // are not entirely necessary, but they do serve some documentation 
        // function.
        return blockNamePrefix(pos,kind) + "_" + (++blockCount);
    }
    
    protected String blockNamePrefix(int pos, String kind) {
        return blockPrefix + pos + kind;
    }
    
    
    
    // UTILITY METHODS


    /** Should not need this when everything is implemented */
    protected void notImpl(JCTree that) {
        log.getWriter(WriterKind.NOTICE).println("Internal error - visit method NOT IMPLEMENTED: " + getClass() + " - "+ that.getClass());
        result = treeutils.trueLit;
    }
    
    /** Called by visit methods that should never be called. */
    protected void shouldNotBeCalled(JCTree that) {
        log.error("esc.internal.error","Did not expect to be calling a " + that.getClass() + " within " + getClass());
        throw new JmlInternalError();
    }
    

    // GENERAL AND HELPER METHODS FOR PROCESSING BLOCKS
    
    // This stack of blocks to be processed is used to
    // avoid recursive calls that become very deeply nested
    // (of the order of the length of the program, not of the
    // nesting in the program).
    Stack<T> todo = new Stack<>();
    
    public void processBlocks() {
        while (!todo.isEmpty()) {
            processBlock(todo.pop());
        }
    }
    
    public Stack<T> pushTodo() {
        Stack<T> savedTodo = new Stack<T>();
        savedTodo.addAll(todo);
        todo.clear();
        return savedTodo;
    }
    
    public Stack<T> popTodo(Stack<T> savedTodo) {
        todo.addAll(savedTodo);
        savedTodo.clear();
        return null;
    }
    

    /** Does the conversion of a block with Java statements into basic program
     * form. Newly created blocks should be processed by recursive calls
     * to this method. This method operates by calling startBlock to 
     * initialize block processing (which also sets the value of currentBlock
     * and puts all statements from the currentBlock on the remainingStatements
     * list), then calling processCurrentBlock() to process everything on
     * remainingStatements; processCurrentBlock() also calls completeBlock() to 
     * wrap up any processing on the block.
     * 
     * @param block the block to process
     */
    protected void processBlock(@NonNull T block) {
        if (block.preceders().isEmpty()) {
            // Delete any blocks that do not follow anything
            // This can happen for example if the block is an afterIf block
            // and both the then branch and the else branch terminate with
            // a return or throw statement. If the block does contain some
            // statement then those will never be executed. They should 
            // have been warned about by the compiler. Here we will 
            // log a warning, ignore the block, and continue processing.
            // Note that the block will still have an id and be in the 
            // id map (blockLookup).
            // This can also happen if the previous block ended with a JML end or halt statement.
            if (!block.statements.isEmpty() && !block.id().name.toString().contains(TRYFINALLYNORMAL) && !block.id().name.toString().contains("finallyExit")) {
                // Because of the possibility of end statements, for now we will not issue this warning
                //                log.warning("jml.internal","A basic block has no predecessors - ignoring it: " + block.id);
            }
            program.blocks.remove(block);
            for (T b: block.followers()) {
                b.preceders().remove(block);
            }
            return;
        }
        if (!program.blocks.contains(block)) {
            startBlock(block);
            processCurrentBlock();
        } else {
            log.warning("jml.internal","Basic block " + block.id + " is being re-processed");
        }
    }
    
    /** Finishes processing statements on the remainingStatements list;
     * call this to complete processing the currentBlock once processing
     * has been started (e.g., when new statements have been added to the
     * remainingStatements list).
     */
    protected void processCurrentBlock() {
        continuation = Continuation.CONTINUE;
        processStats(remainingStatements);
        if (currentBlock != null && continuation == Continuation.HALT) replaceFollows(currentBlock,(List<T>)null);
        completeBlock(currentBlock);
    }
    
    protected void processStats(List<JCStatement> stats) {
        while (!stats.isEmpty()) {
            JCStatement s = stats.remove(0);
            if (s != null) s.accept(this);  // A defensive check - statements in the list should not be null
            if (continuation != Continuation.CONTINUE) {
                stats.clear();
                break;
            }
        }
    }
    

    /** Initialize the processing of the given block:
     * <UL>
     * <LI> checks that any preceding blocks are already processed (if not, something has gone wrong)
     * <LI> does special processing for finally and lop-after blocks
     * <LI> sets the argument as the current block (and sets the currentMap and the remainingstatements)
     * </UL>
     * 
     * @param b the block for which to initialize processing 
     */
    protected void startBlock(@NonNull T b) {
        
        // Check that all preceding blocks are actually completed
        // This is defensive programming and should not actually be needed
        //log.noticeWriter.println("Checking block " + b.id());
        loop: while (true) {
            for (T pb: b.preceders()) {
                //log.noticeWriter.println("   " + b.id() + " follows " + pb.id());
                if (!program.blocks.contains(pb)) {
                    log.getWriter(WriterKind.NOTICE).println("Internal Error: block " + pb.id.name + " precedes block " + b.id.name + " , but was not processed before it"); //$NON-NLS-1$ //$NON-NLS-2$
                    processBlock(pb);
                    continue loop; // the list of preceding blocks might have changed - check it over again
                }
            }
            break;  // all preceding blocks were processed
        }

        //log.noticeWriter.println("Starting block " + b.id);
        program.blocks.add(b);
        setCurrentBlock(b);
    }
    
    /** Sets all the variables that are supposed to stay in synch with the value of
     * currentBlock
     * @param b the new currentBlock
     */
    protected void setCurrentBlock(T b) {
        if (currentBlock != null) {
            log.warning("jml.internal.notsobad","Starting block " + b.id + " when " + currentBlock.id + " is not completed"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
        }
        currentBlock = b;
        remainingStatements = currentBlock.statements;
        currentBlock.statements = new ArrayList<JCStatement>();
    }
    
    /** Allows derived classes to do any cleanup activity.
     * @param b the completed block
     */
    protected void completeBlock(@NonNull T b) {
        // remainingStatements should be null, but we don't bother to do the defensive check
        currentBlock = null;
    }
    
    /** Updates the data structures to indicate that the after block follows the
     * before block
     * @param before block that precedes after
     * @param after block that follows before
     */
    protected void follows(@NonNull T before, @NonNull T after) {
        before.followers().add(after);
        after.preceders().add(before);
    }
    
    /** Updates the data structures to indicate that all the after blocks follow the
     * before block
     * @param before block that precedes after
     * @param after list of blocks that follow before
     */
    protected void follows(@NonNull T before, @NonNull List<T> after) {
        for (T b: after) {
            before.followers().add(b);
            b.preceders().add(before);
        }
    }
    
    /** Inserts the after block after the before block, replacing anything that
     * used to follow the before block
     * @param before block whose follow list is to be changed
     * @param after new following block
     */
    protected void replaceFollows(@NonNull T before, @NonNull T after) {
        for (T b: before.followers()) {
            b.preceders().remove(before);
        }
        before.followers().clear();
        follows(before,after);
    }
    
    /** Inserts the after blocks after the before block, replacing anything that
     * used to follow the before block
     * @param before
     * @param after
     */
    protected void replaceFollows(@NonNull T before, List<T> after) {
        for (T b: before.followers()) {
            b.preceders().remove(before);
        }
        before.followers().clear();
        if (after != null) for (T b: after) {
            follows(before,b);
        }
    }
    
    /** Creates a new block of type T; 
     * the 'previousBlock' gives up its followers to the newly created block. 
     */
    public T newBlock(JCIdent id, T previousBlock) {
        T nb = newBlock(id);
        List<T> s = nb.followers(); // empty, just don't create a new empty list
        nb.followers = previousBlock.followers();
        previousBlock.followers = s;
        for (T f: nb.followers()) {
            f.preceders().remove(previousBlock);
            f.preceders().add(nb);
        }
        String name = id.name.toString();
        blockLookup.put(name,nb);
        name = name.substring(0,name.lastIndexOf("_"));
        blockLookup.put(name, nb);
        return nb;
    }
    
    /** Returns a new, empty block
     * 
     * @param name the name to give the block
     * @param pos a position to associate with the JCIdent for the block
     * @return the new block
     */
    protected @NonNull T newBlock(@NonNull String key, int pos) {
        String name = blockName(pos,key);
        JCIdent id = treeutils.makeIdent(pos,name,syms.booleanType);
        T bb = newBlock(id);
        bb.unique = blockCount;
        blockLookup.put(name,bb);
        name = name.substring(0,name.lastIndexOf("_"));
        blockLookup.put(name, bb);
        return bb;
    }
    
    /** Returns a new, empty block, but the new block takes all of the 
     * followers of the given block; the previousBlock will then have no
     * followers.
     * 
     * @param name the name to give the block
     * @param pos a position to associate with the JCIdent for the block
     * @param previousBlock the block that is giving up its followers
     * @return the new block
     */
    protected @NonNull T newBlock(@NonNull String key, int pos, @NonNull T previousBlock) {
        String name = blockName(pos,key);
        // See the comment in the newBlock(...) method above
        JCIdent id = treeutils.makeIdent(pos,name,syms.booleanType);
        T bb = newBlock(id,previousBlock);
        bb.unique = blockCount;
        blockLookup.put(name, bb);
        name = name.substring(0,name.lastIndexOf("_"));
        blockLookup.put(name, bb);
        return bb;
    }
    
    /** Returns a new, empty T, but the new block takes all of the 
     * followers and the remaining statements of the current block; the 
     * currentBlock will then have no remaining statements and no followers.
     * 
     * @param name the name to give the block
     * @param pos a position to associate with the block
     * @return the new block
     */
    protected T newBlockWithRest(@NonNull String key, int pos) {
        T b = newBlock(key,pos,currentBlock);// it gets all the followers of the current block
        b.statements.addAll(remainingStatements); // it gets all of the remaining statements
        remainingStatements.clear(); // empty
        return b;
    }
    
    /** A helper initialization routine for derived classes, called internally at
     * the start of converting a method body
     */
    protected void initialize(@NonNull JCMethodDecl methodDecl, 
           @NonNull JCClassDecl classDecl, @NonNull JmlAssertionAdder assertionAdder) {
        this.methodDecl = (JmlMethodDecl)methodDecl;
        this.program = newProgram(context);
        this.program.methodDecl = methodDecl;
        this.isConstructor = methodDecl.sym.isConstructor();
        this.isStatic = methodDecl.sym.isStatic();
        if (classDecl.sym == null) {
            log.error("jml.internal","The class declaration in convertMethodBody appears not to be typechecked");
        }
        this.terminationSym = (VarSymbol)assertionAdder.terminationSymbols.get(methodDecl);
        this.exceptionSym = (VarSymbol)assertionAdder.exceptionSymbols.get(methodDecl);
        this.blockLookup.clear();
        this.loopStack.clear();
        this.continueMap.clear();
        this.breakBlocks.clear();
        this.breakStack.clear();
        this.catchStack.clear();
        this.finallyStack.clear();
        this.blockCount = 0;
        // Fields that do not need initialization: result, remainingStatements, currentBlock
    }

    /** Associates end position information with newnode, taking the information
     * from srcnode; the information is stored in the end-position table that
     * is part of log.currentSource(). No action happens if either argument is null.
     */
    public void copyEndPosition(@Nullable JCTree newnode, @Nullable JCTree srcnode) {
        EndPosTable z = log.currentSource().getEndPosTable();
        if (z != null && srcnode != null) { // srcnode can be null when processing a switch statement
            int end = srcnode.getEndPosition(z);
            if (end != Position.NOPOS) z.storeEnd(newnode, end);
        }
    }
    

    // METHODS TO ADD ASSUME AND ASSERT STATEMENTS
    
    /** Adds a new assume statement to the end of the given statements list; the assume statement is
     * given the declaration pos and label from the arguments; it is presumed the input expression is
     * translated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param that the (translated) expression being assumed
     * @param statements the list to add the new assume statement to
     */
    protected JmlStatementExpr addAssume(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        JmlStatementExpr st = M.at(pos).JmlExpressionStatement(assumeID, assumeClause, label,that);
        copyEndPosition(st,that);
        st.type = null; // statements do not have a type
        statements.add(st);
        return st;
    }
    
    ListBuffer<JCStatement> temp = new ListBuffer<>();
    protected void addAssumeCheck(java.util.List<JCStatement> statements, String bbname) {
        JmlEsc.instance(context).assertionAdder.addAssumeCheck(treeutils.trueLit, temp, "BB-Assume" );
        statements.add(temp.first());
        temp.clear();
    }

    
    /** Adds a new assume statement to the end of the given statements list; the assume statement is
     * given the declaration pos, endpos and label from the arguments; it is presumed the input expression is
     * translated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param that the (translated) expression being assumed
     * @param statements the list to add the new assume statement to
     */
    protected JmlStatementExpr addAssume(int startpos, JCTree endpos, Label label, JCExpression that, List<JCStatement> statements) {
        if (startpos < 0) startpos = that.pos;
        JmlStatementExpr st = M.at(startpos).JmlExpressionStatement(assumeID, assumeClause,label,that);
        copyEndPosition(st,endpos);
        st.type = null; // statements do not have a type
        statements.add(st);
        return st;
    }
        
    /** This generates a comment statement (not added to any statement list) whose content is the
     * given String.
     */
    public JmlStatementExpr comment(DiagnosticPosition pos, String s) {
        return M.at(pos).JmlExpressionStatement(commentID, commentClause,null,M.Literal(s));
    }
    
    /** This generates a comment statement (not in any statement list) whose content is the
     * given JCTree, pretty-printed.
     */
    public JmlStatementExpr comment(JCTree t) {
        return comment(t.pos(),JmlPretty.write(t,false));
    }
    

    // JAVA CONTROL STATEMENT NODES
    
    // Translation of a switch statement
    //  switch (swexpr) {
    //       case A:
    //              SA;
    //              break;
    //       case B:
    //              SB;
    //              // fall through
    //       case C:
    //              SC;
    //              break;
    //       default:
    //              SD;
    //   }
    //   translates to
    //   -- continuation of current block:
    //          assume $$switchExpression$<pos>$<pos> == swexpr;
    //          goto $$case$<A>,$$case$<B>,$$case$<C>,$$defaultcase$<D>
    //     $$case$<A>:
    //          assume $$switchExpression$<pos>$<pos> == A;
    //          SA
    //          goto $$BL$<pos>$switchEnd
    //     $$case$<B>:
    //          assume $$switchExpression$<pos>$<pos> == B;
    //          SB
    //          goto $$caseBody$<C>
    //     $$case$<C>:
    //          assume $$switchExpression$<pos>$<pos> == C;
    //          goto $$caseBody$<C>
    //     $$caseBody$<C>:  // Need this block because B fallsthrough to C
    //          SC
    //          goto $$BL$<pos>$switchEnd
    //     $$defaultcase$<D>:
    //          assume !($$switchExpression$<pos>$<pos> == A && ...);
    //          SD
    //          goto $$BL$<pos>$switchEnd
    //     $$BL$<pos>$switchEnd:
    //          ....
    //   
    // FIXME - need to implement/test for switch expressions that are Strings or Enums
    @Override
    public void visitSwitch(JCSwitch that) { 
        currentBlock.statements.add(comment(that.pos(),"switch ..."));
        int pos = that.pos;
        int swpos = that.selector.getStartPosition();
        scan(that.selector);
        JCExpression switchExpression = result;
        List<JCCase> cases = that.cases;
        T previousBreakBlock = breakBlocks.get(names.empty);
        
        // Create the ending block name
        T blockAfter = null;
        
        try {
            breakStack.add(0,that);

            // We create a new auxiliary variable to hold the switch value, so 
            // we can track its value and so the subexpression does not get
            // replicated.  We add an assumption about its value and add it to
            // list of new variables
            String switchName = SWITCHEXPR + pos;
            JCIdent vd = treeutils.makeIdent(swpos,switchName,switchExpression.type);
            scan(vd);
            
            program.declarations.add(vd);

            JCExpression newexpr = treeutils.makeBinary(swpos,JCTree.Tag.EQ,vd,switchExpression);
            addAssume(swpos,switchExpression,Label.SWITCH_VALUE,newexpr,currentBlock.statements);
            T switchStart = currentBlock;

            // Now create an (unprocessed) block for everything that follows the
            // switch statement
            blockAfter = newBlockWithRest(AFTERSWITCH,pos);// it gets all the followers of the current block
            breakBlocks.put(names.empty, blockAfter);
            
            // Now we need to make a block for each of the case statements,
            // adding them to the todo list to be processed at the end
            // Note that there might be nesting of other switch statements etc.
            java.util.LinkedList<T> blocks = new java.util.LinkedList<T>();
            T prevCaseBlock = null;
            JCExpression defaultCond = treeutils.falseLit;
            JmlTree.JmlStatementExpr defaultAsm = null;
            boolean fallthrough = false; // Nothing to fall through to the first case
            for (JCCase caseStatement: cases) {
                /*@ nullable */ JCExpression caseValue = caseStatement.getExpression();
                List<JCStatement> stats = caseStatement.getStatements();
                int casepos = caseStatement.getStartPosition();
                
                // create a block for this case test
                T blockForTest = newBlock(caseValue == null ? CASEDEFAULT : CASETEST ,
                        caseValue == null ? casepos: caseStatement.getStartPosition()); // FIXME - this is a meaningless distinction, goiven the assignment to casepos
                blocks.add(blockForTest);
                follows(switchStart,blockForTest);
                
                // create the case test, or null if this is the default case
                JCIdent vdd = treeutils.makeIdent(caseValue == null ? Position.NOPOS : caseValue.getStartPosition(),vd.sym);
                /*@ nullable */ JCExpression eq = caseValue == null ? null : treeutils.makeBinary(caseValue.getStartPosition(),JCTree.Tag.EQ,vdd,(caseValue));
                if (caseValue != null && switchExpression.type == syms.stringType) {
                    
                    
                }
                JmlStatementExpr asm = addAssume(vdd.pos,
                		Label.CASECONDITION,eq,blockForTest.statements);
                
                // continue to build up the default case test
                if (caseValue == null) defaultAsm = asm; // remember the assumption for the default case
                else defaultCond = treeutils.makeOr(caseValue.getStartPosition(),eq,defaultCond);

                // It is always safe for the value of 'fallthrough' to be true, 
                // since processing of the blocks will take care of changing a
                // block's followers in the case where there is no fall through.
                // However, it is a bit of an optimization to know when 'fallthrough'
                // is false, since we avoid creating an unnecessary block.
                
                if (!fallthrough) {
                    // statements can go in the same block
                    blockForTest.statements.addAll(stats);
                    follows(blockForTest,blockAfter); // The following block is reset if there is fallthrough to a next block
                    prevCaseBlock = blockForTest;
                } else {
                    // (possibly) falling through from the previous case
                    // since there is fall-through, the statements need to go in their own block
                    T blockForStats = newBlock(CASEBODY,caseStatement.getStartPosition());
                    blockForStats.statements.addAll(stats);
                    
                    follows(blockForTest,blockForStats);
                    replaceFollows(prevCaseBlock,blockForStats);
                    follows(blockForStats,blockAfter); // The following block is reset if there turns out to be fallthrough
                    blocks.add(blockForStats);
                    prevCaseBlock = blockForStats;
                }
                
                // Compute and remember whether control falls through to the next case
                fallthrough = stats.isEmpty() ||
                        !(prevCaseBlock.statements.get(prevCaseBlock.statements.size()-1) instanceof JCBreak);
            }

            // Now fix up the default case (which is not necessarily last).
            // Fortunately we remembered it
            int dpos = defaultAsm == null ? pos : defaultAsm.pos;
            JCExpression eq = treeutils.makeUnary(dpos,JCTree.Tag.NOT,defaultCond);
            if (defaultAsm != null) {
                // There was a default case already made, but at the time we just
                // put in null for the case condition, since we did not know it
                // yet (and we wanted to process the statements in textual order).
                // So here we violate encapsulation a bit and poke it in.
                defaultAsm.expression = eq;
            } else {
                // There was no default - we need to construct an empty one
                // create a block for this case test
                T blockForTest = newBlock(CASEDEFAULT,pos);
                blocks.add(blockForTest);
                follows(switchStart,blockForTest);
                follows(blockForTest,blockAfter);
                
                addAssume(that.pos,Label.CASECONDITION,eq,blockForTest.statements);
            }
            
            Stack<T> savedTodo = pushTodo();
            
            processCurrentBlock(); // Complete the current block
            processBlocks();
            // Now process all of the blocks we created, in order
            for (T b: blocks) {
                processBlock(b);
                processBlocks();
            }
            savedTodo = popTodo(savedTodo);
        } finally {
            breakStack.remove(0);
            breakBlocks.put(names.empty, previousBreakBlock);
        }
        // Should never actually be null, unless some exception happened
        if (blockAfter != null) todo.push(blockAfter);
    }
    
    // OK
    /** Should never call this because case statements are handled in switch. */
    public void visitCase(JCCase that) { shouldNotBeCalled(that); }
    
    /** Stack to hold Blocks for catch clauses, when try statements are nested */
    final protected java.util.List<T> catchStack = new java.util.LinkedList<T>();
    
    /** Stack to hold Blocks for finally clauses, when try statements are nested */
    final protected java.util.List<T> finallyStack = new java.util.LinkedList<T>();

    // This sets up a complicated arrangement of blocks
    //
    // currentBlock:    try statement
    //                  rest of statements
    //
    // becomes
    //
    // currentBlock:    try statement block
    //                      throw - set exceptionVar, terminationVar; goto catchBlocks
    //                      return - set returnValue, terminationVar; goto finallyBlock
    //                  goto finallyBlock
    //
    // catchBlocks:     assume condition on exception
    //                  reset terminationVar to 0, exceptionVar to null
    //                  catch block statements
    //                  goto finallyBlock
    //
    // finallyBlock:    any finally block statements
    //                  if exceptionVar is not null, goto next outer catch block, else the corresponding finally block
    //                  if terminationVar is not 0, goto next outer finally block
    //                  goto afterTryBlock
    //
    // afterTryBlock:   rest of statements
    //
    //
    // FIXME - unify the use of the termination var?
    @Override
    public void visitTry(JCTry that) {
        currentBlock.statements.add(comment(that.pos(),"try..."));

        // Create an (unprocessed) block for everything that follows the
        // try statement
        int pos = that.pos;
        T afterTry = newBlockWithRest(AFTERTRY,pos);// it gets all the followers of the current block
        
        // remainingStatements is now empty
        // Put the statements in the try block into the currentBlock
        remainingStatements.add(that.getBlock());
        
        // We make an empty block that will contain
        // both catch clause statements and finally block statements. It serves
        // as the target for any return or throw statements and for exits from
        // the finally blocks of nested try statements.
        T targetBlock = newBlock(TRYTARGET,pos);
        T finallyBlock = newBlock(FINALLY,pos);
        follows(currentBlock,targetBlock);
        
        List<T> blocks = new LinkedList<T>();
        blocks.add(targetBlock);
        
        // NOTE: A lot of structure sharing occurs in the following.
        
        // First create the non-exception path
        // Note: value for exceptionSym != null ==> an exception has been thrown
        //       value for terminationSym != 0 ==> return or throw executed
        //       value for terminationSym == 0 ==> no return or throw executed
        
        JCIdent ex = treeutils.makeIdent(pos, exceptionSym);
        JCExpression noex = treeutils.makeEqObject(pos,ex,treeutils.nullLit);
        T noexceptionBlock = newBlock(TRYNOEXCEPTION,pos);
        addAssume(pos,Label.IMPLICIT_ASSUME,noex,noexceptionBlock.statements);
        follows(targetBlock,noexceptionBlock);
        follows(noexceptionBlock,finallyBlock);
        blocks.add(noexceptionBlock);
        
        // Now create the paths for each catch 
        List<JCStatement> assumptions = new LinkedList<JCStatement>();
        for (JCCatch catcher: that.catchers) {
            JCExpression ty = catcher.param != null ? catcher.param.vartype : treeutils.makeType(catcher.pos, syms.exceptionType);
            JCExpression tt = M.at(catcher.pos).TypeTest(ex,ty).setType(syms.booleanType);
            tt = M.at(catcher.pos).Parens(tt).setType(tt.type);
            T catchBlock = newBlock(CATCH,catcher.pos);
            follows(targetBlock,catchBlock);
            follows(catchBlock,finallyBlock);
            addAssumeCheck(catchBlock.statements, catchBlock.id().toString() + "-start");
            catchBlock.statements.addAll(assumptions);
            addAssumeCheck(catchBlock.statements, catchBlock.id().toString() + "- +1");
            addAssume(catcher.pos,Label.IMPLICIT_ASSUME,tt,catchBlock.statements);
            addAssumeCheck(catchBlock.statements, catchBlock.id().toString() + "- +2");
            addAssume(catcher.pos,Label.IMPLICIT_ASSUME,treeutils.makeNot(catcher.pos,tt),assumptions);
            JCVariableDecl d = treeutils.makeVariableDecl(catcher.param.sym, ex);
                d.pos = catcher.param.pos;
            catchBlock.statements.add(d);
            JCIdent nex = treeutils.makeIdent(catcher.pos, exceptionSym);
            catchBlock.statements.add(treeutils.makeAssignStat(catcher.pos,nex,treeutils.nullLit)); // FIXME - seems to duplicate an item in catcher.body.stats
            JCIdent term = treeutils.makeIdent(catcher.pos, terminationSym);
            catchBlock.statements.add(treeutils.makeAssignStat(catcher.pos,term,treeutils.zero));
            catchBlock.statements.addAll(catcher.body.stats);
            blocks.add(catchBlock);
        }
        
        // And the path if an exception is not caught by anything
        T noCatchBlock = newBlock(NOCATCH,pos);
        addAssume(pos,Label.IMPLICIT_ASSUME,treeutils.makeNeqObject(pos,ex,treeutils.nullLit),noCatchBlock.statements);
        noCatchBlock.statements.addAll(assumptions);
        follows(targetBlock,noCatchBlock);
        follows(noCatchBlock,finallyBlock);
        blocks.add(noCatchBlock);
    
        // Need to save the current global exception and termination value
        Symbol owner = methodDecl != null ? methodDecl.sym : null; // FIXME ? classDecl.sym;
        JCVariableDecl savedException = treeutils.makeVarDef(syms.exceptionType, names.fromString("__JMLsavedException_" + that.pos), owner, that.pos); // FIXME - may need to have a non-null owner
        JCAssign saveAssignment = treeutils.makeAssign(that.pos, treeutils.makeIdent(that.pos, savedException.sym), treeutils.makeIdent(that.pos,exceptionSym));
        finallyBlock.statements.add(M.at(that.pos).Exec(saveAssignment));
        
        JCVariableDecl savedTermination = treeutils.makeVarDef(syms.intType, names.fromString("__JMLsavedTermination_" + that.pos), owner, that.pos); // FIXME - may need to have a non-null owner
        saveAssignment = treeutils.makeAssign(that.pos, treeutils.makeIdent(that.pos, savedTermination.sym), treeutils.makeIdent(that.pos,terminationSym));
        finallyBlock.statements.add(M.at(that.pos).Exec(saveAssignment));
        
        
        JCBlock finallyStat = that.getFinallyBlock();
        if (finallyStat != null) finallyBlock.statements.addAll(finallyStat.getStatements()); // it gets the statements of the finally statement
        
        // Restore the global exception
        JCAssign restoreAssignment = treeutils.makeAssign(that.pos, treeutils.makeIdent(that.pos, exceptionSym), treeutils.makeIdent(that.pos,savedException.sym));
        finallyBlock.statements.add(M.at(that.pos).Exec(restoreAssignment));
        restoreAssignment = treeutils.makeAssign(that.pos, treeutils.makeIdent(that.pos, terminationSym), treeutils.makeIdent(that.pos,savedTermination.sym));
        finallyBlock.statements.add(M.at(that.pos).Exec(restoreAssignment));
        
        
        // And lastly, the blocks for out-of-band exits from the finally block
        // The normal ending block is for when there is no pending exception or return;
        // it takes all the finallyBlock followers and itself follows the finallyBlock.
        // The return/exception ending block follows the finallyBlock and precedes
        // the targetBlock for enclosing try-finally block.
        T finallyNormalBlock = newBlock(TRYFINALLYNORMAL,pos);
        follows(finallyBlock,finallyNormalBlock);
        follows(finallyNormalBlock,afterTry);
        JCIdent term = treeutils.makeIdent(pos, terminationSym);
        JCBinary bin = treeutils.makeBinary(pos,JCTree.Tag.EQ,treeutils.inteqSymbol,term,treeutils.zero);
        addAssume(pos,Label.IMPLICIT_ASSUME,bin,finallyNormalBlock.statements);

        T finallyExitBlock = newBlock(TRYFINALLYEXIT,pos);
        term = treeutils.makeIdent(pos, terminationSym);
        bin = treeutils.makeBinary(pos,JCTree.Tag.NE,treeutils.intneqSymbol,term,treeutils.zero);
        addAssume(pos,Label.IMPLICIT_ASSUME,bin,finallyExitBlock.statements);
        follows(finallyBlock,finallyExitBlock);
        if (!finallyStack.isEmpty()) follows(finallyExitBlock,finallyStack.get(0));
        else follows(finallyExitBlock,afterTry);
        
        // Put targetBlock on the finallyStack - it is the destination for 
        // any return or throw during the try statement body
        finallyStack.add(0,targetBlock);
        
        Stack<T> savedTodo = pushTodo();
        
        // Finish the processing of the current block; it might
        // refer to the finally block during processing
        processCurrentBlock();
        processBlocks();
        finallyStack.remove(0); // Remove targetBlock
        // Now the finally block is the destination of any return or throw
        // during catch clauses
        finallyStack.add(0,finallyBlock);
        for (T b: blocks) {
            processBlock(b);
            processBlocks();
        }
        finallyStack.remove(0);

        savedTodo = popTodo(savedTodo);
        
        // Blocks pushed in reverse order
        todo.push(afterTry);
        todo.push(finallyExitBlock);
        todo.push(finallyNormalBlock);
        todo.push(finallyBlock);
    }
    
    /** Catch statements are handled in visitTry */
    public void visitCatch(JCCatch that) { 
        shouldNotBeCalled(that); 
    }
    
    // OK
    public void visitIf(JCIf that) {
        int pos = that.pos;
        int posc = that.cond != null ? that.cond.pos : pos;
        currentBlock.statements.add(comment(that.pos(),"if..."));
        
        // Now create an (unprocessed) block for everything that follows the
        // if statement
        T afterIf = newBlockWithRest(AFTERIF,pos);// it gets all the followers of the current block
        
        // Now make the then block
        T thenBlock = newBlock(THENSUFFIX,pos);
        addAssume(posc, Label.BRANCHT, that.cond, thenBlock.statements);
        thenBlock.statements.add(that.thenpart);
        follows(thenBlock,afterIf);
        follows(currentBlock,thenBlock);
        
        // Now make the else block
        T elseBlock = newBlock(ELSESUFFIX,pos);
        addAssume(posc, Label.BRANCHE, treeutils.makeNot(posc,that.cond), elseBlock.statements);
        if (that.elsepart != null) elseBlock.statements.add(that.elsepart);
        follows(elseBlock,afterIf);
        follows(currentBlock,elseBlock);
        
        processCurrentBlock(); // complete current block
        todo.push(afterIf);
        todo.push(elseBlock);
        todo.push(thenBlock);
//        processBlock(thenBlock);
//        processBlock(elseBlock);
//        processBlock(afterIf);
    }
    
    /** This is a stack of loops and switch statements - anything that can 
     * contain a break statement
     */
    final protected java.util.List<JCTree> breakStack = new java.util.LinkedList<JCTree>();
    
    /** This is a map of label to Block, giving the block to which a labelled break
     * should jump - which is the Block after the labelled statement.
     */
    final protected java.util.Map<Name,T> breakBlocks = new java.util.HashMap<Name,T>();
    
    @Override // OK
    public void visitBreak(JCBreak that) { 
        if (that.label != null) {
            // Note that a break with a label exits the labelled statement, even
            // if we are currently in a switch
            T breakBlock = breakBlocks.get(that.label);
            if (breakBlock == null) {
                log.error(that.pos(),"jml.internal","No target found for break label " + that.label);
            } else {
                replaceFollows(currentBlock,breakBlock);
            }
        } else if (breakStack.isEmpty()) {
          log.error(that.pos(),"jml.internal","Empty break stack");

        } else {
            JCTree tree = breakStack.get(0);
            if (tree instanceof JCSwitch) {
                // Don't need to do anything.  If the break is not at the end of a block,
                // the compiler would not have passed this.  If it is at the end of a block
                // the logic in handling JCSwitch has taken care of everything.
                T b = breakBlocks.get(names.empty);
                if (b == null) {
                    log.error(that.pos(),"jml.internal","Corresponding break target is not found"); //$NON-NLS-1$ //$NON-NLS-2$
                } else {
                    replaceFollows(currentBlock,b);
                }

            } else {
                T b = breakBlocks.get(names.empty);
                if (b == null) {
                    log.error(that.pos(),"jml.internal","Corresponding break target is not found");  //$NON-NLS-1$//$NON-NLS-2$
                } else {
                    replaceFollows(currentBlock,b);
                }
            }
        }
        if (!remainingStatements.isEmpty()) {
            log.warning(remainingStatements.get(0).pos(),"jml.internal.notsobad","Statements after a break statement are unreachable and are ignored"); //$NON-NLS-1$ //$NON-NLS-2$
        }
    }
    
    // FIXME - implement: intervening finally blocks
    public void visitContinue(JCContinue that) {
        currentBlock.statements.add(comment(that));
        if (loopStack.isEmpty()) {
            log.error(that.pos(),"jml.internal","Empty loop stack for continue statement"); //$NON-NLS-1$ //$NON-NLS-2$
        } else if (that.label == null) {
            JCTree t = loopStack.get(0);
            String blockName = blockNamePrefix(t.pos,LOOPCONTINUE);
            T b = blockLookup.get(blockName);
            if (b == null) log.error(that.pos(),"jml.internal","No continue block found to match this continue statement");  //$NON-NLS-1$//$NON-NLS-2$
            else replaceFollows(currentBlock,b);
        } else {
            Name label2 = names.fromString("_$"+that.label.toString());
            JCTree t = continueMap.get(label2);
            String blockName = blockNamePrefix(t.pos,LOOPCONTINUE);
            T b = blockLookup.get(blockName);
            if (b == null) log.error(that.pos(),"jml.internal","No continue block found to match this continue statement, with label ", that.label); //$NON-NLS-1$ //$NON-NLS-2$
            else replaceFollows(currentBlock,b);
        }
        if (!remainingStatements.isEmpty()) {
            log.warning(remainingStatements.get(0).pos(),"jml.internal.notsobad","Statements after a continue statement are unreachable and are ignored"); //$NON-NLS-1$ //$NON-NLS-2$
        }
    }
    
    // OK - presumes that the program has already been modified to record
    // the return value and that the entire method body is enclosed in an
    // outer try-finally block
    public void visitReturn(JCReturn that) {
        if (!remainingStatements.isEmpty()) {
            JCStatement stat = remainingStatements.get(0);
            if (stat.toString().contains("JMLsaved")) remainingStatements.remove(0);
            if (remainingStatements.get(0).toString().contains("JMLsaved")) remainingStatements.remove(0);
            if (!remainingStatements.isEmpty()) {
                // Not fatal, but does indicate a problem with the original
                // program, which the compiler may have already identified
                if (continuation == Continuation.CONTINUE) log.warning(remainingStatements.get(0).pos,
                        "esc.internal.error", //$NON-NLS-1$
                        "Unexpected statements following a return statement are ignored"); //$NON-NLS-1$
                remainingStatements.clear();
            }
            if (continuation == Continuation.CONTINUE) continuation = Continuation.EXIT;
        }
        
        // There are no remaining statements, so this new block is empty.
        // But we create it so there is a block that marks the return statement
        // and can be used to note the termination point in a trace
        
        // The format of the block name is relied upon in JmlEsc.reportInvalidAssertion
        T afterReturn = newBlockWithRest(RETURN,that.pos);
        follows(currentBlock,afterReturn);
        
        if (finallyStack.isEmpty()) {
            // We don't expect the finallyStack to ever be empty when there is
            // a return statement only because
            // JmlAssertionAdder wraps everything in a try-finally statement
            // TODO - generalize this
            log.warning(that.pos(),"esc.internal.error","finally stack is unexpectedly empty");  //$NON-NLS-1$//$NON-NLS-2$
        } else {
            T finallyBlock = finallyStack.get(0);
            replaceFollows(afterReturn,finallyBlock);
        }
        
        processCurrentBlock();
        todo.push(afterReturn);
    }
    
    // OK - presumes that the program has already been modified to record
    // the value of the exception being thrown
    public void visitThrow(JCThrow that) { 
        
        if (!remainingStatements.isEmpty()) {
            JCStatement stat = remainingStatements.get(0);
            if (stat.toString().contains("JMLsaved")) remainingStatements.remove(0);
            if (remainingStatements.get(0).toString().contains("JMLsaved")) remainingStatements.remove(0);
            if (!remainingStatements.isEmpty()) {
                // Not fatal, but does indicate a problem with the original
                // program, which the compiler may have already identified
                if (continuation == Continuation.CONTINUE) log.warning(remainingStatements.get(0).pos,
                        "esc.internal.error",
                        "Unexpected statements following a throw statement");
                remainingStatements.clear();
            }
            if (continuation == Continuation.CONTINUE) continuation = Continuation.EXIT;
        }
        
        // There are no remaining statements, so this new block is empty.
        // But we create it so there is a block that marks the throw statement
        // and can be used to note the termination point in a trace
        T afterThrow = newBlockWithRest(THROW,that.pos);
        follows(currentBlock,afterThrow);
        
        if (finallyStack.isEmpty()) {
            // We don't expect the finallyStack to ever be empty when there is
            // a return statement only because
            // JmlAssertionAdder wraps everything in a try-finally statement
            // TODO - generalize this
            log.warning(that.pos(),"esc.internal.error","finally stack is unexpectedly empty");
        } else {
            T targetBlock = finallyStack.get(0);
            replaceFollows(afterThrow,targetBlock);
        }

        processCurrentBlock();
        todo.push(afterThrow);

    }
    
    // OK - FIXME - turn into a try-finally with lock operations?
    public void visitSynchronized(JCSynchronized that)   { 
        super.visitSynchronized(that);
    }
    

    // LOOPS
    
    
    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that)  { 
        currentBlock.statements.add(comment(that.pos(),"while..."));
        loopHelper(that, null, that.cond, null, that.body);
    }
    
    @Override
    public void visitWhileLoop(JCWhileLoop that) {
        currentBlock.statements.add(comment(that.pos(),"while..."));
        loopHelper(that, null, that.cond, null, that.body);
    }
    
    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        currentBlock.statements.add(comment(that.pos(),"for..."));
        loopHelper(that,that.init,that.cond,that.step,that.body);
    }
    
    @Override
    public void visitForLoop(JCForLoop that) { 
        currentBlock.statements.add(comment(that.pos(),"for..."));
        loopHelper(that,that.init,that.cond,that.step,that.body);
    }
    
    /** A stack of the (nested) loops encountered */
    final protected List<JCTree> loopStack = new LinkedList<JCTree>();
    
    /** A map of labels to loops for continue statements */
    final protected Map<Name,JCTree> continueMap = new HashMap<Name,JCTree>();
    
    /* for (Init; Test; Update) S
     * becomes
     * LoopStart: - is actually the end of the current Block
     *   Init;
     * IF UNROLLING:
     *          compute loop condition
     *          goto LoopUnroll0, LoopEnd
     *       LoopUnroll0:
     *          assume loop condition
     *          S
     *          Update
     *       [  compute loop condition
     *          goto LoopUnroll1, LoopEnd
     *       LoopUnroll1:
     *          assume loop condition
     *          S
     *          Update
     *        ]  
     *   compute loop condition
     *   goto LoopBody, LoopEnd
     * LoopBody:
     *   assume loop condition value
     *   S  [ break -> LoopBreak; continue -> LoopContinue ]
     *   goto LoopContinue
     * LoopContinue:  <-- all continues go here
     *   Update;
     *   
     * LoopEnd:
     *   assume !(loop condition value) 
     *   goto LoopBreak
     * LoopBreak: <-- all breaks go here
     *   goto LoopAfter...
     */ // FIXME - allow for unrolling; review the above and the implementation

    // FIXME - check and document; add backedges
    protected void loopHelper(JCTree that, List<JCStatement> init, JCExpression test, List<JCExpressionStatement> update, JCStatement body) {
        loopStack.add(0,that);
        breakStack.add(0,that);
        int pos = that.pos;
        T bloopBody = newBlock(LOOPBODY,pos);
        T bloopContinue = newBlock(LOOPCONTINUE,pos);
        T bloopEnd = newBlock(LOOPEND,pos);

        // Now create a block for everything that follows the
        // loop statement
        T bloopAfter = newBlockWithRest(LOOPAFTER,pos);// it gets all the followers and statements of the current block
        T previousBreakBlock = breakBlocks.put(names.empty, bloopAfter);
        
        if (init != null) remainingStatements.addAll(init);
        scan(test);
        JCExpression ntest = result;
        
        T bloopStart = currentBlock;
        follows(bloopStart,bloopBody);
        follows(bloopStart,bloopEnd);

        // Create the loop body block
        addAssume(test.pos,Label.LOOP,ntest,bloopBody.statements);
        bloopBody.statements.add(body);
        follows(bloopBody,bloopContinue);
        
        // Create the loop continue block
        // It does the update
        if (update != null) bloopContinue.statements.addAll(update);
        
        // Create the loop end block
        addAssume(test.pos,Label.LOOP,treeutils.makeNot(test.pos, ntest),bloopEnd.statements);
        
        follows(bloopEnd,bloopAfter);

        // Now process all the blocks
        Stack<T> savedTodo = pushTodo();
        
        processCurrentBlock();
        processBlocks();
        processBlock(bloopBody);
        processBlocks();
        processBlock(bloopContinue);
        processBlocks();
        processBlock(bloopEnd);
        processBlocks();
        loopStack.remove(0);
        breakStack.remove(0);
        breakBlocks.put(names.empty, previousBreakBlock);
        
        savedTodo = popTodo(savedTodo);
        todo.push(bloopAfter);
        
    }
    
    @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        currentBlock.statements.add(comment(that.pos(),"for..."));
        loopHelperEFor(that);
    }

    @Override
    public void visitForeachLoop(JCEnhancedForLoop that) {
        currentBlock.statements.add(comment(that.pos(),"for..."));
        loopHelperEFor(that);
    }
    
    // FIXME - not implemented at all
    protected void loopHelperEFor(JCEnhancedForLoop that) {
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
//            loopHelper(that,null,treeutils.trueLit,null,M.at(that.body.pos).Block(0,newbody.toList()));
//            
//            
//        } else {
            notImpl(that);
//        }
    }
    
    @Override
    public void visitDoLoop(JCDoWhileLoop that) {
        currentBlock.statements.add(comment(that.pos(),"do..."));
        loopHelperDoWhile(that);
    }    

    @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        currentBlock.statements.add(comment(that.pos(),"do..."));
        loopHelperDoWhile(that);
    }

    /* FOR A DO-WHILE LOOP
     * do { S; } while (Test)    becomes
     * 
     * LoopBody:
     *   S  [ break -> LoopBreak; continue -> LoopContinue ]
     *   goto LoopContinue
     * LoopContinue:  <-- all continues go here
     *   compute loop condition (which may have side effects creating other statements)
     *   goto LoopEnd
     * LoopEnd:
     *   assume !(loop condition value) 
     *   goto LoopBreak
     * LoopBreak: <-- all breaks go here
     *   goto rest...
     */ // FIXME - allow for unrolling
    protected void loopHelperDoWhile(JCDoWhileLoop that) {
        loopStack.add(0,that);
        breakStack.add(0,that);
        int pos = that.pos;
        T bloopBody = newBlock(LOOPBODY,pos);
        T bloopContinue = newBlock(LOOPCONTINUE,pos);
        T bloopEnd = newBlock(LOOPEND,pos);
        T bloopBreak = newBlock(LOOPBREAK,pos);
        follows(currentBlock,bloopBody);
        follows(bloopBody,bloopContinue);
        follows(bloopContinue,bloopEnd);
        follows(bloopEnd,bloopBreak);

        // Create an (unprocessed) block for everything that follows the
        // loop statement
        T bloopAfter = newBlockWithRest(LOOPAFTERDO,pos);// it gets all the followers of the current block
        follows(bloopBreak,bloopAfter);
        T previousBreakBlock = breakBlocks.put(names.empty, bloopBreak);
        
        Stack<T> savedTodo = pushTodo();
        try {
            // do the loop body
            bloopBody.statements.add(that.body);

            processCurrentBlock();
            processBlocks();
            processBlock(bloopBody);
            processBlocks();
            scan(that.cond); // TODO - fix for case that has side -effects - not currently used
            JCExpression ntest = result;
            addAssume(that.cond.pos,Label.LOOP,treeutils.makeNot(ntest.pos,ntest),bloopEnd.statements);
            processBlock(bloopContinue);
            processBlocks();

        } finally {
            loopStack.remove(0);
            breakStack.remove(0);
            breakBlocks.put(names.empty,previousBreakBlock);
        }
        
        savedTodo = popTodo(savedTodo);
        todo.push(bloopAfter);
        todo.push(bloopBreak);
        todo.push(bloopEnd);
        
//        processBlock(bloopEnd);
//        processBlock(bloopBreak);
//        processBlock(bloopAfter);
    }


    // JAVA OTHER STATEMENT AND EXPRESSION NODES
    
    // Just process all the statements in the block prior to any other
    // remaining statements 
    // OK
    @Override
    public void visitBlock(JCBlock that) {
        List<JCStatement> s = that.getStatements();
        if (s != null) {
            // Add the block statements BEFORE any remaining statements
            remainingStatements.addAll(0,s);
        }
    }
    
    @Override
    public void visitJmlBlock(JmlBlock that) {
        visitBlock(that);
    }
    
    /** Finds the statement that a labeled statement labels, stripping off all
     * nested labels.
     */
    JCTree stripLabels(JCStatement st) {
        while (st instanceof JCLabeledStatement) st = ((JCLabeledStatement)st).getStatement();
        return st;
    }
    
    // OK
    @Override
    public void visitLabelled(JCLabeledStatement that) {
        shouldNotBeCalled(that);
    }
    
    @Override 
    public void visitJmlLabeledStatement(JmlLabeledStatement that) {
        List<JCStatement> copy = new LinkedList<>();
        copy.addAll(that.extraStatements);
        processStats(copy);
        T nextBlock = newBlockWithRest(AFTERLABEL,that.pos);
        follows(currentBlock,nextBlock);
        breakBlocks.put(that.label, nextBlock);
        continueMap.put(that.label, stripLabels(that));
        try {
            Stack<T> savedTodo = pushTodo();
            remainingStatements.add(that.getStatement());
            processCurrentBlock();
            processBlocks();
            savedTodo = popTodo(savedTodo);
        } finally {
            breakBlocks.remove(that.label);
            continueMap.remove(that.label);
        }
        todo.push(nextBlock);
    }

    @Override public void visitTopLevel(JCCompilationUnit that)    { shouldNotBeCalled(that); }
    @Override public void visitImport(JCImport that)               { shouldNotBeCalled(that); }
    @Override public void visitClassDef(JCClassDecl that)          { shouldNotBeCalled(that); } // should always be JmlClassDecl objects
    @Override public void visitMethodDef(JCMethodDecl that)        { shouldNotBeCalled(that); }
    @Override public void visitVarDef(JCVariableDecl that)         { notImpl(that); }

    @Override public void visitTypeIdent(JCPrimitiveTypeTree that) { notImpl(that); }
    @Override public void visitTypeArray(JCArrayTypeTree that)     { notImpl(that); }
    @Override public void visitTypeApply(JCTypeApply that)         { notImpl(that); }
    @Override public void visitTypeParameter(JCTypeParameter that) { notImpl(that); }
    @Override public void visitWildcard(JCWildcard that)           { notImpl(that); }
    @Override public void visitTypeBoundKind(TypeBoundKind that)   { notImpl(that); }
    @Override public void visitAnnotation(JCAnnotation that)       { notImpl(that); }
    @Override public void visitModifiers(JCModifiers that)         { notImpl(that); }
    @Override public void visitErroneous(JCErroneous that)         { notImpl(that); }
    @Override public void visitLetExpr(LetExpr that)               { notImpl(that); }

    // OK
    @Override public void visitExec(JCExpressionStatement that)    { 
        // This includes assignments and stand-alone method invocations
        scan(that.expr);
    }

 // Do not need to override these methods
//  @Override public void visitSkip(JCSkip that) { super.visitSkip(that); }

    // No default implementation for these
    @Override public void visitApply(JCMethodInvocation that) { notImpl(that); }
    @Override public void visitAssert(JCAssert that) { notImpl(that); }
    @Override public void visitAssign(JCAssign that) { notImpl(that); }
    @Override public void visitAssignop(JCAssignOp that) { notImpl(that); }
    
    // Expressions just need to set the result field
    @Override public void visitBinary(JCBinary that) {
        scan(that.lhs);
        that.lhs = result;
        scan(that.rhs);
        that.rhs = result;
        result = that; 
    }
    
    @Override public void visitConditional(JCConditional that) { 
        scan(that.cond);
        that.cond = result;
        scan(that.truepart);
        that.truepart = result;
        scan(that.falsepart);
        that.falsepart = result;
        result = that; 
    }

    // NOTE: Likely should be overridden
    @Override public void visitIdent(JCIdent that) { 
        result = that; 
    }
    
    @Override public void visitIndexed(JCArrayAccess that) {
        scan(that.indexed);
        that.indexed = result;
        scan(that.index);
        that.index = result;
        result = that; 
    }
    
    @Override public void visitLiteral(JCLiteral that) { 
        result = that; 
    }
    
    @Override public void visitNewArray(JCNewArray that) {
        scan(that.elemtype);
        that.elemtype = result;
        scan(that.dims);
        scan(that.elems);
        result = that; 
    }
    
    @Override public void visitNewClass(JCNewClass that) {
        scan(that.encl);
        that.encl = result;
        scan(that.typeargs);
        scan(that.clazz);
        that.clazz = result;
        scan(that.args);
        scan(that.def);
        result = that; 
    }
    
    @Override public void visitParens(JCParens that) { 
        scan(that.expr);
        that.expr = result;
        result = that; 
    }
    
    @Override public void visitSelect(JCFieldAccess that) {
        scan(that.selected);
        that.selected = result;
        result = that; 
    }
    
    @Override public void visitTypeCast(JCTypeCast that) { 
        scan(that.clazz);
        that.clazz = result;
        scan(that.expr);
        that.expr = result;
        result = that; 
    }
    
    @Override public void visitTypeTest(JCInstanceOf that) { 
        scan(that.clazz);
        that.clazz = result;
        scan(that.expr);
        that.expr = result;
        result = that; 
    }
    
    @Override public void visitUnary(JCUnary that) { 
        scan(that.arg);
        that.arg = result;
        result = that; 
    }
    

    // FIXME _ what about the BB nodes

    
    
    // JML NODES - BasicBlockers asssume that nearly all JML specs have been 
    // translated into asserts and assume statements, or into uninterpreted
    // functions.
    
    // Needs implementation in derived classes
    @Override public void visitJmlMethodInvocation(JmlMethodInvocation that)    { notImpl(that); }
    @Override public void visitJmlVariableDecl(JmlVariableDecl that)            { notImpl(that); }
    @Override public void visitJmlSingleton(JmlSingleton that)                  { notImpl(that); }

    @Override public void visitJmlBinary(JmlBinary that)                        { shouldNotBeCalled(that); }
    @Override public void visitJmlChoose(JmlChoose that)                        { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodSig(JmlMethodSig that) { shouldNotBeCalled(that); }
    @Override public void visitJmlGroupName(JmlGroupName that)                  { shouldNotBeCalled(that); }
    @Override public void visitJmlLblExpression(JmlLblExpression that)          { shouldNotBeCalled(that); }    
    @Override public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that)    { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that)    { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodSpecs(JmlMethodSpecs that)              { shouldNotBeCalled(that); }
    @Override public void visitJmlModelProgramStatement(JmlModelProgramStatement that) { shouldNotBeCalled(that); }
    @Override public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that)        { shouldNotBeCalled(that); }
    @Override public void visitJmlSetComprehension(JmlSetComprehension that)    { shouldNotBeCalled(that); }
    @Override public void visitJmlSpecificationCase(JmlSpecificationCase that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlStatement(JmlStatement that)                  { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementDecls(JmlStatementDecls that)        { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that){ shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that)      { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseIn(JmlTypeClauseIn that)            { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that)        { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that)        { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that)        { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) { shouldNotBeCalled(that); }

    // These do not need to be implemented
    @Override public void visitJmlCompilationUnit(JmlCompilationUnit that)      { shouldNotBeCalled(that); }
    @Override public void visitJmlImport(JmlImport that)                        { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodDecl(JmlMethodDecl that)                { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementSpec(JmlStatementSpec that)          { shouldNotBeCalled(that); }


    
    /** This method is not called for top-level classes, since the BasicBlocker
     *  is invoked directly for each method.
     */
    // FIXME - what about for anonymous classes or local classes or nested classes
    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        // Nested classes are found in JmlEsc.  We get to this point if there is a local
        // class declaration within method body.
        
        JmlEsc.instance(context).visitClassDef(that);
    }


    
    // OK - e.g., assert, assume, comment statements
    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) { 
        currentBlock.statements.add(that);
    }
    
    // OK
    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) { 
        notImpl(that);
    }
    

}
