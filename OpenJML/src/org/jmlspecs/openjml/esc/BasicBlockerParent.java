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

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicProgramParent.BlockParent;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.ListBuffer;
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
 * 
 * @typeparam T basic block type
 * @typeparam P basic block program type
 * @author David Cok
 */
abstract public class BasicBlockerParent<T extends BlockParent<T>,P extends BasicProgramParent<T>> extends JmlTreeScanner {

    // FIXME - can this stuff be common?
    /////// To have a unique BasicBlocker instance for each method translated
    // In the initialization of tools, call  BasicBlocker.Factory.preRegister(context);
    // Obtain a new BasicBlocker when desired with  context.get(BasicBlocker.class);
        
//    /** Register a Ter Factory, if nothing is registered yet */
//    public static void preRegister(final Context context) {
//        //if (context.get(key) != null) return;
//        context.put(key, new Context.Factory<BasicBlocker>() {
//            @Override
//            public BasicBlocker make(Context context) {
//                return new BasicBlocker(context);
//            }
//        });
//    }
//    
//    final public static Context.Key<BasicBlocker> key =
//        new Context.Key<BasicBlocker>();
    
    /////// To have one BasicBlocker instance per context use this method without the pre-registration
    // Don't need pre-registration since we are not replacing any tool and not using a factory
    // To obtain a reference to the instance of BasicBlocker for the current context
    //                                 BasicBlocker.instance(context);
    
//    /** Get the instance for this context. 
//     * 
//     * @param context the compilation context
//     * @return a (unique for the context) Ter instance
//     */
//    public static BasicBlocker instance(@NonNull Context context) {
//        BasicBlocker instance = context.get(key);
//        // This is lazily initialized so that a derived class can preRegister to
//        // replace this Ter
//        if (instance == null) {
//            instance = new BasicBlocker(context);
//        }
//        return instance;
//    }
    

    // THE FOLLOWING ARE ALL FIXED STRINGS
    
    //-----------------------------------------------------------------
    // Names for various basic blocks
    
    /** The prefix used for names of blocks */
    public static final @NonNull String blockPrefix = "BL_";
    
    /** Standard name for the block that starts the body */
    public static final @NonNull String BODY_BLOCK_NAME = "bodyBegin";
    
    /** Standard name for the starting block of the program (just has the preconditions) */
    public static final @NonNull String START_BLOCK_NAME = "Start";
    
    /** Suffix for the name of a basic block for a finally block */
    public static final String FINALLY = "_finally";
    
    /** Suffix for the name of a basic block for a finally block */
    public static final String AFTERTRY = "_AfterTry";
    
    /** Suffix for the name of a basic block that comes after a switch statement */
    public static final String AFTERLABEL = "_AfterLabel";
    
    /** Suffix for the name of a basic block that comes after a switch statement */
    public static final String AFTERSWITCH = "_AfterSwitch";
    
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
    
    /** Suffix for the name of a basic block after a return statement */
    public static final String RETURN = "_return";
    
    /** Suffix for the name of a basic block after a throw statement */
    public static final String THROW = "_throw";
    
    // FIXME - use this or not?
    /** Prefix for branch condition variables */
    public static final String BRANCHCONDITION_PREFIX = "branchCondition_";
    

    
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
    @NonNull final protected JmlTree.Maker M;

    // THE FOLLOWING FIELDS ARE USED IN THE COURSE OF DOING THE WORK OF CONVERTING
    // TO BASIC BLOCKS.  They are fields of the class because they need to be
    // shared across the visitor methods.
    
    /** List of blocks completed processing - in basic block state */
    protected java.util.List<T> blocksCompleted;
    
    /** A map of names to blocks */
    protected java.util.Map<String,T> blockLookup;
    
    /** A variable to hold the block currently being processed */
    protected T currentBlock;
    
    /** Ordered list of statements from the current block that are yet to be processed into basic program form */
    protected List<JCStatement> remainingStatements;
    
    /** The program being constructed */
    protected P program = null;
    
    // Characteristics of the method under study
    // FIXME - what about methods in anonymous classes - do we have to be reentrant?
    
    /** The declaration of the method under conversion */
    protected JmlMethodDecl methodDecl;
    
    /** True if the method being converted is a constructor */
    protected boolean isConstructor;
    
    /** True if the method being converted is static */
    protected boolean isStatic;
    
    /** A counter used to make sure that block names are unique */
    protected int blockCount = 0;
    
    // FIXME - do we need this?
    /** Holds the result of any of the visit methods that produce JCExpressions, since the visitor
     * template used here does not have a return value.  [We could have used the templated visitor,
     * but other methods do not need to return anything, we don't need the additional parameter,
     * and that visitor is complicated by the use of interfaces for the formal parameters.]
     */
    protected JCExpression result;
    
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
    
    /** Creates a block name - note that this format is presumed when 
     * proof failures are being traced and understood.
     * @param pos the character position of the statement for which the block is being generated
     * @param kind a suffix to indicate the reason for block
     * @return a composite name for a block
     */
    public String blockName(int pos, String kind) {
        return blockPrefix + pos + kind;
    }
    
    /** The constructor, but use the instance() method to get a new instance,
     * in order to support extension.  This constructor should only be
     * invoked by a derived class constructor.
     * @param context the compilation context
     */
    protected BasicBlockerParent(@NonNull Context context) {
//        context.put(key, this);
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
    
    /** Creates a new block of the appropriate type; 
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
        return nb;
    }
    
    
    
    // METHODS


    /** Should not need this when everything is implemented */
    protected void notImpl(JCTree that) {
        log.noticeWriter.println("Internal error - visit method NOT IMPLEMENTED: " + getClass() + " - "+ that.getClass());
        result = treeutils.trueLit;
    }
    
    /** Called by visit methods that should never be called. */
    protected void shouldNotBeCalled(JCTree that) {
        log.error("esc.internal.error","Did not expect to be calling a " + that.getClass() + " within " + getClass());
        throw new JmlInternalError();
    }
    
    // FIXME - use treeutils?
    /** Creates a translated expression whose value is the given type;
     * the result is a JML type, e.g. a representation of an instantiated generic.*/
    protected JCExpression makeTypeLiteral(Type type, int pos) {
        return treeutils.trType(pos,type);
    }
    
    
    

    /** Start the processing of the given block:
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
            for (T pb: b.preceders) {
                //log.noticeWriter.println("   " + b.id() + " follows " + pb.id());
                if (!program.blocks.contains(pb)) {
                    log.noticeWriter.println("Internal Error: block " + pb.id.name + " precedes block " + b.id.name + " , but was not processed before it");
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
        currentBlock = b;
        remainingStatements = currentBlock.statements;
        currentBlock.statements = new ArrayList<JCStatement>();
    }
    
    /** Files away a completed block, adding it to the blocksCompleted list and
     * to the lookup Map; returns true if the block was already completed or is null.
     * @param b the completed block
     */
    protected boolean completed(@NonNull T b) {
        if (b == null) return true;
        if (blocksCompleted.contains(b)) return true; // Already completed - if a block's processing is ended early, it will have already been marked completed
        blocksCompleted.add(b);
        //log.noticeWriter.println("Completed block " + b.id);
        return false;
    }
    
    /** Updates the data structures to indicate that the after block follows the
     * before block
     * @param before block that precedes after
     * @param after block that follows before
     */
    protected void follows(@NonNull T before, @NonNull T after) {
        before.followers.add(after);
        after.preceders.add(before);
    }
    
    /** Updates the data structures to indicate that all the after blocks follow the
     * before block
     * @param before block that precedes after
     * @param after list of blocks that follow before
     */
    protected void follows(@NonNull T before, @NonNull List<T> after) {
        for (T b: after) {
            before.followers.add(b);
            b.preceders.add(before);
        }
    }
    
    /** Inserts the after block after the before block, replacing anything that
     * used to follow the before block
     * @param before block whose follow list is to be changed
     * @param after new following block
     */
    protected void replaceFollows(@NonNull T before, @NonNull T after) {
        for (T b: before.followers) {
            b.preceders.remove(before);
        }
        before.followers.clear();
        follows(before,after);
    }
    
    /** Inserts the after blocks after the before block, replacing anything that
     * used to follow the before block
     * @param before
     * @param after
     */
    protected void replaceFollows(@NonNull T before, @NonNull List<T> after) {
        for (T b: before.followers) {
            b.preceders.remove(before);
        }
        before.followers.clear();
        for (T b: after) {
            follows(before,b);
        }
    }
    
    
    /** Returns a new, empty block
     * 
     * @param name the name to give the block
     * @param pos a position to associate with the JCIdent for the block
     * @return the new block
     */
    protected @NonNull T newBlock(@NonNull String key, int pos) {
        String name = blockName(pos,key);
        JCIdent id = treeutils.makeIdent(pos,name + "_" + (++blockCount),syms.booleanType);
        T bb = newBlock(id);
        blockLookup.put(id.name.toString(),bb);
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
        JCIdent id = treeutils.makeIdent(pos,name + "_" + (++blockCount),syms.booleanType);
        T bb = newBlock(id,previousBlock);
        blockLookup.put(id.name.toString(), bb);
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
        // We do this switch to avoid creating more new lists
        List<JCStatement> temp = b.statements; // empty
        b.statements = remainingStatements; // it gets all of the remaining statements
        remainingStatements = temp; // empty
        return b;
    }
    
    /** A helper initialization routine for derived classes, to be called at
     * the start of converting a method body
     */
    protected @NonNull void initialize(@NonNull JCMethodDecl methodDecl, 
           @NonNull JCClassDecl classDecl) {
        this.methodDecl = (JmlMethodDecl)methodDecl;
        program = newProgram(context);
        program.methodDecl = methodDecl;
        isConstructor = methodDecl.sym.isConstructor();  // FIXME - careful if there is nesting???
        isStatic = methodDecl.sym.isStatic();
        if (classDecl.sym == null) {
            log.error("jml.internal","The class declaration in convertMethodBody appears not to be typechecked");
            return;
        }
        blocksCompleted = new ArrayList<T>();
        blockLookup = new java.util.HashMap<String,T>();
    }

    
    /** Does the conversion of a block with Java statements into basic program
     * form, possibly creating new blocks on the todo list
     * @param block the block to process
     */
    protected void processBlock(@NonNull T block) {
        if (block.preceders.isEmpty()) {
            // Delete any blocks that do not follow anything
            // This can happen for example if the block is an afterIf block
            // and both the then branch and the else branch terminate with
            // a return or throw statement. If the block does contain some
            // statement then those will never be executed. They should 
            // have been warned about by the compiler. Here we will 
            // log a warning, ignore the block, and continue processing.
            // Note that the block will still have an id and be in the 
            // id map.
            if (!block.statements.isEmpty()) {
                log.warning("jml.internal","A basic block has no predecessors - ignoring it: " + block.id);
            }
            for (T b: block.followers) {
                b.preceders.remove(block);
            }
            return;// Don't add it to the completed blocks
        }
        if (!program.blocks.contains(block)) {
            startBlock(block);
            processBlockStatements(true);
        } else {
            log.warning("jml.internal","Basic block " + block.id + " is being processed another time");
        }
    }
    
    /** Iterates through the statements on the remainingStatements list, processing them
     * 
     * @param complete call 'completed' on the currentBlock, if true
     */
    protected void processBlockStatements(boolean complete) {
        while (!remainingStatements.isEmpty()) {
            JCStatement s = remainingStatements.remove(0);
            if (s != null) s.accept(this);  // A defensive check - statements in the list should not be null
        }
        if (complete) completed(currentBlock);
    }
    
    
    
    /** Associates end position information with newnode, taking the information
     * from srcnode; the information is stored in the end-position table that
     * is part of log.currentSource(). No action happens if either argument is null.
     */
    public void copyEndPosition(@Nullable JCTree newnode, @Nullable JCTree srcnode) {
        Map<JCTree,Integer> z = log.currentSource().getEndPosTable();
        if (z != null && srcnode != null) { // srcnode can be null when processing a switch statement
            int end = srcnode.getEndPosition(z);
            if (end != Position.NOPOS) z.put(newnode, end);
        }
    }

    
    
//    // FIXME - REVIEW and document
//    /** Adds a new assume statement to the end of the currentBlock; the assume statement is
//     * given the declaration pos and label from the arguments; it is presumed the input expression is
//     * translated, as is the produced assume statement.
//     * @param pos the declaration position of the assumption
//     * @param label the kind of assumption
//     * @param that the (translated) expression being assumed
//     */
//    protected void addAssume(int pos, Label label, JCExpression that) {
//        addAssume(pos,label,that,currentBlock.statements);
//    }
    
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
        JmlStatementExpr st;
//        if (useAssumeDefinitions) {
//            JCIdent id = factory.Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
//            id.type = syms.booleanType;
//            newdefs.add(new BasicProgram.Definition(that.pos,id,that)); // FIXME- end position?
//            st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,id);
//        } else {
            st = M.at(pos).JmlExpressionStatement(JmlToken.ASSUME,label,that);
//        }
        copyEndPosition(st,that);
        st.type = null; // statements do not have a type
        statements.add(st);
        return st;
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
        if (startpos < 0) startpos = that.pos; // FIXME - temp - and probably is not really the startpos
        JmlStatementExpr st;
//        if (useAssumeDefinitions) {
//            JCIdent id = factory.Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
//            id.type = syms.booleanType;
//            newdefs.add(new BasicProgram.Definition(that.pos,id,that)); // FIXME- start, end position?
//            st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,id);
//        } else {
            st = M.at(startpos).JmlExpressionStatement(JmlToken.ASSUME,label,that);
//        }
        copyEndPosition(st,endpos);
        st.type = null; // statements do not have a type
        statements.add(st);
        return st;
    }
    
//    // FIXME - REVIEW and document
//    /** Adds a new UNTRANSLATED assume statement to the end of the given statements list; the statements list
//     * should be a list of statements that will be processed (and translated) at some later time;
//     * the assume statement is
//     * given the declaration pos and label from the arguments; it is presumed the input expression is
//     * untranslated, as is the produced assume statement.
//     * @param pos the declaration position of the assumption
//     * @param label the kind of assumption
//     * @param that the (untranslated) expression being assumed
//     * @param statements the list to add the new assume statement to
//     */
//    protected JmlStatementExpr addUntranslatedAssume(int pos, Label label, JCExpression that, List<JCStatement> statements) {
//        JmlStatementExpr st = M.at(pos).JmlExpressionStatement(JmlToken.ASSUME,label,that);
//        st.type = null; // statements do not have a type
////        copyEndPosition(st,that);
//        statements.add(st);
//        return st;
//    }
    
//    // FIXME - REVIEW and document
//    protected JmlStatementExpr addUntranslatedAssume(int pos, JCTree posend, Label label, JCExpression that, List<JCStatement> statements) {
//        JmlStatementExpr st = M.at(pos).JmlExpressionStatement(JmlToken.ASSUME,label,that);
//        st.type = null; // statements do not have a type
////        copyEndPosition(st,posend);
//        statements.add(st);
//        return st;
//    }
    
    
    
    /** This generates a comment statement (not added to any statement list) whose content is the
     * given String.
     */
    public JmlStatementExpr comment(DiagnosticPosition pos, String s) {
        return M.at(pos).JmlExpressionStatement(JmlToken.COMMENT,null,M.Literal(s));
    }
    
    /** This generates a comment statement (not in any statement list) whose content is the
     * given JCTree, pretty-printed.
     */
    public JmlStatementExpr comment(JCTree t) {
        return comment(t.pos(),JmlPretty.write(t,false));
    }
    


    
    // FIXME - do we need this - here?
    /** Makes a JML \typeof expression, with the given expression as the argument */
    protected JCExpression makeTypeof(JCExpression e) {
        JCExpression typeof = M.at(e.pos).JmlMethodInvocation(JmlToken.BSTYPEOF,e);
        typeof.type = syms.classType;
        return typeof;
    }
    
//    // FIXME - review and document
//    /** Makes a Java this parse tree node (attributed) */
//    protected JCIdent makeThis(int pos) {
//        return treeutils.makeIdent(pos,methodDecl._this);
//    }
    
    // FIXME - review and document
    /** Makes the equivalent of an instanceof operation: \typeof(e) <: \type(type) */
    protected JCExpression makeNNInstanceof(JCExpression e, int epos, Type type, int typepos) {
        JCExpression e1 = makeTypeof(e);
        JCExpression e2 = makeTypeLiteral(type,typepos);
        //if (inSpecExpression) e2 = trSpecExpr(e2,null);
        JCExpression ee = treeutils.makeJmlBinary(epos,JmlToken.SUBTYPE_OF,e1,e2);
        return ee;
    }
    
//    // FIXME - review and document
//    /** Makes the equivalent of an instanceof operation: e !=null && \typeof(e) <: \type(type) */
//    protected JCExpression makeInstanceof(JCExpression e, int epos, Type type, int typepos) {
//        JCExpression e1 = treeutils.makeNeqObject(epos,e,treeutils.nulllit);
//        JCExpression e2 = treeutils.makeJmlBinary(epos,JmlToken.SUBTYPE_OF,makeTypeof(e),makeTypeLiteral(type,typepos));
//        //if (inSpecExpression) e2 = trSpecExpr(e2,null);
//        JCExpression ee = treeutils.makeBinary(epos,JCTree.AND,e1,e2);
//        return ee;
//    }
    
//    // FIXME - review and document
//    protected MethodSymbol makeFunction(Name name, Type resultType, Type... argTypes) {
//        ListBuffer<Type> args = new ListBuffer<Type>().appendArray(argTypes);
//        MethodType methodType = new MethodType(args.toList(),resultType,com.sun.tools.javac.util.List.<Type>nil(),syms.methodClass);
//        MethodSymbol meth = new MethodSymbol(Flags.STATIC,name,methodType,null); // no owner
//        return meth;
//    }
    
//    // FIXME - review and document
//    protected JCExpression makeFunctionApply(int pos, MethodSymbol meth, JCExpression... args) {
//        JCIdent methid = M.at(pos).Ident(meth);
//        JCExpression e = M.at(pos).Apply(null,methid,new ListBuffer<JCExpression>().appendArray(args).toList());
//        e.type = meth.getReturnType();
//        return e;
//    }
    
//    // FIXME - review and document
//    protected JCExpression makeSignalsOnly(JmlMethodClauseSignalsOnly clause) {
//        JCExpression e = treeutils.makeBooleanLiteral(clause.pos,false);
//        JCExpression id = M.at(0).JmlSingleton(JmlToken.BSEXCEPTION);
//        for (JCExpression typetree: clause.list) {
//            int pos = typetree.getStartPosition();
//            e = treeutils.makeBinary(pos, 
//                    JCTree.OR, makeNNInstanceof(id, pos, typetree.type, pos), e);
//        }
//        return e;
//    }

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


    // JAVA CONTROL STATEMENT NODES
    
    // FIXME - update this
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
    @Override
    public void visitSwitch(JCSwitch that) { 
        currentBlock.statements.add(comment(that.pos(),"switch ..."));
        int pos = that.pos;
        scan(that.selector);
        JCExpression switchExpression = (that.selector);
        int swpos = switchExpression.getStartPosition();
        List<JCCase> cases = that.cases;
        
        // Create the ending block name
        T brest = null;
        
        try {
            breakStack.add(0,that);

            // We create a new auxiliary variable to hold the switch value, so 
            // we can track its value and so the subexpression does not get
            // replicated.  We add an assumption about its value and add it to
            // list of new variables
            String switchName = ("_switchExpression_" + pos); // FIXME - define string?
 
            JCIdent vd = treeutils.makeIdent(swpos,switchName,switchExpression.type);
            if (program instanceof BoogieProgram)
              ((BoogieProgram)program).declarations.add(vd);   // FIXME
            else if (program instanceof BasicProgram)
                ((BasicProgram)program).declarations.add(vd);   // FIXME
            JCExpression newexpr = treeutils.makeBinary(swpos,JCTree.EQ,vd,switchExpression);
            addAssume(swpos,switchExpression,Label.SWITCH_VALUE,newexpr,currentBlock.statements);
            T switchStart = currentBlock;

            // Now create an (unprocessed) block for everything that follows the
            // switch statement
            brest = newBlockWithRest(AFTERSWITCH,pos);// it gets all the followers of the current block
            breakBlocks.put(names.empty, brest);
            
            // Now we need to make an unprocessed block for each of the case statements,
            // adding them to the todo list at the end
            // Note that there might be nesting of other switch statements etc.
            java.util.LinkedList<T> blocks = new java.util.LinkedList<T>();
            T prev = null;
            JCExpression defaultCond = treeutils.falseLit;
            JmlTree.JmlStatementExpr defaultAsm = null;
            for (JCCase caseStatement: cases) {
                /*@ nullable */ JCExpression caseValue = caseStatement.getExpression();
                List<JCStatement> stats = caseStatement.getStatements();
                int casepos = caseStatement.getStartPosition();
                
                // create a block for this case test
                T blockForTest = newBlock(caseValue == null ? "_default" : "_case" ,
                        caseValue == null ? casepos: caseStatement.getStartPosition());
                blocks.add(blockForTest);
                follows(switchStart,blockForTest);
                
                // create the case test, or null if this is the default case
                /*@ nullable */ JCBinary eq = caseValue == null ? null : treeutils.makeBinary(caseValue.getStartPosition(),JCTree.EQ,vd,(caseValue));
                JmlStatementExpr asm = addAssume(caseStatement.pos,Label.CASECONDITION,eq,blockForTest.statements);
                
                // continue to build up the default case test
                if (caseValue == null) defaultAsm = asm; // remember the assumption for the default case
                else defaultCond = treeutils.makeOr(caseValue.getStartPosition(),eq,defaultCond);

                // determine whether this case falls through to the next
                boolean fallthrough = stats.isEmpty() || !(stats.get(stats.size()-1) instanceof JCBreak);
                
                if (prev == null) {
                    // statements can go in the same block
                    blockForTest.statements.addAll(stats);
                    follows(blockForTest,brest); // The following block is reset if there is fallthrough to a next block
                    prev = fallthrough ? blockForTest : null;
                } else {
                    // falling through from the previous case
                    // since there is fall-through, the statements need to go in their own block
                    T blockForStats = newBlock("_caseBody_",caseStatement.getStartPosition());
                    blockForStats.statements.addAll(stats);
                    follows(blockForTest,blockForStats);
                    replaceFollows(prev,blockForStats);
                    follows(blockForStats,brest);
                    blocks.add(blockForStats);
                    prev = fallthrough ?  blockForStats : null;
                }
            }

            // Now fix up the default case (which is not necessarily last).
            // Fortunately we remembered it
            int dpos = defaultAsm == null ? pos : defaultAsm.pos;
            JCExpression eq = treeutils.makeUnary(dpos,JCTree.NOT,defaultCond);
            if (defaultAsm != null) {
                // There was a default case already made, but at the time we just
                // put in null for the case condition, since we did not know it
                // yet (and we wanted to process the statements in textual order).
                // So here we violate encapsulation a bit and poke it in.
                defaultAsm.expression = eq;
            } else {
                // There was no default - we need to construct an empty one
                // create a block for this case test
                T blockForTest = newBlock("_defaultcase_",pos);
                blocks.add(blockForTest);
                follows(switchStart,blockForTest);
                follows(blockForTest,brest);
                
                addAssume(that.pos,Label.CASECONDITION,eq,blockForTest.statements);
            }
            
            processBlockStatements(true); // Complete the current block
            // Now process all of the blocks we created
            for (T b: blocks) {
                processBlock(b);
            }
        } finally {
            breakStack.remove(0);
            breakBlocks.remove(names.empty);
        }
        // Should never actually be null
        if (brest != null) processBlock(brest);
    }
    
    // OK
    /** Should call this because case statements are handled in switch. */
    public void visitCase(JCCase that) { shouldNotBeCalled(that); }
    
    /** Stack to hold Ts for catch clauses, when try statements are nested */
    protected java.util.List<T> catchStack = new java.util.LinkedList<T>();
    
    /** Stack to hold Ts for finally clauses, when try statements are nested */
    protected java.util.List<T> finallyStack = new java.util.LinkedList<T>();

    // This sets up a complicated arrangement of blocks
    //
    // currentBlock:    try statement
    //                  rest of statements
    //
    // becomes
    //
    // currentBlock:    try statement block
    //                      throw - goto catchBlocks
    //                      return - goto tryreturnBlock
    //                  goto finallyBlock
    //
    // tryreturnBlock:  assume terminationVar > 0
    //                  goto finallyBlock
    //
    // catchBlocks:     assume terminationVar < 0
    //                  assume condition on exception
    //                  reset terminationVar to 0
    //                  catch block statements
    //                  goto finallyBlock
    //
    // finallyBlock:    any finally block statements
    //                  goto afterTryBlock, condExceptionBlock, condReturnBlock
    //                [ if the try block is nested then instead we
    //                  goto afterTryBlock, catchBlocks of outer try, tryreturnBlock of outer try]
    //
    // afterTryBlock:   assume terminationVar == 0
    //                  rest of statements
    //
    //
    // FIXME - the catch blocks should use Java not JML subtype tests
    // FIXME - review
    // FIXME - unify the use of the termination var?
    @Override
    public void visitTry(JCTry that) {
        currentBlock.statements.add(comment(that.pos(),"try..."));

        // Create an (unprocessed) block for everything that follows the
        // try statement
        int pos = that.pos;
        T brest = newBlockWithRest(AFTERTRY,pos);// it gets all the followers of the current block
        
        // remainingStatements is now empty
        // Put the statements in the try block into the currentBlock
        remainingStatements.add(that.getBlock());
        
        // We make an empty finally block if the try statement does not
        // have one, just to simplify things
        T finallyBlock = newBlock(FINALLY,pos);
        JCBlock finallyStat = that.getFinallyBlock();
        if (finallyStat != null) finallyBlock.statements.addAll(finallyStat.getStatements()); // it gets the (unprocessed) statements of the finally statement
        follows(currentBlock,finallyBlock);
        follows(finallyBlock,brest);

        finallyStack.add(0,finallyBlock);
        
        // FIXME - why no catch blocks?

        // Finish the processing of the current block; it might
        // refer to the finally block during processing
        processBlockStatements(true);
        finallyStack.remove(0);
        processBlock(finallyBlock);
        processBlock(brest);
    }
    
    // is this true FIMXE review this
    /** Should call this because catch statements are desugared before calling the Ter. */
    public void visitCatch(JCCatch that) { 
        shouldNotBeCalled(that); 
    }
    
    // OK
    public void visitIf(JCIf that) {
        int pos = that.pos;
        currentBlock.statements.add(comment(that.pos(),"if..."));
        
        // Now create an (unprocessed) block for everything that follows the
        // if statement
        T brest = newBlockWithRest(AFTERIF,pos);// it gets all the followers of the current block
        processBlockStatements(true); // complete current block
        
        // Now make the then block
        T thenBlock = newBlock(THENSUFFIX,pos);
        addAssume(that.cond.pos, Label.BRANCHT, that.cond, thenBlock.statements);
        thenBlock.statements.add(that.thenpart);
        follows(thenBlock,brest);
        follows(currentBlock,thenBlock);
        
        // Now make the else block
        T elseBlock = newBlock(ELSESUFFIX,pos);
        addAssume(that.cond.pos, Label.BRANCHE, treeutils.makeNot(that.cond.pos,that.cond), elseBlock.statements);
        if (that.elsepart != null) elseBlock.statements.add(that.elsepart);
        follows(elseBlock,brest);
        follows(currentBlock,elseBlock);
        
        processBlock(thenBlock);
        processBlock(elseBlock);
        processBlock(brest);
    }
    
    /** This is a stack of loops and switch statements - anything that can 
     * contain a break statement
     */
    protected java.util.List<JCTree> breakStack = new java.util.LinkedList<JCTree>();
    
    /** This is a map of label to Block, giving the block to which a labelled break
     * should jump - which is the Block after the labelled statement.
     */
    protected java.util.Map<Name,T> breakBlocks = new java.util.HashMap<Name,T>();
    
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
                    log.error(that.pos(),"jml.internal","Corresponding break target is not found");
                } else {
                    replaceFollows(currentBlock,b);
                }

            } else {
                T b = breakBlocks.get(names.empty);
                if (b == null) {
                    log.error(that.pos(),"jml.internal","Corresponding break target is not found");
                } else {
                    replaceFollows(currentBlock,b);
                }
            }
        }
        if (!remainingStatements.isEmpty()) {
            log.warning(remainingStatements.get(0).pos(),"jml.internal.notsobad","Statements after a break statement are unreachable and are ignored");
        }
    }
    
    // FIXME - review with loops
    public void visitContinue(JCContinue that) {
        currentBlock.statements.add(comment(that));
        if (loopStack.isEmpty()) {
            log.error(that.pos(),"jml.internal","Empty loop stack for continue statement");
        } else if (that.label == null) {
            JCTree t = loopStack.get(0);
            String blockName = blockName(t.pos,LOOPCONTINUE);
            T b = blockLookup.get(blockName);
            if (b == null) log.noticeWriter.println("NO CONTINUE BLOCK: " + blockName);
            else replaceFollows(currentBlock,b);
        } else {
            log.warning("esc.not.implemented","continue statements with labels in BasicBlockerParent");
        }
        if (!remainingStatements.isEmpty()) {
            log.warning(remainingStatements.get(0).pos(),"jml.internal/notsobad","Statements after a break statement are unreachable and are ignored");
        }

    }
    
    // OK - presumes that the program has already been modified to record
    // the return value and that the entire method body is enclosed in an
    // outer try-finally block
    public void visitReturn(JCReturn that) {
        if (!remainingStatements.isEmpty()) {
            // Not fatal, but does indicate a problem with the original
            // program, which the compiler may have already identified
            log.warning(remainingStatements.get(0).pos,
                    "esc.internal.error",
                    "Unexpected statements following a return statement are ignored");
            remainingStatements.clear();
        }
        
        // FIXME - not sure why these statements are here
        T b = newBlockWithRest(RETURN,that.pos);
        follows(currentBlock,b);
        processBlockStatements(true);
        processBlock(b);
        
        // FIXME - need to check what shuold/does happen if the return statement
        // is in a catch or finally block
        
        if (finallyStack.isEmpty()) {
            // We don't expect the finallyStack to ever be empty when there is
            // a return statement only because
            // JmlAssertionAdder wraps everything in a try-finally statement
            // TODO - generalize this
            log.warning("esc.internal.error","finally stack is unexpectedly empty");
        } else {
            T finallyBlock = finallyStack.get(0);
            replaceFollows(b,finallyBlock);
        }
    }
    
    // OK - presumes that the program has already been modified to record
    // the value of the exception being thrown
    public void visitThrow(JCThrow that) { 
        
        if (!remainingStatements.isEmpty()) {
            // Not fatal, but does indicate a problem with the original
            // program, which the compiler may have already identified
            log.warning(remainingStatements.get(0).pos,
                    "esc.internal.error",
                    "Unexpected statements following a throw statement");
            remainingStatements.clear();
        }
        
        // FIXME - why are these here
        T b = newBlockWithRest(blockName(that.pos,THROW),that.pos);
        follows(currentBlock,b);
        processBlockStatements(true);
        processBlock(b);
        
        // FIXME - if we are already in a catch block we keep the finally block
        // as our follower.
        // FIXME - shouldn't throws go to the catch blocks?
        
        if (finallyStack.isEmpty()) {
            // We don't expect the finallyStack to ever be empty when there is
            // a return statement only because
            // JmlAssertionAdder wraps everything in a try-finally statement
            // TODO - generalize this
            log.warning("esc.internal.error","finally stack is unexpectedly empty");
        } else {
            T finallyBlock = finallyStack.get(0);
            replaceFollows(currentBlock,finallyBlock);
        }
        
    }
    
    // OK - FIXME - turn into a try-finally with lock operations?
    public void visitSynchronized(JCSynchronized that)   { 
        super.visitSynchronized(that);
    }
    

    // LOOPS
    
    
    // FIXME - review and document
    protected List<JCTree> loopStack = new LinkedList<JCTree>();
    
    /* for (Init; Test; Update) S
     * becomes
     * LoopStart: - is actually the end of the current Block
     *   Init;
     *   assert loop invariants
     *   [ goto LoopDo     <<< if a do while loop ]
     * IF UNROLLING:
     *          compute loop condition
     *          goto LoopUnroll0, LoopEnd
     *       LoopUnroll0:
     *          assume loop condition
     *          compute decreasing, check that it is >= 0
     *          S
     *          Update
     *          assert loop invariant
     *          check that decreasing has decreased
     *       [  compute loop condition
     *          goto LoopUnroll1, LoopEnd
     *       LoopUnroll1:
     *          assume loop condition
     *          compute decreasing, check that it is >= 0
     *          S
     *          Update
     *          assert loop invariant
     *          check that decreasing has decreased
     *        ]  
     *   havoc any loop modified variables
     *   assume loop invariants
     *   compute loop condition (which may have side effects creating other statements)
     *   goto LoopBody, LoopEnd
     * LoopBody:
     *   assume loop condition value
     *   compute decreasing, check that it is >= 0
     *   S  [ break -> LoopBreak; continue -> LoopContinue ]
     *   goto LoopContinue
     * LoopContinue:  <-- all continues go here
     *   Update;
     *   assert loop invariants
     *   check that decreasing is less
     * LoopEnd:
     *   assume !(loop condition value) 
     *   goto LoopBreak
     * LoopBreak: <-- all breaks go here
     *   //assert loop invariants 
     *   goto rest...
     */ // FIXME - allow for unrolling; review the above and the implementation

    // FIXME - check and document
    protected void visitLoopWithSpecs(JCTree that, List<JCStatement> init, JCExpression test, List<JCExpressionStatement> update, JCStatement body, List<JmlStatementLoop> loopSpecs) {
        loopStack.add(0,that);
        breakStack.add(0,that);
        int pos = that.pos;
        T bloopBody = newBlock(LOOPBODY,pos);
        T bloopContinue = newBlock(LOOPCONTINUE,pos);
        T bloopEnd = newBlock(LOOPEND,pos);
        T bloopBreak = newBlock(LOOPBREAK,pos);

        // Now create an (unprocessed) block for everything that follows the
        // loop statement
        T brest = newBlockWithRest(LOOPAFTER,pos);// it gets all the followers and statements of the current block
        T previousBreakBlock = breakBlocks.put(names.empty, brest);
        
        // Finish out the current block with the loop initialization
        if (init != null) remainingStatements.addAll(init);
        processBlockStatements(false);
        scan(test);  // FIXME - is this needed? if so, how about elsewehere?
        completed(currentBlock);
        
        T bloopStart = currentBlock;
        follows(bloopStart,bloopBody);
        if (tempFromForeachLoop) follows(bloopStart,bloopEnd);

        // Create the loop body block
        bloopBody.statements.add(body);
        follows(bloopBody,bloopContinue);
        
        // Create the loop continue block
        // do the update
        if (update != null) bloopContinue.statements.addAll(update);
        
        int end = endPos(body);
        if (end <= 0) {
            log.noticeWriter.println("BAD EBND");
        }
        
        // Create the (empty) LoopEnd block
        follows(bloopEnd,bloopBreak);
        
        // Create the (empty) LoopBreak block
        follows(bloopBreak,brest);

        // Now process all the blocks
        processBlock(bloopBody);
        processBlock(bloopContinue);
        processBlock(bloopEnd);
        processBlock(bloopBreak);
        loopStack.remove(0);
        breakStack.remove(0);
        breakBlocks.put(names.empty, previousBreakBlock);
        
        processBlock(brest);
        
    }
    
    
    boolean tempFromForeachLoop = false;
    
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        currentBlock.statements.add(comment(that.pos(),"for..."));
        tempFromForeachLoop = true;
        visitForeachLoopWithSpecs(that,that.loopSpecs);
        tempFromForeachLoop = false;
    }

    public void visitForeachLoop(JCEnhancedForLoop that) {
        currentBlock.statements.add(comment(that.pos(),"for..."));
        visitForeachLoopWithSpecs(that,null);
    }
    
    protected void visitForeachLoopWithSpecs(JCEnhancedForLoop that, com.sun.tools.javac.util.List<JmlStatementLoop> loopSpecs) {
        if (that.expr.type.tag == TypeTags.ARRAY) {
            // for (T v; arr) S
            // becomes
            //   for (int $$index=0; $$index<arr.length; $$index++) { v = arr[$$index]; S }
            
            // make   int $$index = 0;   as the initialization
//            Name name = names.fromString("$$index$"+that.pos);
//            JCVariableDecl decl = makeVariableDecl(name,syms.intType,treeutils.makeIntLiteral(0,pos),pos);
//            JCVariableDecl decl = ((JmlEnhancedForLoop)that).indexDecl;
//            JCVariableDecl vdecl = ((JmlEnhancedForLoop)that).indexDecl;
//            com.sun.tools.javac.util.List<JCStatement> initList = com.sun.tools.javac.util.List.<JCStatement>of(decl,vdecl);

            // make assume \values.size() == 0
            
//            // make   $$index < <expr>.length   as the loop test
//            JCIdent id = (JCIdent)factory.at(pos).Ident(decl);
//            id.type = decl.type;
//            JCExpression fa = factory.at(pos).Select(that.getExpression(),syms.lengthVar);
//            fa.type = syms.intType;
//            JCExpression test = treeutils.makeBinary(pos,JCTree.LT,id,fa);

//            // make   $$index = $$index + 1  as the update list
//            JCIdent idd = (JCIdent)factory.at(pos+1).Ident(decl);
//            id.type = decl.type;
//            JCAssign asg = factory.at(idd.pos).Assign(idd,
//                    treeutils.makeBinary(idd.pos,JCTree.PLUS,id,treeutils.makeIntLiteral(pos,1)));
//            asg.type = syms.intType;
//            JCExpressionStatement update = factory.at(idd.pos).Exec(asg);
//            com.sun.tools.javac.util.List<JCExpressionStatement> updateList = com.sun.tools.javac.util.List.<JCExpressionStatement>of(update);
            
//            // make   <var> = <expr>[$$index]    as the initialization of the target and prepend it to the body
//            JCArrayAccess aa = factory.at(pos).Indexed(that.getExpression(),id);
//            aa.type = that.getVariable().type;
//            JCIdent v = (JCIdent)factory.at(pos).Ident(that.getVariable());
//            v.type = aa.type;
//            asg = factory.at(pos).Assign(v,aa);
//            asg.type = v.type;
            ListBuffer<JCStatement> newbody = new ListBuffer<JCStatement>();
//            newbody.append(factory.at(pos).Exec(asg));
            newbody.append(that.body);
            
            // add 0 <= $$index && $$index <= <expr>.length
            // as an additional loop invariant
//            JCExpression e1 = treeutils.makeBinary(pos,JCTree.LE,treeutils.makeIntLiteral(pos,0),id);
//            JCExpression e2 = treeutils.makeBinary(pos,JCTree.LE,id,fa);
//            JCExpression e3 = treeutils.makeBinary(pos,JCTree.AND,e1,e2);
//            JmlStatementLoop inv =factory.at(pos).JmlStatementLoop(JmlToken.LOOP_INVARIANT,e3);
//            if (loopSpecs == null) {
//                loopSpecs = com.sun.tools.javac.util.List.<JmlStatementLoop>of(inv);
//            } else {
//                ListBuffer<JmlStatementLoop> buf = new ListBuffer<JmlStatementLoop>();
//                buf.appendList(loopSpecs);
//                buf.append(inv);
//                loopSpecs = buf.toList();
//            }
            visitLoopWithSpecs(that,null,treeutils.trueLit,null,M.at(that.body.pos).Block(0,newbody.toList()),null);
            
            
        } else {
            notImpl(that); // FIXME
        }
    }
    
    public void visitDoLoop(JCDoWhileLoop that) {
        currentBlock.statements.add(comment(that.pos(),"do..."));
        visitDoLoopWithSpecs(that,null);
    }    

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        currentBlock.statements.add(comment(that.pos(),"do..."));
        visitDoLoopWithSpecs(that,that.loopSpecs);
    }

    // FIXME - rewview this
    /* FOR A DO-WHILE LOOP
     * do { S; } while (Test)    becomes
     * 
     * LoopStart: - is actually the end of the current Block
     *   assert loop invariants
     *   havoc any loop modified variables
     *   assume loop invariants
     *   compute decreasing, check that it is >= 0
     *   S  [ break -> LoopBreak; continue -> LoopContinue ]
     *   goto LoopContinue
     * LoopContinue:  <-- all continues go here
     *   compute loop condition (which may have side effects creating other statements)
     *   assert loop invariants
     *   check that decreasing is less
     *   goto LoopEnd
     * LoopEnd:
     *   assume !(loop condition value) 
     *   goto LoopBreak
     * LoopBreak: <-- all breaks go here
     *   goto rest...
     */ // FIXME - allow for unrolling
    protected void visitDoLoopWithSpecs(JCDoWhileLoop that, List<JmlStatementLoop> loopSpecs) {
        loopStack.add(0,that);
        breakStack.add(0,that);
        int pos = that.pos;
        T bloopStart = currentBlock;
        T bloopContinue = newBlock(LOOPCONTINUE,pos);
        T bloopEnd = newBlock(LOOPEND,pos);
        T bloopBreak = newBlock(LOOPBREAK,pos);

        // Create an (unprocessed) block for everything that follows the
        // loop statement
        T brest = newBlockWithRest(LOOPAFTERDO,pos);// it gets all the followers of the current block
        T previousBreakBlock = breakBlocks.put(names.empty, bloopBreak);
        
        try {
            // do the loop body
            remainingStatements.add(that.body);
            processBlockStatements(true);

            follows(bloopStart,bloopContinue);
            follows(bloopContinue,bloopEnd); // FIXME - really?
            follows(bloopEnd,bloopBreak);
            follows(bloopBreak,brest);

            processBlock(bloopContinue);

        } finally {
            currentBlock = null;
            loopStack.remove(0);
            breakStack.remove(0);
            breakBlocks.put(names.empty,previousBreakBlock);
        }
        processBlock(bloopEnd);
        processBlock(bloopBreak);
        processBlock(brest);
    }

    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that)  { 
        currentBlock.statements.add(comment(that.pos(),"while..."));
        visitLoopWithSpecs(that, null, that.cond, null, that.body, null);
    }
    
    @Override
    public void visitWhileLoop(JCWhileLoop that) {
        currentBlock.statements.add(comment(that.pos(),"while..."));
        visitLoopWithSpecs(that, null, that.cond, null, that.body, null);
    }
    
    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        currentBlock.statements.add(comment(that.pos(),"for..."));
        visitLoopWithSpecs(that,that.init,that.cond,that.step,that.body,that.loopSpecs );
    }
    
    @Override
    public void visitForLoop(JCForLoop that) { 
        currentBlock.statements.add(comment(that.pos(),"for..."));
        visitLoopWithSpecs(that,that.init,that.cond,that.step,that.body,null );
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
            //processBlockStatements(false); // FIXME - this should not be needed now that visitLabelled is fixed
        }
    }
    
    // OK
    @Override
    public void visitLabelled(JCLabeledStatement that) {
        T nextBlock = newBlockWithRest(AFTERLABEL,that.pos);
        follows(currentBlock,nextBlock);
        breakBlocks.put(that.label, nextBlock);
        try {
            remainingStatements.add(that.getStatement());
            processBlockStatements(true);
        } finally {
            breakBlocks.remove(that.label);
        }
        processBlock(nextBlock);
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
    @Override public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) { shouldNotBeCalled(that); }
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
    @Override public void visitJmlStatementLoop(JmlStatementLoop that)          { shouldNotBeCalled(that); }
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
