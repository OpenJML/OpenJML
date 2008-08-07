package org.jmlspecs.openjml.esc;

import static com.sun.tools.javac.code.TypeTags.CLASS;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;


import org.jmlspecs.openjml.JmlInternalError;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;

import org.jmlspecs.annotations.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

import java.util.List;

import javax.tools.JavaFileObject;

/** This class converts a Java AST into basic block form (including DSA and
 * passification).
 * <P>
 * Basic block form contains only this subset of AST nodes:
 * <UL>
 * <LI> JCLiteral - numeric (all of them? FIXME), null, boolean, class (String?, character?)
 * <LI> JCIdent
 * <LI> JCParens
 * <LI> JCUnary
 * <LI> JCBinary
 * <LI> JmlBinary
 * <LI> JmlBBFieldAccess
 * <LI> JmlBBArrayAccess
 * <LI> JmlBBFieldAssign
 * <LI> JmlBBArrayAssign
 * <LI> JCInstanceOf
 * <LI> JCTypeCast
 * <LI> JCMethodInvocation - only pure methods within specifications
 * <LI> JmlMethodInvocation - old, typeof
 * <LI> JCConditional
 * <LI> JmlQuantifiedExpr
 * </UL>
 * 
 * @author David Cok
 */
public class BasicBlocker extends JmlTreeScanner {

    /** The context key for the basic blocker factory. */
    @NonNull 
    protected static final Context.Key<BasicBlocker> basicBlockerKey =
        new Context.Key<BasicBlocker>();

    /** Get the Factory instance for this context. 
     * 
     * @param context the compilation context
     * @return a (unique for the context) BasicBlocker instance
     */  // FIXME - do we really want to reuse a common instance?
    public static BasicBlocker instance(@NonNull Context context) {
        BasicBlocker instance = context.get(basicBlockerKey);
        if (instance == null)
            instance = new BasicBlocker(context);
        return instance;
    }

    /** The constructor, but use the instance() method to get a new instance,
     * in order to support extension.  This constructor should only be
     * invoked by a derived class constructor.
     * @param context the compilation context
     */
    protected BasicBlocker(@NonNull Context context) {
        this.context = context;
        this.factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
        this.names = Name.Table.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        
        trueLiteral = factory.Literal(TypeTags.BOOLEAN,1);
        trueLiteral.type = syms.booleanType;
        falseLiteral = factory.Literal(TypeTags.BOOLEAN,0);
        falseLiteral.type = syms.booleanType;
        nullLiteral = factory.at(0).Literal(TypeTags.BOT,0);
        nullLiteral.type = syms.objectType; // FIXME - object type?
        zeroLiteral = makeLiteral(0,0);
        zeroLiteral.type = syms.intType;
        
        allocIdent = newAuxIdent("$$alloc",syms.intType,0); // FIXME - magic string
        allocSym = (VarSymbol)allocIdent.sym;

        lengthIdent = factory.at(0).Ident(syms.lengthVar.name);
        lengthIdent.sym = syms.lengthVar;
        lengthIdent.type = syms.lengthVar.type;
        lengthSym = syms.lengthVar;

        currentThisId = newAuxIdent("this",syms.objectType,0); // FIXME - object type?
    }
    
    // THE FOLLOWING FIELDS ARE EXPECTED TO BE CONSTANT FOR THE LIFE OF THE OBJECT
    // They are either initialized in the constructor or initialized on first use
    
    /** The compilation context */
    @NonNull protected Context context;
    
    /** The specifications database for this compilation context, initialized in the constructor */
    @NonNull protected JmlSpecs specs;
    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull protected Symtab syms;
    
    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull protected Name.Table names;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull protected JmlTree.Maker factory;

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

    /** Symbol of a synthesized object field holding the allocation time of the object, initialized in the constructor */
    @NonNull protected VarSymbol allocSym;

    /** Identifier of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull protected JCIdent lengthIdent;

    /** Symbol of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull protected VarSymbol lengthSym;
    
    /** A fixed id for 'this' of the method being translated (see currentThisId
     * for the 'this' of called methods). */
    @NonNull protected JCIdent thisId;

    // These are constant but initialized on beginning the translation of a given
    // method
    
    /** A holding spot for the conditional return block of a program under normal termination */
    protected BasicBlock condReturnBlock;
    
    /** A holding spot for the return block of a program under normal termination */
    protected BasicBlock returnBlock;
    
    /** A holding spot for the conditional exception block (after try-finally) */
    protected BasicBlock condExceptionBlock;
    
    /** A holding spot for the last block of a program when there is an exception */
    protected BasicBlock exceptionBlock;
    
    // THE FOLLOWING FIELDS ARE USED IN THE COURSE OF DOING THE WORK OF CONVERTING
    // TO BASIC BLOCKS.  They are fields of the class because they need to be
    // shared across the visitor methods.
    
    /** visit methods that emit statements put them here */
    protected List<JCStatement> newstatements;  // FIXME - just use currentBlock.statements ???
    
    /** Place to put new definitions, such as the equalities defining auxiliary variables */
    protected List<JCExpression> newdefs;
    
    /** Place to put new background assertions, such as class predicates */
    protected List<JCExpression> background;
    
    /** List of blocks yet to be processed (from conventional program to basic program state) */
    protected java.util.List<BasicBlock> blocksToDo;
    
    /** List of blocks completed processing - in basic state */
    protected java.util.List<BasicBlock> blocksCompleted;
    
    /** A map of names to blocks */
    protected java.util.Map<String,BasicBlock> blockLookup;  // FIXME don't need this, I think
    
    /** A variable to hold the block currently being processed */
    protected BasicBlock currentBlock;
    
    /** The variable name that is currently the 'this' variable */
    protected JCIdent currentThisId;
    
    /** Ordered list of statements from the current block that are yet to be processed into basic program form */
    protected List<JCStatement> remainingStatements;
    
    /** The guarding condition so far in processing an expression */
    protected JCExpression condition;
    
    // FIXME - document the following
    
    protected JCExpression resultVar = null;
    protected JCIdent exceptionVar = null;
    protected JCIdent signalsVar = null; //Used when translating a signals clause
    protected JCIdent allocVar;
    //protected JCIdent stateVar;
    protected JCIdent terminationVar;  // 0=no termination requested; 1=return executed; 2 = exception happening
    
    protected JCIdent assumeCheckCountVar;
    protected int assumeCheckCount; 
    
    /** Holds the result of any of the visit methods that produce JCExpressions, since the visitor
     * template used here does not have a return value.  [We could have used the templated visitor,
     * but other methods do not need to return anything, we don't need the additional parameter,
     * and that visitor is complicated by the use of interfaces for the formal parameters.]
     */
    private JCExpression result;
    
    /** A mapping from BasicBlock to the sym->incarnation map giving the map that
     * FIXME !!!!.  FIXME - change this to a map to the new JCIdent
     */
    @NonNull protected Map<BasicBlock,Map<VarSymbol,Integer>> blockmaps = new HashMap<BasicBlock,Map<VarSymbol,Integer>>();
    
    /** A mapping from labels to the sym->incarnation map operative at the position
     * of the label.
     */
    @NonNull protected Map<Name,Map<VarSymbol,Integer>> labelmaps = new HashMap<Name,Map<VarSymbol,Integer>>();
    
    /** A mapping from labels to the sym->incarnation map operative at the position
     * of the label.
     */
    @NonNull protected Map<Name,JCTree> labelmapStatement = new HashMap<Name,JCTree>();
    
    /** The map from symbol to incarnation number in current use */
    @NonNull protected Map<VarSymbol,Integer> currentMap;
    
    /** The mapping of variables to incarnations to use when in the scope of an \old */
    @NonNull protected Map<VarSymbol,Integer> oldMap = new HashMap<VarSymbol,Integer>();

    /** The class info block when walking underneath a given class. */
    JmlClassInfo classInfo;
    
    // THE FOLLOWING ARE ALL FIXED STRINGS
    
    public static final @NonNull String blockPrefix = "$$BL$";
    
    /** Standard name for the variable that tracks termination */
    public static final @NonNull String TERMINATION_VAR = "$$terminationVar";
    
    /** Standard name for the block that starts the body */
    public static final @NonNull String BODY_BLOCK_NAME = "$$BL$bodyBegin";
    
    /** Standard name for the starting block of the program (just has the preconditions) */
    public static final @NonNull String START_BLOCK_NAME = "$$BL$Start";
    
    /** Standard name for the return block, whether or not a value is returned */
    public static final @NonNull String RETURN_BLOCK_NAME = "$$BL$return";
    
    /** Standard name for the postcondition block, whether or not a value is returned */
    public static final @NonNull String COND_RETURN_BLOCK_NAME = "$$BL$condReturn";
    
    /** Standard name for the exception block */
    public static final @NonNull String EXCEPTION_BLOCK_NAME = "$$BL$exception";
    
    /** Standard name for the conditional exception block */
    public static final @NonNull String COND_EXCEPTION_BLOCK_NAME = "$$BL$condException";
    
    // METHODS
    
    /** Should not need this when everything is implemented */
    protected void notImpl(JCTree that) {
        System.out.println("NOT IMPLEMENTED: BasicBlocker - " + that.getClass());
        result = trueLiteral;
    }
    
    /** Called by visit methods that should never be called. */
    protected void shouldNotBeCalled(JCTree that) {
        Log.instance(context).error("esc.internal.error","Did not expect to be calling a " + that.getClass() + " within BasicBlocker");
        throw new JmlInternalError();
    }
    
    // FIXME - document
    protected <T extends JCExpression> T copyInfo(T newnode, T oldnode) {
        newnode.type = oldnode.type;
        // FIXME - store end information?
        return newnode;
    }
    
    // FIXME - document
    protected <T extends JCIdent> T copyInfo(T newnode, T oldnode) {
        newnode.type = oldnode.type;
        newnode.sym = oldnode.sym;
        // FIXME - store end information?
        return newnode;
    }
    
    // THE FOLLOWING METHODS CREATE AST NODES.  Since type checking has
    // already been performed, we make sure that each node gets correct
    // type information assigned.  Also, we give it a reasonable position - 
    // something related to the source code location that occasioned this 
    // new node, even if it has no direct representation in the original source.
    
    /** Makes an int literal
     * @param value the value of the literal
     * @param pos the pseudo source code location of the node
     * @return the new literal
     */
    protected JCLiteral makeLiteral(int value, int pos) {
        JCLiteral lit = factory.at(pos).Literal(TypeTags.INT,value);
        lit.type = syms.intType;
        return lit;
    }
    
    protected JCLiteral makeTypeLiteral(Type type, int pos) {
        JCLiteral lit = factory.at(pos).Literal(TypeTags.CLASS,type);
        lit.type = syms.classType;
        return lit;
    }
    
    /** Makes an boolean literal
     * @param value the value of the literal
     * @param pos the pseudo source code location of the node
     * @return the new literal
     */
    protected JCLiteral makeLiteral(boolean value, int pos) {
        JCLiteral lit = factory.at(pos).Literal(TypeTags.BOOLEAN,value?1:0);
        lit.type = syms.booleanType;
        return lit;
    }
    
    /** Makes an identifier for a symbol, as in the AST prior to any translation
     * by BasicBlocker.
     * @param sym the variable to put in the AST
     * @param pos the pseudo-position at which to place it
     * @return a JCIdent node
     */
    protected JCIdent makeIdent(VarSymbol sym, int pos) {
        JCIdent id = factory.at(pos).Ident(sym);
        id.type = sym.type;
        return id;
    }
    
    /** Makes a Jml binary operator node (with boolean result)
     * @param op the binary operator (producing a boolean result), e.g. JmlToken.IMPLIES
     * @param lhs the left-hand expression
     * @param rhs the right-hand expression
     * @param pos the pseudo source code location of the node
     * @return the new node
     */
    protected JmlBinary makeJmlBinary(JmlToken op, JCExpression lhs, JCExpression rhs, int pos) {
        JmlBinary e = factory.at(pos).JmlBinary(op,lhs,rhs);
        e.type = syms.booleanType;
        return e;
    }
    
    /** Makes a Java binary operator node (with boolean result)
     * @param op the binary operator (producing a boolean result), e.g. JCTree.EQ
     * @param lhs the left-hand expression
     * @param rhs the right-hand expression
     * @param pos the pseudo source code location of the node
     * @return the new node
     */
    protected JCBinary makeBinary(int op, JCExpression lhs, JCExpression rhs, int pos) {
        JCBinary e = factory.at(pos).Binary(op,lhs,rhs);
        switch (op) {
            case JCTree.EQ:
            case JCTree.NE:
            case JCTree.GT:
            case JCTree.GE:
            case JCTree.LT:
            case JCTree.LE:
            case JCTree.OR:
            case JCTree.AND:
                e.type = syms.booleanType;
                break;

            case JCTree.PLUS:
            case JCTree.MINUS:
            case JCTree.MUL:
            case JCTree.DIV:
            case JCTree.MOD:
                if (lhs.type == syms.doubleType || rhs.type == syms.doubleType)
                    e.type = syms.doubleType;
                else if (lhs.type == syms.floatType || rhs.type == syms.floatType)
                    e.type = syms.floatType;
                else if (lhs.type == syms.longType || rhs.type == syms.longType)
                    e.type = syms.longType;
                else e.type = syms.intType;
                break;

            case JCTree.BITOR:
            case JCTree.BITAND:
            case JCTree.BITXOR:
            case JCTree.SR:
            case JCTree.USR:
            case JCTree.SL:
                // FIXME - check that this is correct
                if (lhs.type == syms.longType || rhs.type == syms.longType)
                    e.type = syms.longType;
                else e.type = syms.intType;
                break;
                
            default:
                Log.instance(context).error("esc.not.implemented","Unknown binary operator in BasicBlocker.makeBinary "+op);
        }
        return e;
    }
    
    /** Makes a Java unary operator node
     * @param op the unary operator, e.g. JCTree.NOT, JCTree.NEG, JCTree.COMPL, ...
     * @param lhs the left-hand expression
     * @param rhs the right-hand expression
     * @param pos the pseudo source code location of the node
     * @return the new node
     */
    protected JCExpression makeUnary(int op, JCExpression expr, int pos) {
        JCUnary e = factory.at(pos).Unary(op,expr);
        if (op == JCTree.NOT) e.type = syms.booleanType;
        else if (expr.type == syms.doubleType) e.type = expr.type;
        else if (expr.type == syms.floatType) e.type = expr.type;
        else if (expr.type == syms.longType) e.type = expr.type;
        else e.type = syms.intType;  // NEG POS COMPL PREINC PREDEC POSTINC POSTDEC
        return e;
    }
    
    /** Makes a new variable declaration for helper variables in the AST translation;
     * a new VarSymbol is also created in conjunction with the variable
     * @param name the variable name, as it might be used in program text
     * @param type the variable type
     * @param init the initialization expression as it would appear in a declaration
     * @param pos the pseudo source code location for the new node
     * @returns a new JCVariableDecl node
     */
    protected JCVariableDecl makeVariableDecl(Name name, Type type, JCExpression init, int pos) {
        VarSymbol vsym = new VarSymbol(0, name, type, null);
        vsym.pos = pos;
        JCVariableDecl decl = factory.at(pos).VarDef(vsym,init);
        return decl;
    }
    
    /** This creates an (unprocessed) assignment and adds it to the given block.
     * This is appropriate for blocks that are being added to the todo list.
     * @param b block to which to add the new statement
     * @param pos the source position to use for the new expressions
     * @param lhs target of the assignment
     * @param rhs value of the assignment
     */
    protected void addAssignmentStatement(BasicBlock b, int pos, JCExpression lhs, JCExpression rhs) {
        JCAssign asg = factory.at(pos).Assign(lhs,rhs);
        asg.type = lhs.type;
        JCExpressionStatement exec = factory.at(pos).Exec(asg);
        //exec.type = ??? FIXME
        b.statements.add(exec);        
    }
    
    /** Creates an encoded name from a symbol and an incarnation position of the form
     *    <symbol name>$<declaration position>$<use position>
     * If the symbol has a negative declaration position, that value is not included in the string
     * @param sym the symbol being given a logical name
     * @param incarnationPosition the incarnation position for which to give a new name
     * @return the new name
     */
    protected Name encodedName(VarSymbol sym, int incarnationPosition) {
        return names.fromString(sym.getQualifiedName() + (sym.pos < 0 ? "$" : ("$" + sym.pos + "$")) + incarnationPosition);
    }
    
    /** Creates an encoded name from a symbol and an incarnation position of the form
     *    <symbol name>$<declaration position>$<use position>
     * If the symbol has a negative declaration position, that value is not included in the string
     * @param sym the symbol being given a logical name
     * @param incarnationPosition the incarnation position for which to give a new name
     * @return the new name
     */
    protected Name encodedName(MethodSymbol sym, int declpos, int incarnationPosition) {
        return names.fromString(sym.getQualifiedName() + (declpos < 0 ? "$" : ("$" + declpos + "$")) + incarnationPosition);
    }
    
    /** Creates an identifier nodes for a new incarnation of the variable, that is,
     * when the variable is assigned to.
     * @param id the old identifier, giving the root name, symbol and type
     * @param incarnationPosition the position (and incarnation number) of the new variable
     * @return the new identifier
     */
    protected JCIdent newIdentIncarnation(JCIdent id, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedName((VarSymbol)id.sym,incarnationPosition));
        copyInfo(n,id);
        currentMap.put((VarSymbol)id.sym,incarnationPosition);
        return n;
    }
    
    // FIXME - document
    protected JCIdent newArrayIncarnation(Type componentType, int usePosition) {
        JCIdent id = getArrayIdent(componentType);
        currentMap.put((VarSymbol)id.sym,Integer.valueOf(usePosition));
        id = newIdentUse((VarSymbol)id.sym,usePosition,usePosition);
        return id;
    }
    
    /** Creates an identifier node for a use of a variable at a given source code
     * position and with a given incarnation position.
     * @param sym the underlying symbol (which gives the declaration location)
     * @param useposition the source position of its use
     * @param incarnation the position of the last assignment of this variable
     * @return
     */ // FIXME - not sure anyone should use this - use newIdentIncarnation instead?
    protected JCIdent newIdentUse(VarSymbol sym, int useposition, int incarnation) {
        JCIdent n = factory.at(useposition).Ident(encodedName(sym,incarnation));
        n.sym = sym;
        n.type = sym.type;
        return n;
    }
    
    /** Creates an identifier node for a use of a variable at a given source code
     * position; the current incarnation value is used
     * @param sym the underlying symbol (which gives the declaration location)
     * @param useposition the source position of its use
     * @return
     */
    protected JCIdent newIdentUse(VarSymbol sym, int useposition) {
        Integer ipos = currentMap.get(sym);
        int pos = ipos == null? 0 : ipos;
        return newIdentUse(sym,useposition,pos);
    }
    
    /** Creates a newly incarnated variable corresponding to the given declaration.
     * The incarnation number will be the position of the declaration for some
     * declarations, but not, for example, for a formal argument of a method call -
     * then it would be the position of the actual parameter expression.
     * @param id the original declaration
     * @param incarnation the incarnation number to use
     * @return the new variable node
     */
    protected JCIdent newIdentIncarnation(JCVariableDecl id, int incarnation) {
        JCIdent n = factory.at(incarnation).Ident(encodedName((VarSymbol)id.sym,incarnation));
        n.sym = id.sym;
        n.type = id.type;
        // FIXME - end information?
        currentMap.put((VarSymbol)id.sym,incarnation);
        return n;
    }
    
    /** Creates a new variable representing an auxiliary variable, for use as a
     * logical variable in the basic program; this is a one-time
     * defined variable - it may not be assigned to again (and thus has no
     * future incarnations)  FIXME - is that true for all uses?
     * @param name the full name of the variable, including any position encoding
     * @param type the type of the variable
     * @param pos the position to assign as its pseudo-location of use
     * @return
     */
    protected JCIdent newAuxIdent(@NonNull String name, @NonNull Type type, int pos) {
        JCIdent id = factory.at(pos).Ident(names.fromString(name));
        id.sym = new VarSymbol(0,id.name,type,null);
        id.type = type;
        return id;
    }
    
    /** Start the processing of the given block
     * 
     * @param b the block for which to initialize processing 
     */
    protected void startBlock(@NonNull BasicBlock b) {
        if (b.id.toString().endsWith("$finally")) tryStack.remove(0);
        currentBlock = b;
        remainingStatements = currentBlock.statements;
        newstatements = currentBlock.statements = new ArrayList<JCStatement>();
        currentMap = initMap(currentBlock);
    }
    
    /** Files away a completed block, adding it to the blocksCompleted list and
     * to the lookup Map.
     * @param b the completed block
     */
    protected void completed(@NonNull BasicBlock b) {
        if (b == null) return;
        blocksCompleted.add(b);
        blockmaps.put(b,currentMap);
        blockLookup.put(b.id.name.toString(),b);
    }
    
    /** Updates the data structures to indicate that the after block follows the
     * before block
     * @param before block that precedes after
     * @param after block that follows before
     */
    protected void follows(@NonNull BasicBlock before, @NonNull BasicBlock after) {
        before.succeeding.add(after);
        after.preceding.add(before);
    }
    
    /** Inserts the after block after the before block, replacing anything that
     * used to follow the before block
     * @param before
     * @param after
     */
    protected void replaceFollows(@NonNull BasicBlock before, @NonNull BasicBlock after) {
        for (BasicBlock b: before.succeeding) {
            b.preceding.remove(before);
        }
        before.succeeding.clear();
        follows(before,after);
    }
    
    /** This utility method converts an expression from AST to BasicProgram
     * form; the method may have side-effects
     * in creating new statements (in newstatements).  The returned expression
     * node is expected to have position, type and symbol information set.
     * @param expr the expression to convert
     * @return the converted expression
     */
    protected JCExpression trExpr(JCExpression expr) {
        if (expr == null) return null;
        expr.accept(this);
        return result;
    }
    
    /** true when translating a spec expression, which has particular effect on
     * the translation of method calls */
    protected boolean inSpecExpression;
    
    /** This utility method converts an expression from AST to BasicProgram
     * form; the argument is expected to be a spec-expression;
     * the method may have side-effects
     * in creating new statements (in newstatements).  The returned expression
     * node is expected to have position, type and symbol information set.
     * @param expr the expression to convert
     * @return the converted expression
     */
    protected JCExpression trSpecExpr(JCExpression expr) {
        if (expr == null) return null;
        if (inSpecExpression) {
            return trExpr(expr);
        } else {
            boolean prevInSpecExpression = inSpecExpression;
            inSpecExpression = true;
            try {
                JCExpression result = trExpr(expr);
                return result;
            } finally {
                inSpecExpression = prevInSpecExpression;
            }
        }
    }
    
    protected JCExpression trJavaExpr(JCExpression expr) {
        return trExpr(expr);
    }    
    
    /** Static entry point that converts an AST (the block of a method) into basic block form
     * 
     * @param context the compilation context
     * @param tree the block of a method
     * @param denestedSpecs the specs of the method
     * @param classInfo the info about the enclosing class
     * @return the resulting BasicProgram
     */
    protected static @NonNull BasicProgram convertToBasicBlocks(@NonNull Context context, 
            @NonNull JCMethodDecl tree, JmlMethodSpecs denestedSpecs, JCClassDecl classDecl) {
        BasicBlocker blocker = instance(context);
        return blocker.convertMethodBody(tree,denestedSpecs,classDecl);
    }
    
    /** Returns a new, empty BasicBlock
     * 
     * @param name the name to give the block
     * @param pos a position to associate with the JCIdent for the block
     * @return the new block
     */
    protected @NonNull BasicBlock newBlock(@NonNull String name, int pos) {
        JCIdent id = newAuxIdent(name,syms.booleanType,pos);
        BasicBlock bb = new BasicBlock(id);
        blockLookup.put(id.name.toString(),bb);
        return bb;
    }
    
    /** Returns a new, empty BasicBlock, but the new block takes all of the 
     * followers of the given block; the previuosBlock will then have no
     * followers.
     * 
     * @param name the name to give the block
     * @param pos a position to associate with the JCIdent for the block
     * @param previousBlock the block that is giving up its followers
     * @return the new block
     */
    protected @NonNull BasicBlock newBlock(@NonNull String name, int pos, @NonNull BasicBlock previousBlock) {
        JCIdent id = newAuxIdent(name,syms.booleanType,pos);
        return new BasicBlock(id,previousBlock);
    }
    
    // characteristics of the method under study
    boolean isConstructor;
    boolean isStatic;
    boolean isHelper;

    /** Converts the top-level block of a method into the elements of a BasicProgram 
     * 
     * @param tree the method to convert to to a BasicProgram
     * @param denestedSpecs the specs of the method
     * @param classDecl the declaration of the containing class
     * @return the completed BasicProgram
     */
    protected @NonNull BasicProgram convertMethodBody(@NonNull JCMethodDecl tree, 
            JmlMethodSpecs denestedSpecs, @NonNull JCClassDecl classDecl) {
        isConstructor = tree.sym.isConstructor();  // FIXME - careful if there is nesting???
        isStatic = tree.sym.isStatic();
        isHelper = isHelper(tree.sym);
        typesAdded = new HashSet<TypeSymbol>();
        int pos = tree.pos;
        inSpecExpression = false;
        JmlClassInfo classInfo = getClassInfo(classDecl.sym);
        this.classInfo = classInfo;
        newdefs = new LinkedList<JCExpression>();
        background = new LinkedList<JCExpression>();
        blocksToDo = new LinkedList<BasicBlock>();
        blocksCompleted = new ArrayList<BasicBlock>();
        blockLookup = new java.util.HashMap<String,BasicBlock>();
        thisId = newAuxIdent("this$",syms.objectType,pos); // FIXME - object type?
        currentThisId = thisId;
        if (tree.getReturnType() != null) {
            resultVar = newAuxIdent("$$result",tree.getReturnType().type,0); 
        }
        terminationVar = newAuxIdent(TERMINATION_VAR,syms.intType,0);
        exceptionVar = newAuxIdent("$$exception",syms.exceptionType,0);
        allocVar = newAuxIdent("$$alloc",syms.intType,0); // FIXME - would this be better as its own uninterpreted type?
        //stateVar = newAuxIdent("$$state",syms.intType,0); // FIXME - would this be better as its own uninterpreted type?
        assumeCheckCountVar = newAuxIdent("$$assumeCheckCount",syms.intType,0);
        assumeCheckCount = 0;
        
        JCBlock block = tree.getBody();
        
        // Define the conditional return block
        condReturnBlock = newBlock(COND_RETURN_BLOCK_NAME,pos);
        JCExpression e = makeBinary(JCTree.GT,terminationVar,zeroLiteral,pos);
        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);  // FIXME pos
        condReturnBlock.statements.add(asm);
        
        // Define the return block
        returnBlock = newBlock(RETURN_BLOCK_NAME,pos);
        follows(condReturnBlock,returnBlock);
        
        // Define the conditional exception block
        condExceptionBlock = newBlock(COND_EXCEPTION_BLOCK_NAME,pos);
        e = makeBinary(JCTree.LT,terminationVar,zeroLiteral,pos);
        asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);// FIXME pos
        condExceptionBlock.statements.add(asm);
        
        // Define the exception block
        exceptionBlock = newBlock(EXCEPTION_BLOCK_NAME,pos);
        follows(condExceptionBlock,exceptionBlock);
        
        // Define the start block
        BasicBlock startBlock = newBlock(START_BLOCK_NAME,pos);
        
        // Define the body block
        // Put all the program statements in the Body Block
        BasicBlock bodyBlock = newBlock(BODY_BLOCK_NAME,tree.body.pos);
        // First a couple key statements
        e = makeBinary(JCTree.EQ,terminationVar,zeroLiteral,tree.body.pos);
        asm = factory.at(tree.body.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);
        bodyBlock.statements.add(asm);
        e = makeBinary(JCTree.EQ,exceptionVar,nullLiteral,tree.body.pos);
        asm = factory.at(tree.body.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);
        bodyBlock.statements.add(asm);
        // Then the program
        bodyBlock.statements.addAll(block.getStatements());
        follows(startBlock,bodyBlock);
        follows(bodyBlock,returnBlock); // implicit, unconditional return
        
        // Put the blocks in the todo list
        blocksToDo.add(0,exceptionBlock);
        blocksToDo.add(0,condExceptionBlock);
        blocksToDo.add(0,returnBlock);
        blocksToDo.add(0,condReturnBlock);
        blocksToDo.add(0,bodyBlock);
        condition = trueLiteral;
        
        // Handle the start block a little specially
        // It does not have any statements in it
        startBlock(startBlock);
        if (!isStatic) {
            e = makeBinary(JCTree.NE,thisId,nullLiteral,tree.body.pos);
            asm = factory.at(tree.body.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);
            startBlock.statements.add(asm);
        }
        addPreconditions(startBlock,tree,denestedSpecs);
        completed(currentBlock);

        // Pick a block to do and process it
        while (!blocksToDo.isEmpty()) {
            processBlock(blocksToDo.remove(0));
        }
        addPostconditions(returnBlock,tree,denestedSpecs);
        addExPostconditions(exceptionBlock,tree,denestedSpecs);
        
        // Make the BasicProgram
        BasicProgram program = new BasicProgram();
        program.startId = startBlock.id;
        program.blocks.addAll(blocksCompleted);
        program.definitions = newdefs;
        program.background = background;
        program.assumeCheckVar = assumeCheckCountVar;
        
        // Find all the variables so they can be declared if necessary
        Set<JCIdent> vars = new HashSet<JCIdent>();
        for (BasicBlock bb : blocksCompleted) {
            VarFinder.findVars(bb.statements,vars);
        }
        for (JCExpression ex : newdefs) {
            VarFinder.findVars(ex,vars);
        }
        for (JCExpression ex : background) {
            VarFinder.findVars(ex,vars);
        }
        Collection<JCIdent> decls = program.declarations;
        Set<Name> varnames = new HashSet<Name>();
        for (JCIdent id: vars) {
            if (varnames.add(id.getName())) decls.add(id);
        }
        return program;
    }
    
    /** Does the conversion of a block with Java statements into basic program
     * form, possibly creating new blocks on the todo list
     * @param block the block to process
     */
    protected void processBlock(@NonNull BasicBlock block) {
        startBlock(block);
        processBlockStatements(true);
    }
    
    /** Iterates through the statements on the remainingStatements list, processing them
     * 
     * @param complete call 'completed' on the currentBlock, if true
     */
    protected void processBlockStatements(boolean complete) {
        while (!remainingStatements.isEmpty()) {
            JCStatement s = remainingStatements.remove(0);
            condition = trueLiteral;
            s.accept(this);
        }
        if (complete) completed(currentBlock);
    }
    
    /** A cache for the symbol */
    private ClassSymbol helperAnnotationSymbol = null;
    /** Returns true if the given symbol has a helper annotation
     * 
     * @param symbol the symbol to check
     * @return true if there is a helper annotation
     */
    protected boolean isHelper(@NonNull Symbol symbol) {
        if (helperAnnotationSymbol == null) {
            helperAnnotationSymbol = ClassReader.instance(context).
                enterClass(names.fromString("org.jmlspecs.annotations.Helper"));
        }
        return symbol.attribute(helperAnnotationSymbol)!=null;
    }  // FIXME - isn't there a utility method somewhere else that does this

    
    /** Inserts assumptions corresponding to the preconditions into the given block.
     * Uses classInfo to get the class-level preconditions.
     * 
     * @param b      the block into which to add the assumptions
     * @param tree   the method being translated
     * @param denestedSpecs  the denested specs for that method
     */
    protected void addPreconditions(@NonNull BasicBlock b, @NonNull JCMethodDecl tree, @NonNull JmlMethodSpecs denestedSpecs) {
        
        addClassPreconditions(classInfo,b);

        JCExpression expr = falseLiteral;
        MethodSymbol msym = tree.sym;
        JmlMethodInfo mi = getMethodInfo(msym);
        if (mi.requiresPredicates.size() == 0) expr = trueLiteral;
        else for (JCExpression pre: mi.requiresPredicates) {
            pre = trSpecExpr(pre);
            if (expr == falseLiteral) expr = pre;
            else {
                expr = makeBinary(JCTree.OR,expr,pre,expr.pos);
            }
        }
        expr.pos = expr.getStartPosition();
        
        addClassPredicate(classInfo.csym.type);
        
        Iterator<JCVariableDecl> baseParams = tree.params.iterator();
        while (baseParams.hasNext()) {
            JCVariableDecl base = baseParams.next();
            if (!base.type.isPrimitive()) {
                // for each reference parameter p: assume (p == null) || ( \typeof(p) <: <statictype> )
                // also add the class predicate for the argument type
                addClassPredicate(base.type);
                JCIdent baseId = newIdentUse(base.sym,base.pos);
                JCExpression t = factory.at(base.pos).JmlMethodInvocation(JmlToken.BSTYPEOF,com.sun.tools.javac.util.List.<JCExpression>of(baseId));
                t.type = syms.classType;
                JCExpression lit = makeTypeLiteral(base.type,base.pos);
                JCExpression eq = makeJmlBinary(JmlToken.SUBTYPE_OF,t,lit,base.pos);
                eq = makeBinary(JCTree.OR,makeBinary(JCTree.EQ,baseId,nullLiteral,base.pos),eq,baseId.pos);
                addAssume(Label.SYN,eq,b.statements,false);
            }
        }
            // Need definedness checks?  FIXME
        if (!isConstructor && !isStatic) {
            while ((msym=getOverrided(msym)) != null) {
                expr = addMethodPreconditions(b,msym,tree,tree.pos,expr);
            }
        }
        
        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.PRECONDITION,expr);// FIXME pos
        b.statements.add(asm);

    }
    
    protected JCExpression addMethodPreconditions(@NonNull BasicBlock b, @NonNull MethodSymbol msym, @NonNull JCMethodDecl baseMethod, int pos, JCExpression expr) {

        // FIXME - argument names???  Will the pre and post names be different?
        JmlMethodInfo mi = getMethodInfo(msym);
        if (msym != baseMethod.sym) {
            addParameterMappings(baseMethod,mi.decl,pos,b);
        }

        for (JCExpression pre: mi.requiresPredicates) {
            int p = expr.pos == 0 ? pre.getStartPosition() : expr.pos;
            pre = trSpecExpr(pre);
            if (expr == null) expr = pre;
            else expr = makeBinary(JCTree.OR,expr,pre,p);
        }
        return expr;
    }
    
    protected void addClassPreconditions(JmlClassInfo cInfo, BasicBlock b) {
        if (cInfo.superclassInfo != null) {
            addClassPreconditions(cInfo.superclassInfo,b);
        }
        JmlClassInfo prevClassInfo = classInfo;
        classInfo = cInfo; // Set the global value so trExpr calls have access to it
        try {
            // The axioms should perhaps be part of a class predicate?  // FIXME
            for (JmlTypeClauseExpr ax : cInfo.axioms) {
                JCExpression e = ax.expression;
                e = trSpecExpr(e);
                JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.INVARIANT,e);// FIXME pos
                b.statements.add(asm);
            }

            if (!isConstructor && !isHelper) {
                for (JmlTypeClauseExpr inv : cInfo.staticinvariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e);
                    JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.INVARIANT,e);// FIXME pos
                    b.statements.add(asm);
                }
                if (!isStatic) {
                    for (JmlTypeClauseExpr inv : cInfo.invariants) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e);
                        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.INVARIANT,e);// FIXME pos
                        b.statements.add(asm);
                    }
                }
            }
        } finally {
            classInfo = prevClassInfo;
        }
    }
    
    boolean useAuxDefinitions = true;

    protected void addAssert(Label label, JCExpression that, int declpos, List<JCStatement> statements, int usepos) {
        JmlStatementExpr st;
        if (useAuxDefinitions) {
            String n = "assert$" + usepos + "$" + declpos + "$" + label;
            JCExpression id = newAuxIdent(n,syms.booleanType,that.getStartPosition());
            JCExpression expr = makeBinary(JCTree.EQ,id,that,that.pos);
                    // FIXME - start and end?
            newdefs.add(expr);
            that = id;
        }
        st = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSERT,label,that);
        st.optionalExpression = null;
        st.type = null; // FIXME - is this right?
        // FIXME - what about source and line?
        statements.add(st);
        //return that;
    }
    
    protected void addAssume(Label label, JCExpression that, List<JCStatement> statements, boolean track) {
        addAssume(that.pos,label,that,statements,track);
    }
    
    protected void addAssume(int pos, Label label, JCExpression that, List<JCStatement> statements, boolean track) {
        if (track) {
//            int pos = now.pos;
//            String n = "assumeCheck$" + that.pos + "$" + that.label.toString();
//            JCExpression count = makeLiteral(that.pos,that.pos);
//            JCExpression e = makeBinary(JCTree.NE,assumeCheckCountVar,count,pos);
//            JCExpression id = newAuxIdent(n,syms.booleanType,e.pos);
//            e = makeJmlBinary(JmlToken.EQUIVALENCE,id,e,pos);
//            JmlStatementExpr st = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSUME_CHECK,e);
//            newstatements.add(st);
//            // an assert without tracking
//            st = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSERT,Label.ASSUME_CHECK,id);
//            // FIXME - start and end?
//            st.optionalExpression = null;
//            st.type = null; // FIXME - is this right?
//            // FIXME - what about source and line?
//            newstatements.add(st);
            
        }
        that.type = syms.booleanType;
        JCStatement st = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,label,that);
        // st.type = ??? FIXME
        statements.add(st);
    }
    
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
    
    private Map<String,JCIdent> arrayIdMap = new HashMap<String,JCIdent>();
    
    protected JCIdent getArrayIdent(Type componentType) {
        String s = "arrays$" + encodeType(componentType);
        JCIdent id = arrayIdMap.get(s);
        if (id == null) {
            id = factory.Ident(names.fromString(s));
            id.pos = 0;
            id.type = componentType;
            id.sym = new VarSymbol(0,id.name,id.type,null);
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
     * @returns the variable corresponding the the given String argument
     */
    // FIXME - modifies the content of currentBlock.statements
    protected @NonNull JCIdent addAuxVariable(@NonNull String name, @NonNull Type type, @NonNull JCExpression expr, boolean makeDefinition) {
        JCExpression newexpr = trExpr(expr);
        JCIdent vd = newAuxIdent(name,type,newexpr.getStartPosition());
        // FIXME - use a definition?
        if (makeDefinition) {
            newdefs.add(makeBinary(JCTree.EQ,vd,newexpr,newexpr.pos));
        } else {
            JmlTree.JmlStatementExpr asm = factory.at(expr.getStartPosition()).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,makeBinary(JCTree.EQ,vd,newexpr,newexpr.pos));
            currentBlock.statements.add(asm);
        }
        return vd;
    }

    protected void addPostconditions(BasicBlock b, JCMethodDecl decl, JmlMethodSpecs denestedSpecs) {
        currentBlock = b;
        currentMap = blockmaps.get(b);

        addMethodPostconditions(decl.sym,b,decl.pos,decl);

        if (!isConstructor && !isStatic) {
            MethodSymbol msym = decl.sym;
            while ((msym = getOverrided(msym)) != null) {
                addMethodPostconditions(msym,b,decl.pos,decl);
            }
        }
        
        // FIXME - reevaluate the last argument: this is the location that the error message
        // indicates as where the assertion failed - it could be the return statement, or the
        // ending close paren.  But the only information we have at this point is the preferred
        // location of the method declaration (unless we could get the ending information).
        addClassPostconditions(classInfo,b,decl.pos);

        // FIXME - this is wrong - we assume th OR of everything
    }
    
    protected void addMethodPostconditions(MethodSymbol msym, BasicBlock b, int pos, JCMethodDecl baseMethod) {
        List<JCStatement> statements = b.statements;

        // FIXME - argument names???  Will the pre and post names be different?
        JmlMethodInfo mi = getMethodInfo(msym);
        if (msym != baseMethod.sym) {
            addParameterMappings(baseMethod,mi.decl,pos,b);
        }
        for (JCExpression post: mi.ensuresPredicates) {
            addAssert(Label.POSTCONDITION,trSpecExpr(post),post.getStartPosition(),statements,pos);
        }
    }
    
    protected void addExPostconditions(BasicBlock b, JCMethodDecl decl, JmlMethodSpecs denestedSpecs) {
        currentBlock = b;
        currentMap = blockmaps.get(b);

        addMethodExPostconditions(decl.sym,b,decl.pos,decl);

        if (!isConstructor && !isStatic) {
            MethodSymbol msym = decl.sym;
            while ((msym = getOverrided(msym)) != null) {
                addMethodExPostconditions(msym,b,decl.pos,decl);
            }
        }
    }
    
    protected void addMethodExPostconditions(MethodSymbol msym, BasicBlock b, int pos, JCMethodDecl baseMethod) {
        List<JCStatement> statements = b.statements;

        // FIXME - argument names???  Will the pre and post names be different?
        JmlMethodInfo mi = getMethodInfo(msym);
        if (msym != baseMethod.sym) {
            addParameterMappings(baseMethod,mi.decl,pos,b);
        }
        // signals/exsures predicates
        for (JCExpression post: mi.exPredicates) {
            JCExpression ex = ((JmlBinary)post).lhs;
            ex = ((JmlBinary)ex).lhs;
            ex = ((JmlMethodInvocation)ex).args.get(0);
            signalsVar = (JCIdent)ex;
            addAssert(Label.SIGNALS,trSpecExpr(post),post.getStartPosition(),statements,pos);
            signalsVar = null;
        }
        // signals_only predicates
        for (JCExpression post: mi.sigPredicates) {
            addAssert(Label.SIGNALS,trSpecExpr(post),post.getStartPosition(),statements,pos);
        }
    }
    
    protected void addClassPostconditions(JmlClassInfo cInfo, BasicBlock b, int usepos) {
        if (cInfo.superclassInfo != null) {
            addClassPostconditions(cInfo.superclassInfo,b,usepos);
        }

        currentBlock = b;
        currentMap = blockmaps.get(b);
        List<JCStatement> statements = b.statements;
        if (!isHelper) {
            for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                JCExpression e = inv.expression;
                e = trSpecExpr(e);
                addAssert(Label.INVARIANT,e,inv.expression.getStartPosition(),statements,usepos);
            }
            if (!isStatic) {
                for (JmlTypeClauseExpr inv : classInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e);
                    addAssert(Label.INVARIANT,e,inv.expression.getStartPosition(),statements,usepos);
                }
            }
            if (!isConstructor) {
                for (JmlTypeClauseConstraint inv : classInfo.staticconstraints) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e);
                    addAssert(Label.CONSTRAINT,e,inv.expression.getStartPosition(),statements,usepos);
                }
                if (!isStatic) {
                    for (JmlTypeClauseConstraint inv : classInfo.constraints) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e);
                        addAssert(Label.CONSTRAINT,e,inv.expression.getStartPosition(),statements,usepos);
                    }
                }
            } else {
                for (JmlTypeClauseExpr inv : classInfo.initiallys) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e);
                    addAssert(Label.INITIALLY,e,inv.expression.getStartPosition(),statements,usepos);
                }
            }
        }
    }
    
    Set<TypeSymbol> typesAdded = new HashSet<TypeSymbol>();
    protected void addClassPredicate(Type type) {
        if (typesAdded.contains(type.tsym)) return;
        typesAdded.add(type.tsym);
        TypeSymbol t = ((ClassSymbol)type.tsym).getSuperclass().tsym;
        if (t != null && t.type.tag != TypeTags.NONE) {
            addClassPredicate(t.type);
            JCLiteral lit1 = makeTypeLiteral(type,0);
            JCLiteral lit2 = makeTypeLiteral(t.type,0);
            JCExpression e = makeJmlBinary(JmlToken.SUBTYPE_OF,lit1,lit2,0);
            background.add(e);
        }
    }
    
    /** This method returns the method symbol of the method in some superclass
     * that the argument overrides.  It does not check interfaces.
     * @param msym the overriding method
     * @return the overridden method, or null if none
     */
    @Nullable
    protected MethodSymbol getOverrided(@NonNull MethodSymbol msym) {
        Types types = Types.instance(context);
        for (Type t = types.supertype(msym.owner.type); t.tag == CLASS;
                            t = types.supertype(t)) {
            TypeSymbol c = t.tsym;
            Scope.Entry e = c.members().lookup(msym.name);
            while (e.scope != null) {
                if (msym.overrides(e.sym, (TypeSymbol)msym.owner, types, false)) {
                    return (MethodSymbol)e.sym;
                }
                e = e.next();
            }
        }
        return null;
    }
    
    /** Adds assumptions to equate parameters of a overridden method with those 
     * of an overriding method.
     * @param baseMethod the overriding method
     * @param otherMethod the overridden method
     * @param pos a position to use in creating new variable locations
     * @param b the block into which to add the assumptions
     */
    protected void addParameterMappings(@NonNull JCMethodDecl baseMethod, @NonNull JCMethodDecl otherMethod, int pos, BasicBlock b) {
        Iterator<JCVariableDecl> baseParams = baseMethod.params.iterator();
        Iterator<JCVariableDecl> newParams = otherMethod.params.iterator();
        while (baseParams.hasNext()) {
            JCVariableDecl base = baseParams.next();
            JCVariableDecl newp = newParams.next();
            JCIdent baseId = newIdentUse(base.sym,pos);
            JCIdent newId = newIdentIncarnation(newp,0);
            JCExpression eq = makeBinary(JCTree.EQ,newId,baseId,pos);
            addAssume(Label.SYN,eq,b.statements,false);
        }
    }
    
    protected Map<VarSymbol,Integer> initMap(BasicBlock block) {
        Map<VarSymbol,Integer> newMap = new HashMap<VarSymbol,Integer>();
        if (block.preceding.size() == 0) {
            // keep the empty one
        } else if (block.preceding.size() == 1) {
            newMap.putAll(blockmaps.get(block.preceding.get(0))); 
        } else {
            List<Map<VarSymbol,Integer>> all = new LinkedList<Map<VarSymbol,Integer>>();
            Map<VarSymbol,Integer> combined = new HashMap<VarSymbol,Integer>();
            for (BasicBlock b : block.preceding) {
                Map<VarSymbol,Integer> m = blockmaps.get(b);
                all.add(m);
                combined.putAll(m);
            }
            for (VarSymbol sym: combined.keySet()) {
                int max = -1;
                for (Map<VarSymbol,Integer> m: all) {
                    Integer i = m.get(sym);
                    if (i != null && i > max) max = i;
                }
                for (BasicBlock b: block.preceding) {
                    Map<VarSymbol,Integer> m = blockmaps.get(b);
                    Integer i = m.get(sym);
                    if (i == null) i = 0;
                    if (i < max) {
                        // No position information for these nodes
                        // Type information put in, though I don't know that we need it
                        JCIdent pold = newIdentUse(sym,0,i);
                        JCIdent pnew = newIdentUse(sym,0,max);
                        JCBinary eq = makeBinary(JCTree.EQ,pnew,pold,0);
                        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,eq);// FIXME pos
                        b.statements.add(asm);
                        m.put(sym,max);
                    }
                }
                newMap.put(sym,max);
            }
        }
        return newMap;
    }
    

    static public class JmlMethodInfo {
        public JmlMethodInfo(JCMethodDecl d) { 
            this.decl = d; 
            this.owner = d.sym; 
            this.source = ((JmlMethodDecl)d).sourcefile;
        }
        MethodSymbol owner;
        JCMethodDecl decl;
        JmlClassInfo classInfo;
        JavaFileObject source;
        String resultName;
        boolean resultUsed = false;
        JCExpression exceptionDecl;
        VarSymbol exceptionLocal;
        ListBuffer<JCVariableDecl> olds = new ListBuffer<JCVariableDecl>();
        java.util.List<JCExpression> requiresPredicates = new LinkedList<JCExpression>();
        java.util.List<JCExpression> ensuresPredicates = new LinkedList<JCExpression>();
        java.util.List<JCExpression> exPredicates = new LinkedList<JCExpression>();
        java.util.List<JCExpression> sigPredicates = new LinkedList<JCExpression>();
        java.util.List<JCExpression> divergesPredicates = new LinkedList<JCExpression>();
        
        public static class Entry {
            public Entry(JCExpression pre, java.util.List<JCTree> list) {
                this.pre = pre;
                this.storerefs = list;
            }
            public JCExpression pre;
            public java.util.List<JCTree> storerefs;
        }
        
        java.util.List<Entry> assignables = new LinkedList<Entry>();
    }

    Map<Symbol,JmlMethodInfo> methodInfoMap = new HashMap<Symbol,JmlMethodInfo>();

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
        JmlMethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(msym);
        if (mspecs == null) {
            System.out.println("METHOD SPECS IS UNEXPECTEDLY NULL " + msym);
            return null;
        }
        if (mspecs.decl == null) {
            System.out.println("METHOD DECL IS UNEXPECTEDLY NULL " + msym);
            return null;
        }
        JmlMethodInfo mi = new JmlMethodInfo(mspecs.decl);
        JmlMethodSpecs denestedSpecs = msym == null ? null : specs.getDenestedSpecs(msym);
        if (JmlEsc.escdebug) System.out.println("SPECS FOR " + msym.owner + " " + msym + " " + (denestedSpecs != null));
        if (JmlEsc.escdebug) System.out.println(denestedSpecs == null ? "     No denested Specs" : denestedSpecs.toString("   "));

        List<JCStatement> prev = newstatements;
        newstatements = new LinkedList<JCStatement>();
        if (denestedSpecs != null) {
            // preconditions
            JCExpression pre = denestedSpecs.cases.size() == 0 ? makeLiteral(true,mspecs.decl==null?0:mspecs.decl.pos) : null;
            int num = 0;
            for (JmlSpecificationCase spc: denestedSpecs.cases) {
                JCExpression spre = null;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.REQUIRES) {
                        num++;
                        JCExpression e = (((JmlMethodClauseExpr)c).expression);
                        if (spre == null) spre = e;
                        else spre = makeBinary(JCTree.AND,spre,e,spre.pos);
                    }
                    if (spre == null) spre = makeLiteral(true,spc.pos);
                }
                if (pre == null) pre = spre;
                else pre = makeBinary(JCTree.OR,pre,spre,pre.pos);
            }
            mi.requiresPredicates.add(pre);  // Just one composite precondition for all of the spec cases
            
            // postconditions
            for (JmlSpecificationCase spc: denestedSpecs.cases) {
                JCExpression spre = trueLiteral;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.REQUIRES) {
                        int pos = spre==trueLiteral ? c.pos : spre.pos;
                        spre = makeBinary(JCTree.AND,spre,(((JmlMethodClauseExpr)c).expression),pos);
                    }
                }
                JCExpression nspre = factory.at(spre.pos).JmlMethodInvocation(JmlToken.BSOLD,com.sun.tools.javac.util.List.of(spre));
                nspre.type = spre.type;
                spre = nspre;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.ENSURES) {
                        JCExpression e = ((JmlMethodClauseExpr)c).expression;
                        JCExpression post = makeJmlBinary(JmlToken.IMPLIES,spre,e,e.getStartPosition());
                        mi.ensuresPredicates.add(post);
                    } else if (c.token == JmlToken.ASSIGNABLE) {
                        JmlMethodClauseAssignable mod = (JmlMethodClauseAssignable)c;
                        // spre is the precondition under which the store-refs are modified
                        List<JCTree> list = mod.list; // store-ref expressions
                        mi.assignables.add(new JmlMethodInfo.Entry(spre,list));
                    } else if (c.token == JmlToken.SIGNALS) {
                        // FIXME - what if there is no variable? - is there one already inserted or is it null?
                        JmlMethodClauseSignals mod = (JmlMethodClauseSignals)c;
                        JCExpression e = mod.expression;
                        // If vardef is null, then there is no declaration in the signals clause (e.g. it is just false).
                        // We use the internal \exception token instead; we presume the type is java.lang.Exception 
                        JCExpression post = makeJmlBinary(JmlToken.IMPLIES,spre,e,e.getStartPosition());
                        if (mod.vardef != null) {
                            JCIdent id = makeIdent(mod.vardef.sym,mod.vardef.pos);
                            e = makeInstanceof(id,c.pos, mod.vardef.type, mod.vardef.pos);
                            post = makeJmlBinary(JmlToken.IMPLIES,e,post,c.pos);
                        } else {
                            JCExpression id = factory.at(c.pos).JmlSingleton(JmlToken.BSEXCEPTION);
                            e = makeInstanceof(id,c.pos, syms.exceptionType, c.pos);
                            post = makeJmlBinary(JmlToken.IMPLIES,e,post,c.pos);
                        }
                        mi.exPredicates.add(post);
                    } else if (c.token == JmlToken.DIVERGES) {
                        JCExpression e = ((JmlMethodClauseExpr)c).expression;
                        JCExpression post = makeJmlBinary(JmlToken.IMPLIES,spre,e,e.getStartPosition());
                        mi.divergesPredicates.add(post);
                    } else if (c.token == JmlToken.SIGNALS_ONLY) {
                        mi.sigPredicates.add(makeSignalsOnly((JmlMethodClauseSigOnly)c));
                    }
                    // FIXME - is signals_only desugared or handled here?
                    // FIXME - we are ignoring forall old when diverges duration working_space callable accessible measured_by captures
                }
            }
        }
        newstatements = prev;
        return mi;
    }
    
    protected JCExpression makeTypeof(JCExpression e) {
        JCExpression typeof = factory.at(e.pos).JmlMethodInvocation(JmlToken.BSTYPEOF,e);
        typeof.type = syms.classType;
        return typeof;
    }
    
    /** Makes the equivalent of an instanceof operation:  \typeof(e) <: \type(type) */
    protected JCExpression makeInstanceof(JCExpression e, int epos, Type type, int typepos) {
        return makeJmlBinary(JmlToken.SUBTYPE_OF,makeTypeof(e),makeTypeLiteral(type,typepos),epos);
    }
    
    protected JCExpression makeSignalsOnly(JmlMethodClauseSigOnly clause) {
        JCExpression e = makeLiteral(false,clause.pos);
        JCExpression id = factory.at(0).JmlSingleton(JmlToken.BSEXCEPTION);
        for (JCExpression typetree: clause.list) {
            int pos = typetree.getStartPosition();
            e = makeBinary(JCTree.OR, 
                    makeInstanceof(id, pos, typetree.type, pos), e, pos);
        }
        return e;
    }


    // STATEMENT NODES
    
    // Just process all the statements in the block prior to any other
    // remaining statements 
    public void visitBlock(JCBlock that) {
        List<JCStatement> s = that.getStatements();
        if (s != null) remainingStatements.addAll(0,s);
    }
    
    public void visitJmlWhileLoop(JmlWhileLoop that)  { 
        visitLoopWithSpecs(that, null, that.cond, null, that.body, that.loopSpecs);
    }
    
    public void visitWhileLoop(JCWhileLoop that) {
        visitLoopWithSpecs(that, null, that.cond, null, that.body, null);
    }
    
    public void visitJmlForLoop(JmlForLoop that) {
        visitLoopWithSpecs(that,that.init,that.cond,that.step,that.body,that.loopSpecs );
    }
    
    public void visitForLoop(JCForLoop that) { 
        visitLoopWithSpecs(that,that.init,that.cond,that.step,that.body,null );
    }
    
    List<JCTree> loopStack = new LinkedList<JCTree>();
    
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
     */ // FIXME - allow for unrolling

    
    protected void visitLoopWithSpecs(JCTree that, List<JCStatement> init, JCExpression test, List<JCExpressionStatement> update, JCStatement body, List<JmlStatementLoop> loopSpecs) {
        loopStack.add(0,that);
        int pos = that.pos;
        BasicBlock bloopBody = newBlock(blockPrefix + pos + "$LoopBody",pos);
        BasicBlock bloopContinue = newBlock(blockPrefix + pos + "$LoopContinue",pos);
        BasicBlock bloopEnd = newBlock(blockPrefix + pos + "$LoopEnd",pos);
        BasicBlock bloopBreak = newBlock(blockPrefix + pos + "$LoopBreak",pos);
        String restName = blockPrefix + pos + "$LoopAfter";

        // Now create an (unprocessed) block for everything that follows the
        // loop statement
        BasicBlock brest = newBlock(restName,pos,currentBlock);// it gets all the followers of the current block
        List<JCStatement> temp = brest.statements; // an empty list
        brest.statements = remainingStatements; // it gets all of the remaining statements
        remainingStatements = temp;
        blocksToDo.add(0,brest); // push it on the front of the to do list

        // Finish out the current block with the loop initialization
        if (init != null) remainingStatements.addAll(init);
        processBlockStatements(false);
        
        // check the loop invariants
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,that.getStartPosition());

        // Now havoc any variables changed in the loop body
        {
            List<JCExpression> targets = TargetFinder.findVars(body,null);
            TargetFinder.findVars(test,targets);
            if (update != null) TargetFinder.findVars(update,targets);
            // synthesize a modifies list
            int wpos = body.pos;
            for (JCExpression e: targets) {
                if (e instanceof JCIdent) {
                    newIdentIncarnation((JCIdent)e,wpos);
                } else {
                    // FIXME - havoc in loops
                    System.out.println("UNIMPLEMENTED HAVOC IN LOOP " + e.getClass());
                }
            }
        }
        
        // assume the loop invariants
        addLoopInvariants(JmlToken.ASSUME,loopSpecs,that.getStartPosition());
        
        // compute the loop variants
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                String dec = "$$decreases" + "$" + loopspec.getStartPosition();
                addAuxVariable(dec,syms.longType,trSpecExpr(loopspec.expression),false);
            }
        }
        
        // compute the loop condition
        String loopTestVarName = "forCondition"  
            + "$" + test.getStartPosition() + "$" + test.getStartPosition(); // FIXME - end position?
        JCIdent loopTest = addAuxVariable(loopTestVarName,syms.booleanType,trJavaExpr(test),false);
        completed(currentBlock);
        BasicBlock bloopStart = currentBlock;
        follows(bloopStart,bloopBody);
        follows(bloopStart,bloopEnd);

        // Create the loop body block
        startBlock(bloopBody);
        
        // assume the loop invariants
        addAssume(Label.LOOP,loopTest,bloopBody.statements,false);
        
        // check that the loop variants are not negative
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                int p = loopspec.getStartPosition();
                String dec = "$$decreases" + "$" + p;
                JCIdent v = newAuxIdent(dec,syms.longType,p);
                JCExpression e = makeBinary(JCTree.GE,v,makeLiteral(0,p),p);
                addAssert(Label.LOOP_DECREASES_NEGATIVE,e,p,currentBlock.statements,body.getStartPosition()); // FIXME - track which continue is causing a problem?
            }
        }
        
        // do the loop body
        remainingStatements.add(body);
        follows(bloopBody,bloopContinue);
        processBlockStatements(true);
        
        // Create a loop continue block
        startBlock(bloopContinue);
        // do the update
        if (update != null) remainingStatements.addAll(update);
        processBlockStatements(false);
        // Check that loop invariants are still established
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,body.getStartPosition());
        // Check that loop variants are decreasing
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                String dec = "$$decreases$" + loopspec.getStartPosition();
                JCIdent id = newAuxIdent(dec,syms.longType,loopspec.getStartPosition());
                JCExpression newexpr = trSpecExpr(loopspec.expression);
                JCExpression e = makeBinary(JCTree.LT,newexpr,id,newexpr.getStartPosition());
                addAssert(Label.LOOP_DECREASES,e,loopspec.getStartPosition(),currentBlock.statements,body.getStartPosition()); // FIXME - track which continue is causing a problem?
            }
        }
        completed(bloopContinue);
        
        // Create the LoopEnd block
        startBlock(bloopEnd);
        follows(bloopEnd,bloopBreak);
        JCExpression neg = makeUnary(JCTree.NOT,loopTest,loopTest.pos);
        addAssume(Label.LOOP,neg,currentBlock.statements,false);
        completed(bloopEnd);
        
        // fill in the LoopBreak block
        startBlock(bloopBreak);
        follows(bloopBreak,brest);
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,body.getStartPosition()+1); // FIXME _ use end position - keep different from Continue
        completed(bloopBreak);

        // Go on processing the loop body
        currentBlock = null;
        newstatements = null;
        loopStack.remove(0);
    }

    protected void addLoopInvariants(JmlToken t, java.util.List<JmlStatementLoop> loopSpecs, int usepos) {
        if (loopSpecs == null) return;
        for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.LOOP_INVARIANT) {
                JCExpression e = trSpecExpr(loopspec.expression);
                if (t == JmlToken.ASSUME) addAssume(Label.LOOP_INVARIANT,e,currentBlock.statements,false);
                else addAssert(Label.LOOP_INVARIANT,e,loopspec.getStartPosition(),currentBlock.statements,usepos);
            }
        }
    }
    
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        visitForeachLoopWithSpecs(that,that.loopSpecs);
    }

    public void visitForeachLoop(JCEnhancedForLoop that) {
        visitForeachLoopWithSpecs(that,null);
    }
    
    protected void visitForeachLoopWithSpecs(JCEnhancedForLoop that, com.sun.tools.javac.util.List<JmlStatementLoop> loopSpecs) {
        int pos = that.pos;
        if (that.expr.type.tag == TypeTags.ARRAY) {
            // for (T v; arr) S
            // becomes
            //   for (int i=0; i<arr.length; i++) { v = arr[i]; S }
            
            // make   int $$foreach = 0;   as the initialization
            Name name = names.fromString("$$foreach");
            JCVariableDecl decl = makeVariableDecl(name,syms.intType,makeLiteral(0,pos),pos);
            com.sun.tools.javac.util.List<JCStatement> initList = com.sun.tools.javac.util.List.<JCStatement>of(decl);
            
            // make   $$foreach < <expr>.length   as the loop test
            JCIdent id = (JCIdent)factory.at(pos).Ident(decl);
            id.type = decl.type;
            JCExpression fa = factory.at(pos).Select(that.getExpression(),syms.lengthVar);
            fa.type = syms.intType;
            JCExpression test = makeBinary(JCTree.LT,id,fa,pos);

            // make   $$foreach = $$foreach + 1  as the update list
            JCIdent idd = (JCIdent)factory.at(pos+1).Ident(decl);
            id.type = decl.type;
            JCAssign asg = factory.at(idd.pos).Assign(idd,
                    makeBinary(JCTree.PLUS,id,makeLiteral(1,pos),idd.pos));
            asg.type = syms.intType;
            JCExpressionStatement update = factory.at(idd.pos).Exec(asg);
            com.sun.tools.javac.util.List<JCExpressionStatement> updateList = com.sun.tools.javac.util.List.<JCExpressionStatement>of(update);
            
            // make   <var> = <expr>[$$foreach]    as the initialization of the target and prepend it to the body
            JCArrayAccess aa = factory.at(pos).Indexed(that.getExpression(),id);
            aa.type = that.getVariable().type;
            JCIdent v = (JCIdent)factory.at(pos).Ident(that.getVariable());
            v.type = aa.type;
            asg = factory.at(pos).Assign(v,aa);
            asg.type = v.type;
            ListBuffer<JCStatement> newbody = new ListBuffer<JCStatement>();
            newbody.append(factory.at(pos).Exec(asg));
            newbody.append(that.body);
            
            // add 0 <= $$foreach && $$foreach <= <expr>.length
            // as an additional loop invariant
            JCExpression e1 = makeBinary(JCTree.LE,makeLiteral(0,pos),id,pos);
            JCExpression e2 = makeBinary(JCTree.LE,id,fa,pos);
            JCExpression e3 = makeBinary(JCTree.AND,e1,e2,pos);
            JmlStatementLoop inv =factory.at(pos).JmlStatementLoop(JmlToken.LOOP_INVARIANT,e3);
            if (loopSpecs == null) {
                loopSpecs = com.sun.tools.javac.util.List.<JmlStatementLoop>of(inv);
            } else {
                ListBuffer<JmlStatementLoop> buf = new ListBuffer<JmlStatementLoop>();
                buf.appendList(loopSpecs);
                buf.append(inv);
                loopSpecs = buf.toList();
            }
            visitLoopWithSpecs(that,initList,test,updateList,factory.at(that.body.pos).Block(0,newbody.toList()),loopSpecs);
        } else {
            notImpl(that); // FIXME
        }
    }
    
    public void visitDoLoop(JCDoWhileLoop that) {
        visitDoLoopWithSpecs(that,null);
    }    

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        visitDoLoopWithSpecs(that,that.loopSpecs);
    }

    
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
    public void visitDoLoopWithSpecs(JCDoWhileLoop that, List<JmlStatementLoop> loopSpecs) {
        JCExpression test = that.getCondition();
        JCStatement body = that.getStatement();
        loopStack.add(0,that);
        int pos = that.pos;
        BasicBlock bloopStart = currentBlock;
        BasicBlock bloopContinue = newBlock(blockPrefix + pos + "$LoopContinue",pos);
        BasicBlock bloopEnd = newBlock(blockPrefix + pos + "$LoopEnd",pos);
        BasicBlock bloopBreak = newBlock(blockPrefix + pos + "$LoopBreak",pos);
        String restName = blockPrefix + pos + "$LoopAfter";

        // Create an (unprocessed) block for everything that follows the
        // loop statement
        BasicBlock brest = newBlock(restName,pos,currentBlock);// it gets all the followers of the current block
        List<JCStatement> temp = brest.statements;
        brest.statements = remainingStatements; // it gets all of the remaining statements
        remainingStatements = temp;
        blocksToDo.add(0,brest); // push it on the front of the to do list

        // Back to the current block
        // test the loop invariants
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,that.getStartPosition());

        // Now havoc any variables changed in the loop
        {
            List<JCExpression> targets = TargetFinder.findVars(body,null);
            TargetFinder.findVars(test,targets);
            // synthesize a modifies list
            int wpos = body.pos;
            for (JCExpression e: targets) {
                if (e instanceof JCIdent) {
                    newIdentIncarnation((JCIdent)e,wpos);
                } else {
                    // FIXME - havoc in loops
                    System.out.println("UNIMPLEMENTED HAVOC IN LOOP " + e.getClass());
                }
            }
        }

        // assume the loop invariant
        addLoopInvariants(JmlToken.ASSUME,loopSpecs,that.getStartPosition());

        // Compute the loop variant and Check that the variant is not negative
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                int p = loopspec.getStartPosition();
                String dec = "$$decreases" + "$" + p;
                JCIdent v = addAuxVariable(dec,syms.longType,trSpecExpr(loopspec.expression),false);
                JCExpression e = makeBinary(JCTree.GE,v,makeLiteral(0,p),p);
                addAssert(Label.LOOP_DECREASES_NEGATIVE,e,p,currentBlock.statements,body.getStartPosition()); // FIXME - track which continue is causing a problem?
            }
        }
        // do the loop body
        remainingStatements.add(that.body);
        processBlockStatements(true);
        follows(bloopStart,bloopContinue);

        // Create a loop continue block
        startBlock(bloopContinue);
        processBlockStatements(false);
        // Compute the loop condition, with any side-effect
        String loopTestVarName = "forCondition"  
            + "$" + test.getStartPosition() + "$" + test.getStartPosition(); // FIXME - end position?
        JCIdent loopTest = addAuxVariable(loopTestVarName,syms.booleanType,trJavaExpr(test),false);

        // Check that loop invariants are still established
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,body.getStartPosition()); // FIXME - use end position?

        // Check that loop variants are decreasing
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                String dec = "$$decreases$" + loopspec.getStartPosition();
                JCIdent id = newAuxIdent(dec,syms.longType,loopspec.getStartPosition());
                JCExpression newexpr = trSpecExpr(loopspec.expression);
                JCExpression e = makeBinary(JCTree.LT,newexpr,id,newexpr.getStartPosition());
                addAssert(Label.LOOP_DECREASES,e,loopspec.getStartPosition(),currentBlock.statements,body.getStartPosition()); // FIXME - track which continue is causing a problem?
            }
        }
        follows(bloopContinue,bloopEnd);
        completed(bloopContinue);

        // Create the LoopEnd block
        startBlock(bloopEnd);
        follows(bloopEnd,bloopBreak);
        JCExpression neg = makeUnary(JCTree.NOT,loopTest,loopTest.pos);
        addAssume(Label.LOOP,neg,currentBlock.statements,false);
        completed(bloopEnd);

        // fill in the LoopBreak block
        startBlock(bloopBreak);
        follows(bloopBreak,brest);
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,body.getStartPosition()+1); // FIXME _ use end position - keep different from Continue
        completed(bloopBreak);

        currentBlock = null;
        newstatements = null;
        loopStack.remove(0);
    }
    
    public void visitLabelled(JCLabeledStatement that) {
        JCTree target = that.getStatement();
        while (target instanceof JCLabeledStatement) ((JCLabeledStatement)target).getStatement();
        Map<VarSymbol,Integer> map = new HashMap<VarSymbol,Integer>(currentMap);
        labelmaps.put(that.label,map);
        labelmapStatement.put(that.label,target);
        that.getStatement().accept(this);
    }
    
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
    //          goto $$case$<A>,$$case$<B>,$$case$<C>
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
    //     $$defaultcase$<C>:
    //          assume !($$switchExpression$<pos>$<pos> == A && ...);
    //          SD
    //          goto $$BL$<pos>$switchEnd
    //     $$BL$<pos>$switchEnd:
    //          ....
    //     
    public void visitSwitch(JCSwitch that) { 
        int pos = that.pos;
        JCExpression switchExpression = that.selector;
        int swpos = switchExpression.pos;
        List<JCCase> cases = that.cases;
        
        // Create the ending block name
        String endBlock = blockPrefix + pos + "$switchEnd";
        
        try {
            breakStack.add(0,that);

            // We create a new auxiliary variable to hold the switch value, so 
            // we can track its value and so the subexpression does not get
            // replicated.  We add an assumption about its value and add it to
            // list of new variables
            String switchName = "$switchExpression$" + pos;
            JCIdent vd = newAuxIdent(switchName,switchExpression.type,swpos);
            JCExpression newexpr = makeBinary(JCTree.EQ,vd,switchExpression,swpos);
            JmlTree.JmlStatementExpr asm = factory.at(swpos).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,trJavaExpr(newexpr));
            currentBlock.statements.add(asm);
            BasicBlock switchStart = currentBlock;

            // Now create an (unprocessed) block for everything that follows the
            // switch statement
            BasicBlock b = newBlock(endBlock,pos,currentBlock);// it gets all the followers of the current block
            List<JCStatement> temp = b.statements;
            b.statements = remainingStatements; // it gets all of the remaining statements
            remainingStatements = temp;
            blocksToDo.add(0,b); // push it on the front of the to do list
            BasicBlock brest = b;

            // Now we need to make unprocessed blocks for all of the case statements,
            // adding them to the todo list at the end
            // Note that there might be nesting of other switch statements etc.
            java.util.LinkedList<BasicBlock> blocks = new java.util.LinkedList<BasicBlock>();
            BasicBlock prev = null;
            JCExpression defaultCond = falseLiteral;
            JmlTree.JmlStatementExpr defaultAsm = null;
            for (JCCase caseStatement: cases) {
                JCExpression caseValue = caseStatement.getExpression();
                List<JCStatement> stats = caseStatement.getStatements();
                int casepos = caseStatement.getStartPosition();
                
                // create a block for this case test
                String caseName = "$case$" + caseStatement.getStartPosition() ;
                if (caseValue == null) caseName = "$defaultcase$" + casepos ;
                BasicBlock blockForTest = newBlock(caseName,casepos);
                blocks.add(blockForTest);
                follows(switchStart,blockForTest);
                
                // create the case test, or null if this is the default case
                JCBinary eq = caseValue == null ? null : makeBinary(JCTree.EQ,vd,trJavaExpr(caseValue),caseValue.getStartPosition());
                asm = factory.at(caseStatement.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,eq);
                blockForTest.statements.add(asm);
                
                // continue to build up the default case test
                if (caseValue == null) defaultAsm = asm; // remember the assumption for the default case
                else defaultCond = makeBinary(JCTree.OR,eq,defaultCond,caseValue.getStartPosition());

                // determine whether this case falls through to the next
                boolean fallthrough = stats.isEmpty() || !(stats.get(stats.size()-1) instanceof JCBreak);
                
                if (prev == null) {
                    // statements can go in the same block
                    blockForTest.statements.addAll(stats);
                    if (!fallthrough) follows(blockForTest,brest);
                    prev = fallthrough ? blockForTest : null;
                } else {
                    // falling through from the previous case
                    // since there is fall-through, the statements need to go in their own block
                    String caseStats = "$caseBody$" + caseStatement.getStartPosition(); // FIXME - is there certain to be a case statement
                    BasicBlock blockForStats = newBlock(caseStats,caseStatement.getStartPosition());
                    blockForStats.statements.addAll(stats);
                    follows(blockForTest,blockForStats);
                    replaceFollows(prev,blockForStats);
                    follows(blockForStats,brest);
                    blocks.add(blockForStats);
                    prev = fallthrough ?  blockForStats : null;
                }
            }
            JCExpression eq = makeUnary(JCTree.NOT,defaultCond,0);  // FIXME pos
            if (defaultAsm != null) {
                defaultAsm.expression = eq;
            } else {
                // There was no default - we need to construct an empty one
                // create a block for this case test
                String caseName = "$defaultcase$" + pos ;
                BasicBlock blockForTest = newBlock(caseName,pos);
                blocks.add(blockForTest);
                follows(switchStart,blockForTest);
                follows(blockForTest,brest);
                
                defaultAsm = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,eq);
                blockForTest.statements.add(defaultAsm);
            }
            // push all of the blocks onto the to do list
            while (!blocks.isEmpty()) {
                blocksToDo.add(0,blocks.removeLast());
            }
            // continue on to complete the current block
        } finally {
            breakStack.remove(0);  // FIXME - this is not going to work for embedded breaks
        }
        
        
    }
    
    // Should never get here because case statements are handled in switch
    public void visitCase(JCCase that) { shouldNotBeCalled(that); }
    
    protected java.util.List<BasicBlock> tryStack = new java.util.LinkedList<BasicBlock>();

    public void visitTry(JCTry that) {
        // Create an (unprocessed) block for everything that follows the
        // try statement
        BasicBlock brest = newBlock(blockPrefix + that.pos + "$afterTry",that.pos,currentBlock);// it gets all the followers of the current block

        // Add an initial assumption to the rest of the statements that the program
        // is still executing normally (no return or throw has happened)
        JCExpression e = makeBinary(JCTree.EQ,terminationVar,zeroLiteral,that.pos);
        addAssume(Label.SYN,e,brest.statements,false);// FIXME - pos
        brest.statements.addAll(remainingStatements); // it gets all of the remaining statements
        blocksToDo.add(0,brest);
        remainingStatements.clear();
        remainingStatements.add(that.getBlock());
        
        // We make an empty finally block if the try statement does not
        // have one, just to simplify things
        JCBlock finallyStat = that.getFinallyBlock();
        int pos = that.pos;
        String finallyBlockName = blockPrefix + pos + "$finally";
        BasicBlock finallyBlock = newBlock(finallyBlockName,pos,currentBlock);// it gets all the followers of the current block
        if (finallyStat != null) finallyBlock.statements.add(finallyStat); // it gets all of the remaining statements
        blocksToDo.add(0,finallyBlock); // push it on the front of the to do list
        follows(finallyBlock,brest);
        if (tryStack.isEmpty()) {
            follows(finallyBlock,condReturnBlock);
            follows(finallyBlock,condExceptionBlock);
        } else {
            BasicBlock nextFinallyBlock = tryStack.get(0);
            follows(finallyBlock,nextFinallyBlock);
        }
        tryStack.add(0,finallyBlock);

        int i = 0;
        JCExpression cond = trueLiteral;
        for (JCCatch catcher: that.catchers) {
            // A catch block has these statements
            // assume <exception condition>
            // assume <catchVar> = <exceptionVar>
            // assume <terminationVar> = 0
            // statements of the catch block
            int cpos = catcher.pos;
            String catchBlockName = blockPrefix + cpos + "$catch";
            BasicBlock catchBlock = newBlock(catchBlockName,cpos);

            addClassPredicate(catcher.param.vartype.type);
            JCIdent ev = newIdentUse((VarSymbol)exceptionVar.sym,cpos);
            JCExpression inst = factory.at(cpos).TypeTest(ev,catcher.param.vartype);
            inst.type = syms.booleanType;
            addAssume(Label.CATCH_CONDITION,makeBinary(JCTree.AND,cond,inst,cpos),catchBlock.statements,false); // FIXME - track?
            cond = makeBinary(JCTree.AND,cond,makeUnary(JCTree.NOT,inst,cpos),cpos);

            JCIdent id = newIdentUse(catcher.param.sym,cpos);
            addAssignmentStatement(catchBlock,cpos,id,ev);

            id = newIdentUse((VarSymbol)terminationVar.sym,cpos);
            addAssignmentStatement(catchBlock,cpos,id,zeroLiteral);
            
            catchBlock.statements.add(catcher.getBlock()); // it gets all of the remaining statements
            follows(currentBlock,catchBlock);
            follows(catchBlock,finallyBlock);
            blocksToDo.add(i++,catchBlock); // push it on the to do list
        }
        // If there are any catch blocks then we need one finally block for the
        // case that no other blocks have caught the exception.  This block may not feasible
        if (!that.catchers.isEmpty()) {
            String catchBlockName = blockPrefix + that.pos + "$catchrest";
            BasicBlock catchBlock = newBlock(catchBlockName,that.pos);
            addAssume(Label.CATCH_CONDITION,cond,catchBlock.statements,false); // Do not track 
            follows(currentBlock,catchBlock);
            follows(catchBlock,finallyBlock);
            blocksToDo.add(i++,catchBlock); // push it on the to do list
        } else {
            follows(currentBlock,finallyBlock);
        }

        // Finish the processing of the current block 
        processBlockStatements(false);
    }
    
    public void visitCatch(JCCatch that) { 
        shouldNotBeCalled(that); 
    }
    
    public void visitIf(JCIf that) {
        int pos = that.pos;
        // Create a bunch of block names
        String thenName = blockPrefix + pos + "$then";
        String elseName = blockPrefix + pos + "$else";
        String restName = blockPrefix + pos + "$afterIf";
        
        // We create a new auxiliary variable to hold the branch condition, so 
        // we can track its value and so the subexpression does not get
        // replicated.  We add an assumption about its value and add it to
        // list of new variables
        String condName = "branchCondition$" + that.getStartPosition();
        JCIdent vd = newAuxIdent(condName,syms.booleanType,that.getStartPosition());
        JCExpression newexpr = makeBinary(JCTree.EQ,vd,that.cond,that.cond.pos);
        JmlTree.JmlStatementExpr asm = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,trJavaExpr(newexpr));
        newstatements.add(asm);
        
        // Now create an (unprocessed) block for everything that follows the
        // if statement
        BasicBlock b = newBlock(restName,pos,currentBlock);// it gets all the followers of the current block
        List<JCStatement> temp = b.statements;
        b.statements = remainingStatements; // it gets all of the remaining statements
        remainingStatements = temp;
        blocksToDo.add(0,b); // push it on the front of the to do list
        BasicBlock brest = b;
        
        // Now make the else block, also unprocessed
        b = newBlock(elseName,pos);
        JCExpression c = makeUnary(JCTree.NOT,vd,pos);
        JmlTree.JmlStatementExpr t = factory.at(that.cond.pos + 1).JmlExpressionStatement(JmlToken.ASSUME,Label.BRANCHE,c);
        b.statements.add(t);
        if (that.elsepart != null) b.statements.add(that.elsepart);
        blocksToDo.add(0,b);
        follows(b,brest);
        follows(currentBlock,b);
        
        // Now make the then block, also still unprocessed
        b = newBlock(thenName,pos);
        c = vd;
        t = factory.at(that.cond.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.BRANCHT,c);
        b.statements.add(t);
        b.statements.add(that.thenpart);
        blocksToDo.add(0,b);
        follows(b,brest);
        follows(currentBlock,b);
    }
    
    public void visitExec(JCExpressionStatement that)    { 
        // This includes assignments and stand-alone method invocations
        that.expr.accept(this);
        // ignore the result; any statements are already added
    }
    
    protected java.util.List<JCStatement> breakStack = new java.util.LinkedList<JCStatement>();
    
    public void visitBreak(JCBreak that) { 
        if (breakStack.isEmpty()) {
            // ERROR - FIXME
        } else if (breakStack.get(0) instanceof JCSwitch) {
            // Don't need to do anything.  If the break is not at the end of a block,
            // the compiler would not have passed this.  If it is at the end of a block
            // the logic in handling JCSwitch has taken care of everything.
            
            // FIXME - for safety, check and warn if there are any remaining statements in the block
        } else {
            // Some kind of loop
        }
    }
    
    public void visitContinue(JCContinue that) {
        if (that.label == null) {
            JCTree t = loopStack.get(0);
            String s = blockPrefix + t.pos + "$loopContinue";
            BasicBlock b = blockLookup.get(s);
            if (b == null) System.out.println("NO CONTINUE BLOCK: " + s);
            else replaceFollows(currentBlock,b);
        } else {
            Log.instance(context).error("esc.not.implemented","continue statements with labels in BasicBlocker");
        }
    }
    
    public void visitReturn(JCReturn that)               {
        if (that.getExpression() != null) {
            int p = that.getExpression().getStartPosition();
            JCExpression res = makeBinary(JCTree.EQ,resultVar,trJavaExpr(that.getExpression()),p);  // resultVar is not translated - shoudl be incase there are multiple returns executed FIXME
            JmlStatementExpr asm = factory.at(p).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,(res));
            newstatements.add(asm);
        }
        int pos = that.getStartPosition();
        JCIdent id = newIdentIncarnation(terminationVar,pos);
        JCLiteral lit = makeLiteral(pos,pos);
        JCExpression e = makeBinary(JCTree.EQ,id,lit,pos);
        JmlStatementExpr asm = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);
        newstatements.add(asm);
        if (tryStack.isEmpty()) {
            replaceFollows(currentBlock,returnBlock);
        } else {
            BasicBlock finallyBlock = tryStack.get(0);
            replaceFollows(currentBlock,finallyBlock);
        }
        // FIXME check and warn if there are remaining statements
    }
    
    public void visitThrow(JCThrow that) { 
        
        // Capture the exception expression
        int p = that.getExpression().getStartPosition();
        JCExpression res = trJavaExpr(that.getExpression());
        JCIdent idex = newIdentIncarnation(exceptionVar,p);
        JCExpression now = makeBinary(JCTree.EQ,idex,res,p);
        addAssume(p,Label.ASSIGNMENT,now,currentBlock.statements,false);
        
        int pos = that.getStartPosition();
        JCIdent id = newIdentIncarnation(terminationVar,pos);
        JCLiteral lit = makeLiteral(-pos,pos);
        JCExpression expr = makeBinary(JCTree.EQ,id,lit,pos);
        addAssume(Label.SYN,expr,currentBlock.statements,false);
        
        if (tryStack.isEmpty()) {
            replaceFollows(currentBlock,exceptionBlock);
        }
        // If the tryStack is not empty, the following blocks have already
        // been setup in visitTry, to go to either the set of catch blocks
        // (if there are any) or to the finally block
        
        if (!remainingStatements.isEmpty()) {
            // Not fatal
            Log.instance(context).warning("esc.internal.error","Unexpected statements following a throw statement");
        }
    }
    
    public void visitAssert(JCAssert that) { // This is a Java assert statement
        JCExpression cond = trJavaExpr(that.cond);
        JCExpression detail = trJavaExpr(that.detail);
        // FIXME - what to do with detail
        // FIXME - for now turn cond into a JML assertion
        // FIXME - need a label for the assert statement
        // FIXME - set line and source
        addAssert(Label.EXPLICIT_ASSERT, cond, that.cond.getStartPosition(), newstatements, that.cond.getStartPosition());
    }
    
    public void visitApply(JCMethodInvocation that) { 
        // This is an expression so we just use trExpr
        JCExpression now;
        JCExpression obj;
        MethodSymbol msym;
        if (that.meth instanceof JCIdent) {
            now = trJavaExpr(that.meth);
            msym = (MethodSymbol)((JCIdent)now).sym;
            if (msym.isStatic()) obj = null;
            else obj = thisId;
        } else if (that.meth instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)that.meth;
            msym = (MethodSymbol)(fa.sym);
            if (msym.isStatic()) obj = null;
            else obj = trExpr( fa.selected );
        } else {
            // FIXME - not implemented
            msym = null;
            obj = null;
        }

        // FIXME - what does this translation mean?
        ListBuffer<JCExpression> newtypeargs = new ListBuffer<JCExpression>();
        for (JCExpression arg: that.typeargs) {
            JCExpression n = trExpr(arg);
            newtypeargs.append(n);
        }

        ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
        for (JCExpression arg: that.args) {
            JCExpression n = trExpr(arg);
            newargs.append(n);
        }

        // FIXME - concerned that the position here is not after the
        // positions of all of the arguments
        if (inSpecExpression) {
            result = insertSpecMethodCall(that.pos,msym,obj,newtypeargs.toList(),newargs.toList());
        } else {
            result = insertMethodCall(that.pos,msym,obj,newargs.toList());
        }
        return;
    }

    public void visitJmlMethodInvocation(JmlMethodInvocation that) { 
            // This is an expression so we just use trExpr
//        System.out.println("NO CHECK OF APPLY");  FIXME
//        that.meth.accept(this);
//        for (JCExpression arg: that.args) {
//            arg.accept(this);
//        }

        JmlToken token = that.token;
        
        switch (token) {
            case BSOLD:
            case BSPRE:
                Map<VarSymbol,Integer> prev = currentMap;
                currentMap = oldMap;
                try {
                    // FIXME - labeled old
                    // There is only one argument to translate
                    // FIXME - think through the semantics of guarded conditions with \old in them
                    result = trExpr(that.args.get(0));
                } finally {
                    currentMap = prev;
                }
                return;
                
            case BSTYPEOF:
                ListBuffer<JCExpression> lb = new ListBuffer<JCExpression>();
                lb.append(trExpr(that.args.get(0)));
                result = factory.at(that.pos).JmlMethodInvocation(token,lb.toList());
                return;

            case BSTYPELC:
                Type type = that.args.get(0).type;
                addClassPredicate(type);
                result = makeTypeLiteral(type,that.pos);
                return;

            case BSELEMTYPE :
            case BSNONNULLELEMENTS :
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
            case BSNOTMODIFIED:
                Log.instance(context).error("esc.not.implemented","Not yet implemented token in BasicBlocker: " + that.token.internedName());
                result = trueLiteral; // FIXME - may not even be a boolean typed result
                break;

            default:
                Log.instance(context).error("esc.internal.error","Unknown token in BasicBlocker: " + that.token.internedName());
                result = trueLiteral; // FIXME - may not even be a boolean typed result
                break;
        }

    }
    
    /** This is not a tree walker visitor, but just a helper method called when 
     * there is a (pure) method invocation inside a specification expression.
     * The translation here is to keep the call (modified) but at an assumption
     * that implies values for the method.
     * 
     * @param pos
     * @param sym
     * @param obj already translated method receiver, or null if static
     * @param args already translated method arguments
     * @returns
     */
    protected JCExpression insertSpecMethodCall(int pos, MethodSymbol sym, JCExpression obj, com.sun.tools.javac.util.List<JCExpression> typeargs, com.sun.tools.javac.util.List<JCExpression> args) {
        Map<VarSymbol,Integer> prevOldMap = oldMap;
        JCIdent prevThisId = thisId;
        JCExpression prevResultVar = resultVar;
        
        // FIXME - need to do a definedness check that the called method is guaranteed to normally terminate
        
        try {
            JmlMethodSpecs mspecs = specs.getSpecs(sym);
            JCExpression newapply = null;
            if (mspecs == null) {
                System.out.println("NO SPECS FOR METHOD CALL");
            } else {
                JmlMethodDecl decl = mspecs.decl;
                JmlMethodInfo mi = getMethodInfo(sym);
                JCIdent newMethodName = newAuxIdent(encodedName(sym,decl.pos,pos).toString(),sym.getReturnType(),pos); // FIXME - string to name to string to name
                
                if (obj == null && args.size() == 0) {
                    // Static and no arguments, so we just use the new method name
                    // as a constant
                    newapply = newMethodName;
                    resultVar = newMethodName; // FIXME - what about typeargs
                    for (JCExpression post: mi.ensuresPredicates) {
                        JCExpression expr = trExpr(post);
                        addAssume(Label.METHODAXIOM,expr,newstatements,false);
                    }
                } else {
                    // Construct what we are going to replace \result with
                    ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
                    if (obj != null) newargs.append(obj);
                    for (JCExpression e: args) newargs.append(e);
                    newapply = factory.at(pos).Apply(typeargs,newMethodName,newargs.toList());
                    // FIXME - needs type

                    // Construct what we are going to replace \result with
                    ListBuffer<JCExpression> margs = new ListBuffer<JCExpression>();
                    ListBuffer<Name> fparams = new ListBuffer<Name>();
                    ListBuffer<JCExpression> localtypes = new ListBuffer<JCExpression>();
                    
                    if (obj != null) {
                        margs.append(thisId);
                        fparams.append(thisId.name);
                        localtypes.append(factory.Type(syms.objectType));
                    }
                    for (JCVariableDecl e: decl.params) {
                        JCIdent p = newIdentUse(e.sym,0);
                        margs.append(p);
                        fparams.append(p.name);
                        localtypes.append(e.vartype);
                    }
                    JCExpression mapply = factory.at(pos).Apply(null,newMethodName,margs.toList()); // FIXME - what about typeargs
                    mapply.type = sym.getReturnType();
                    
                    ListBuffer<Name> single = new ListBuffer<Name>();
                    single.append(thisId.name);
                    resultVar = mapply;
                    for (JCExpression post: mi.ensuresPredicates) {
                        JCExpression predicate = trExpr(post);
                        JmlQuantifiedExpr expr = factory.at(pos).JmlQuantifiedExpr(
                                JmlToken.BSFORALL, null, localtypes,
                                fparams, null, predicate);
                        expr.type = syms.booleanType;
                        addAssume(Label.METHODAXIOM,expr,newstatements,false);
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
        
    protected JCIdent insertMethodCall(int pos, MethodSymbol sym, JCExpression obj, List<JCExpression> args) {
        Map<VarSymbol,Integer> prevOldMap = oldMap;
        JCIdent prevThisId = thisId;
        JCIdent retId = sym.type == null ? null : newAuxIdent("$$result$"+pos,sym.getReturnType(),pos);
        JCExpression prevResultVar = resultVar;
        
        // What do do about 'condition' when checking the preconditions
        
        try {
            JmlMethodSpecs mspecs = specs.getSpecs(sym);
            if (mspecs == null) {
                System.out.println("NO SPECS FOR METHOD CALL");
            } else {
                
                JCExpression expr;
                // Note: need to do all of the expression translation before
                // we assign the new currentThisId
                
                // Evaluate all of the arguments and assign them to a new variable
                JmlMethodDecl decl = mspecs.decl;
                int i = 0;
                for (JCVariableDecl vd  : decl.params) {
                    expr = args.get(i++);
                    JCIdent id = newIdentIncarnation(vd,pos);
                    // FIXME - end information?  use copyInfo?
                    expr = makeBinary(JCTree.EQ,id,expr,id.pos);
                    JCStatement st = factory.at(id.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
                    newstatements.add(st);
                }
                
                currentThisId = newAuxIdent("this$"+pos,syms.objectType,pos); // FIXME - object type?
                if (obj != null) {
                    expr = makeBinary(JCTree.EQ,currentThisId,obj,obj.pos);
                    JCStatement st = factory.at(obj.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
                    newstatements.add(st);
                }

                boolean isStaticCalled = sym.isStatic();
                boolean isConstructorCalled = sym.isConstructor();
                boolean isHelperCalled = isHelper(sym);
                JmlClassInfo calledClassInfo = getClassInfo(sym.owner);
                if (isConstructorCalled) {
                    // Presuming that isConstructor
                    // We are calling a this or super constructor
                    // static invariants have to hold
                    if (!isHelperCalled) {
                        for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e);
                            addAssert(Label.INVARIANT,e,inv.getStartPosition(),newstatements,pos);
                        }
                    }
                } else if (!isConstructor && !isHelper) {
                    for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e);
                        addAssert(Label.INVARIANT,e,inv.getStartPosition(),newstatements,pos);
                    }
                    if (!isStatic) {
                        for (JmlTypeClauseExpr inv : classInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e);
                            addAssert(Label.INVARIANT,e,inv.getStartPosition(),newstatements,pos);
                        }
                    }
                }
                JCExpression exprr = null;
                JmlMethodInfo mi = getMethodInfo(sym);
                if (mi.requiresPredicates.size()==0) exprr = makeLiteral(true,mi.decl.pos);
                else for (JCExpression pre: mi.requiresPredicates) {
                    pre = trSpecExpr(pre);
                    if (exprr == null) exprr = pre;
                    else {
                        exprr = makeBinary(JCTree.OR,exprr,pre,exprr.pos);
                    }
                }
                
                if (!isConstructorCalled && !isStaticCalled) {
                    MethodSymbol msym = sym;
                    while ((msym=getOverrided(msym)) != null) {
                        exprr = addMethodPreconditions(currentBlock,msym,decl,decl.pos,exprr);
                    }
                }
                addAssert(Label.PRECONDITION,exprr,exprr.getStartPosition(),newstatements,pos);


                oldMap = new HashMap<VarSymbol,Integer>(currentMap);

                for (JmlMethodInfo.Entry entry: mi.assignables) {
                    // What to do with preconditions?  FIXME
                            for (JCTree sr: entry.storerefs) {
                                if (sr instanceof JCIdent) {
                                    JCIdent id = (JCIdent)sr;
                                    newIdentIncarnation(id,pos+1); // new incarnation
                                } else if (sr instanceof JmlSingleton) {
                                    if (((JmlSingleton)sr).token == JmlToken.BSNOTHING) {
                                        // OK
                                    } else {
                                        System.out.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                                    }
                                } else if (sr instanceof JmlStoreRefKeyword) {
                                    if (((JmlStoreRefKeyword)sr).token == JmlToken.BSNOTHING) {
                                        // OK
                                    } else {
                                        System.out.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                                    }
                                } else {
                                    System.out.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                                }
                            }
                }
                
                resultVar = retId;
                for (JCExpression post: mi.ensuresPredicates) {
                    addAssume(Label.POSTCONDITION,trSpecExpr(post),newstatements,false);
                }
                if (!isConstructorCalled && !isStaticCalled) {
                    MethodSymbol msym = sym;
                    while ((msym=getOverrided(msym)) != null) {
                        mi = getMethodInfo(msym);
                        for (JCExpression post: mi.ensuresPredicates) {
                            addParameterMappings(mspecs.decl,mi.decl,pos,currentBlock);
                            addAssume(Label.POSTCONDITION,trSpecExpr(post),newstatements,false);
                        }
                    }
                }

                resultVar = prevResultVar;
                
                if (isConstructorCalled) {
                    // Presuming that isConstructor
                    // Calling a super or this constructor
                    if (!isHelperCalled) {
                        for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e);
                            addAssume(Label.INVARIANT,e,newstatements,false);
                        }
                        for (JmlTypeClauseExpr inv : calledClassInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e);
                            addAssume(Label.INVARIANT,e,newstatements,false);
                        }
                        for (JmlTypeClauseConstraint inv : calledClassInfo.staticconstraints) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e);
                            addAssume(Label.CONSTRAINT,e,newstatements,false);
                        }
                    }
                } else if (!isHelper) {
                    for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e);
                        addAssume(Label.INVARIANT,e,newstatements,false);
                    }
                    if (!isStatic) {
                        for (JmlTypeClauseExpr inv : classInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e);
                            addAssume(Label.INVARIANT,e,newstatements,false);
                        }
                    }
                    for (JmlTypeClauseConstraint inv : classInfo.staticconstraints) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e);
                        addAssume(Label.CONSTRAINT,e,newstatements,false);
                    }
                    if (!isConstructor) {
                        if (!isStatic) {
                            for (JmlTypeClauseConstraint inv : classInfo.constraints) {
                                JCExpression e = inv.expression;
                                e = trSpecExpr(e);
                                addAssume(Label.CONSTRAINT,e,newstatements,false);
                            }
                        }
                    }
                }
                // Take out the temporary variables for the arguments
                for (JCVariableDecl vd  : decl.params) {
                    currentMap.remove((VarSymbol)vd.sym);
                }
            }
        } finally {
            oldMap = prevOldMap;
            currentThisId = prevThisId;
            resultVar = prevResultVar;
            result = retId;
        }
        return retId;
    }
    
    public void visitSkip(JCSkip that)                   {
        // do nothing
    }
    public void visitJmlStatement(JmlStatement that) {
        // These are the set and debug statements
        // Just do all the JML statements as if they were Java statements, 
        // since they are part of specifications
        boolean prevInSpecExpression = inSpecExpression;
        try {
            inSpecExpression = true;
            that.statement.accept(this);
        } finally {
            inSpecExpression = prevInSpecExpression;
        }
    }
    
    public void visitJmlStatementLoop(JmlStatementLoop that) { 
        shouldNotBeCalled(that); // These are the specs for loops - they are handled in the loop visitors
    }
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        notImpl(that); // None of these are implemented as yet - FIXME
    }
    
    public void visitJmlStatementExpr(JmlStatementExpr that) { 
        JmlStatementExpr now = null;
        if (that.token == JmlToken.ASSUME || that.token == JmlToken.ASSERT) {
            JCExpression expr = trSpecExpr(that.expression);
            JCExpression opt = trSpecExpr(that.optionalExpression);
            if (that.token == JmlToken.ASSUME) {
                if (that.label == Label.EXPLICIT_ASSUME || that.label == Label.BRANCHT || that.label == Label.BRANCHE) {
                    now = factory.at(that.pos).JmlExpressionStatement(that.token,that.label,expr);
                    now.optionalExpression = opt;
                    now.type = that.type;   
                    currentBlock.statements.add(now);

                    JCExpression id = newAuxIdent("checkAssumption$" + that.label + "$" + that.pos, syms.booleanType, that.pos);
                    now = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSERT,Label.EXPLICIT_ASSUME,id);
                    now.optionalExpression = null;
                    now.type = that.type;   
                    //currentBlock.statements.add(now);
                    newdefs.add(makeBinary(JCTree.EQ,id,trueLiteral,that.pos));
                } else {
                    now = factory.JmlExpressionStatement(that.token,that.label,expr);
                    now.optionalExpression = opt;
                    now.pos = that.pos;
                    now.type = that.type;   
                }
                currentBlock.statements.add(now);
            } else {
                addAssert(that.label,expr,that.getStartPosition(),newstatements,that.pos);
            }
            if (that.token == JmlToken.ASSUME && (that.label == Label.EXPLICIT_ASSUME 
                    || that.label == Label.BRANCHT || that.label == Label.BRANCHE)) {
                int pos = now.pos;
                String n = "assumeCheck$" + that.pos + "$" + that.label.toString();
                JCExpression count = makeLiteral(that.pos,that.pos);
                JCExpression e = makeBinary(JCTree.NE,assumeCheckCountVar,count,pos);
                JCExpression id = newAuxIdent(n,syms.booleanType,e.pos);
                e = makeJmlBinary(JmlToken.EQUIVALENCE,id,e,pos);
                JmlStatementExpr st = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSUME_CHECK,e);
                newstatements.add(st);
                // an assert without tracking
                st = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSERT,Label.ASSUME_CHECK,id);
                // FIXME - start and end?
                st.optionalExpression = null;
                st.type = null; // FIXME - is this right?
                // FIXME - what about source and line?
                newstatements.add(st);
            }

        } else if (that.token == JmlToken.UNREACHABLE) {
            JCExpression expr = makeLiteral(false,that.getStartPosition());
            addAssert(Label.UNREACHABLE,expr,that.getStartPosition(),currentBlock.statements,that.getStartPosition());
        } else if (that.token == JmlToken.HENCE_BY) {
            Log.instance(context).error("esc.not.implemented","hence_by is in BasicBlocker");
        } else {
            Log.instance(context).error("esc.internal.error","Unknown token in BasicBlocker: " + that.token.internedName());
        }
    }
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        // This wraps local declarations within the body of a method:
        // ghost local variables and model local classes
        // Just treat them like Java local declarations  FIXME - check this - see also JmlVariableDecl
        boolean prevInSpecExpression = inSpecExpression;
        try {
            inSpecExpression = true;
            for (JCTree t: that.list) {
                t.accept(this);
            }
        } finally {
            inSpecExpression = prevInSpecExpression;
        }
    }
    
    // Expression nodes to be implemented
    
    public void visitParens(JCParens that) { 
        JCExpression expr = trExpr(that.expr);
        JCParens now = factory.Parens(expr);
        now.type = that.type;
        now.pos = that.pos;
        result = now;
    }
    
    public void visitConditional(JCConditional that) { 
        JCExpression cond = trExpr(that.cond);
        JCExpression truepart;
        JCExpression falsepart;
        JCExpression prev = condition;
        try {
            condition = makeBinary(JCTree.AND,prev,cond,that.pos);
            truepart = trExpr(that.truepart);
            condition = makeBinary(JCTree.AND,prev,
                          makeUnary(JCTree.NOT,cond,that.pos),that.pos);
            falsepart = trExpr(that.falsepart);
        } finally {
            condition = prev;
        }
        JCConditional now = factory.Conditional(cond,truepart,falsepart);
        now.type = that.type;
        now.pos = that.pos;
        result = now;
    }
    
    public void visitUnary(JCUnary that)                 { 
        JCExpression arg = trExpr(that.arg);
        int tag = that.getTag();
        if (tag == JCTree.POSTDEC || tag == JCTree.POSTINC ||
                tag == JCTree.PREDEC || tag == JCTree.PREINC) {
            int op = tag == JCTree.PREDEC || tag == JCTree.POSTDEC ?
                    JCTree.MINUS : JCTree.PLUS;
            JCExpression e = makeBinary(op,arg,makeLiteral(1,that.pos),that.pos);
            result = doAssignment(that.type,arg,e,that.pos);
            if (tag == JCTree.POSTDEC || tag == JCTree.POSTINC) result = arg;
            return;
        }
        if (arg == that.arg) { result = that; return; }
        JCUnary now = factory.at(that.pos).Unary(that.getTag(),arg);
        now.operator = that.operator;
        now.type = that.type;  // FIXME - is this right
        result = now;
    }
    
    public void visitBinary(JCBinary that) { 
        JCExpression left = trExpr(that.lhs);
        JCExpression right;
        if (that.getTag() == JCTree.OR) {
            JCExpression prev = condition;
            try {
                condition = makeBinary(JCTree.AND,
                        condition,
                        makeUnary(JCTree.NOT,left,that.lhs.pos),
                        that.lhs.pos);
                right = trExpr(that.rhs);
            } finally {
                condition = prev;
            }
        } else if (that.getTag() == JCTree.AND) {
            JCExpression prev = condition;
            try {
                condition = makeBinary(JCTree.AND,
                        condition,
                        left,
                        that.lhs.pos);
                right = trExpr(that.rhs);
            } finally {
                condition = prev;
            }
        } else {
            right = trExpr(that.rhs);
        }
        JCBinary now = factory.Binary(that.getTag(),left,right);
        now.operator = that.operator;
        now.type = that.type;
        if (now.type == null) now.type = syms.booleanType; // HACK
        now.pos = that.pos;
        result = now;
        if (that.getTag() == JCTree.DIV || that.getTag() == JCTree.MOD) {
            JCExpression e = makeBinary(JCTree.NE,that.rhs,zeroLiteral,that.rhs.pos);
            e = makeJmlBinary(JmlToken.IMPLIES,condition,e,that.rhs.pos);
            addAssert(inSpecExpression?Label.UNDEFINED_DIV0:Label.POSSIBLY_DIV0,
                    e,that.pos,currentBlock.statements,that.pos);
        }
    }
    
    public void visitTypeCast(JCTypeCast that) { 
        // FIXME - need to do a definedness check
        JCExpression e = trExpr(that.getExpression());
        Type type = that.getType().type;
        JCTypeCast now = factory.at(that.pos).TypeCast(type,e);
        now.type = that.type;
        result = now;
    }
    
    public void visitTypeTest(JCInstanceOf that) {
        JCExpression e = trExpr(that.getExpression());
        // Note - we are not translating the type argument
        e = factory.at(that.pos).JmlMethodInvocation(JmlToken.BSTYPEOF,com.sun.tools.javac.util.List.<JCExpression>of(e));
        JCLiteral lit = makeTypeLiteral(that.getType().type,that.pos);
        e = makeJmlBinary(JmlToken.SUBTYPE_OF,e,lit,that.pos);
        result = e;
    }
    
    public void visitIndexed(JCArrayAccess that) { 
        JCExpression array = trExpr(that.getExpression());

        // Require  that.indexed is not null
        // FIXME - avoid checking that this is not null?
        JCExpression e = makeBinary(JCTree.NE,array,nullLiteral,that.indexed.pos);
        e = makeJmlBinary(JmlToken.IMPLIES,condition,e,e.pos);
        addAssert(inSpecExpression?Label.UNDEFINED_NULL:Label.POSSIBLY_NULL,
                e,that.pos,currentBlock.statements,that.pos);
        
        JCExpression index = trExpr(that.getIndex());
        
        // Require  that.index is not negative
        e = makeBinary(JCTree.GE,index,zeroLiteral,that.index.pos);
        e = makeJmlBinary(JmlToken.IMPLIES,condition,e,e.pos);
        addAssert(inSpecExpression?Label.UNDEFINED_NEGATIVEINDEX:Label.POSSIBLY_NEGATIVEINDEX,
                e,that.pos,currentBlock.statements,that.pos);
        
        // Require  that.index is not too large
        e = new JmlBBFieldAccess(lengthIdent,array);
        e.pos = that.pos;
        e.type = syms.intType;
        e = makeBinary(JCTree.LT,index,e,that.indexed.pos);
        e = makeJmlBinary(JmlToken.IMPLIES,condition,e,e.pos);
        addAssert(inSpecExpression?Label.UNDEFINED_TOOLARGEINDEX:Label.POSSIBLY_TOOLARGEINDEX,
                e,that.pos,currentBlock.statements,that.pos);

        JCIdent arrayID = getArrayIdent(that.type);
        JCArrayAccess now = new JmlBBArrayAccess(arrayID,array,index);
        now.pos = that.pos;
        now.type = that.type;
        result = now;
    }
    
    public void visitSelect(JCFieldAccess that) {
        Symbol sym = that.sym;
        if (sym == null) {
            System.out.println("NULL SYM IN SELECT: " + that.name); // FIXME
        } else if (sym.isStatic()) {
            // FIXME - is there something predefined to compare against?
            if (sym.toString().equals("class")) {
                // Class literal
                addClassPredicate(that.selected.type);
                JCExpression now = factory.at(that.pos).Literal(TypeTags.CLASS,that.selected.type);
                now.type = syms.classType;
                result = now;
            } else {
                VarSymbol vsym = (VarSymbol)that.sym;
                JCIdent now = newIdentUse(vsym,that.pos);
                now.type = that.type;
                result = now;
            }
        } else if (sym instanceof VarSymbol){
            JCExpression selected = trExpr(that.selected);

            // Require  that.selected is not null
            // FIXME - avoid checking that this is not null?
            JCExpression e = makeBinary(JCTree.NE,selected,nullLiteral,that.selected.pos);
            e = makeJmlBinary(JmlToken.IMPLIES,condition,e,e.pos);
            addAssert(inSpecExpression?Label.UNDEFINED_NULL:Label.POSSIBLY_NULL,
                    e,that.pos,currentBlock.statements,that.pos);

            JCIdent id = newIdentUse((VarSymbol)sym,that.pos);
            JCFieldAccess now = new JmlBBFieldAccess(id,selected);
            now.pos = that.pos;
            now.type = that.type;
            result = now;
        } else if (sym instanceof MethodSymbol) {
            // FIXME - should not get here
        } else {
            // FIXME - don't know what this could be
        }
    }
    
    public void visitIdent(JCIdent that) { 
        if (that.sym instanceof VarSymbol) {
            VarSymbol vsym = (VarSymbol)that.sym;
            Symbol owner = that.sym.owner;
            if (owner != null && owner instanceof ClassSymbol && !vsym.isStatic() &&
                    !vsym.toString().equals("this")) {
                // This is a field reference without the default this. prefix
                // We need to make it a JCFieldAccess with a 'this'
                
                // FIXME - is the symbol for 'this' stored somewhere, or can
                // we get it by a lookup (so we're sure to have all the correct
                // type and symbol information)?  or at least do all of the following
                // computations just once
                JCIdent thisIdX = factory.Ident(names.fromString("this"));
                thisIdX.pos = that.pos;
                VarSymbol v = new VarSymbol(0,thisIdX.name,owner.type,owner);
                v.pos = 0;
                thisIdX.sym = v;
                thisIdX.type = owner.type;
                JCFieldAccess now = factory.Select(thisIdX,vsym.name);
                now.pos = that.pos;
                now.type = that.type;
                now.sym = vsym;
                result = trExpr(now);
            } else if (signalsVar != null && vsym == signalsVar.sym) {
                result = newIdentUse((VarSymbol)exceptionVar.sym,that.pos);
            } else if (vsym.toString().equals("this")) {
                result = currentThisId;
            } else {
                result = newIdentUse(vsym,that.pos);
            }
        } else {
            result = that;
        }
    }
    
    Map<String,Integer> strings = new HashMap<String,Integer>();
    
    public void visitLiteral(JCLiteral that) { 
        // numeric, boolean, character, String, null
        // FIXME - not sure about characters or String or class literals
        result = that;
        if (that.typetag == TypeTags.CLASS) {
            if (that.value instanceof Type) {
                Type type = (Type)that.value;
                addClassPredicate(type);
            } else if (that.value instanceof String) {
                String s = that.value.toString();
                Integer i = strings.get(s);
                if (i == null) {
                    i = strings.size();
                    strings.put(s,i);
                }
                Name n = names.fromString("STRING" + i);
                result = factory.at(that.pos).Ident(n);
                result.type = that.type;
            }
        }
    }
    
    public void visitAssign(JCAssign that) { 
        JCExpression left = trExpr(that.lhs);
        JCExpression right = trExpr(that.rhs);
        result = doAssignment(that.type,left,right,that.pos);
    }
    
    // FIXME - embedded assignments to array elements are not implemented; no warning either
    
    protected JCExpression doAssignment(Type restype, JCExpression left, JCExpression right, int pos) {
        if (left instanceof JCIdent) {
            JCIdent id = (JCIdent)left;
            left = newIdentIncarnation(id,pos);
            JCBinary expr = makeBinary(JCBinary.EQ,left,right,pos);

            // FIXME - set line and source
            JmlStatementExpr assume = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
            newstatements.add(assume); 
            return left;
        } else if (left instanceof JCArrayAccess) {
            JCIdent arr = getArrayIdent(right.type);
            JCExpression ex = ((JCArrayAccess)left).indexed;
            JCIdent nid = newArrayIncarnation(right.type,pos);
            JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,((JCArrayAccess)left).index,right);
            expr.pos = pos;
            expr.type = restype;

            // FIXME - set line and source
            JmlStatementExpr assume = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
            newstatements.add(assume); 
            return left;
        } else if (left instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)left;
            Name tsym = fa.name;
            JCIdent oldfield = newIdentUse((VarSymbol)fa.sym,pos);
            JCIdent newfield = newIdentIncarnation(oldfield,pos);
            JCExpression expr = new JmlBBFieldAssignment(newfield,oldfield,fa.selected,right);
            expr.pos = pos;
            expr.type = restype;

            // FIXME - set line and source
            JmlStatementExpr assume = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
            newstatements.add(assume); 
            return left;
        } else {
            System.out.println("INCARNATION NOT IMPLERMENTED - visitAssign");
            return null;
        }
    }
    
    // += -= *= /= %= >>= <<=  >>>= &= |= ^=
    public void visitAssignop(JCAssignOp that) { 
        JCExpression left = trExpr(that.lhs);
        JCExpression right = trExpr(that.rhs);
        int op = that.getTag() - JCTree.ASGOffset;
        JCExpression e = makeBinary(op,left,right,that.pos);
        result = doAssignment(that.type,left,e,that.pos);
    }

    public void visitVarDef(JCVariableDecl that) { 
        JCIdent lhs = newIdentIncarnation(that,that.getPreferredPosition());
        if (that.init != null) {
            // Create and store the new lhs incarnation before translating the
            // initializer because the initializer is in the scope of the newly
            // declared variable.  Actually if there is such a situation, it 
            // will likely generate an error about use of an uninitialized variable.
            JCExpression init = trJavaExpr(that.init);
            JCBinary expr = makeBinary(JCBinary.EQ,lhs,init,that.pos);
            JmlStatementExpr assume = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
            newstatements.add(assume);       
        }
    }
    
    public void visitSynchronized(JCSynchronized that)   { 
        // FIXME - for now ignore any synchronization
        trExpr(that.getExpression());  // just in case there are side-effects
        that.body.accept(this);
    }
    
    public void visitNewClass(JCNewClass that) {
        // FIXME - ignoring enclosing expressions; ignoring anonymous classes
        
        boolean isHelper = false;
        JmlMethodInfo mi = null;
        JmlMethodDecl decl = null;
        
        // This is the id of a new variable that represents the result of the
        // new operation.
        JCIdent id = newAuxIdent("$$new"+that.pos+"$",that.type,that.pos);
        JCIdent prevId = currentThisId;
        Map<VarSymbol,Integer> prevOldMap = oldMap;
        JCExpression prevResultVar = resultVar;
        
        try {
            currentThisId = id;
            resultVar = currentThisId;
            
            Symbol.MethodSymbol sym = (MethodSymbol)that.constructor;
            JmlMethodSpecs mspecs = specs.getSpecs(sym);
            if (mspecs == null) {
                Log.instance(context).error("jml.internal.error","Unexpected failure to find specifications (even an empty spec) for class " + sym.flatName());
                throw new JmlInternalError();
            } 
            int pos = that.pos;

            {
                // Evaluate all of the arguments and assign them to new variables
                decl = mspecs.decl;
                int i = 0;
                for (JCVariableDecl vd  : decl.params) {
                    JCExpression expr = that.args.get(i++);
                    JCIdent pid = newIdentIncarnation(vd,pos);
                    expr = makeBinary(JCTree.EQ,pid,trExpr(expr),pid.pos);
                    JCStatement st = factory.at(pid.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
                    newstatements.add(st);
                }

                // FIXME - observed that for the Object() constructor sym != mspecs.decl.sym ?????

                isHelper = isHelper(sym);
                mi = getMethodInfo(sym);
                for (JCExpression pre: mi.requiresPredicates) {
                    addAssert(Label.PRECONDITION,trExpr(pre),decl.pos,newstatements,pos);
                }
            }


            // Save the current incarnation map, so that instances of \old in the
            // postconditions of the called method are mapped to values just before
            // the havoc of assigned variables (and not to the values at the beginning
            // of the method being translated).
            HashMap<VarSymbol,Integer> currentCopy = new HashMap<VarSymbol,Integer>();
            currentCopy.putAll(currentMap);
            oldMap = currentCopy;

            {

                // Now make a new incarnation value for anything in the assignables list,
                // effectively making its value something legal but undefined.
                for (JmlMethodInfo.Entry entry: mi.assignables) {
                    // What to do with preconditions?  FIXME
                    for (JCTree sr: entry.storerefs) {
                        if (sr instanceof JCIdent) {
                            JCIdent pid = (JCIdent)sr;
                            newIdentIncarnation(pid,pos+1); // new incarnation
                        } else if (sr instanceof JmlSingleton) {
                            if (((JmlSingleton)sr).token == JmlToken.BSNOTHING) {
                                // OK
                            } else {
                                System.out.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                            }
                        } else if (sr instanceof JmlStoreRefKeyword) {
                            if (((JmlStoreRefKeyword)sr).token == JmlToken.BSNOTHING) {
                                // OK
                            } else {
                                System.out.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                            }
                        } else {
                            System.out.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                        }
                    }
                }
            }
            
            addClassPredicate(that.clazz.type);

            JCIdent oldalloc = newIdentUse((VarSymbol)allocVar.sym,pos);
            JCIdent alloc = newIdentIncarnation(allocVar,pos);

            // assume <oldalloc> < <newalloc>
            JCExpression ee = makeBinary(JCTree.LT,oldalloc,alloc,pos);
            addAssume(Label.SYN,ee,newstatements,false);

            // assume <newid> != null;
            ee = makeBinary(JCTree.NE,id,nullLiteral,pos);
            addAssume(Label.SYN,ee,newstatements,false);

            // assume \typeof(<newid>) <: <declared type>
            ee = factory.at(pos).JmlMethodInvocation(JmlToken.BSTYPEOF,com.sun.tools.javac.util.List.<JCExpression>of(id));
            ee.type = syms.classType;
            JCLiteral lit = makeTypeLiteral(that.clazz.type,pos); // FIXME - type arguments?
            ee = makeBinary(JCTree.EQ,ee,lit,pos);
            addAssume(Label.SYN,ee,newstatements,false);
            
            // assume <newid>.alloc = <newalloc>
            ee = new JmlBBFieldAccess(allocIdent,id);  // FIXME pos, factory
            ee.pos = pos;
            ee.type = syms.intType;
            ee = makeBinary(JCTree.EQ,ee,alloc,pos);
            addAssume(Label.SYN,ee,newstatements,false);

            for (JCExpression post: mi.ensuresPredicates) {
                addAssume(Label.POSTCONDITION,trSpecExpr(post),newstatements,false);
            }
            if (!isHelper) {
                for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e);
                    addAssume(Label.INVARIANT,e,newstatements,false);
                }
                for (JmlTypeClauseExpr inv : classInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e);
                    addAssume(Label.INVARIANT,e,newstatements,false);
                }
            }
            // Take out the temporary variables for the arguments
            for (JCVariableDecl vd  : decl.params) {
                currentMap.remove((VarSymbol)vd.sym);
            }

            result = id;
        } finally {
            oldMap = prevOldMap;
            currentThisId = prevId;
            resultVar = prevResultVar;
        }
    }
    
    public void visitNewArray(JCNewArray that) { //that.dims, elems, elemtype
        // that.dims - the array of explicit dimensions, if they exist; empty list if the dimensions are implicit
        // that.elems - list of initializers
        // that.elemtype - the element type.  This includes all implicit dimensions
        //    but not the explicit ones.  So
        //       new boolean[][]           dims = empty list elems != null     elemtype = boolean[]    type = boolean[][]
        //       new boolean[3][]          dims = {3},       elems = null      elemtype = boolean[]    type = boolean[][]
        //       new boolean[3][5]         dims = {3,5}      elems = null,     elemtype = boolean      type = boolean[][]
        // This visit method is also called for the sub-initializers of an initializer, in which case, for example for the components of  { {1}, {2,3,4} }
        //                                 dims = empty list elems != null     elemtype = null         type = int[]
        
        // First translate the initializer if it exists, since it makes recursive calls
        List<JCExpression> newelems = null;
        if (that.elems != null) {
            newelems = new LinkedList<JCExpression>();
            for (JCExpression elem: that.elems) {
                newelems.add(trExpr(elem));
            }
        }
        
        // assume <oldalloc> < <newalloc>
        JCIdent oldalloc = newIdentUse((VarSymbol)allocVar.sym,that.pos);
        JCIdent alloc = newIdentIncarnation(allocVar,that.pos);
        JCExpression e = makeBinary(JCTree.LT,oldalloc,alloc,that.pos);
        addAssume(Label.SYN,e,newstatements,false);
        
        // assume <newarray> != null;
        JCIdent newarray = newAuxIdent("$$newarray$"+that.pos+"$",that.type,that.pos);
        e = makeBinary(JCTree.NE,newarray,nullLiteral,that.pos);
        addAssume(Label.SYN,e,newstatements,false);
        
        // assume <newarray>.alloc = <newalloc>
        e = new JmlBBFieldAccess(allocIdent,newarray);
        e.pos = that.pos;
        e.type = syms.intType;
        e = makeBinary(JCTree.EQ,e,alloc,that.pos);
        addAssume(Label.SYN,e,newstatements,false);
        
        List<JCExpression> dims = that.dims;
        int ndims = dims.size();
        Type arrayType = that.type;
        
        ListBuffer<JCExpression> types = ListBuffer.<JCExpression>lb();
        JCExpression intTypeTree = factory.at(that.pos).TypeIdent(TypeTags.INT);
        intTypeTree.type = syms.intType;
        ListBuffer<Name> inames = ListBuffer.<Name>lb();
        JCExpression range = trueLiteral;
        JCExpression access = null;
        
        if (newelems == null) {
            // no initializer, one or more dimensions given
            // FIXME - need to set the last elements to null
            
            int ind;
            for (ind = 0; ind<ndims; ind++) {

                JCExpression len = trExpr(that.dims.get(ind));
                if (ind == 0) {
                    // <newarray>.length == <len>
                    e = new JmlBBFieldAccess(lengthIdent,newarray);
                    e.pos = that.pos;
                    e.type = syms.intType;
                    e = makeBinary(JCTree.EQ,e,trExpr(len),that.pos);
                    access = newarray;
                } else {
                    // (forall (i1::int ...) <range> => (...( <newarray> i1 ) i2 ) ... in ).length == <len> )
                    types.append(intTypeTree);
                    Name nm = names.fromString("i"+ind);
                    JCIdent id = factory.at(that.pos).Ident(nm);
                    id.type = syms.intType;
                    inames.append(nm);
                    range = makeBinary(JCTree.AND, range,
                                makeBinary(JCTree.AND,
                                      makeBinary(JCTree.LE,zeroLiteral,id,that.pos),
                                      makeBinary(JCTree.LT,id,len,that.pos),
                                      that.pos),
                                that.pos);
                    arrayType = ((ArrayType)arrayType).elemtype;
                    JCIdent arraysID = getArrayIdent(arrayType);
                    access = new JmlBBArrayAccess(arraysID,access,id);
                    access.pos = that.pos;
                    access.type = arrayType;
                    JCExpression predicate = new JmlBBFieldAccess(lengthIdent,access);
                    predicate.pos = that.pos;
                    predicate.type = syms.intType;
                    predicate = makeBinary(JCTree.AND,
                                        makeBinary(JCTree.NE,access,nullLiteral,that.pos),
                                        makeBinary(JCTree.EQ,predicate,trExpr(len),that.pos),that.pos);
                    e = factory.at(that.pos).JmlQuantifiedExpr(JmlToken.BSFORALL,null,types,inames,range,predicate);
                }
                addAssume(Label.SYN,e,newstatements,false);
            }
            // (forall (i1::int ...) (...( <newarray> i1 ) i2 ) ... in ) != null )
            arrayType = ((ArrayType)arrayType).elemtype;
            if (arrayType instanceof ArrayType) {
                types.append(intTypeTree);
                Name nm = names.fromString("i"+ind);
                JCIdent id = factory.at(that.pos).Ident(nm);
                id.type = syms.intType;
                inames.append(nm);
                JCIdent arraysID = getArrayIdent(arrayType);
                access = new JmlBBArrayAccess(arraysID,access,id);
                access.pos = that.pos;
                access.type = arrayType;
                e = makeBinary(JCTree.EQ,access,nullLiteral,that.pos);
                e = factory.at(that.pos).JmlQuantifiedExpr(JmlToken.BSFORALL,null,types,inames,trueLiteral,e);
                addAssume(Label.SYN,e,newstatements,false);
            }
            

        } else {
            // an initializer, but no dimensions given

            int num = newelems.size();
            JCExpression len = makeLiteral(num,that.pos);

            // <newarray>.length == <len>
            e = new JmlBBFieldAccess(lengthIdent,newarray);
            e.pos = that.pos;
            e.type = syms.intType;
            e = makeBinary(JCTree.EQ,e,trExpr(len),that.pos);
            addAssume(Label.SYN,e,newstatements,false);

            int i = 0;
            for (JCExpression ee: newelems) {
                // create an assumption about each element of the new array, 
                // given the initializer value (which might be a new array itself)
                JCLiteral lit = makeLiteral(i++,ee.pos);
                e = new JmlBBArrayAccess(getArrayIdent(ee.type),newarray,lit);
                e.pos = ee.pos;
                e.type = ee.type;
                e = makeBinary(JCTree.EQ,e,ee,ee.pos);
                addAssume(Label.SYN,e,newstatements,false);
            }
        }
        result = newarray;
    }
    
    
    // FIXME
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
    
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        // This includes ghost local declarations
        // FIXME ??? ghost and model field declarations?
        // FIXME ??? java declarations?
        // FIXME - need to add various field specs tests
        JCIdent vd = newIdentIncarnation(that,that.pos);
        if (that.init != null) {
            int p = that.init.pos;
            boolean prevInSpecExpression = inSpecExpression;
            try {
                if (Utils.isJML(that.mods)) inSpecExpression = true;
                JCExpression ninit = trJavaExpr(that.init);
                JmlTree.JmlStatementExpr asm = factory.at(p).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,makeBinary(JCTree.EQ,vd,ninit,p));
                newstatements.add(asm);
            } finally {
                inSpecExpression = prevInSpecExpression;
            }
        }
    }
    
    public void visitJmlSingleton(JmlSingleton that) { 
        switch (that.token) {
            case BSRESULT:
                if (resultVar == null) {
                    throw new RuntimeException(); // FIXME - do something more informative - should not ever get here
                } else {
                    result = resultVar;
                }
                break;

            case INFORMAL_COMMENT:
                result = makeLiteral(true,that.pos);
                break;
                
            case BSEXCEPTION:
                if (exceptionVar == null) {
                    // FIXME -error
                    System.out.println("EXCEPTION VAR IS NULL");
                    result = null;
                } else {
                    result = newIdentUse((VarSymbol)exceptionVar.sym,that.pos);
                }
                break;
                
            case BSLOCKSET:
            case BSSAME:
            case BSNOTSPECIFIED:
            case BSNOTHING:
            case BSEVERYTHING:
                Log.instance(context).error(that.pos, "jml.unimplemented.construct",that.token.internedName(),"BasicBlocker.visitJmlSingleton");
                // FIXME - recovery possible?
                break;

            default:
                Log.instance(context).error(that.pos, "jml.unknown.construct",that.token.internedName(),"BasicBlocker.visitJmlSingleton");
            // FIXME - recovery possible?
                break;
        }
        //result = that; // TODO - can all of these be present in a basic block?
    }
    
//    public void visitJmlFunction(JmlFunction that) {
//        switch (that.token) {
//            case BSOLD :
//            case BSPRE :
//                // Handling of incarnation occurs later
//                result = that; 
//                break;
//                
//            case BSTYPEOF :
//            case BSELEMTYPE :
//            case BSNONNULLELEMENTS :
//            case BSMAX :
//            case BSFRESH :
//            case BSREACH :
//            case BSSPACE :
//            case BSWORKINGSPACE :
//            case BSDURATION :
//            case BSISINITIALIZED :
//            case BSINVARIANTFOR :
//            case BSNOWARN:
//            case BSNOWARNOP:
//            case BSWARN:
//            case BSWARNOP:
//            case BSBIGINT_MATH:
//            case BSSAFEMATH:
//            case BSJAVAMATH:
//            case BSNOTMODIFIED:
//            case BSTYPELC:
//                Log.instance(context).error("esc.not.implemented","Not yet implemented token in BasicBlocker: " + that.token.internedName());
//                result = trueLiteral; // FIXME - may not even be a boolean typed result
//                break;
//
//            default:
//                Log.instance(context).error("esc.internal.error","Unknown token in BasicBlocker: " + that.token.internedName());
//                result = trueLiteral; // FIXME - may not even be a boolean typed result
//        }
//    }

    public void visitJmlBinary(JmlBinary that) { 
        JCExpression left = trExpr(that.lhs);
        JCExpression right;
        if (that.op == JmlToken.IMPLIES) {
            JCExpression prev = condition;
            try {
                condition = makeBinary(JCTree.AND,condition,left,that.lhs.pos);
                right = trExpr(that.rhs);
            } finally {
                condition = prev;
            }
        } else if (that.op == JmlToken.REVERSE_IMPLIES) {
            // This is rhs=>lhs, which is equivalent to lhs || !rhs
            // The short-circuit semantics is  (lhs ? true : !rhs)   [ instead of ( !rhs ? true : lhs) ]
            JCExpression prev = condition;
            try {
                condition = makeBinary(JCTree.AND,condition,makeUnary(JCTree.NOT,left,that.lhs.pos),that.lhs.pos);
                right = trExpr(that.rhs);
            } finally {
                condition = prev;
            }
        } else {
            right = trExpr(that.rhs);
        }

        JmlBinary now = makeJmlBinary(that.op,left,right,that.pos);
        now.op = that.op;
        now.type = that.type;
        result = now;
    }
    
    // FIXME - how are these checked for definedness?
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        JmlToken op = that.op;
        if (op == JmlToken.BSFORALL || op == JmlToken.BSEXISTS) {
            JCExpression prevCondition = condition;
            try {
                JCExpression range = trExpr(that.range);
                condition = makeBinary(JCTree.AND,condition,range,condition.pos);
                JCExpression predicate = trExpr(that.predicate);
                JmlQuantifiedExpr now = factory.at(that.pos).JmlQuantifiedExpr(op,that.modifiers,that.localtypes,that.names,range,predicate);
                now.type = that.type;
                result = now;
            } finally {
                condition = prevCondition;
            }
        } else {
            result = trueLiteral;
            notImpl(that);
        }
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) { notImpl(that); }
    
    public void visitJmlLblExpression(JmlLblExpression that) {
        String n = "$$" + that.token.toString().substring(2) + "$" + that.pos + "$" + that.label;
        JCIdent id = newAuxIdent(n,that.type,that.pos);
        JCExpression e = makeBinary(JCTree.EQ,id,trExpr(that.expression),that.pos);
        JmlStatementExpr asm = factory.at(that.getStartPosition()).JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);
        newstatements.add(asm);
        result = id;
    }
    
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that){ notImpl(that); }
    public void visitJmlGroupName(JmlGroupName that)               { notImpl(that); }
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that)         { notImpl(that); }
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that)     { notImpl(that); }
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that)     { notImpl(that); }
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that)     { notImpl(that); }
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) { notImpl(that); }
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) { notImpl(that); }
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) { notImpl(that); }
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) { notImpl(that); }
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) { notImpl(that); }
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) { notImpl(that); }
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) { notImpl(that); }
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) { notImpl(that); }
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) { notImpl(that); }
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) { notImpl(that); }
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) { notImpl(that); }
    public void visitJmlMethodClauseAssignable(JmlMethodClauseAssignable that) { notImpl(that); }
    public void visitJmlSpecificationCase(JmlSpecificationCase that){ notImpl(that); }
    public void visitJmlMethodSpecs(JmlMethodSpecs that)           {  } // FIXME - IGNORE NOT SURE WHY THIS IS ENCOUNTERED IN CLASS.defs
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that){ notImpl(that); }
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that)   { notImpl(that); }
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that){ notImpl(that); }

    // These do not need to be implemented
    public void visitTopLevel(JCCompilationUnit that)    { shouldNotBeCalled(that); }
    public void visitImport(JCImport that)               { shouldNotBeCalled(that); }
    public void visitJmlCompilationUnit(JmlCompilationUnit that)   { shouldNotBeCalled(that); }
    public void visitJmlRefines(JmlRefines that)                   { shouldNotBeCalled(that); }
    public void visitJmlImport(JmlImport that)                     { shouldNotBeCalled(that); }

    public void visitClassDef(JCClassDecl that) {
        System.out.println("YES THIS IS CALLED - visitClassDef");
//        scan(tree.mods);
//        scan(tree.typarams);
//        scan(tree.extending);
//        scan(tree.implementing);
        scan(that.defs); // FIXME - is this ever called for top level class; is it correct for a class definition statement?
    }
    
    @Override
    public void visitMethodDef(JCMethodDecl that)        { notImpl(that); }
    
    //public void visitJmlClassDecl(JmlClassDecl that) ; // OK to inherit - FIXME - when called?
 
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        System.out.println("YES THIS IS CALLED - visitJMLMethodDecl");
        //convertMethodBody(that.body); // FIXME - do the proof?? // Is it ever called? in local classes?
    }
    

    // FIXME - this will go away
    public static class VarFinder extends JmlTreeScanner {
        
        private Set<JCIdent> vars; // FIXME - change to a collection?
        
        public VarFinder() {}
        
        public static Set<JCIdent> findVars(List<? extends JCTree> that, Set<JCIdent> v) {
            VarFinder vf = new VarFinder();
            return vf.find(that,v);
        }
        
        public static Set<JCIdent> findVars(JCTree that, Set<JCIdent> v) {
            VarFinder vf = new VarFinder();
            return vf.find(that,v);
        }
        
        public Set<JCIdent> find(List<? extends JCTree> that, Set<JCIdent> v) {
            if (v == null) vars = new HashSet<JCIdent>();
            else vars = v;
            for (JCTree t: that) t.accept(this);
            return vars;
        }
        
        public Set<JCIdent> find(JCTree that, Set<JCIdent> v) {
            if (v == null) vars = new HashSet<JCIdent>();
            else vars = v;
            that.accept(this);
            return vars;
        }
        
        public void visitIdent(JCIdent that) {
            vars.add(that);
        }
    } 
    
    /** This class is a tree walker that finds any references to classes in the
     * tree being walked: types of anything, explicit type literals
     * 
     * @author David Cok
     *
     */
    public static class ClassFinder extends JmlTreeScanner {
        
        private Set<Type> types;
        
        public ClassFinder() {}
        
        public static Set<Type> findS(List<? extends JCTree> that, Set<Type> v) {
            ClassFinder vf = new ClassFinder();
            return vf.find(that,v);
        }
        
        public static Set<Type> findS(JCTree that, Set<Type> v) {
            ClassFinder vf = new ClassFinder();
            return vf.find(that,v);
        }
        
        public Set<Type> find(List<? extends JCTree> that, Set<Type> v) {
            if (v == null) types = new HashSet<Type>();
            else types = v;
            for (JCTree t: that) t.accept(this);
            return types;
        }
        
        public Set<Type> find(JCTree that, Set<Type> v) {
            if (v == null) types = new HashSet<Type>();
            else types = v;
            that.accept(this);
            return types;
        }
        
        // visitAnnotation  - FIXME

        // visitApply - expression: just scan the component expressions
        // visitAssert - statement: just scan the component expressions
        // visitAssign - no new types - just scan the component expressions
        // visitAssignOp - no new types - just scan the component expressions
        // visitBinary - only primitive types
        // visitBlock - statement: just scan the component expressions
        // visitBreak - statement: just scan the component expressions
        // visitCase - statement: just scan the component expressions
        // visitCatch - statement: just scan the component expressions - FIXME - make sure to get the declaration
        // visitClassDef - FIXME ???
        // visitConditional - no new types - just scan the component expressions
        // visitContinue - statement: just scan the component expressions
        // visitDoLoop - statement: just scan the component expressions
        // visitErroneous - statement: just scan the component expressions
        // visitExec - statement: just scan the component expressions
        // visitForEachLoop - statement: just scan the component expressions - FIXME - implied iterator?
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
        // visitSwitch - statement: just scan the component expressions (FIXME _ might be an Enum)
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
        // visitJmlMethodClause... - scan all component expressions - FIXME : watch Decls, Signals, SigOnly
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
        // visitJmlTypeClause... - scan all components - FIXME - is there more to do?
        // visitJmlVariableDecl - FIXME??
        // visitJmlWhileLoop - FIXME - be sure to scan specs
        
        // FIXME - some things that can probably always be counted on: Object, String, Class
        // FIXME - closure of super types and super interfaces 
    } 
    

    /** This class is a tree walker that finds everything that is the target of
     * a modification in the tree being walked: assignments, assignment-ops, 
     * increment and decrement operators, fields specified as modified by a
     * method call.
     * 
     * FIXME - is the tree already in reduced BasicBlock form?
     * 
     * @author David Cok
     *
     */
    public static class TargetFinder extends JmlTreeScanner {
        
        private List<JCExpression> vars;
        
        public TargetFinder() {}
        
        public static List<JCExpression> findVars(JCTree that, List<JCExpression> v) {
            TargetFinder vf = new TargetFinder();
            return vf.find(that,v);
        }
        
        public static List<JCExpression> findVars(Iterable<? extends JCTree> list, List<JCExpression> v) {
            TargetFinder vf = new TargetFinder();
            return vf.find(list,v);
        }
        
        public List<JCExpression> find(Iterable<? extends JCTree> list, List<JCExpression> v) {
            if (v == null) vars = new ArrayList<JCExpression>();
            else vars = v;
            for (JCTree t: list) t.accept(this);
            return vars;
        }
        
        public List<JCExpression> find(JCTree that, List<JCExpression> v) {
            if (v == null) vars = new ArrayList<JCExpression>();
            else vars = v;
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
            if (op == JCTree.POSTDEC || op == JCTree.POSTINC ||
                    op == JCTree.PREINC || op == JCTree.PREDEC)
                vars.add(that.getExpression());
        }
        
        // FIXME - also need targets of method calls, update statements of loops,
        // initialization statements of loops

    } 

    /** A Map that caches class info for a given class symbol */
    @NonNull Map<Symbol,JmlClassInfo> classInfoMap = new HashMap<Symbol,JmlClassInfo>();

    /** Returns the jmlClassInfo structure for a class, computing and caching 
     * it if necessary.
     * @param cls the declaration whose info is desired
     * @return the corresponding JmlClassInfo structure; may be null if the
     *   argument has no associated symbol
     */
    //@ modifies (* contents of the classInfoMap *);
    //@ ensures cls.sym != null <==> \result != null;
    @Nullable JmlClassInfo getClassInfo(@NonNull JCClassDecl cls) {
        JmlClassInfo mi = classInfoMap.get(cls.sym);
        if (mi == null) {
            mi = computeClassInfo(cls.sym);
            classInfoMap.put(cls.sym,mi);
        }
        return mi;
    }
    
    /** Returns the JmlClassInfo structure for the given Class Symbol,
     * computing and caching it if necessary
     * @param sym the Symbol for the class whose JmlClassInfo is wanted
     * @return the corresponding JmlClassInfo structure, null if sym is null
     */
    @Nullable JmlClassInfo getClassInfo(@NonNull Symbol sym) {
        ClassSymbol csym = (ClassSymbol)sym;
        JmlClassInfo mi = classInfoMap.get(sym);
        if (mi == null) {
            mi = computeClassInfo(csym);
            classInfoMap.put(sym,mi);
        }
        return mi;
    }
    
    /** Computes the class information for a given class declaration.
     * @param csym the ClassSymbol for which to get JmlClassInfo
     * @return the corresponding JmlClassInfo
     */
    //@ ensures sym != null <==> \result != null;
    protected @Nullable JmlClassInfo computeClassInfo(@NonNull ClassSymbol csym) {
        TypeSpecs typeSpecs = specs.get(csym);
        if (typeSpecs == null) {  // FIXME - when might this happen
            System.out.println("UNEXPECTEDLY NO TYPE SPECS " + csym);
            return null;
        }
        JCClassDecl tree = typeSpecs.decl;
        if (tree == null) {
            System.out.println("UNEXPECTEDLY NO DECL " + csym);
        }
        JmlClassInfo classInfo = new JmlClassInfo(tree);
        classInfo.typeSpecs = typeSpecs;
        classInfo.csym = csym;
        
        // FIXME - this comment makes no sense since we do not change anything in the ast

        // Remove any non-Java declarations from the Java AST before we do translation
        // After the superclass translation, we will add back in all the JML stuff.
//        ListBuffer<JCTree> newlist = new ListBuffer<JCTree>();
//        for (JCTree tt: tree.defs) {
//            if (tt == null || tt.getTag() >= JmlTree.JMLFUNCTION) {
//                // skip it
//            } else {
//                newlist.append(tt);
//            }
//        }
        
        Type type = csym.getSuperclass();
        classInfo.superclassInfo = (csym == syms.objectType.tsym) ? null : getClassInfo(type.tsym);

        // Divide up the various type specification clauses into the various types
        ListBuffer<JmlTypeClauseRepresents> represents = new ListBuffer<JmlTypeClauseRepresents>();
        ListBuffer<JCVariableDecl> modelFields = new ListBuffer<JCVariableDecl>();

        if (typeSpecs != null) for (JmlTypeClause c: typeSpecs.clauses) {
            boolean isStatic = c.modifiers != null && (c.modifiers.flags & Flags.STATIC) != 0;
            if (c instanceof JmlTypeClauseDecl) {
                JCTree tt = ((JmlTypeClauseDecl)c).decl;
                if (tt instanceof JCVariableDecl && ((JmlAttr)Attr.instance(context)).isModel(((JCVariableDecl)tt).mods)) {
                    // model field - find represents or make into abstract method
                    modelFields.append((JCVariableDecl)tt);
                } else {
                    // ghost fields, model methods, model classes are used as is
                    //newlist.append(tt);
                }
            } else {
                JmlToken token = c.token;
                if (token == JmlToken.INVARIANT) {
                    if (isStatic) classInfo.staticinvariants.add((JmlTypeClauseExpr)c);
                    else          classInfo.invariants.add((JmlTypeClauseExpr)c);
                } else if (token == JmlToken.REPRESENTS) {
                    JmlTypeClauseRepresents r = (JmlTypeClauseRepresents)c;
                    represents.append(r);
                } else if (token == JmlToken.CONSTRAINT) {
                    if (isStatic) classInfo.staticconstraints.add((JmlTypeClauseConstraint)c);
                    else          classInfo.constraints.add((JmlTypeClauseConstraint)c);
                } else if (token == JmlToken.INITIALLY) {
                    classInfo.initiallys.add((JmlTypeClauseExpr)c);
                } else if (token == JmlToken.AXIOM) {
                    classInfo.axioms.add((JmlTypeClauseExpr)c);
                } else {
                    Log.instance(context).warning("esc.not.implemented","JmlEsc does not yet implement (and ignores) " + token.internedName());
                    // FIXME - readable if, writable if, monitors for, in, maps, initializer, static_initializer, (model/ghost declaration?)
                }
            }
        }
        return classInfo;
    }

    /** This class converts a counterexample into more readable information */
    public static class Tracer extends JmlTreeScanner {
        
        /** The compilation context */
        @NonNull Context context;
        
        /** The counterexample information */
        @NonNull ICounterexample ce;
        
        /** The log for output */
        @NonNull Log log;
        
        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
        private static class ReturnException extends RuntimeException {
            private static final long serialVersionUID = -3475328526478936978L;}
        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
        private static class ExException extends RuntimeException {
            private static final long serialVersionUID = -5610207201211221750L;}
        
        /** Outputs the counterexample information in more readable form
         * @param context the compilation context
         * @param decl the method declaration 
         * @param s the counterexample information to translate
         */
        public static void trace(@NonNull Context context, @NonNull JCMethodDecl decl, @NonNull ICounterexample s) {
            try {
                decl.accept(new Tracer(context,s));
            } catch (ReturnException e) {
                // ignore
            } catch (ExException e) {
                // ignore
            } catch (RuntimeException e) {
                System.out.println("FAILED : " + e);
            }
            System.out.println("END");
        }
        
        /** Translates the given position information into source, line and column information 
         * @param pos the position information to translate
         * @return A String containing human-readable source location information
         */
        public String getPosition(int pos) {
            return log.currentSource().getName() + ":" + log.getLineNumber(pos) + " (col " + log.getColumnNumber(pos) + "): ";
        }
        
        /** The constructor for this class
         * @param context the compilation context
         * @param s the counterexample information
         */
        protected Tracer(@NonNull Context context, @NonNull ICounterexample s) {
            this.context = context;
            ce = s;
            log = Log.instance(context);
        }
        
        // CAUTION: The Strings in use in these visit methods correspond to the
        // encoding used in the BasicBlocker methods.  The BasicBlocker encodes
        // variables using combinations of variable name, declaration position,
        // and incarnation position.  These are reflected in the counterexample 
        // information and we need to match that as we interpret the counterexample
        // information in these methods.
        
        // FIXME - this implementation needs fleshing out
        
        public void visitMethodDef(JCMethodDecl that) {
            System.out.println("START METHOD " + that.sym);
            for (JCVariableDecl param: that.params) {
                String s = param.name + "$" + param.pos + "$0";
                String value = ce.get(s);
                System.out.println("Parameter value: " + param.name + " = " + (value == null ? "<unused>" : value));
            }
            super.visitMethodDef(that);
        }
        
        public void visitIf(JCIf that) {
            String s = "branchCondition$" + that.pos + "$" + 0;
            String value = ce.get(s);
            if (value == null) System.out.println(getPosition(that.pos) + "!!!  Could not find value for branch ("+s+")");
            else {
                System.out.println(getPosition(that.pos) + "Branch condition value: " + value);
                if (value.equals("true")) {
                    if (that.thenpart != null) that.thenpart.accept(this);
                } else if (value.equals("false")) {
                    if (that.elsepart != null) that.elsepart.accept(this);
                } else {
                    System.out.println("!!! Unknown value: " + value);
                }
            }
        }
        
        public void visitAssign(JCAssign that) {
            if (that.lhs instanceof JCIdent) {
                JCIdent id = (JCIdent)that.lhs;
                String s = id.name + "$" + ((VarSymbol)id.sym).pos + "$" + that.pos;
                String value = ce.get(s);
                if (value == null) System.out.println(getPosition(that.pos) + "!!!  Could not find value for variable ("+s+")");
                else System.out.println(getPosition(that.pos) + "Assignment: " + id.name + " = " + value);
            }
        }
        
        public void visitTry(JCTry that) {
            try {
                that.body.accept(this);
            } catch (ReturnException e) {
                // do the finally block
                if (that.finalizer != null) {
                    System.out.println(getPosition(that.finalizer.pos) + "Executing finally block");
                    that.finalizer.accept(this);
                }
                throw e;
            } catch (ExException e) {
                // FIXME
            }
        }
        
        public void visitReturn(JCReturn that) {
            String s = "$$result";
            String value = ce.get(s);
            if (that.expr != null) {
                if (value == null) System.out.println(getPosition(that.pos) + "!!!  Could not find return value ("+s+")");
                else System.out.println(getPosition(that.pos) + "Executed return: value = " + value);
            } else {
                System.out.println(getPosition(that.pos) + "Executed return");
            }
            throw new ReturnException();
        }
    } 
    

    /** This class converts a counterexample into more readable information;
     * it uses the basic program form rather than using the Java AST. */
    public static class TracerBB extends JmlTreeScanner {
        
        /** The counterexample information */
        ICounterexample ce;
        
        /** The log for output */
        @NonNull Log log;
        
        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
        private static class ReturnException extends RuntimeException {
            private static final long serialVersionUID = -3475328526478936978L;}
        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
        private static class ExException extends RuntimeException {
            private static final long serialVersionUID = -5610207201211221750L;}
        
        /** Outputs the counterexample information in more readable form
         * @param context the compilation context
         * @param decl the method declaration 
         * @param ce the counterexample information to translate
         */
        public static void trace(@NonNull Context context, @NonNull BasicProgram program, @NonNull ICounterexample ce) {
            try {
                (new TracerBB(context)).trace(program,ce);
            } catch (ReturnException e) {
                // ignore
            } catch (ExException e) {
                // ignore
            } catch (RuntimeException e) {
                System.out.println("FAILED : " + e);
            }
            System.out.println("END");
        }
        
        /** Translates the given position information into source, line and column information 
         * @param pos the position information to translate
         * @return A String containing human-readable source location information
         */
        public String getPosition(int pos) {
            return log.currentSource().getName() + ":" + log.getLineNumber(pos) + " (col " + log.getColumnNumber(pos) + "): ";
        }
        
        /** The constructor for this class
         * @param context the compilation context
         * @param s the counterexample information
         */
        protected TracerBB(@NonNull Context context) {
            log = Log.instance(context);
        }
        
        public void trace(@NonNull BasicProgram program, ICounterexample ce) {
            this.ce = ce;
            BasicBlock block = program.startBlock();
            outer: while (traceBlockStatements(block)) {
                for (BasicBlock next: block.succeeding()) {
                    String s = next.id().toString();
                    String value = ce.get(s);
                    if (value.equals("false")) {
                        block = next;
                        continue outer;
                    }
                }
                break;
            }
        }
        
        // CAUTION: The Strings in use in these visit methods correspond to the
        // encoding used in the BasicBlocker methods.  The BasicBlocker encodes
        // variables using combinations of variable name, declaration position,
        // and incarnation position.  These are reflected in the counterexample 
        // information and we need to match that as we interpret the counterexample
        // information in these methods.
        
        protected boolean traceBlockStatements(BasicBlock b) {
            System.out.println(" [ block " + b.id() + " ]");
            for (JCStatement statement: b.statements) {
                if (!(statement instanceof JmlStatementExpr)) {
                    log.error(statement.pos,"esc.internal.error","Incorrect statement type in traceBlockStatements: " + statement.getClass());
                    continue;
                }
                JmlStatementExpr s = (JmlStatementExpr)statement;
                JCExpression expr = s.expression;
                String pos = getPosition(s.pos);
                Label label = s.label;
                if (s.token == JmlToken.ASSUME) {
                    if (label == Label.ASSIGNMENT) {
                        // FIXME - array, field assignments
                        if (expr instanceof JCBinary) {
                            JCExpression target = ((JCBinary)expr).lhs;
                            if (target instanceof JCIdent) {
                                JCIdent lhs = (JCIdent)target;
                                String value = ce.get(lhs.name.toString());
                                System.out.println(pos + "Assign " + lhs + " = " + value);
                            }
                        } else if (expr instanceof JmlBBArrayAssignment){
                            JmlBBArrayAssignment lhs = (JmlBBArrayAssignment)expr;
                            System.out.println(pos + "JmlBBArrayAssignment " + lhs); // FIXME

                        } else {
                            System.out.println(pos + "Assign " + expr); // FIXME
                        }
                    } else if (label == Label.SYN) {  // FIXME - rename the SYN types that are wanted
                        if (expr instanceof JCBinary) {
                            JCExpression lhs = ((JCBinary)expr).lhs;
                            if (lhs instanceof JCIdent) {
                                String value = ce.get(((JCIdent)lhs).name.toString());
                                System.out.println(pos + "Syn " + lhs + " = " + value);
                            } else {
                                System.out.println(pos + "Syn " + lhs + " : " + lhs.getClass());
                            }
                        }
                    } else if (label == Label.EXPLICIT_ASSUME) {
                        if (expr instanceof JCIdent) {
                            String n = ((JCIdent)expr).name.toString();
                            String value = ce.get(n);
                            System.out.println(pos + "Assume " + n + " = " + value);
                        } else {
                            System.out.println(pos + "Assume " + label + " " + expr);
                        }
                    } else {
                        System.out.println(pos + "Assume " + label + " " + expr);
                    }
                } else if (s.token == JmlToken.ASSERT) {
                    if (label == Label.EXPLICIT_ASSERT) {
                        if (expr instanceof JCIdent) {
                            String v = ((JCIdent)expr).toString();
                            String value = ce.get(v);
                            //System.out.println(pos + "Assert " + value);
                            System.out.println(pos + "Assert " + v + " " + value);
                            if ("false".equals(value)) return false;
                        } else {
                            System.out.println(pos + "Assert " + label + " " + expr);
                        }
                    } else {
                        System.out.println(pos + "Assert " + label + " " + expr);
                    }
                } else {
                    log.error(pos,"esc.internal.error","Incorrect token type in traceBlockStatements: " + s.token.internedName());
                }
            }
            return true;
        }
    }
}
