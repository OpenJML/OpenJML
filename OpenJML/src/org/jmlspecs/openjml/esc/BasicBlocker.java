package org.jmlspecs.openjml.esc;

import static com.sun.tools.javac.code.TypeTags.CLASS;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.*;


import org.jmlspecs.openjml.JmlInternalError;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.provers.YicesProver;

import org.jmlspecs.annotation.*;

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
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

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
        this.log = Log.instance(context);
        this.factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        
        unique = 0;
        
        trueLiteral = factory.Literal(TypeTags.BOOLEAN,1);
        trueLiteral.type = syms.booleanType;
        falseLiteral = factory.Literal(TypeTags.BOOLEAN,0);
        falseLiteral.type = syms.booleanType;
        nullLiteral = factory.at(0).Literal(TypeTags.BOT,0);
        nullLiteral.type = syms.objectType; // FIXME - object type?
        zeroLiteral = makeLiteral(0,0);
        zeroLiteral.type = syms.intType;
        
        // This is the field name used to access the allocation time of an object
        allocIdent = newAuxIdent(ALLOC_VAR,syms.intType,0,false);
        allocSym = (VarSymbol)allocIdent.sym; //newAuxVarSym(0,ALLOC_VAR,syms.intType);

        terminationSym = newAuxVarSym(0,TERMINATION_VAR,syms.intType);
        
        lengthIdent = factory.at(0).Ident(syms.lengthVar.name);
        lengthIdent.sym = syms.lengthVar;
        lengthIdent.type = syms.lengthVar.type;
        lengthSym = syms.lengthVar;

        //currentThisId = newAuxIdent(names._this,syms.objectType,0,false); // FIXME - object type?
    }
    
    static public final String ASSUMPTION_PREFIX = "$assumption";
    
    // THE FOLLOWING FIELDS ARE EXPECTED TO BE CONSTANT FOR THE LIFE OF THE OBJECT
    // They are either initialized in the constructor or initialized on first use
    
    /** The compilation context */
    @NonNull protected Context context;
    
    @NonNull protected Log log;
    
    /** The specifications database for this compilation context, initialized in the constructor */
    @NonNull protected JmlSpecs specs;
    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull protected Symtab syms;
    
    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull protected Names names;
    
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

    /** Symbol of a synthesized object field holding the allocation time of the object, initialized in the constructor */
    @NonNull protected VarSymbol terminationSym;

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
    
    /** The program being constructed */
    protected BasicProgram program = null;
    
    protected JCExpression resultVar = null;
    protected JCIdent exceptionVar = null;
    protected JCIdent signalsVar = null; //Used when translating a signals clause
    protected JCIdent heapVar;
    protected JCIdent terminationVar;  // 0=no termination requested; 1=return executed; 2 = exception happening
    
    protected JCIdent assumeCheckCountVar;
    protected int assumeCheckCount; 
    
    protected int unique;
    
    /** Holds the result of any of the visit methods that produce JCExpressions, since the visitor
     * template used here does not have a return value.  [We could have used the templated visitor,
     * but other methods do not need to return anything, we don't need the additional parameter,
     * and that visitor is complicated by the use of interfaces for the formal parameters.]
     */
    private JCExpression result;
    
    /** A mapping from BasicBlock to the sym->incarnation map giving the map that
     * FIXME !!!!.  FIXME - change this to a map to the new JCIdent
     */
    @NonNull protected Map<BasicBlock,VarMap> blockmaps = new HashMap<BasicBlock,VarMap>();
    
    /** A mapping from labels to the sym->incarnation map operative at the position
     * of the label.
     */
    @NonNull protected Map<Name,VarMap> labelmaps = new HashMap<Name,VarMap>();
    
    /** A mapping from labels to the sym->incarnation map operative at the position
     * of the label.
     */
    @NonNull protected Map<Name,JCTree> labelmapStatement = new HashMap<Name,JCTree>();
    
    public static class VarMap {
        
        private Map<VarSymbol,Integer> map = new HashMap<VarSymbol,Integer>();
        private Map<VarSymbol,Name> mapn = new HashMap<VarSymbol,Name>();
        int everythingIncarnation = 0;
        
        public VarMap copy() {
            VarMap v = new VarMap();
            v.map.putAll(this.map);
            v.mapn.putAll(this.mapn);
            v.everythingIncarnation = this.everythingIncarnation;
            return v;
        }
        
        public Name getName(VarSymbol vsym) {
            Name s = mapn.get(vsym);
            return s;
        }
        
        public Integer get(VarSymbol vsym) {
            Integer i = map.get(vsym);
            if (i == null) {
                i = everythingIncarnation;
                map.put(vsym,i);
            }
            return i;
        }
        
        public void put(VarSymbol vsym, Integer i, Name s) {
            map.put(vsym,i);
            mapn.put(vsym,s);
        }
        
        public void putAll(VarMap m) {
            map.putAll(m.map);
            mapn.putAll(m.mapn);
            everythingIncarnation = m.everythingIncarnation;
        }
        
        public Integer remove(VarSymbol v) {
            mapn.remove(v);
            return map.remove(v);
        }
        
        public Set<VarSymbol> keySet() {
            return map.keySet();
        }
        
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
            s.append("]");
            return s.toString();
        }
    }
    /** The map from symbol to incarnation number in current use */
    @NonNull protected VarMap currentMap;
    
    /** The mapping of variables to incarnations to use when in the scope of an \old */
    @NonNull protected VarMap oldMap = new VarMap();

    /** The class info block when walking underneath a given class. */
    JmlClassInfo classInfo;
    
    // THE FOLLOWING ARE ALL FIXED STRINGS
    
    //-----------------------------------------------------------------
    // Names for a bunch of synthetic variables 
    /** Standard name for the variable that tracks termination */
    public static final @NonNull String TERMINATION_VAR = "_terminationVar$$";
    
    /** Standard name for the variable that represents the heap (which exclued local variables) */
    public static final @NonNull String HEAP_VAR = "_heap$$";
    
    /** Standard name for the variable that tracks allocations */
    public static final @NonNull String ALLOC_VAR = "_alloc$$";
    
    //-----------------------------------------------------------------
    // Names for various basic blocks
    
    public static final @NonNull String blockPrefix = "_$BL$";
    
    /** Standard name for the block that starts the body */
    public static final @NonNull String BODY_BLOCK_NAME = blockPrefix + "bodyBegin";
    
    /** Standard name for the starting block of the program (just has the preconditions) */
    public static final @NonNull String START_BLOCK_NAME = blockPrefix + "Start";
    
    /** Standard name for the return block, whether or not a value is returned */
    public static final @NonNull String RETURN_BLOCK_NAME = blockPrefix + "return";
    
    /** Standard name for the postcondition block, whether or not a value is returned */
    public static final @NonNull String COND_RETURN_BLOCK_NAME = blockPrefix + "condReturn";
    
    /** Standard name for the exception block */
    public static final @NonNull String EXCEPTION_BLOCK_NAME = blockPrefix + "exception";
    
    /** Standard name for the conditional exception block */
    public static final @NonNull String COND_EXCEPTION_BLOCK_NAME = blockPrefix + "condException";
    
    // METHODS
    
    /** Should not need this when everything is implemented */
    protected void notImpl(JCTree that) {
        log.noticeWriter.println("NOT IMPLEMENTED: BasicBlocker - " + that.getClass());
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
    
    protected JCVariableDecl makeVariableDecl(Name name, Type type, int pos) {
        VarSymbol vsym = new VarSymbol(0, name, type, null);
        vsym.pos = pos;
        JCVariableDecl decl = factory.at(pos).VarDef(vsym,null);
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
        return names.fromString(sym.getQualifiedName() + (sym.pos < 0 ? "$" : ("$" + sym.pos + "$")) + incarnationPosition + "$" + (unique++));
    }
    
    protected Name encodedNameNoUnique(VarSymbol sym, int incarnationPosition) {
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
        return names.fromString(sym.getQualifiedName() + (declpos < 0 ? "$" : ("$" + declpos + "$")) + incarnationPosition ); //+ "$" + (unique++));
    }
    
    /** Creates an identifier nodes for a new incarnation of the variable, that is,
     * when the variable is assigned to.
     * @param id the old identifier, giving the root name, symbol and type
     * @param incarnationPosition the position (and incarnation number) of the new variable
     * @return the new identifier
     */
    protected JCIdent newIdentIncarnation(JCIdent id, int incarnationPosition) {
        return newIdentIncarnation((VarSymbol)id.sym,incarnationPosition);
//        JCIdent n = factory.at(incarnationPosition).Ident(encodedName((VarSymbol)id.sym,incarnationPosition));
//        copyInfo(n,id);
//        currentMap.put((VarSymbol)id.sym,incarnationPosition,n.name);
//        return n;
    }
    
    protected JCIdent newIdentIncarnation(VarSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedName(vsym,incarnationPosition));
        n.type = vsym.type;
        n.sym = vsym;
        //.println("NEW INCARNATION " + vsym + " " + incarnationPosition + " " + n.name);
        currentMap.put(vsym,incarnationPosition,n.name);
        return n;
    }
    
    // FIXME - document
    protected JCIdent newArrayIncarnation(Type componentType, int usePosition) {
        JCIdent id = getArrayIdent(componentType);
        id = newIdentIncarnation((VarSymbol)id.sym,usePosition);
        //currentMap.put((VarSymbol)id.sym,Integer.valueOf(usePosition),id.name);
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
        Name name = currentMap.getName(sym);
        if (name != null) {
            JCIdent n = factory.at(useposition).Ident(name);
            n.sym = sym;
            n.type = sym.type;
            return n;
        }
        JCIdent n = factory.at(useposition).Ident(encodedName(sym,incarnation));
        n.sym = sym;
        n.type = sym.type;
        currentMap.put(sym,incarnation,n.name);
        return n;
    }
    
    protected JCIdent newIdentUse(VarSymbol sym, Name name, int useposition) {
        if (name != null) {
            JCIdent n = factory.at(useposition).Ident(name);
            n.sym = sym;
            n.type = sym.type;
            return n;
        }
        JCIdent n = factory.at(useposition).Ident(encodedNameNoUnique(sym,0));
        n.sym = sym;
        n.type = sym.type;
        currentMap.put(sym,0,n.name);
        return n;
    }
    
    /** Creates an identifier node for a use of a variable at a given source code
     * position; the current incarnation value is used
     * @param sym the underlying symbol (which gives the declaration location)
     * @param useposition the source position of its use
     * @return
     */
    protected JCIdent newIdentUse(VarSymbol sym, int useposition) {
        Name name = currentMap.getName(sym);
        if (name != null) {
            JCIdent n = factory.at(useposition).Ident(name);
            n.sym = sym;
            n.type = sym.type;
            return n;
        }
        Integer iipos = currentMap.get(sym);
        Integer ipos = iipos == null ? 0 : iipos; 
        JCIdent n;
        if (sym.pos < 0) {
            n = factory.at(useposition).Ident(sym.name);
            n.sym = sym;
            n.type = sym.type;
        } else {
            n = factory.at(useposition).Ident(encodedNameNoUnique(sym,ipos));
            n.sym = sym;
            n.type = sym.type;
        }
        if (iipos == null) currentMap.put(sym,ipos,n.name);
        return n;
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
        currentMap.put((VarSymbol)id.sym,incarnation,n.name);
        return n;
    }
    
    /** Creates a new variable representing an auxiliary variable, for use as a
     * logical variable in the basic program; this is a one-time
     * defined variable - it may not be assigned to again (and thus has no
     * future incarnations)  FIXME - is that true for all uses?
     * The VarSymbol associated with the JCIdent has a declaration position of
     * -1 (to indicate it should not have incarnations).
     * @param name the full name of the variable, including any position encoding
     * @param type the type of the variable
     * @param pos the position to assign as its pseudo-location of use
     * @return
     */ 
    protected JCIdent newAuxIdent(@NonNull String name, @NonNull Type type, int pos, boolean incarnations) {
        return newAuxIdent(names.fromString(name),type,pos,incarnations);
    }
    
    protected VarSymbol newAuxVarSym(long flags, @NonNull String name, @NonNull Type type) {
        // We leave thet symbol's declaration position as Position.NOPOS (-1).
        return new VarSymbol(flags,names.fromString(name),type,null);
    }
    
    protected JCIdent newAuxIdent(@NonNull Name name, @NonNull Type type, int pos, boolean incarnations) {
        JCIdent id = factory.at(pos).Ident(name);
        VarSymbol s = new VarSymbol(0,id.name,type,null);
        s.pos = incarnations ? pos : -1;
        id.sym = s;
        id.type = type;
        return id;
    }
    
    // untranslated JCIdent
    protected JCIdent newAuxIdent(VarSymbol sym, int pos) {
        JCIdent id = factory.at(pos).Ident(sym.name);
        id.sym = sym;
        id.type = sym.type;
        return id;
    }
    
    /** Start the processing of the given block
     * 
     * @param b the block for which to initialize processing 
     */
    protected void startBlock(@NonNull BasicBlock b) {
        // Check that all preceding blocks are actually completed
        // This should not actually be needed
        loop: while (true) {
            for (BasicBlock pb: b.preceding) {
                if (!blocksCompleted.contains(pb)) {
                    log.noticeWriter.println("PROCESSING A BLOCK OUT OF ORDER");
                    processBlock(pb);
                    if (blocksCompleted.contains(pb)) return;
                    continue loop; // the list of preceders might have changed - check it over again
                }
            }
            break;  // all were completed
        }
        // FIXME - replace this with some anonymous classes in OO fashion
        if (b.id.toString().endsWith("$finally")) {
            // Once we are processing a finally block, all returns and throws
            // exit the finally block and go to whatever enclosing catchblocks
            // or tryreturn blocks there are.
            catchListStack.remove(0);
            tryreturnStack.remove(0);
        } else if (b.id.toString().endsWith("$catchrest")) {
            // Once we are processing the catchrest block then all throws go
            // to the finally block, not to the catch blocks.  SO we adjust
            // the content of the top of the catcList stack, which visitThrow
            // uses to set the following blocks to the throw statement
            BasicBlock finallyBlock = tryreturnStack.get(0).succeeding().get(0);
            catchListStack.get(0).clear();
            catchListStack.get(0).add(finallyBlock);
        } else if (b.id.toString().endsWith("$loopAfter")) {
            loopStack.remove(0);
        }
        //log.noticeWriter.println("Starting block " + b.id);
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
        currentMap = null; // Defensive - so no inadvertent assignments
        //log.noticeWriter.println("Completed block " + b.id);
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
    
    protected void follows(@NonNull BasicBlock before, @NonNull List<BasicBlock> after) {
        for (BasicBlock b: after) {
            before.succeeding.add(b);
            b.preceding.add(before);
        }
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
    
    protected void replaceFollows(@NonNull BasicBlock before, @NonNull List<BasicBlock> after) {
        for (BasicBlock b: before.succeeding) {
            b.preceding.remove(before);
        }
        before.succeeding.clear();
        for (BasicBlock b: after) {
            follows(before,b);
        }
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
    
    // FIXME - comment - this is used to avoid recursive axiomatization of the same method
    // it also serves to avoid repeated axiomatization of the same method within one spec experession
    Map<MethodSymbol,Name> specMethodCalls = new HashMap<MethodSymbol,Name>();
    
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
    public static @NonNull BasicProgram convertToBasicBlocks(@NonNull Context context, 
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
        JCIdent id = newAuxIdent(name,syms.booleanType,pos,false);
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
        JCIdent id = newAuxIdent(name,syms.booleanType,pos,false);
        return new BasicBlock(id,previousBlock);
    }
    
    // characteristics of the method under study
    JmlMethodDecl methodDecl;
    boolean isConstructor;
    boolean isStatic;
    boolean isHelper;

    /** Converts the top-level block of a method into the elements of a BasicProgram 
     * 
     * @param methodDecl the method to convert to to a BasicProgram
     * @param denestedSpecs the specs of the method
     * @param classDecl the declaration of the containing class
     * @return the completed BasicProgram
     */
    protected @NonNull BasicProgram convertMethodBody(@NonNull JCMethodDecl methodDecl, 
            JmlMethodSpecs denestedSpecs, @NonNull JCClassDecl classDecl) {
        program = new BasicProgram();
        unique = 0;
        isConstructor = methodDecl.sym.isConstructor();  // FIXME - careful if there is nesting???
        isStatic = methodDecl.sym.isStatic();
        isHelper = isHelper(methodDecl.sym);
        typesAdded = new HashSet<TypeSymbol>();
        int pos = methodDecl.pos;
        inSpecExpression = false;
        if (classDecl.sym == null) {
            throw new RuntimeException("UNEXPECTED NULL SYM FOR " + classDecl.name);
        }
        JmlClassInfo classInfo = getClassInfo(classDecl.sym);
        if (classInfo == null) {
            throw new RuntimeException("UNEXPECTED NULL CLASSINFO FOR " + classDecl.name);
        }
        this.classInfo = classInfo;
        newdefs = new LinkedList<JCExpression>();
        background = new LinkedList<JCExpression>();
        blocksToDo = new LinkedList<BasicBlock>();
        blocksCompleted = new ArrayList<BasicBlock>();
        blockLookup = new java.util.HashMap<String,BasicBlock>();
        this.methodDecl = (JmlMethodDecl)methodDecl;
        thisId = newAuxIdent("this$",methodDecl.sym.owner.type,pos,false);
        currentThisId = thisId;
        

        if (methodDecl.getReturnType() != null) {
            resultVar = newAuxIdent("$$result",methodDecl.getReturnType().type,0,true); 
        }
        terminationVar = newAuxIdent(terminationSym,0);
        exceptionVar = newAuxIdent("$$exception",syms.exceptionType,0,true);
//        allocVar = newAuxIdent(ALLOC_VAR,syms.intType,0,true); // this needs to be an int so we can compare values, though ideally it is an int that is not related to any other int
        heapVar = newAuxIdent(HEAP_VAR,syms.intType,0,true); // FIXME - would this be better as its own uninterpreted type?
        assumeCheckCountVar = newAuxIdent("__assumeCheckCount",syms.intType,0,false);
        assumeCheckCount = 0;
        
        JCBlock block = methodDecl.getBody();
        
        // Define the conditional return block
        condReturnBlock = newBlock(COND_RETURN_BLOCK_NAME,pos);
        JCExpression e = makeBinary(JCTree.GT,terminationVar,zeroLiteral,pos);
        addAssumeNoDefs(0,Label.SYN,e,condReturnBlock.statements);
        
        // Define the return block
        returnBlock = newBlock(RETURN_BLOCK_NAME,pos);
        follows(condReturnBlock,returnBlock);
        
        // Define the conditional exception block
        condExceptionBlock = newBlock(COND_EXCEPTION_BLOCK_NAME,pos);
        e = makeBinary(JCTree.LT,terminationVar,zeroLiteral,pos);
        addAssumeNoDefs(0,Label.SYN,e,condExceptionBlock.statements);
        
        // Define the exception block
        exceptionBlock = newBlock(EXCEPTION_BLOCK_NAME,pos);
        follows(condExceptionBlock,exceptionBlock);
        
        // Define the start block
        BasicBlock startBlock = newBlock(START_BLOCK_NAME,pos);

        // Define the body block
        // Put all the program statements in the Body Block
        BasicBlock bodyBlock = newBlock(BODY_BLOCK_NAME,methodDecl.body.pos);
        // First a key statements
        e = makeBinary(JCTree.EQ,terminationVar,zeroLiteral,methodDecl.body.pos);
        addAssumeNoDefs(methodDecl.body.pos,Label.SYN,e,bodyBlock.statements); // Don't use defs to make sure it is translated later

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
        startBlock(startBlock); // Start it so the currentMap is defined
        newIdentIncarnation(heapVar,0);
        newIdentIncarnation(terminationSym,0);
        newIdentIncarnation(exceptionVar,0);
        newIdentIncarnation(allocSym,0);
        if (!isStatic) {
            e = makeBinary(JCTree.NE,thisId,nullLiteral,methodDecl.body.pos);
            addAssume(methodDecl.body.pos,Label.SYN,e,startBlock.statements,false);
        }
        addGlobalPreconditions(startBlock,(JmlMethodDecl)methodDecl,(JmlClassDecl)classDecl);
        addPreconditions(startBlock,methodDecl,denestedSpecs);
        checkAssumption(methodDecl.pos,Label.PRECONDITION);
        completed(startBlock);

        // Pick a block to do and process it
        while (!blocksToDo.isEmpty()) {
            processBlock(blocksToDo.remove(0));
        }
        addPostconditions(returnBlock,methodDecl,denestedSpecs);
        addExPostconditions(exceptionBlock,methodDecl,denestedSpecs);
        
        // Make the BasicProgram
        program.methodDecl = methodDecl;
        program.startId = startBlock.id;
        program.blocks.addAll(blocksCompleted);
        if (assumeCheck != null) booleanAssumeCheck = assumeCheck;
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
//        Collection<JCIdent> decls = program.declarations;
//        Set<Name> varnames = new HashSet<Name>();
//        for (JCIdent id: vars) {
//            if (varnames.add(id.getName())) decls.add(id);
//        }
        return program;
    }
    
    /** Does the conversion of a block with Java statements into basic program
     * form, possibly creating new blocks on the todo list
     * @param block the block to process
     */
    protected void processBlock(@NonNull BasicBlock block) {
        if (block.preceding.isEmpty()) {
            // Delete any blocks that do not follow anything
            for (BasicBlock b: block.succeeding) {
                b.preceding.remove(block);
            }
            return;// Don't add it to the completed blocks
        }
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
                enterClass(names.fromString("org.jmlspecs.annotation.Helper"));
        }
        return symbol.attribute(helperAnnotationSymbol)!=null;
    }  // FIXME - isn't there a utility method somewhere else that does this

    protected void addGlobalPreconditions(@NonNull BasicBlock b, @NonNull JmlMethodDecl tree,
            @NonNull JmlClassDecl classDecl) {
        ClassCollector collector = ClassCollector.collect(classDecl,tree);
        int d = 0;
//        MethodSymbol distinct = makeFunction(names.fromString("distinct"),syms.intType,syms.classType);
//        for (ClassSymbol csym : collector.classes) {
//            // each class symbol is distinct
//            JCLiteral id = makeTypeLiteral(csym.type,0);
//            JCExpression e = makeFunctionApply(0,distinct,id);
//            e = makeBinary(JCTree.EQ,e,makeLiteral(++d,0),0);
//            addAssume(Label.IMPLICIT_ASSUME,trExpr(e),b.statements,false); // FIXME - track?
//        }

    }
    
    /** Inserts assumptions corresponding to the preconditions into the given block.
     * Uses classInfo to get the class-level preconditions.
     * 
     * @param b      the block into which to add the assumptions
     * @param tree   the method being translated
     * @param denestedSpecs  the denested specs for that method
     */
    protected void addPreconditions(@NonNull BasicBlock b, @NonNull JCMethodDecl tree, @NonNull JmlMethodSpecs denestedSpecs) {
        
        addClassPreconditions(classInfo,b);

        if (!tree.sym.isStatic()){
            // \typeof(this) <: <currenttype>
            int pos = 0;
            JCExpression e = makeThis(pos);
            e = makeTypeof(e);
            JCLiteral lit = makeTypeLiteral(classInfo.csym.type,pos); // FIXME - not necessarily a literal
            e = makeJmlBinary(JmlToken.SUBTYPE_OF,e,lit,pos);
            addAssume(Label.IMPLICIT_ASSUME,trExpr(e),b.statements,false);
        }
        
        JCExpression expr = falseLiteral;
        MethodSymbol msym = tree.sym;
        JmlMethodInfo mi = getMethodInfo(msym);
        if (mi.requiresPredicates.size() == 0) expr = trueLiteral;
        else for (JmlMethodClauseExpr pre: mi.requiresPredicates) {
            JCExpression pexpr = trSpecExpr(pre.expression,pre.source());
            if (expr == falseLiteral) expr = pexpr;
            else {
                expr = makeBinary(JCTree.OR,expr,pexpr,expr.pos);
            }
        }
        expr.pos = expr.getStartPosition();
        
        addClassPredicate(classInfo.csym.type);
        
        JCIdent alloc = newIdentUse(allocSym,tree.pos);
        Iterator<JCVariableDecl> baseParams = tree.params.iterator();
        while (baseParams.hasNext()) {
            JCVariableDecl base = baseParams.next();
            if (!base.type.isPrimitive()) {
                int pos = base.pos;
                // for each reference parameter p: assume (p == null) || (( \typeof(p) <: <statictype> ) && p.alloc < allocVar )
                // also add the class predicate for the argument type
                Type transType = trType(base.type); // Translated in case it is a type variable
                addClassPredicate(transType);
                JCIdent baseId = newIdentUse(base.sym,pos);
                JCExpression t = factory.at(pos).JmlMethodInvocation(JmlToken.BSTYPEOF,com.sun.tools.javac.util.List.<JCExpression>of(baseId));
                t.type = syms.classType;
                JCExpression lit = makeTypeLiteral(transType,pos);
                // FIXME - need subtypes for all of a parameters bounds
                JCExpression eq = makeJmlBinary(JmlToken.SUBTYPE_OF,t,lit,pos);
                
                // <newid>.alloc < <alloc>
                JCExpression ee = new JmlBBFieldAccess(allocIdent,baseId);
                ee.pos = pos;
                ee.type = syms.intType;
                ee = makeBinary(JCTree.LT,ee,alloc,pos);

                eq = makeBinary(JCTree.AND,eq,ee,pos);
                eq = makeBinary(JCTree.OR,makeBinary(JCTree.EQ,baseId,nullLiteral,pos),eq,pos);
                addAssume(Label.SYN,eq,b.statements,false);
            }
        }
        
        { // this is defined before the call
            JCExpression ee = new JmlBBFieldAccess(allocIdent,thisId);
            ee.pos = tree.pos;
            ee.type = syms.intType;
            ee = makeBinary(JCTree.LT,ee,alloc,tree.pos);
            addAssume(Label.SYN,ee,b.statements,false);
        }

        // Need definedness checks?  FIXME
        if (!isConstructor && !isStatic) {
            while ((msym=getOverrided(msym)) != null) {
                expr = addMethodPreconditions(b,msym,tree,tree.pos,expr);
            }
        }
        
        addAssume(tree.pos,Label.PRECONDITION,expr,b.statements,false);

    }
    
    protected JCExpression addMethodPreconditions(@NonNull BasicBlock b, @NonNull MethodSymbol msym, @NonNull JCMethodDecl baseMethod, int pos, JCExpression expr) {

        // Note: msym, the MethodSymbol of an overridden method, always exists,
        // but if the super class it is in is only binary then msym.params is null.
        // So instead we use mi.decl; it however is null if there are no specs.
        // However if there are no specs, there is nothing to do anyway.  Also,
        // mi.decl will contain the parameter names used in the specs.
        
        // FIXME - argument names???  Will the pre and post names be different?
        JmlMethodInfo mi = getMethodInfo(msym);
        if (mi.decl == null) return trueLiteral;
        
        if (msym != baseMethod.sym) {
            addParameterMappings(baseMethod,mi.decl,pos,b);
        }

        for (JmlMethodClauseExpr req: mi.requiresPredicates) {
            JCExpression pre = req.expression;
            int p = (expr == null || expr.pos == 0) ? pre.getStartPosition() : expr.pos;
            pre = trSpecExpr(pre,req.source());
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
                b.statements.add(comment(ax));
                JCExpression e = ax.expression;
                e = trSpecExpr(e,ax.source());
                JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.INVARIANT,e);// FIXME pos
                b.statements.add(asm);
            }
            
            // For each field we need a type predicate: f == null || f.alloc < allocVar
            for (Symbol d : cInfo.csym.members().getElements()) {
                if ((d instanceof VarSymbol) && !d.type.isPrimitive()) {
                    VarSymbol v = (VarSymbol)d;
                    if (v.isStatic()) { // FIXME - not right for JML fields in interfaces
                        declareAllocated(v,v.pos);
                    } else {
                        JCIdent id = newIdentUse(v,v.pos);
                        JCExpression e = new JmlBBFieldAccess(id,currentThisId);
                        e.pos = v.pos;
                        declareAllocated(e,v.pos);
                    }
                }
            }

            if (!isConstructor && !isHelper) {
                for (JmlTypeClauseExpr inv : cInfo.staticinvariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e,inv.source());
                    JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.INVARIANT,e);// FIXME pos
                    b.statements.add(asm);
                }
                if (!isStatic) {
                    for (JmlTypeClauseExpr inv : cInfo.invariants) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e,inv.source());
                        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.INVARIANT,e);// FIXME pos
                        b.statements.add(asm);
                    }
                }
            }
        } finally {
            classInfo = prevClassInfo;
        }
    }
    
    static boolean useAssertDefinitions = true;

    static Map<JavaFileObject,Integer> jfoMap = new HashMap<JavaFileObject,Integer>();
    static ArrayList<JavaFileObject> jfoArray = new ArrayList<JavaFileObject>();
    static {
        jfoArray.add(0,null);
    }
    
    protected void addAssert(Label label, JCExpression that, int declpos, List<JCStatement> statements, int usepos, JavaFileObject source) {
        JmlStatementExpr st;
        if (useAssertDefinitions && label != Label.ASSUME_CHECK) {
            //if (extraEnv) { usepos++; declpos++; }
            String n;
            if (source == log.currentSourceFile()) {
                n = "assert$" + usepos + "$" + declpos + "$" + label + "$" + (unique++);
            } else {
                Integer i = jfoMap.get(source);
                if (i == null) {
                    i = jfoArray.size();
                    jfoMap.put(source,i);
                    jfoArray.add(i,source);
                }
                n = "assert$" + usepos + "$" + declpos + "@" + i + "$" + label + "$" + (unique++);
            }
             
            JCExpression id = newAuxIdent(n,syms.booleanType,that.getStartPosition(),false);
            JCExpression expr = makeBinary(JCTree.EQ,id,that,that.pos);
                    // FIXME - start and end?
            newdefs.add(expr);
            that = id;
        }
        st = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSERT,label,that);
        st.optionalExpression = null;
        st.source = source;
        st.type = null; // FIXME - is this right?
        statements.add(st);
        //return that;
    }

    
    protected void addUntranslatedAssert(Label label, JCExpression that, int declpos, List<JCStatement> statements, int usepos, JavaFileObject source) {
        JmlStatementExpr st;
        st = factory.at(usepos).JmlExpressionStatement(JmlToken.ASSERT,label,that);
        st.optionalExpression = null;
        st.source = source;
        st.declPos = declpos;
        st.type = null; // FIXME - is this right?
        statements.add(st);
        //return that;
    }
    
    protected void addAssertNoTrack(Label label, JCExpression that, List<JCStatement> statements, int usepos, JavaFileObject source) {
        JmlStatementExpr st;
        st = factory.at(usepos).JmlExpressionStatement(JmlToken.ASSERT,label,that);
        st.optionalExpression = null;
        st.type = null; // FIXME - is this right?
        st.source = source;
        statements.add(st);
        //return that;
    }
    
    protected void addAssume(Label label, JCExpression that, List<JCStatement> statements, boolean track) {
        addAssume(that.pos,label,that,statements,track);
    }
    
    protected void addAssume(int pos, Label label, JCExpression that) {
        addAssume(pos,label,that,currentBlock.statements,false);
    }
    
    public static boolean useAssumeDefinitions = true;
    
    protected JmlStatementExpr addAssume(int pos, Label label, JCExpression that, List<JCStatement> statements, boolean track) {
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
        factory.at(pos);
        JmlStatementExpr st;
        if (useAssumeDefinitions) {
            JCIdent id = factory.Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
            id.type = syms.booleanType;
            JCExpression e = factory.Binary(JCTree.EQ,id,that).setType(syms.booleanType);
            newdefs.add(e);
            st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,id);
        } else {
            st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,that);
        }
        // st.type = ??? FIXME
        statements.add(st);
        return st;
    }
    
    protected JmlStatementExpr addAssumeNoDefs(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        factory.at(pos);
//        JCIdent id = factory.Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
//        id.type = syms.booleanType;
//        JCExpression e = factory.Binary(JCTree.EQ,id,that).setType(syms.booleanType);
        JmlStatementExpr st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,that);
        // st.type = ??? FIXME
        statements.add(st);
        return st;
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
     * @returns the variable corresponding the the given String argument
     */
    // FIXME - modifies the content of currentBlock.statements
    protected @NonNull JCIdent addAuxVariable(@NonNull String name, @NonNull Type type, @NonNull JCExpression expr, boolean makeDefinition) {
        JCExpression newexpr = trExpr(expr);
        JCIdent vd = newAuxIdent(name,type,newexpr.getStartPosition(),false);
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
        int pos = decl.pos;
        currentBlock = b;
        currentMap = blockmaps.get(b);
        if (currentMap == null) return; // no normal return

        //checkAssumption(pos,Label.RETURN);

        JCIdent id = newIdentUse(terminationSym,0);
        addAssume(0,Label.SYN,makeBinary(JCTree.EQ,terminationVar,id,0));
        
        addMethodPostconditions(decl.sym,b,pos,decl);

        if (!isConstructor && !isStatic) {
            MethodSymbol msym = decl.sym;
            while ((msym = getOverrided(msym)) != null) {
                addMethodPostconditions(msym,b,pos,decl);
            }
        }
        
        // FIXME - reevaluate the last argument: this is the location that the error message
        // indicates as where the assertion failed - it could be the return statement, or the
        // ending close paren.  But the only information we have at this point is the preferred
        // location of the method declaration (unless we could get the ending information).
        addClassPostconditions(classInfo,b,pos);

        // FIXME - this is wrong - we assume th OR of everything
    }
    
    protected void addMethodPostconditions(MethodSymbol msym, BasicBlock b, int pos, JCMethodDecl baseMethod) {
        List<JCStatement> statements = b.statements;
        // Note: msym, the MethodSymbol of an overridden method, always exists,
        // but if the super class it is in is only binary then msym.params is null.
        // So instead we use mi.decl; it however is null if there are no specs.
        // However if there are no specs, there is nothing to do anyway.  Also,
        // mi.decl will contain the parameter names used in the specs.

        // FIXME - argument names???  Will the pre and post names be different?
        JmlMethodInfo mi = getMethodInfo(msym);
        if (mi.decl == null) return;
        if (msym != baseMethod.sym) {
            addParameterMappings(baseMethod,mi.decl,pos,b);
        }
        for (JmlMethodClauseExpr post: mi.ensuresPredicates) {
            addAssert(Label.POSTCONDITION,trSpecExpr(post.expression,post.source()),post.getStartPosition(),statements,pos,post.source());
        }
    }
    
    protected void addExPostconditions(BasicBlock b, JCMethodDecl decl, JmlMethodSpecs denestedSpecs) {
        currentBlock = b;
        currentMap = blockmaps.get(b);
        if (currentMap == null) return; // no exceptions ever thrown

        JCIdent id = newIdentUse(terminationSym,0);
        addAssume(0,Label.SYN,makeBinary(JCTree.EQ,terminationVar,id,0));

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
        // Note: msym, the MethodSymbol of an overridden method, always exists,
        // but if the super class it is in is only binary then msym.params is null.
        // So instead we use mi.decl; it however is null if there are no specs.
        // However if there are no specs, there is nothing to do anyway.  Also,
        // mi.decl will contain the parameter names used in the specs.
        
        // FIXME - argument names???  Will the pre and post names be different?
        JmlMethodInfo mi = getMethodInfo(msym);
        if (mi.decl == null) return;
        if (msym != baseMethod.sym) {
            addParameterMappings(baseMethod,mi.decl,pos,b);
        }
        // signals/exsures predicates
        for (JmlMethodClauseExpr post: mi.exPredicates) {
            JCExpression ex = ((JmlBinary)post.expression).lhs;
            ex = ((JmlBinary)ex).lhs;
            ex = ((JmlMethodInvocation)ex).args.get(0);
            signalsVar = ex instanceof JCIdent ? (JCIdent)ex : null;
            addAssert(Label.SIGNALS,trSpecExpr(post.expression,post.source()),post.getStartPosition(),statements,pos,post.source());
            signalsVar = null;
        }
        // signals_only predicates
        for (JmlMethodClauseExpr post: mi.sigPredicates) {
            addAssert(Label.SIGNALS,trSpecExpr(post.expression,post.source()),post.getStartPosition(),statements,pos,post.source());
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
            for (JmlTypeClauseExpr inv : cInfo.staticinvariants) {
                JCExpression e = inv.expression;
                e = trSpecExpr(e,inv.source());
                addAssert(Label.INVARIANT,e,inv.expression.getStartPosition(),statements,usepos,inv.source());
            }
            if (!isStatic) {
                for (JmlTypeClauseExpr inv : cInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e,inv.source());
                    addAssert(Label.INVARIANT,e,inv.expression.getStartPosition(),statements,usepos,inv.source());
                }
            }
            if (!isConstructor) {
                for (JmlTypeClauseConstraint inv : cInfo.staticconstraints) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e,inv.source());
                    addAssert(Label.CONSTRAINT,e,inv.expression.getStartPosition(),statements,usepos,inv.source());
                }
                if (!isStatic) {
                    for (JmlTypeClauseConstraint inv : cInfo.constraints) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e,inv.source());
                        addAssert(Label.CONSTRAINT,e,inv.expression.getStartPosition(),statements,usepos,inv.source());
                    }
                }
            } else {
                for (JmlTypeClauseExpr inv : cInfo.initiallys) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e,inv.source());
                    addAssert(Label.INITIALLY,e,inv.expression.getStartPosition(),statements,usepos,inv.source());
                }
            }
        }
    }
    
    Set<TypeSymbol> typesAdded = new HashSet<TypeSymbol>();
    protected void addClassPredicate(Type type) {
        // FIXME - this appears to add the class predicate only once for a generic type - is that OK?
        if (typesAdded.contains(type.tsym)) return;
        typesAdded.add(type.tsym);
        pushTypeArgs(type);
        // FIXME _ type can be a TypeVar and type.tsym a TypeSymbol that is not a class Symbol
        if (type.tsym instanceof ClassSymbol) {
            TypeSymbol ts = ((ClassSymbol)type.tsym).getSuperclass().tsym;
            if (ts != null && ts.type.tag != TypeTags.NONE) {
                Type t = trType(ts.type);
                addClassPredicate(t);
                // FIXME - need to have literals for generic types
                JCLiteral lit1 = makeTypeLiteral(type,0);
                JCLiteral lit2 = makeTypeLiteral(t,0);
                JCExpression e = makeJmlBinary(JmlToken.SUBTYPE_OF,lit1,lit2,0);
                
                // FIXME - need to add everything else - e.g. invariants
                background.add(e);
            }
        } else {
            log.noticeWriter.println("adddClassPredicate not implemented for " + type + " " + type.getClass());
        }
        popTypeArgs(type);
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
        if (baseMethod == null) return;  // FIXME - this happens on <array>.clone() - any other time?
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
    
    // FIXME - change to this use everywhere - sort out positions
    protected void addParameterMappings(@NonNull MethodSymbol baseMethod, @NonNull JCMethodDecl otherMethod, int pos, BasicBlock b) {
        Iterator<VarSymbol> baseParams = baseMethod.params.iterator();
        Iterator<JCVariableDecl> newParams = otherMethod.params.iterator();
        while (baseParams.hasNext()) {
            VarSymbol base = baseParams.next();
            JCVariableDecl newp = newParams.next();
            JCIdent baseId = newIdentUse(base,pos);
            JCIdent newId = newIdentIncarnation(newp,0);
            JCExpression eq = makeBinary(JCTree.EQ,newId,baseId,pos);
            addAssume(Label.SYN,eq,b.statements,false);
        }
    }
    
    protected VarMap initMap(BasicBlock block) {
        VarMap newMap = new VarMap();
        if (block.preceding.size() == 0) {
            // keep the empty one
        } else if (block.preceding.size() == 1) {
            newMap.putAll(blockmaps.get(block.preceding.get(0))); 
        } else {
            List<VarMap> all = new LinkedList<VarMap>();
            VarMap combined = new VarMap();
            int maxe = -1;
            for (BasicBlock b : block.preceding) {
                VarMap m = blockmaps.get(b);
                all.add(m);
                combined.putAll(m);
                if (maxe < m.everythingIncarnation) maxe = m.everythingIncarnation;
            }
            combined.everythingIncarnation = maxe;
            for (VarSymbol sym: combined.keySet()) {
                Name maxName = null;
                int max = -1;
                for (VarMap m: all) {
                    Integer i = m.get(sym);
                    if (i != null && i > max) {
                        max = i;
                        maxName = m.getName(sym);
                    }
                }
                for (BasicBlock b: block.preceding) {
                    VarMap m = blockmaps.get(b);
                    Integer i = m.get(sym);
                    if (i == null) i = 0;
                    if (i < max) {
                        // No position information for these nodes
                        // Type information put in, though I don't know that we need it
                        currentMap = m; // In case the next line inserts an assignment into the map
                        JCIdent pold = newIdentUse(sym,m.getName(sym),0);
                        JCIdent pnew = newIdentUse(sym,maxName,0);
                        JCBinary eq = makeBinary(JCTree.EQ,pnew,pold,0);
                        addAssumeNoDefs(0,Label.DSA,eq,b.statements);
                        m.put(sym,max,pnew.name);
                    }
                }
                newMap.put(sym,max,maxName);
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
        public JmlMethodInfo(MethodSymbol msym) { 
            this.decl = null; 
            this.owner = msym; 
            this.source = null;
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
        java.util.List<JmlMethodClauseExpr> requiresPredicates = new LinkedList<JmlMethodClauseExpr>();
        java.util.List<JmlMethodClauseExpr> ensuresPredicates = new LinkedList<JmlMethodClauseExpr>();
        java.util.List<JmlMethodClauseExpr> exPredicates = new LinkedList<JmlMethodClauseExpr>();
        java.util.List<JmlMethodClauseExpr> sigPredicates = new LinkedList<JmlMethodClauseExpr>();
        java.util.List<JmlMethodClauseExpr> divergesPredicates = new LinkedList<JmlMethodClauseExpr>();
        
        public static class Entry {
            public Entry(JCExpression pre, java.util.List<JCExpression> list) {
                this.pre = pre;
                this.storerefs = list;
            }
            public JCExpression pre;
            public java.util.List<JCExpression> storerefs;
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

        JmlMethodInfo mi = mspecs.cases.decl == null ? new JmlMethodInfo(msym) : new JmlMethodInfo(mspecs.cases.decl);
        JmlMethodSpecs denestedSpecs = msym == null ? null : specs.getDenestedSpecs(msym);
        if (JmlEsc.escdebug) log.noticeWriter.println("SPECS FOR " + msym.owner + " " + msym + " " + (denestedSpecs != null));
        if (JmlEsc.escdebug) log.noticeWriter.println(denestedSpecs == null ? "     No denested Specs" : denestedSpecs.toString("   "));

        List<JCStatement> prev = newstatements;
        newstatements = new LinkedList<JCStatement>();
        if (denestedSpecs != null) {
            // preconditions
            JCExpression pre = denestedSpecs.cases.size() == 0 ? makeLiteral(true,mspecs.cases.decl==null?0:mspecs.cases.decl.pos) : null;
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
            }{
                JmlMethodClauseExpr p = factory.at(pre.pos).JmlMethodClauseExpr(JmlToken.SIGNALS,pre);
                p.sourcefile = log.currentSourceFile();
                mi.requiresPredicates.add(p);  // Just one composite precondition for all of the spec cases
            }
            
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
                        JmlMethodClauseExpr p = factory.at(post.pos).JmlMethodClauseExpr(JmlToken.SIGNALS,post);
                        p.sourcefile = c.source();
                        mi.ensuresPredicates.add(p);
                    } else if (c.token == JmlToken.ASSIGNABLE) {
                        JmlMethodClauseStoreRef mod = (JmlMethodClauseStoreRef)c;
                        // spre is the precondition under which the store-refs are modified
                        List<JCExpression> list = mod.list; // store-ref expressions
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
                            e = makeNNInstanceof(id,c.pos, mod.vardef.type, mod.vardef.pos);
                            post = makeJmlBinary(JmlToken.IMPLIES,e,post,c.pos);
                        } else {
                            JCExpression id = factory.at(c.pos).JmlSingleton(JmlToken.BSEXCEPTION);
                            e = makeNNInstanceof(id,c.pos, syms.exceptionType, c.pos);
                            post = makeJmlBinary(JmlToken.IMPLIES,e,post,c.pos);
                        }
                        JmlMethodClauseExpr p = factory.at(post.pos).JmlMethodClauseExpr(JmlToken.SIGNALS,post);
                        p.sourcefile = c.source();
                        mi.exPredicates.add(p);
                    } else if (c.token == JmlToken.DIVERGES) {
                        JCExpression e = ((JmlMethodClauseExpr)c).expression;
                        JCExpression post = makeJmlBinary(JmlToken.IMPLIES,spre,e,e.getStartPosition());
                        JmlMethodClauseExpr p = factory.at(post.pos).JmlMethodClauseExpr(JmlToken.DIVERGES,post);
                        p.sourcefile = c.source();
                        mi.divergesPredicates.add(p);
                    } else if (c.token == JmlToken.SIGNALS_ONLY) {
                        JCExpression post = makeSignalsOnly((JmlMethodClauseSigOnly)c);
                        JmlMethodClauseExpr p = factory.at(post.pos).JmlMethodClauseExpr(JmlToken.SIGNALS,post);
                        p.sourcefile = c.source();
                        mi.sigPredicates.add(p);
                    }
                    // FIXME - is signals_only desugared or handled here?
                    // FIXME - we are ignoring forall old when duration working_space callable accessible measured_by captures
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
    
    /** Makes a Java this parse tree node (attributed) */
    protected JCIdent makeThis(int pos) {
        return makeIdent(methodDecl._this,pos);
    }
    
    /** Makes the equivalent of an instanceof operation: \typeof(e) <: \type(type) */
    protected JCExpression makeNNInstanceof(JCExpression e, int epos, Type type, int typepos) {
        return makeJmlBinary(JmlToken.SUBTYPE_OF,makeTypeof(e),makeTypeLiteral(type,typepos),epos);
    }
    
    /** Makes the equivalent of an instanceof operation: e !=null && \typeof(e) <: \type(type) */
    protected JCExpression makeInstanceof(JCExpression e, int epos, Type type, int typepos) {
        JCExpression e1 = makeBinary(JCTree.NE,e,nullLiteral,epos);
        JCExpression e2 = makeJmlBinary(JmlToken.SUBTYPE_OF,makeTypeof(e),makeTypeLiteral(type,typepos),epos);
        return makeBinary(JCTree.AND,e1,e2,epos);
    }
    
    protected MethodSymbol makeFunction(Name name, Type resultType, Type... argTypes) {
        ListBuffer<Type> args = new ListBuffer<Type>().appendArray(argTypes);
        MethodType methodType = new MethodType(args.toList(),resultType,com.sun.tools.javac.util.List.<Type>nil(),syms.methodClass);
        MethodSymbol meth = new MethodSymbol(Flags.STATIC,name,methodType,null); // no owner
        return meth;
    }
    
    protected JCExpression makeFunctionApply(int pos, MethodSymbol meth, JCExpression... args) {
        JCIdent methid = factory.at(pos).Ident(meth);
        JCExpression e = factory.at(pos).Apply(null,methid,new ListBuffer<JCExpression>().appendArray(args).toList());
        e.type = meth.getReturnType();
        return e;
    }
    
    protected JCExpression makeSignalsOnly(JmlMethodClauseSigOnly clause) {
        JCExpression e = makeLiteral(false,clause.pos);
        JCExpression id = factory.at(0).JmlSingleton(JmlToken.BSEXCEPTION);
        for (JCExpression typetree: clause.list) {
            int pos = typetree.getStartPosition();
            e = makeBinary(JCTree.OR, 
                    makeNNInstanceof(id, pos, typetree.type, pos), e, pos);
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
        currentBlock.statements.add(comment(that.pos,"while..."));
        visitLoopWithSpecs(that, null, that.cond, null, that.body, that.loopSpecs);
    }
    
    public void visitWhileLoop(JCWhileLoop that) {
        currentBlock.statements.add(comment(that.pos,"while..."));
        visitLoopWithSpecs(that, null, that.cond, null, that.body, null);
    }
    
    public void visitJmlForLoop(JmlForLoop that) {
        currentBlock.statements.add(comment(that.pos,"for..."));
        visitLoopWithSpecs(that,that.init,that.cond,that.step,that.body,that.loopSpecs );
    }
    
    public void visitForLoop(JCForLoop that) { 
        currentBlock.statements.add(comment(that.pos,"for..."));
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
        blockLookup.put(bloopContinue.id.name.toString(),bloopContinue);
        blockLookup.put(bloopBreak.id.name.toString(),bloopBreak);

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
        
        // check the loop invariants (translated)
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,that.getStartPosition(),currentBlock,Label.LOOP_INVARIANT_PRELOOP);

        // Now havoc any variables changed in the loop body
        {
            List<JCExpression> targets = TargetFinder.findVars(body,null);
            TargetFinder.findVars(test,targets);
            if (update != null) TargetFinder.findVars(update,targets);
            // synthesize a modifies list
            int wpos = body.pos+1;
            //log.noticeWriter.println("HEAP WAS " + currentMap.get((VarSymbol) heapVar.sym));
            newIdentIncarnation(heapVar,wpos);
            //log.noticeWriter.println("HEAP NOW " + currentMap.get((VarSymbol) heapVar.sym) + " " + (wpos+1));
            for (JCExpression e: targets) {
                if (e instanceof JCIdent) {
                    newIdentIncarnation((JCIdent)e,wpos);
                //} else if (e instanceof JCFieldAccess) {
                //} else if (e instanceof JCArrayAccess) {
                    
                } else {
                    // FIXME - havoc in loops
                    log.noticeWriter.println("UNIMPLEMENTED HAVOC IN LOOP " + e.getClass());
                }
            }
        }
        
        // assume the loop invariants (translated)
        addLoopInvariants(JmlToken.ASSUME,loopSpecs,that.getStartPosition(),currentBlock, Label.LOOP_INVARIANT);
        
        // compute the loop variants
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                String dec = "$$decreases" + "$" + loopspec.getStartPosition();
                addAuxVariable(dec,syms.longType,trSpecExpr(loopspec.expression,log.currentSourceFile()),false);
            }
        }
        
        // compute the loop condition
        int testPos = test == null ? that.pos : test.getStartPosition();
        String loopTestVarName = "loopCondition"  
            + "$" + testPos + "$" + testPos; // FIXME - end position?
        JCIdent loopTest = addAuxVariable(loopTestVarName,syms.booleanType,test == null ? trueLiteral : trJavaExpr(test),false);
        completed(currentBlock);
        BasicBlock bloopStart = currentBlock;
        follows(bloopStart,bloopBody);
        follows(bloopStart,bloopEnd);

        // Create and process the loop body block
        startBlock(bloopBody);
        
        // assume the loop condition (translated)
        addAssume(Label.LOOP,loopTest,bloopBody.statements,false);
        
        // check that the loop variants are not negative (translated)
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                int p = loopspec.getStartPosition();
                String dec = "$$decreases" + "$" + p;
                JCIdent v = newAuxIdent(dec,syms.longType,p,false);
                JCExpression e = makeBinary(JCTree.GE,v,makeLiteral(0,p),p);
                addAssert(Label.LOOP_DECREASES_NEGATIVE,trSpecExpr(e,log.currentSourceFile()),p,currentBlock.statements,body.getStartPosition(),log.currentSourceFile());
            }
        }
        
        // do the loop body - the loop body will continue to be processed after
        // we setup the remaining blocks for later processing
        remainingStatements.add(body);
        follows(bloopBody,bloopContinue);
        
        // Create an unprocessed loop continue block (untranslated)
        // do the update
        if (update != null) bloopContinue.statements.addAll(update);
        
        int end = endPos(body);
        if (end <= 0) {
            log.noticeWriter.println("BAD EBND");
        }
        // Check that loop invariants are still established
        addUntranslatedLoopInvariants(JmlToken.ASSERT,loopSpecs,end,bloopContinue,Label.LOOP_INVARIANT);
        // Check that loop variants are decreasing
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                String dec = "$$decreases$" + loopspec.getStartPosition();
                JCIdent id = newAuxIdent(dec,syms.longType,loopspec.getStartPosition(),false);
                JCExpression newexpr = loopspec.expression;
                JCExpression e = makeBinary(JCTree.LT,newexpr,id,newexpr.getStartPosition());
                addUntranslatedAssert(Label.LOOP_DECREASES,e,loopspec.getStartPosition(),bloopContinue.statements,end,log.currentSourceFile()); // FIXME - track which continue is causing a problem?
            }
        }
        
        // Create the LoopEnd block (untranslated)
        follows(bloopEnd,bloopBreak);
        JCExpression neg = makeUnary(JCTree.NOT,loopTest,loopTest.pos);  // loopTest is already processed - but that is OK since it is just an auxiliary ident
        addAssumeNoDefs(neg.pos,Label.LOOP,neg,bloopEnd.statements);
        
        // Create the LoopBreak block (untranslated)
        follows(bloopBreak,brest);
        addUntranslatedLoopInvariants(JmlToken.ASSERT,loopSpecs,end+1,bloopBreak,Label.LOOP_INVARIANT_ENDLOOP);

        // Push the blocks at the beginning of the todo list (in appropriate order)
        blocksToDo.add(0,bloopBreak);
        blocksToDo.add(0,bloopEnd);
        blocksToDo.add(0,bloopContinue);
        
        // Go on to process the loopBody block
    }
    
    int endPos(JCTree t) {
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

    protected void addLoopInvariants(JmlToken t, java.util.List<JmlStatementLoop> loopSpecs, int usepos, BasicBlock block, Label label) {
        if (loopSpecs == null) return;
        for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.LOOP_INVARIANT) {
                currentBlock.statements.add(comment(loopspec));
                JCExpression e = trSpecExpr(loopspec.expression,log.currentSourceFile());
                if (t == JmlToken.ASSUME) addAssume(label,e,currentBlock.statements,false);
                else addAssert(label,e,loopspec.getStartPosition(),block.statements,usepos,log.currentSourceFile());
            }
        }
    }
    
    protected void addUntranslatedLoopInvariants(JmlToken t, java.util.List<JmlStatementLoop> loopSpecs, int usepos, BasicBlock block, Label label) {
        if (loopSpecs == null) return;
        for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.LOOP_INVARIANT) {
                currentBlock.statements.add(comment(loopspec));
                JCExpression e = loopspec.expression;
                if (t == JmlToken.ASSUME) addAssumeNoDefs(usepos,label,e,currentBlock.statements);
                else addUntranslatedAssert(label,e,loopspec.getStartPosition(),block.statements,usepos,log.currentSourceFile());
            }
        }
    }
    
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        currentBlock.statements.add(comment(that.pos,"for..."));
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
            //   for (int $$index=0; $$index<arr.length; $$index++) { v = arr[$$index]; S }
            
            // make   int $$index = 0;   as the initialization
//            Name name = names.fromString("$$index$"+that.pos);
//            JCVariableDecl decl = makeVariableDecl(name,syms.intType,makeLiteral(0,pos),pos);
            JCVariableDecl decl = ((JmlEnhancedForLoop)that).indexDecl;
            JCVariableDecl vdecl = ((JmlEnhancedForLoop)that).indexDecl;
            com.sun.tools.javac.util.List<JCStatement> initList = com.sun.tools.javac.util.List.<JCStatement>of(decl,vdecl);

            // make assume \values.size() == 0
            
            // make   $$index < <expr>.length   as the loop test
            JCIdent id = (JCIdent)factory.at(pos).Ident(decl);
            id.type = decl.type;
            JCExpression fa = factory.at(pos).Select(that.getExpression(),syms.lengthVar);
            fa.type = syms.intType;
            JCExpression test = makeBinary(JCTree.LT,id,fa,pos);

            // make   $$index = $$index + 1  as the update list
            JCIdent idd = (JCIdent)factory.at(pos+1).Ident(decl);
            id.type = decl.type;
            JCAssign asg = factory.at(idd.pos).Assign(idd,
                    makeBinary(JCTree.PLUS,id,makeLiteral(1,pos),idd.pos));
            asg.type = syms.intType;
            JCExpressionStatement update = factory.at(idd.pos).Exec(asg);
            com.sun.tools.javac.util.List<JCExpressionStatement> updateList = com.sun.tools.javac.util.List.<JCExpressionStatement>of(update);
            
            // make   <var> = <expr>[$$index]    as the initialization of the target and prepend it to the body
            JCArrayAccess aa = factory.at(pos).Indexed(that.getExpression(),id);
            aa.type = that.getVariable().type;
            JCIdent v = (JCIdent)factory.at(pos).Ident(that.getVariable());
            v.type = aa.type;
            asg = factory.at(pos).Assign(v,aa);
            asg.type = v.type;
            ListBuffer<JCStatement> newbody = new ListBuffer<JCStatement>();
            newbody.append(factory.at(pos).Exec(asg));
            newbody.append(that.body);
            
            // add 0 <= $$index && $$index <= <expr>.length
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
        currentBlock.statements.add(comment(that.pos,"do..."));
        visitDoLoopWithSpecs(that,null);
    }    

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        currentBlock.statements.add(comment(that.pos,"do..."));
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
    protected void visitDoLoopWithSpecs(JCDoWhileLoop that, List<JmlStatementLoop> loopSpecs) {
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
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,that.getStartPosition(),currentBlock, Label.LOOP_INVARIANT_PRELOOP);

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
                    log.noticeWriter.println("UNIMPLEMENTED HAVOC IN LOOP " + e.getClass());
                }
            }
        }

        // assume the loop invariant
        addLoopInvariants(JmlToken.ASSUME,loopSpecs,that.getStartPosition(),currentBlock, Label.LOOP_INVARIANT);

        // Compute the loop variant and Check that the variant is not negative
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                int p = loopspec.getStartPosition();
                String dec = "$$decreases" + "$" + p;
                JCIdent v = addAuxVariable(dec,syms.longType,trSpecExpr(loopspec.expression,log.currentSourceFile()),false);
                JCExpression e = makeBinary(JCTree.GE,v,makeLiteral(0,p),p);
                addAssert(Label.LOOP_DECREASES_NEGATIVE,e,p,currentBlock.statements,body.getStartPosition(),log.currentSourceFile()); // FIXME - track which continue is causing a problem?
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
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,endPos(body),currentBlock,Label.LOOP_INVARIANT); // FIXME - use end position?

        // Check that loop variants are decreasing
        if (loopSpecs != null) for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                String dec = "$$decreases$" + loopspec.getStartPosition();
                JCIdent id = newAuxIdent(dec,syms.longType,loopspec.getStartPosition(),false);
                JCExpression newexpr = trSpecExpr(loopspec.expression,log.currentSourceFile());
                JCExpression e = makeBinary(JCTree.LT,newexpr,id,newexpr.getStartPosition());
                addAssert(Label.LOOP_DECREASES,e,loopspec.getStartPosition(),currentBlock.statements,body.getStartPosition(),log.currentSourceFile()); // FIXME - track which continue is causing a problem?
            }
        }
        follows(bloopContinue,bloopEnd);
        completed(bloopContinue);

        // Create the LoopEnd block
        startBlock(bloopEnd);
        follows(bloopEnd,bloopBreak);
        JCExpression neg = makeUnary(JCTree.NOT,loopTest,loopTest.pos);
        addAssumeNoDefs(loopTest.pos,Label.LOOP,neg,currentBlock.statements);
        completed(bloopEnd);

        // fill in the LoopBreak block
        startBlock(bloopBreak);
        follows(bloopBreak,brest);
        addLoopInvariants(JmlToken.ASSERT,loopSpecs,endPos(body),currentBlock, Label.LOOP_INVARIANT_ENDLOOP);
        completed(bloopBreak);

        currentBlock = null;
        newstatements = null;
        loopStack.remove(0);
    }
    
    public void visitLabelled(JCLabeledStatement that) {
        JCTree target = that.getStatement();
        while (target instanceof JCLabeledStatement) ((JCLabeledStatement)target).getStatement();
        VarMap map = currentMap.copy();
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
        currentBlock.statements.add(comment(that.pos,"switch ..."));
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
            JCIdent vd = newAuxIdent(switchName,switchExpression.type,swpos,false);
            JCExpression newexpr = makeBinary(JCTree.EQ,vd,switchExpression,swpos);
            addAssume(swpos,Label.SWITCH_VALUE,trJavaExpr(newexpr));
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
                String caseName = blockPrefix + caseStatement.getStartPosition() + "$case";
                if (caseValue == null) caseName = blockPrefix + casepos +"$default";
                BasicBlock blockForTest = newBlock(caseName,casepos);
                blocks.add(blockForTest);
                follows(switchStart,blockForTest);
                
                // create the case test, or null if this is the default case
                JCBinary eq = caseValue == null ? null : makeBinary(JCTree.EQ,vd,trJavaExpr(caseValue),caseValue.getStartPosition());
                JmlStatementExpr asm = addAssumeNoDefs(caseStatement.pos,Label.CASECONDITION,eq,blockForTest.statements);
                checkAssumption(caseStatement.pos,Label.CASECONDITION,blockForTest.statements);
                
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
            if (prev != null) {
                // The last case statement did not appear to have a break statement
                // Add a break, even if it does not necessarily need it (e.g. it returns)  // FIXME - test this
                follows(prev,brest);
            }
            int dpos = defaultAsm == null ? pos : defaultAsm.pos;
            JCExpression eq = makeUnary(JCTree.NOT,defaultCond,dpos);
            if (defaultAsm != null) {
                // There was a default case already made, but at the time we just
                // put in null for the case condition, since we did not know it
                // yet (and we wanted to process the statements in textual order).
                // So here we violate encapsulation a bit and poke it in.
                defaultAsm.expression = eq;
            } else {
                // There was no default - we need to construct an empty one
                // create a block for this case test
                String caseName = "$defaultcase$" + pos ;
                BasicBlock blockForTest = newBlock(caseName,pos);
                blocks.add(blockForTest);
                follows(switchStart,blockForTest);
                follows(blockForTest,brest);
                
                addAssumeNoDefs(pos,Label.CASECONDITION,eq,blockForTest.statements);
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
    
    protected java.util.List<BasicBlock> tryreturnStack = new java.util.LinkedList<BasicBlock>();
    protected java.util.List<java.util.List<BasicBlock>> catchListStack = new java.util.LinkedList<java.util.List<BasicBlock>>();

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
    public void visitTry(JCTry that) {
        currentBlock.statements.add(comment(that.pos,"try..."));

        // Create an (unprocessed) block for everything that follows the
        // try statement
        int pos = that.pos;
        BasicBlock brest = newBlock(blockPrefix + pos + "$afterTry",pos,currentBlock);// it gets all the followers of the current block

        // Add an initial assumption to the rest of the statements that the program
        // is still executing normally (no return or throw has happened)
        JCExpression e = makeBinary(JCTree.EQ,terminationVar,zeroLiteral,pos);
        addAssumeNoDefs(pos,Label.SYN,e,brest.statements);
        brest.statements.addAll(remainingStatements); // it gets all of the remaining statements
        blocksToDo.add(0,brest);
        remainingStatements.clear();
        remainingStatements.add(that.getBlock());
        
        // We make an empty finally block if the try statement does not
        // have one, just to simplify things
        String finallyBlockName = blockPrefix + pos + "$finally";
        BasicBlock finallyBlock = newBlock(finallyBlockName,pos);
        JCBlock finallyStat = that.getFinallyBlock();
        if (finallyStat != null) finallyBlock.statements.add(finallyStat); // it gets the statements of the finally statement
        blocksToDo.add(0,finallyBlock); // push it on the front of the to do list
        follows(currentBlock,finallyBlock);
        follows(finallyBlock,brest);
        if (tryreturnStack.isEmpty()) {
            follows(finallyBlock,condReturnBlock);
            follows(finallyBlock,condExceptionBlock);
        } else {
            follows(finallyBlock,tryreturnStack.get(0));
            follows(finallyBlock,catchListStack.get(0));
        }
        
        // We need a conditional finally block as the target of nested finally
        // blocks, to distinguish returns from exceptions from continued 
        // execution
        
        String returnBlockName = blockPrefix + pos + "$tryreturn";
        BasicBlock tryreturnBlock = newBlock(returnBlockName,pos);
        //JCIdent tv = newIdentUse((VarSymbol)terminationVar.sym,pos);
        addAssumeNoDefs(pos,Label.SYN,makeBinary(JCTree.GT,terminationVar,zeroLiteral,pos),tryreturnBlock.statements);
        tryreturnStack.add(0,tryreturnBlock);
        blocksToDo.add(0,tryreturnBlock); // push it on the front of the to do list
        follows(tryreturnBlock,finallyBlock);

        // Now all the catch blocks
        // The expressions and assumptinos used here are prior to DSA processing
        List<BasicBlock> catchList = new LinkedList<BasicBlock>();
        int i = 0;
        //JCIdent ev = newIdentUse((VarSymbol)exceptionVar.sym,pos);
        JCExpression condtv = makeBinary(JCTree.AND,makeBinary(JCTree.LT,terminationVar,zeroLiteral,pos),
                                            makeBinary(JCTree.NE,exceptionVar,nullLiteral,pos),pos);
        JCExpression cond = trueLiteral;
        for (JCCatch catcher: that.catchers) {
            // A catch block has these statements
            // assume <exception condition>
            // assume <catchVar> = <exceptionVar>
            // assign <terminationVar> = 0 -- once the exception is caught we proceed normally
            // statements of the catch block
            int cpos = catcher.pos;
            String catchBlockName = blockPrefix + cpos + "$catch";
            BasicBlock catchBlock = newBlock(catchBlockName,cpos);

            addClassPredicate(catcher.param.vartype.type);
            JCExpression inst = makeNNInstanceof(exceptionVar,cpos,catcher.param.type,cpos);
            addAssumeNoDefs(pos,Label.CATCH_CONDITION,makeBinary(JCTree.AND,condtv,makeBinary(JCTree.AND,cond,inst,cpos),cpos),catchBlock.statements);
            
            cond = makeBinary(JCTree.AND,cond,makeUnary(JCTree.NOT,inst,cpos),cpos);

            //JCIdent id = newIdentUse(catcher.param.sym,cpos);
            JCIdent id = makeIdent(catcher.param.sym,cpos);
            addAssignmentStatement(catchBlock,cpos,id,exceptionVar);

            id = newIdentUse((VarSymbol)terminationVar.sym,cpos);
            addAssignmentStatement(catchBlock,cpos,id,zeroLiteral);
            
            catchBlock.statements.add(catcher.getBlock()); // it gets all of the remaining statements
            follows(catchBlock,finallyBlock);
            catchList.add(catchBlock);
            blocksToDo.add(i++,catchBlock); // push it on the to do list
        }
        // If there are any catch blocks then we need one final catch block for the
        // case that no other blocks have caught the exception.  This block may not be feasible.
        // We also make the block even if there are no catch blocks so that we know
        // when the catch blocks have been processed.  This is a bit tricky.
        {
            String catchBlockName = blockPrefix + that.pos + "$catchrest";
            BasicBlock catchBlock = newBlock(catchBlockName,that.pos);
            addAssumeNoDefs(pos,Label.SYN,makeBinary(JCTree.AND,condtv,cond,pos),catchBlock.statements); // Do not track 
            follows(catchBlock,finallyBlock);
            blocksToDo.add(0,catchBlock); // push it on the to do list, before the others
            catchList.add(catchBlock);
        }
        catchListStack.add(0,catchList);

        // Finish the processing of the current block 
        processBlockStatements(false);
    }
    
    public void visitCatch(JCCatch that) { 
        shouldNotBeCalled(that); 
    }
    
    public void visitIf(JCIf that) {
        currentBlock.statements.add(comment(that.pos,"if..."));
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
        JCIdent vd = newAuxIdent(condName,syms.booleanType,that.getStartPosition(),false);
        JCExpression newexpr = makeBinary(JCTree.EQ,vd,that.cond,that.cond.pos);
        addAssume(that.pos,Label.BRANCHC,trJavaExpr(newexpr));
        
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
        currentBlock.statements.add(comment(that));
        // This includes assignments and stand-alone method invocations
        that.expr.accept(this);
        // ignore the result; any statements are already added
    }
    
    protected java.util.List<JCStatement> breakStack = new java.util.LinkedList<JCStatement>();
    
    public void visitBreak(JCBreak that) { 
        currentBlock.statements.add(comment(that));
        if (breakStack.isEmpty()) {
            // ERROR - FIXME
        } else if (breakStack.get(0) instanceof JCSwitch) {
            // Don't need to do anything.  If the break is not at the end of a block,
            // the compiler would not have passed this.  If it is at the end of a block
            // the logic in handling JCSwitch has taken care of everything.
            
            // FIXME - for safety, check and warn if there are any remaining statements in the block
        } else if (that.label == null) {
            JCTree t = loopStack.get(0);
            String s = blockPrefix + t.pos + "$LoopBreak";
            BasicBlock b = blockLookup.get(s);
            if (b == null) log.noticeWriter.println("NO BREAK BLOCK: " + s);
            else replaceFollows(currentBlock,b);
        } else {
            Log.instance(context).error("esc.not.implemented","break statements with labels in BasicBlocker");
        }
    }
    
    public void visitContinue(JCContinue that) {
        currentBlock.statements.add(comment(that));
        if (that.label == null) {
            JCTree t = loopStack.get(0);
            String s = blockPrefix + t.pos + "$LoopContinue";
            BasicBlock b = blockLookup.get(s);
            if (b == null) log.noticeWriter.println("NO CONTINUE BLOCK: " + s);
            else replaceFollows(currentBlock,b);
        } else {
            Log.instance(context).warning("esc.not.implemented","continue statements with labels in BasicBlocker");
        }
    }
    
    public void visitReturn(JCReturn that) {
        currentBlock.statements.add(comment(that));
        if (that.getExpression() != null) {
            int p = that.getExpression().getStartPosition();
            JCExpression res = makeBinary(JCTree.EQ,resultVar,trJavaExpr(that.getExpression()),p);  // resultVar is not translated - shoudl be incase there are multiple returns executed FIXME
            addAssume(p,Label.ASSIGNMENT,res);
        }
        int pos = that.getStartPosition();
        JCIdent id = newIdentIncarnation(terminationVar,pos);
        JCLiteral lit = makeLiteral(pos,pos);
        JCExpression e = makeBinary(JCTree.EQ,id,lit,pos);
        addAssume(pos,Label.RETURN,e);
        if (tryreturnStack.isEmpty()) {
            replaceFollows(currentBlock,returnBlock);
        } else {
            BasicBlock finallyBlock = tryreturnStack.get(0);
            replaceFollows(currentBlock,finallyBlock);
        }
        if (!remainingStatements.isEmpty()) {
            // Not fatal
            Log.instance(context).warning("esc.internal.error","Unexpected statements following a return statement");
        }
    }
    
    public void visitThrow(JCThrow that) { 
        currentBlock.statements.add(comment(that));
        
        // Capture the exception expression
        int p = that.getExpression().getStartPosition();
        JCExpression res = trJavaExpr(that.getExpression());
        JCIdent idex = newIdentIncarnation(exceptionVar,p);
        JCExpression now = makeBinary(JCTree.EQ,idex,res,p);
        addAssume(p,Label.ASSIGNMENT,now); // <exceptionVar> = <throw-expression>
        
        int pos = that.getStartPosition();
        JCIdent id = newIdentIncarnation(terminationVar,pos);
        JCLiteral lit = makeLiteral(-pos,pos);
        JCExpression expr = makeBinary(JCTree.EQ,id,lit,pos);
        addAssume(pos,Label.SYN,expr); // <terminationVar> = -pos
        
        // FIXME - if we are already in a catch block we keep the finally block
        // as our follower.
        
        
        if (catchListStack.isEmpty()) {
            replaceFollows(currentBlock,exceptionBlock);
        } else {
            List<BasicBlock> catchList = catchListStack.get(0);
            if (catchList.isEmpty()) {
                replaceFollows(currentBlock,tryreturnStack.get(0)); // followed by the finally block
            } else {
                replaceFollows(currentBlock,catchList); // followed by all the catch blocks
            }
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
        currentBlock.statements.add(comment(that));
        JCExpression cond = trJavaExpr(that.cond);
        JCExpression detail = trJavaExpr(that.detail);
        // FIXME - what to do with detail
        // FIXME - for now turn cond into a JML assertion
        // FIXME - need a label for the assert statement
        // FIXME - set line and source
        addAssert(Label.EXPLICIT_ASSERT, cond, that.cond.getStartPosition(), newstatements, that.cond.getStartPosition(),log.currentSourceFile());
    }
    
    public void visitApply(JCMethodInvocation that) { 
        // This is an expression so we just use trExpr
        JCExpression now;
        JCExpression obj;
        MethodSymbol msym;
        Type.ForAll tfa = null;
        if (that.meth instanceof JCIdent) {
            now = trExpr(that.meth);
            msym = (MethodSymbol)((JCIdent)now).sym;
            if (msym.isStatic()) obj = null;
            else obj = currentThisId;
        } else if (that.meth instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)that.meth;
            msym = (MethodSymbol)(fa.sym);
            if (msym.isStatic()) obj = null;
            else obj = trExpr( fa.selected );
        } else {
            // FIXME - not implemented
            log.warning("esc.not.implemented","BasicBlocker.visitApply for that.meth.getClass()");
            msym = null;
            obj = null;
            result = trueLiteral;
            return;
        }
        if (msym.type instanceof Type.ForAll) tfa = (Type.ForAll)msym.type;

        // FIXME - what does this translation mean?
//        ListBuffer<JCExpression> newtypeargs = new ListBuffer<JCExpression>();
//        for (JCExpression arg: that.typeargs) {
//            JCExpression n = trExpr(arg);
//            newtypeargs.append(n);
//        }

        ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
        for (JCExpression arg: that.args) {
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
                    typeargs.put(tv.next().tsym,e.next().type);
                }
            } else {
                log.noticeWriter.println("NOT IMPLEMENTED - parameterized method call with implicit type parameters");
            }
        }

        // FIXME - concerned that the position here is not after the
        // positions of all of the arguments
        if (inSpecExpression) {
            result = insertSpecMethodCall(that.pos,msym,obj,that.typeargs,newargs.toList());
        } else {
            result = insertMethodCall(that.pos,msym,obj,newargs.toList()); // typeargs ? FIXME
        }
        
        popTypeArgs();
        return;
    }

    //boolean extraEnv = false;
    public void visitJmlMethodInvocation(JmlMethodInvocation that) { 
            // This is an expression so we just use trExpr
//        log.noticeWriter.println("NO CHECK OF APPLY");  FIXME
//        that.meth.accept(this);
//        for (JCExpression arg: that.args) {
        //            arg.accept(this);
        //        }

        JmlToken token = that.token;
        JCExpression arg;

        if (token == null) {
            
            // Presuming this is the checkfor null method
            // that.meth.sym == ???
            JCExpression e = that.meth;
            if (e instanceof JCFieldAccess) {
                Name n = ((JCFieldAccess)e).sym.name;
                if (n.toString().equals("nonNullCheck")) {
                    arg = trExpr(that.args.get(1));
                    checkForNull(arg,that.pos,trueLiteral,that.label);
                    result = arg;
                } else if (n.toString().equals("zeroIntCheck")) {
                    arg = trExpr(that.args.get(1));
                    checkForZero(arg,that.pos,trueLiteral,that.label);
                    result = arg;
                } else if (n.toString().equals("trueCheck")) {
                    JCExpression cond = trExpr(that.args.get(1));
                    arg = trExpr(that.args.get(2));
                    checkTrue(that.pos,cond,that.label);
                    result = arg;
                } else if (n.toString().equals("eqCheck")) {
                    JCExpression obj = trExpr(that.args.get(1));
                    arg = trExpr(that.args.get(2));
                    JCExpression cond = makeBinary(JCTree.EQ,arg,obj,that.pos);
                    checkTrue(that.pos,cond,that.label);
                    result = arg;
                } else if (n.toString().equals("intRangeCheck")) {
//                    JCExpression cond = trExpr(that.args.get(1));
//                    arg = trExpr(that.args.get(2));
//                    checkTrue(that.pos,cond,that.label);
//                    result = arg;
                } else {
                    System.out.println("NAME " + n);
                }
            } else {
                System.out.println("INTENRAL ERROR " );
                // FIXME 
            }

        } else {

            switch (token) {
                case BSOLD:
                case BSPRE:
                    // FIXME - there is a problem if the argument includes an identifier that
                    // is the quantified variable of a quantifier statement
                    VarMap prev = currentMap;
                    JCIdent label = that.args.size() > 1 ? (JCIdent)( that.args.get(1) ) : null ;
                    currentMap = oldMap;
                    try {
                        if (label != null) {
                            VarMap lmap = labelmaps.get(label.name);
                            if (lmap != null) currentMap = lmap;
                            else {
                                log.noticeWriter.println("BAD LABEL: " + label);
                            }
                        }
                        result = trExpr(that.args.get(0));
                    } finally {
                        currentMap = prev;
                    }
                    return;

                case BSTYPEOF:
                    arg = trExpr(that.args.get(0));
                    checkForNull(arg,that.pos,trueLiteral,null);
                    ListBuffer<JCExpression> lb = new ListBuffer<JCExpression>();
                    lb.append(arg);
                    result = factory.at(that.pos).JmlMethodInvocation(token,lb.toList());
                    result.type = syms.classType;
                    return;

                case BSTYPELC:
                    Type type = that.args.get(0).type;
                    type = trType(type);
                    addClassPredicate(type);
                    result = makeTypeLiteral(type,that.pos);
                    return;

                case BSELEMTYPE :
                    // FIXME - shutting up the warning, but not really implementing this
                    // Also need a check that the argument is non-null
                    arg = trExpr(that.args.get(0));
                    checkForNull(arg,that.pos,trueLiteral,null);
                    result = arg;// FIXME - wrong
                    return;

                case BSMAX :
                case BSREACH :
                case BSSPACE :
                case BSWORKINGSPACE :
                case BSDURATION :
                    Log.instance(context).warning("esc.not.implemented","Not yet implemented token in BasicBlocker: " + that.token.internedName());
                    result = trueLiteral; // FIXME - may not even be a boolean typed result
                    break;


                case BSFRESH :
                { // FIXME - define this to include being non-null - is that the JML definition?
                    int pos = that.pos;
                    JCExpression e = trExpr(that.args.get(0));
                    //checkForNull(e,that.pos,trueLiteral);
                    JCIdent alloc = newIdentUse(allocSym,pos);
                    // assume <newid>.alloc = <newalloc>
                    JCExpression ee = new JmlBBFieldAccess(allocIdent,e);
                    ee.pos = pos;
                    ee.type = syms.intType;
                    result = makeBinary(JCTree.AND,
                            makeBinary(JCTree.NE,e,nullLiteral,pos),
                            makeBinary(JCTree.EQ,ee,alloc,pos),pos);

                }
                break;

                //            case BSNOTMODIFIED:
                //                // Allows multiple arguments; they may be store-refs with wildcards (FIXME)
                //                JCExpression combined = null;
                //                for (JCExpression a : that.args){
                //                    // FIXME - there is an issue with condition - how do we evaluate if old(e) is well-defined?
                //                    //  defined as  arg == \old(arg)
                //                    int pos = that.pos;
                //                    JCExpression e = trExpr(a);
                //                    VarMap prevMap = currentMap;
                //                    currentMap = oldMap;
                //                    try {
                //                        // FIXME - what happens if not_modifieds are nested, or within an old
                //                        //extraEnv = true;
                //                        JCExpression ee = trExpr(a);
                //                        ee = makeBinary(JCTree.EQ,e,ee,pos);
                //                        if (combined == null) combined = ee;
                //                        else combined = makeBinary(JCTree.AND,combined,ee,pos);
                //                    } finally {
                //                        currentMap = prevMap;
                //                        //extraEnv = false;
                //                    }
                //                }
                //                result = combined;
                //                break;

                case BSNONNULLELEMENTS :
                {
                    int pos = that.pos;
                    arg = trExpr(that.args.get(0));
                    //checkForNull(arg,pos,trueLiteral);
                    Name fcnname = names.fromString("nnelement$" + encodeType(arg.type));
                    MethodSymbol msym = makeFunction(fcnname,syms.booleanType,arg.type);
                    result = makeFunctionApply(pos,msym,arg);

                    // also need an axiom: (\forall a, int i; i in range; a[i] != null)
                    Name index = names.fromString("index$");
                    JCIdent indexId = newAuxIdent(index,syms.intType,pos,false);
                    //JCIdent arrayId = newAuxIdent(array,arg.type,pos,false);
                    Type elemType = ((ArrayType)arg.type).elemtype;
                    JCIdent arrays = getArrayIdent(elemType);
                    JCExpression len = new JmlBBFieldAccess(lengthIdent,arg);
                    len.type = syms.intType;
                    len.pos = pos;
                    JCExpression range = makeBinary(JCTree.AND,makeBinary(JCTree.LE,zeroLiteral,indexId,pos),
                            makeBinary(JCTree.LT,indexId,len,pos),pos);
                    JCExpression acc = new JmlBBArrayAccess(arrays,arg,indexId,pos,elemType);
                    JCExpression predicate = makeBinary(JCTree.NE,acc,nullLiteral,pos);
                    JCExpression intTypeTree = factory.at(pos).TypeIdent(TypeTags.INT);
                    intTypeTree.type = syms.intType;
                    JCExpression e = factory.at(pos).JmlQuantifiedExpr(JmlToken.BSFORALL,
                            new ListBuffer<JCVariableDecl>().append(makeVariableDecl(index,syms.intType,pos)),
                            range,predicate);
                    e.type = syms.booleanType;
                    e = makeBinary(JCTree.AND,makeBinary(JCTree.NE,arg,nullLiteral,pos),e,pos);
                    e = makeBinary(JCTree.EQ,makeFunctionApply(pos,msym,arg),e,pos);
                    //                    e = factory.at(pos).JmlQuantifiedExpr(JmlToken.BSFORALL,null,
                    //                            new ListBuffer<JCExpression>().append(factory.Type(arg.type)),
                    //                            new ListBuffer<Name>().append(array),
                    //                            null,e);
                    background.add(e);        
                    //                    Log.instance(context).warning("esc.not.implemented","Not yet implemented token in BasicBlocker: " + that.token.internedName());
                    //                    result = trueLiteral; // FIXME 
                }
                break;

                case BSISINITIALIZED :
                case BSINVARIANTFOR :
                    Log.instance(context).warning("esc.not.implemented","Not yet implemented token in BasicBlocker: " + that.token.internedName());
                    result = trueLiteral; // FIXME 
                    break;

                case BSNOWARN:
                case BSNOWARNOP:
                case BSWARN:
                case BSWARNOP:
                case BSBIGINT_MATH:
                case BSSAFEMATH:
                case BSJAVAMATH:
                    Log.instance(context).warning("esc.not.implemented","Not yet implemented token in BasicBlocker: " + that.token.internedName());
                    result = trExpr(that.args.get(0)); // FIXME - just pass through for now
                    break;

                default:
                    Log.instance(context).error("esc.internal.error","Unknown token in BasicBlocker: " + that.token.internedName());
                result = trueLiteral; // FIXME - may not even be a boolean typed result
                break;
            }
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
        VarMap prevOldMap = oldMap;
        JCIdent prevThisId = thisId;
        JCExpression prevResultVar = resultVar;
        
        // FIXME - need to do a definedness check that the called method is guaranteed to normally terminate
        
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
                mspecs = JmlSpecs.defaultSpecs(0).cases;
            } else {
                decl = mspecs.decl;
            }    
            
            Name newMethod = specMethodCalls.get(sym);
            boolean notYetAxiomatized = newMethod == null;
            if (notYetAxiomatized) {
                // get the heap incarnation number
                Integer heapNum = currentMap.get((VarSymbol)heapVar.sym);
                newMethod = encodedName(sym,mspecs.pos,heapNum);
                specMethodCalls.put(sym,newMethod);
            }
            JCIdent newMethodName = 
                newAuxIdent(newMethod.toString(),sym.getReturnType(),pos,false); // FIXME - string to name to string to name

            if (obj == null && args.size() == 0) {
                // Static and no arguments, so we just use the new method name
                // as a constant
                newapply = newMethodName;
                if (notYetAxiomatized) {
                    resultVar = newMethodName; // FIXME - what about typeargs
                    for (JmlMethodClauseExpr post: mi.ensuresPredicates) {
                        JCExpression expr = trExpr(post.expression);
                        addAssume(Label.METHODAXIOM,expr,newstatements,false);
                    }
                }
            } else {
                // Need precondition check - FIXME

                // Construct what we are going to replace \result with
                ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
                if (obj != null) newargs.append(obj);
                for (JCExpression e: args) newargs.append(e);
                newapply = factory.at(pos).Apply(typeargs,newMethodName,newargs.toList());
                newapply.type = sym.getReturnType();
                // FIXME - needs type - is this right

                // Construct what we are going to replace \result with
                ListBuffer<JCExpression> margs = new ListBuffer<JCExpression>();

                ListBuffer<JCVariableDecl> decls = ListBuffer.<JCVariableDecl>lb();
                if (obj != null) {
                    margs.append(currentThisId);
                    decls.append(makeVariableDecl(thisId.name,syms.objectType,0)); // FIXME _ object type? // FIXME pos
                }
                if (decl != null) {
                    for (JCVariableDecl e: decl.params) {
                        JCIdent p = newIdentUse(e.sym,0);
                        margs.append(p);
                        decls.append(makeVariableDecl(p.name,e.type,0)); // FIXME - position
                    }
                } else {
                    // FIXME - I'm not sure when sym.params is null and when it is an empty list - got my first null with: assert \values.size() == \index
                    if (sym.params != null) for (VarSymbol e: sym.params) {
                        JCIdent p = newIdentUse(e,0);
                        margs.append(p);
                        decls.append(makeVariableDecl(p.name,e.type,0)); // FIXME - position
                    }
                }
                
                JCExpression mapply = factory.at(pos).Apply(null,newMethodName,margs.toList()); // FIXME - what about typeargs
                mapply.type = sym.getReturnType();

//                ListBuffer<Name> single = new ListBuffer<Name>();
//                single.append(thisId.name);
                if (notYetAxiomatized) {
                    resultVar = mapply;
                    for (JmlMethodClauseExpr post: mi.ensuresPredicates) {
                        JCExpression predicate = trExpr(post.expression);
                        JmlQuantifiedExpr expr = factory.at(pos).JmlQuantifiedExpr(
                                JmlToken.BSFORALL, decls, null, predicate);
                        expr.type = syms.booleanType;
                        addAssume(Label.METHODAXIOM,expr,newstatements,false);
                        // Need inherited specs, also interfaces - FIXME
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
    // pos is the preferred position of the method call (e.g. the left parenthesis)
    protected JCIdent insertMethodCall(int pos, MethodSymbol methodSym, JCExpression obj, List<JCExpression> args) {
        MethodSymbol baseMethodSym = methodSym;
        VarMap prevOldMap = oldMap;
        JCIdent prevThisId = thisId;
        JCIdent retId = methodSym.type == null ? null : newAuxIdent("$$result$"+pos,methodSym.getReturnType(),pos,true);
        JCIdent exceptionId = methodSym.type == null ? null : newIdentIncarnation(this.exceptionVar,pos);
        JCExpression prevResultVar = resultVar;
        JCIdent prevExceptionVar = exceptionVar;

        try {
            JmlClassInfo calledClassInfo = getClassInfo(methodSym.owner);
            JmlMethodSpecs mspecs = specs.getDenestedSpecs(methodSym);
            if (mspecs == null) {
                // This happens for a binary class with no specs for the given method.
                //log.noticeWriter.println("NO SPECS FOR METHOD CALL(A) " + sym.owner + "." + sym);
                mspecs = JmlSpecs.defaultSpecs(pos).cases;
            } //else 
            {
                boolean isStaticCalled = methodSym.isStatic();
                boolean isConstructorCalled = methodSym.isConstructor();
                boolean isHelperCalled = isHelper(methodSym);
                
                JCExpression expr;
                // all expressions are already translated, so we can now create
                // a new 'this' - the specs of the called method are translated
                // with 'this' being the receiver object
                
                // Assign the receiver to a new variable.  If the method called
                // is static, obj is null.
                if (obj != null) {
                    currentThisId = newAuxIdent("this$"+pos,methodSym.owner.type,pos,false);
                    addAssume(obj.pos,Label.RECEIVER,makeBinary(JCTree.EQ,currentThisId,obj,obj.pos));
                }
                
                // Assign each of the arguments to a new variable
                JmlMethodDecl decl = mspecs.decl;
                
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
                        for (JCVariableDecl vd  : decl.params) {
                            expr = args.get(i++);
                            JCIdent id = newIdentIncarnation(vd,pos);
                            addAssume(expr.getStartPosition(),Label.ARGUMENT, makeBinary(JCTree.EQ,id,expr,expr.pos));
                        }
                    } else if (methodSym.params != null) {
                        for (VarSymbol vd  : methodSym.params) {
                            expr = args.get(i++);
                            JCIdent id = newIdentIncarnation(vd,pos);
                            addAssume(expr.getStartPosition(),Label.ARGUMENT, makeBinary(JCTree.EQ,id,expr,expr.pos));
                        }
                    } else {
                        // No specifications for a binary method

                        // FIXME - but there might be specs for a super method and we need to have parameter mappings for them
                    }
                }
                

                if (isConstructorCalled) {
                    // Presuming that isConstructor
                    // We are calling a this or super constructor
                    // static invariants have to hold
                    if (!isHelperCalled && calledClassInfo != null) {
                        for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e,inv.source());
                            addAssert(Label.INVARIANT,e,inv.getStartPosition(),newstatements,pos,inv.source());
                        }
                    }
                } else if (!isConstructor && !isHelper) {
                    for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e,inv.source());
                        addAssert(Label.INVARIANT,e,inv.getStartPosition(),newstatements,pos,inv.source());
                    }
                    if (!isStatic) {
                        for (JmlTypeClauseExpr inv : classInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e,inv.source());
                            addAssert(Label.INVARIANT,e,inv.getStartPosition(),newstatements,pos,inv.source());
                        }
                    }
                }
                
                JmlMethodInfo mi = null;
                if (hasArgs) {
                    JCExpression exprr = null;
                    mi = getMethodInfo(methodSym);
                    int dpos = mi.decl == null ? pos : mi.decl.pos;
                    if (mi.requiresPredicates.size()==0) exprr = makeLiteral(true,dpos);
                    else for (JmlMethodClauseExpr pre: mi.requiresPredicates) {
                        JCExpression pexpr = trSpecExpr(pre.expression,pre.source());
                        if (exprr == null) exprr = pexpr;
                        else {
                            exprr = makeBinary(JCTree.OR,exprr,pexpr,exprr.pos);
                        }
                    }

                    if (!isConstructorCalled && !isStaticCalled) {
                        MethodSymbol msym = methodSym;
                        // FIXME - do this for interfaces as well
                        while ((msym=getOverrided(msym)) != null) {
                            exprr = addMethodPreconditions(currentBlock,msym,mi.decl,dpos,exprr); // FIXME - what position to use?
                        }
                    }
                    if (exprr == null) exprr = makeLiteral(true,pos);
                    addAssert(Label.PRECONDITION,exprr,exprr.getStartPosition(),newstatements,pos,log.currentSourceFile());

                    // Grap a copy of the map before we introduce havoced variables
                    oldMap = currentMap.copy();

                    // FIXME - I think there is a problem if the modifies list uses expressions
                    // that are also being havoced
                    havocAssignables(pos,mi); // expressions are evaluated in the pre-state
                }
                
                // Bump up the version of the heap
                boolean isPure = isPure(methodSym) || isPure(methodSym.enclClass());
                if (!isPure) newIdentIncarnation(heapVar,pos);

                // Bump up the allocation, in case there are any fresh declarations
                
                JCIdent oldalloc = newIdentUse(allocSym,pos);
                JCIdent alloc = newIdentIncarnation(allocSym,pos);

                // assume <oldalloc> < <newalloc>
                JCExpression ee = makeBinary(JCTree.LT,oldalloc,alloc,pos);
                addAssume(pos,Label.SYN,ee);

                
                // Take care of termination options
                
                resultVar = retId;
                exceptionVar = exceptionId;
                JCIdent termVar = newIdentIncarnation(terminationSym,pos);
                JCExpression termExp = makeBinary(JCTree.OR,
                                        makeBinary(JCTree.EQ,termVar,zeroLiteral,pos),
                                        makeBinary(JCTree.AND,
                                          makeBinary(JCTree.EQ,termVar,makeBinary(JCTree.MINUS,zeroLiteral,makeLiteral(pos,pos),pos),pos),
                                          makeInstanceof(exceptionVar,pos,syms.exceptionType,pos)
                                            ,pos),pos);
                addAssume(pos,Label.TERMINATION,termExp);

                // If there is a non-primitive result, we need to say that it is allocated (if not null)
                if (!baseMethodSym.isConstructor() && !baseMethodSym.getReturnType().isPrimitive()) {
                    declareAllocated(resultVar,pos);
//                    JCExpression eee = new JmlBBFieldAccess(allocIdent,resultVar);
//                    eee.pos = pos;
//                    eee.type = syms.intType;
//                    eee = makeBinary(JCTree.LT,eee,newIdentUse(allocSym,pos),pos);
//                    eee = makeBinary(JCTree.OR,eee,makeBinary(JCTree.EQ,resultVar,nullLiteral,pos),pos);
//                    addAssume(Label.SYN,eee,currentBlock.statements,false);
                }

                if (hasArgs) {   
                    JCExpression prevCondition2 = condition;
                    JCBinary nn = makeBinary(JCTree.NE,exceptionVar,nullLiteral,pos);
                    try {
                        JCBinary normalTerm = makeBinary(JCTree.LE,zeroLiteral,termVar,pos);
                        condition = makeBinary(JCTree.AND,condition,normalTerm,pos);
                        for (JmlMethodClauseExpr post: mi.ensuresPredicates) {
                            // (termVar >= 0) ==> <ensures condition>
                            addAssume(Label.POSTCONDITION,makeJmlBinary(JmlToken.IMPLIES,normalTerm,trSpecExpr(post.expression,post.source()),pos),newstatements,false);
                        }
                        JCBinary excTerm = makeBinary(JCTree.GT,zeroLiteral,termVar,pos);
                        condition = makeBinary(JCTree.AND,prevCondition2,excTerm,pos);
                        for (JmlMethodClauseExpr post: mi.exPredicates) {
                            JCExpression ex = ((JmlBinary)post.expression).lhs;
                            ex = ((JmlBinary)ex).lhs;
                            ex = ((JmlMethodInvocation)ex).args.get(0);
                            signalsVar = ex instanceof JCIdent ? (JCIdent)ex : null;
                            // (termVar < 0) ==> <signals condition>
                            addAssume(Label.SIGNALS,makeJmlBinary(JmlToken.IMPLIES,excTerm,trSpecExpr(makeBinary(JCTree.AND,nn,post.expression,pos),post.source()),pos),newstatements,false);
                            signalsVar = null;
                        }
                        for (JmlMethodClauseExpr post: mi.sigPredicates) {
                            // (termVar < 0) ==> <signals condition>
                            addAssume(Label.SIGNALS_ONLY,makeJmlBinary(JmlToken.IMPLIES,excTerm,trSpecExpr(makeBinary(JCTree.AND,nn,post.expression,pos),post.source()),pos),newstatements,false);
                        }
                    } finally {
                        condition = prevCondition2;
                    }
                    if (!isConstructorCalled && !isStaticCalled) {
                        // FIXME - do this for interfaces as well
                        MethodSymbol msym = methodSym;
                        while ((msym=getOverrided(msym)) != null) {
                            mi = getMethodInfo(msym);
                            addParameterMappings(mspecs.decl,mi.decl,pos,currentBlock);
                            for (JmlMethodClauseExpr post: mi.ensuresPredicates) {
                                addAssume(post.getStartPosition(),Label.POSTCONDITION,makeJmlBinary(JmlToken.IMPLIES,makeBinary(JCTree.LE,zeroLiteral,termVar,pos),trSpecExpr(makeBinary(JCTree.AND,nn,post.expression,pos),post.source()),pos));
                            }
                            for (JmlMethodClauseExpr post: mi.exPredicates) {
                                JCExpression ex = ((JmlBinary)post.expression).lhs;
                                ex = ((JmlBinary)ex).lhs;
                                ex = ((JmlMethodInvocation)ex).args.get(0);
                                signalsVar = ex instanceof JCIdent ? (JCIdent)ex : null;
                                addAssume(post.getStartPosition(),Label.SIGNALS,makeJmlBinary(JmlToken.IMPLIES,makeBinary(JCTree.GT,zeroLiteral,termVar,pos),trSpecExpr(makeBinary(JCTree.AND,nn,post.expression,pos),post.source()),pos));
                                signalsVar = null;
                            }
                            for (JmlMethodClauseExpr post: mi.sigPredicates) {
                                // (termVar < 0) ==> <signals condition>
                                addAssume(post.getStartPosition(),Label.SIGNALS_ONLY,makeJmlBinary(JmlToken.IMPLIES,makeBinary(JCTree.GT,zeroLiteral,termVar,pos),trSpecExpr(makeBinary(JCTree.AND,nn,post.expression,pos),post.source()),pos));
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
                            e = trSpecExpr(e,inv.source());
                            addAssume(Label.INVARIANT,e,newstatements,false);
                        }
                        for (JmlTypeClauseExpr inv : calledClassInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e,inv.source());
                            addAssume(Label.INVARIANT,e,newstatements,false);
                        }
                        for (JmlTypeClauseConstraint inv : calledClassInfo.staticconstraints) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e,inv.source());
                            addAssume(Label.CONSTRAINT,e,newstatements,false);
                        }
                    }
                } else if (!isHelper) {
                    for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e,inv.source());
                        addAssume(Label.INVARIANT,e,newstatements,false);
                    }
                    if (!isStatic) {
                        for (JmlTypeClauseExpr inv : classInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trSpecExpr(e,inv.source());
                            addAssume(Label.INVARIANT,e,newstatements,false);
                        }
                    }
                    for (JmlTypeClauseConstraint inv : classInfo.staticconstraints) {
                        JCExpression e = inv.expression;
                        e = trSpecExpr(e,inv.source());
                        addAssume(Label.CONSTRAINT,e,newstatements,false);
                    }
                    if (!isConstructor) {
                        if (!isStatic) {
                            for (JmlTypeClauseConstraint inv : classInfo.constraints) {
                                JCExpression e = inv.expression;
                                e = trSpecExpr(e,inv.source());
                                addAssume(Label.CONSTRAINT,e,newstatements,false);
                            }
                        }
                    }
                }
                // Take out the temporary variables for the arguments
                if (decl != null && decl.params != null) for (JCVariableDecl vd  : decl.params) {
                    currentMap.remove((VarSymbol)vd.sym);
                }
                
                // Now create an (unprocessed) block for everything that follows the
                // method call 
                String restName = blockPrefix + pos + "$afterCall$" + (unique++);
                BasicBlock brest = newBlock(restName,pos,currentBlock);// it gets all the followers of the current block
                List<JCStatement> temp = brest.statements; // Empty - swapping lists to avoid copying
                brest.statements = remainingStatements; // it gets all of the remaining statements
                remainingStatements = temp;
                // Don't because we are going to begin it below
                //blocksToDo.add(0,brest); // push it on the front of the to do list
                follows(currentBlock,brest);
                
                // We also need an empty block for the exception to go to.  We cannot
                // go directly to the exception block because some DSA variable
                // renaming may need to be done.
                BasicBlock bexc = newBlock(blockPrefix+pos+"$afterCallExc$" + (unique++),pos);
                blocksToDo.add(0,bexc); // push it on the front of the to do list
                follows(currentBlock,bexc);
                addAssumeNoDefs(pos,Label.SYN,makeBinary(JCTree.LT,terminationVar,zeroLiteral,pos),bexc.statements);
                
                if (tryreturnStack.isEmpty()) {
                    follows(bexc,exceptionBlock);
                } else {
                    // Need to go to all the catchers of the top try block - FIXME
                }
                
                // Now we have to complete the currentBlock and start brest
                // because we may be in the middle of translating an 
                // expression and any statement after this point has to go
                // into the next (the non-exception) block
                
                completed(currentBlock);
                startBlock(brest);
                addAssume(Label.SYN,makeBinary(JCTree.EQ,termVar,zeroLiteral,pos),brest.statements,false);
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
    
    // Generate a (translated) allocation predicate // FIXME - check this out and use it
    protected void declareAllocated(VarSymbol vsym, int pos) {
        JCIdent var = newIdentUse(vsym,pos);
        declareAllocated(var,pos);
    }
    
    // Generate a (translated) allocation predicate // FIXME - check this out and use it
    protected void declareAllocated(JCExpression e, int pos) {
        JCExpression eee = new JmlBBFieldAccess(allocIdent,e);
        eee.pos = pos;
        eee.type = syms.intType;
        eee = makeBinary(JCTree.LE,eee,newIdentUse(allocSym,pos),pos);
        eee = makeBinary(JCTree.OR,eee,makeBinary(JCTree.EQ,e,nullLiteral,pos),pos);
        addAssume(Label.SYN,eee,currentBlock.statements,false);
    }
    
    protected void havocAssignables(int pos, JmlMethodInfo mi) {
//        * a store-ref
//        *  is a JCIdent, a JCSelect (potentially with a null field), or a JmlStoreRefArrayRange;
//        *  there may be more than one use of a JmlStoreRefArrayRange, e.g. a[2..3][4..5] or
//        *  a.f[4..5].g[6..7]
        for (JmlMethodInfo.Entry entry: mi.assignables) {
            JCExpression preCondition = trSpecExpr(entry.pre,log.currentSourceFile()); // FIXME - fix this
            for (JCTree sr: entry.storerefs) {
                if (sr == null) {
                    Log.instance(context).error(pos,"jml.internal.error","Unexpected null store-ref in BasicBlocker.havocAssignables");
                    continue;
                }
                int npos = pos*100000 + sr.pos;
                JCExpression prevCondition = condition;
                if (sr instanceof JCIdent) {
                    JCIdent id = (JCIdent)sr;
                    if (id.sym.isStatic()) {  // FIXME - not correct for JML fields in interfaces
                        JCExpression oldid = trSpecExpr(id,log.currentSourceFile()); // FIXME
                        JCIdent newid = newIdentIncarnation(id,npos); // new incarnation
                        // newid == precondition ? newid : oldid
                        JCExpression e = factory.at(pos).Conditional(preCondition,newid,oldid);
                        e.type = newid.type;
                        e = makeBinary(JCTree.EQ,newid,e,pos);
                        addAssume(pos,Label.HAVOC,e,currentBlock.statements,false);
                    } else {
                        // Same as for JCFieldAccess except that fa.selected is always 'this' (currentThisId)
                        Type type = id.type;
                        checkForNull(currentThisId,id.pos,preCondition,null);

                        JCIdent oldid = newIdentUse((VarSymbol)id.sym,id.pos);
                        JCFieldAccess oldaccess = new JmlBBFieldAccess(oldid,currentThisId);
                        oldaccess.pos = id.pos;
                        oldaccess.type = type;

                        JCIdent newid = newIdentIncarnation(oldid,npos);
                        JCFieldAccess newaccess = new JmlBBFieldAccess(newid,currentThisId);
                        newaccess.pos = id.pos;
                        newaccess.type = type;

                        JCExpression right = factory.at(id.pos).Conditional(preCondition,newaccess,oldaccess);
                        right.type = type;
                        
                        JCExpression expr = new JmlBBFieldAssignment(newid,oldid,currentThisId,right);
                        expr.pos = pos;
                        expr.type = type;

                        addAssume(pos,Label.HAVOC,expr,currentBlock.statements,false);
                    }
                } else if (sr instanceof JCFieldAccess) {
                    // FIXME - this duplicates logic in visitSelect and doAssignment
                    // s.f' = precondition ? s.f' : s.f
                    JCFieldAccess fa = (JCFieldAccess)sr;
                    JCExpression selected = fa.selected;
                    boolean isType = true;
                    if ((selected instanceof JCIdent) && ((JCIdent)selected).sym instanceof ClassSymbol) {
                        // do nothing
                    } else if ((selected instanceof JCFieldAccess) && ((JCFieldAccess)selected).sym instanceof ClassSymbol) {
                        // do nothing
                    } else {
                        selected = trSpecExpr(fa.selected,log.currentSourceFile()); // FIXME
                        isType = false;
                    }

                    try {
                        if (!isType) checkForNull(selected,sr.pos,preCondition,null);

                        if (fa.sym == null) {
                            Symbol ownerSym = fa.selected.type.tsym;
                            if (ownerSym instanceof ClassSymbol) {
                                ClassSymbol csym = (ClassSymbol)ownerSym;
                                Scope.Entry symentry = csym.members().elems;
                                while (symentry != null) {
                                    Symbol sym = symentry.sym;
                                    symentry = symentry.sibling;
                                    if (sym instanceof VarSymbol) {
                                        if (sym.isStatic()) { // FIXME _ not correct for JML fields in interfaces
                                            JCIdent newid = newIdentIncarnation((VarSymbol)sym,npos);
                                            JCExpression e = makeBinary(JCTree.EQ,newid,newid,npos);
                                            addAssume(sr.pos,Label.HAVOC,e,currentBlock.statements,false);
                                            
                                        } else if (!isType) {
                                            havocField((VarSymbol)sym,selected,fa.pos,npos,sym.type,preCondition);
                                        }
                                    }
                                }
                            } else {
                                log.noticeWriter.println("FOUND " + ownerSym.getClass());
                            }

                        } else {
                            VarSymbol vsym = (VarSymbol)fa.sym;
                            havocField(vsym,selected,fa.pos,npos,fa.type,preCondition);
                        }
                    } finally {
                        condition = prevCondition;
                    }
                    
                } else if (sr instanceof JmlStoreRefArrayRange) {
                    JmlStoreRefArrayRange ar = (JmlStoreRefArrayRange)sr;
                    
                    ListBuffer<Name> ns = new ListBuffer<Name>();
                    JCExpression array = extractQuantifiers(ar.expression,ns);

                    condition = makeBinary(JCTree.AND,condition,preCondition,sr.pos);
                    try {
                        if (ar.hi != ar.lo || ar.lo == null) {
                            // wildcard at the top level
                            if (ns.size() > 0) {
                                // and wildcards within
                            } else {
                                // no wildcards within
                                
                                JCIdent arrayId = getArrayIdent(sr.type);
                                
                                array = trSpecExpr(array,log.currentSourceFile()); // FIXME
                                checkForNull(array,sr.pos,trueLiteral,null);

                                JCExpression indexlo = trSpecExpr(ar.lo,log.currentSourceFile()); // FIXME
                                if (indexlo != null) checkArrayAccess(array,indexlo,sr.pos);
                                else indexlo = zeroLiteral;
                                
                                JCExpression indexhi = trSpecExpr(ar.hi,log.currentSourceFile()); // FIXME
                                boolean above = false;
                                if (indexhi != null) checkArrayAccess(array,indexhi,sr.pos);
                                else {
                                    //indexhi = factory.at(sr.pos).Select(array,lengthSym);
                                    indexhi = new JmlBBFieldAccess(lengthIdent,array);
                                    indexhi.pos = sr.pos;
                                    indexhi.type = syms.intType;
                                    above = true;
                                }
                                
                                
                                JCIdent nid = newArrayIncarnation(sr.type,pos);
                                JCExpression e = new JmlBBArrayHavoc(nid,arrayId,array,indexlo,indexhi,preCondition,above);

                                addAssume(pos,Label.HAVOC,e,currentBlock.statements,false);

                            }
                        } else {
                            // single element at the top level

                            if (ns.size() > 0) {
                                // FIXME - this is all wrong
                                // But wild-cards within the ar.expression

//                                JCIdent label = newAuxIdent("havoclabel$"+npos,syms.intType,npos,false);
//                                labelmaps.put(label.name,currentMap.copy());
//                                JCExpression oldaccess = factory.at(npos).JmlMethodInvocation(JmlToken.BSOLD,access,label);
//
//                                JCArrayAccess newaccess = factory.at(access.pos).Indexed(access.indexed,access.index);
//                                newaccess.type = access.type;
//
//                                //                            JCIdent meth = newAuxIdent("arbitrary$",syms.intType,npos);
//                                //                            ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
//                                //                            for (Name n: ns) {
//                                //                                JCIdent id = factory.at(npos).Ident(n);
//                                //                                id.type = syms.intType;
//                                //                                args.append(id);
//                                //                            }
//                                //                            JCMethodInvocation app = factory.at(npos).Apply(null,meth,args.toList());
//                                //                            app.type = ar.type;
//
//                                JCConditional cond = factory.at(sr.pos).Conditional(
//                                        makeBinary(JCTree.AND,entry.pre,accumRange,npos),newaccess,oldaccess);
//                                cond.type = access.type;
//
//                                JCExpression assign = makeBinary(JCTree.EQ,newaccess,cond,npos);
//
//                                JmlQuantifiedExpr quant = factory.at(sr.pos).JmlQuantifiedExpr(JmlToken.BSFORALL,null,factory.Type(syms.intType),ns,fullRange,assign);
//
//                                JCIdent nid = newArrayIncarnation(sr.type,npos);                            
//                                JmlQuantifiedExpr trQuant = (JmlQuantifiedExpr)trSpecExpr(quant,log.currentSourceFile()); // FIXME
//                                // Now we fix up the expression
//                                JCExpression predicate = trQuant.predicate;
//                                JCBinary bin = (JCBinary)predicate;
//                                cond = (JCConditional)bin.rhs;
//                                JmlBBArrayAccess newaa = (JmlBBArrayAccess)cond.truepart;
//                                JmlBBArrayAccess oldaa = (JmlBBArrayAccess)cond.falsepart;
//
//                                JCExpression expr = new JmlBBArrayAssignment(nid,oldaa.arraysId,oldaa.indexed,oldaa.index,cond);
//                                expr.pos = sr.pos;
//                                expr.type = cond.type;
//
//                                trQuant.predicate = expr;
//
//                                addAssume(pos,Label.HAVOC,trQuant,currentBlock.statements,false);

                            } else {
                                // single element
                                // a'[i] = preCondition ? a'[i] : a[i];

                                array = trSpecExpr(array,log.currentSourceFile()); // FIXME
                                checkForNull(array,sr.pos,trueLiteral,null);

                                JCExpression index = trSpecExpr(ar.lo,log.currentSourceFile()); // FIXME
                                checkArrayAccess(array,index,sr.pos);

                                JCIdent arrayID = getArrayIdent(sr.type);
                                JCExpression oldvalue = new JmlBBArrayAccess(arrayID,array,index,sr.pos,sr.type);

                                JCIdent nid = newArrayIncarnation(sr.type,pos);
                                JCExpression newvalue = new JmlBBArrayAccess(nid,array,index,sr.pos,sr.type);

                                JCExpression condValue = factory.at(sr.pos).Conditional(preCondition,newvalue,oldvalue);
                                condValue.type = oldvalue.type;

                                JCExpression expr = new JmlBBArrayAssignment(nid,arrayID,array,index,condValue);
                                expr.pos = sr.pos;
                                expr.type = oldvalue.type;
                                addAssume(pos,Label.HAVOC,expr,currentBlock.statements,false);
                            }
                        }
                    } finally {
                        condition = prevCondition;
                    }
                    
                } else if (sr instanceof JmlStoreRefKeyword) {
                    if (((JmlStoreRefKeyword)sr).token == JmlToken.BSNOTHING) {
                        // OK
                    } else {
                        havocEverything(preCondition,sr.pos);
                    }
                } else if (sr instanceof JmlSingleton) { // FIXME - why do we get JmlSingleton as a store-ref?
                    if (((JmlSingleton)sr).token == JmlToken.BSNOTHING) {
                        // OK
                    } else {
                        havocEverything(preCondition,sr.pos);
                    }
                } else {
                    Log.instance(context).error(sr.pos,"jml.internal.error","Unexpected kind of store-ref in BasicBlocker.havocAssignables: " + sr.getClass());
                }
            }
        }
    }
    
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
                fullRange = makeBinary(JCTree.AND,fullRange,makeBinary(JCTree.LE,zeroLiteral,id,a.pos),a.pos);
                //JCExpression len = factory.at(a.pos).Select(a.expression,lengthSym);
                JCExpression len = new JmlBBFieldAccess(lengthIdent,a.expression);
                len.pos = a.pos;
                len.type = syms.intType;
                fullRange = makeBinary(JCTree.AND,fullRange,makeBinary(JCTree.LT,id,len,a.pos),a.pos);
                if (a.lo != null) accumRange = makeBinary(JCTree.AND,accumRange,makeBinary(JCTree.LE,a.lo,id,a.lo.pos),a.lo.pos);
                if (a.hi != null) accumRange = makeBinary(JCTree.AND,accumRange,makeBinary(JCTree.LE,id,a.hi,a.hi.pos),a.hi.pos);
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

        addAssume(pos,Label.HAVOC,expr,currentBlock.statements,false);

    }
    
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
            e = makeBinary(JCTree.EQ,newid,e,newpos);
            addAssume(newpos,Label.HAVOC,e,currentBlock.statements,false);
        }
        currentMap.everythingIncarnation = newpos; // FIXME - this now applies to every not-yet-referenced variable, independent of the preCondition
    }
    
    public void visitSkip(JCSkip that) {
        // do nothing
    }
    public void visitJmlStatement(JmlStatement that) {
        // These are the set and debug statements
        // Just do all the JML statements as if they were Java statements, 
        // since they are part of specifications
        
        // FIXME _ should never reach this anymore
        log.noticeWriter.println("SHOULD NOT HAVE REACHED HERE - BasicBLocker.visitJmlStatment " + that.token.internedName());
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
    
    public JmlStatementExpr comment(int pos, String s) {
        return factory.at(pos).JmlExpressionStatement(JmlToken.COMMENT,null,factory.Literal(s));
    }
    
    public JmlStatementExpr comment(JCTree t) {
        return comment(t.pos,JmlPretty.write(t,false));
    }
    
    public void visitJmlStatementExpr(JmlStatementExpr that) { 
        JmlStatementExpr now = null;
        if (that.token != JmlToken.COMMENT) currentBlock.statements.add(comment(that));
        if (that.token == JmlToken.ASSUME || that.token == JmlToken.ASSERT) {
            JCExpression expr = trSpecExpr(that.expression,that.source);
            JCExpression opt = trSpecExpr(that.optionalExpression,that.source);
            if (that.token == JmlToken.ASSUME) {
//                if (that.label == Label.EXPLICIT_ASSUME || that.label == Label.BRANCHT || that.label == Label.BRANCHE) {
//                    now = factory.at(that.pos).JmlExpressionStatement(that.token,that.label,expr);
//                    now.optionalExpression = opt;
//                    now.type = that.type;   
//                } else {
                    now = factory.at(that.pos).JmlExpressionStatement(that.token,that.label,expr);
                    now.optionalExpression = opt;
                    now.type = that.type;   
//                }
                currentBlock.statements.add(now);
            } else {
                addAssert(that.label,expr,that.declPos,newstatements,that.pos,that.source);
            }
            if (that.token == JmlToken.ASSUME &&
                    (that.label == Label.EXPLICIT_ASSUME 
                    || that.label == Label.BRANCHT || that.label == Label.BRANCHE)) {
                checkAssumption(that.pos,that.label);
            }

        } else if (that.token == JmlToken.UNREACHABLE) {
            JCExpression expr = makeLiteral(false,that.getStartPosition());
            addAssert(Label.UNREACHABLE,expr,that.getStartPosition(),currentBlock.statements,that.getStartPosition(),log.currentSourceFile());
        } else if (that.token == JmlToken.HENCE_BY) {
            log.error("esc.not.implemented","hence_by is in BasicBlocker");
        } else if (that.token == JmlToken.COMMENT) {
            // skip
        } else {
            log.error("esc.internal.error","Unknown token in BasicBlocker: " + that.token.internedName());
        }
    }
    
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
    
    static public boolean insertAssumptionChecks = true;
    
    static boolean useCountedAssumeCheck = true;
    static JCExpression booleanAssumeCheck;
    JCExpression assumeCheck = null;

    // We introduce the name 'assumeCheck$<int>$<label>' in order to make
    // it easy to identify the places where assumptions are being checked.
    /** Adds (translated) assertions/assumptions that do assumption feasibility checking 
     * for an assumption that is just added to the currentBlock
     * @param _pos a positive integer different than that used for any other checkAssumption call;
     *    it should also be the textual location of the assumption being tested
     * @param label a Label givin gthe kind of assumption being tested (in order to
     *    better interpret the implications of the assumptino not being feasible)
     */
    
    protected void checkAssumption(int pos, /*@ non_null*/ Label label, List<JCStatement> statements) {
        if (!insertAssumptionChecks) return;
        JCExpression e,id;
        String n = "assumeCheck$" + pos + "$" + label.toString();
        if (useCountedAssumeCheck) {
            JCExpression count = makeLiteral(pos,pos);
            e = makeBinary(JCTree.NE,assumeCheckCountVar,count,pos);
            id = newAuxIdent(n,syms.booleanType,e.pos,false);
            e = makeBinary(JCTree.EQ,id,e,pos);
            // assume assumeCheck$<int>$<label> == <assumeCheckCountVar> != <int>
            // To do the coreId method, we need to put this in the definitions list
            // instead.  And it does not hurt anyway.
            //addAssume(pos,Label.ASSUME_CHECK,e); // adds to the currentBlock
            newdefs.add(e);
        } else {
            id = newAuxIdent(n,syms.booleanType,pos,false);
            e = id;
            if (assumeCheck == null) assumeCheck = e;
            else assumeCheck = makeBinary(JCTree.AND,e,assumeCheck,pos);
        }
        program.assumptionsToCheck.add(new Entry(e,n));
        // an assert without tracking
        // assert assumeCheck$<int>$<label>
        addAssertNoTrack(Label.ASSUME_CHECK,id,statements,pos,null); // FIXME - need the position of the assume, I think
    }
    
    public static class Entry implements Map.Entry<JCExpression,String> {
        JCExpression key;
        String value;
        public Entry(JCExpression e, String s) { key=e; value=s; }
        public JCExpression getKey() { return key; }
        public String getValue() { return value; }
        public String setValue(String value) { String v = value; this.value = value; return v;}
    }

    protected void checkAssumption(int pos, /*@ non_null*/ Label label) {
        checkAssumption(pos,label,currentBlock.statements);
    }
    
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        currentBlock.statements.add(comment(that));
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
            result = doAssignment(that.type,arg,e,that.pos+1);
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
        if (that.getTag() == JCTree.PLUS && that.type == syms.stringType) {
            JCIdent concat = newAuxIdent("concat$",syms.stringType,that.pos,false);
            JCExpression nleft = left;
            JCExpression nright = right;
            // FIXME - we should actually use proper conversion methods here and for other binary operators
            if (nleft.type != syms.stringType) {
                nleft = newAuxIdent("STRING$$" + (unique++),syms.stringType,left.pos,false);
            }
            if (nright.type != syms.stringType) {
                nright = newAuxIdent("STRING$$" + (unique++),syms.stringType,right.pos,false);
            }
            JCMethodInvocation now = factory.at(that.pos).Apply(null,concat,com.sun.tools.javac.util.List.<JCExpression>of(nleft,nright));
            now.type = syms.stringType;
            result = now;
            return;
        }
        JCBinary now = makeBinary(that.getTag(),left,right,that.pos);
        now.operator = that.operator;
        now.type = that.type;
        //if (now.type == null) now.type = syms.booleanType; // HACK
        now.pos = that.pos;
        result = now;
        if (that.getTag() == JCTree.DIV || that.getTag() == JCTree.MOD) {
            JCExpression e = makeBinary(JCTree.NE,that.rhs,zeroLiteral,that.rhs.pos);
            e = makeJmlBinary(JmlToken.IMPLIES,condition,e,that.rhs.pos);
            addAssert(inSpecExpression?Label.UNDEFINED_DIV0:Label.POSSIBLY_DIV0,
                    e,that.pos,currentBlock.statements,that.pos,log.currentSourceFile());
        }
    }
    
    public void visitTypeCast(JCTypeCast that) { 
        JCExpression e = trExpr(that.getExpression());
        if (that.type.isPrimitive()) {
            // FIXME - not implemented for numeric casts
            result = e;
        } else {
            Type type = trType(that.getType().type);
            JCExpression nnull = makeBinary(JCTree.EQ,e,nullLiteral,that.pos);
            JCExpression inst = makeNNInstanceof(e,e.pos,type,that.clazz.pos);
            inst = makeBinary(JCTree.OR,nnull,inst,that.pos);
            JCExpression test = makeJmlBinary(JmlToken.IMPLIES,condition,inst,e.getStartPosition());
            addAssert(inSpecExpression?Label.UNDEFINED_BADCAST:Label.POSSIBLY_BADCAST,
                    test,that.pos,currentBlock.statements,that.pos,log.currentSourceFile());

            addClassPredicate(type);
            JCLiteral lit = makeTypeLiteral(type,that.getType().getStartPosition());
            JCTypeCast now = factory.at(that.pos).TypeCast(lit,e);
            now.type = that.type;
            result = now;
        }
    }
    
    public void visitTypeTest(JCInstanceOf that) {
        JCExpression e = trExpr(that.getExpression());
        Type t = trType(that.getType().type);
        result = makeInstanceof(e,e.pos,t,that.getType().pos);
    }
    
    public void visitIndexed(JCArrayAccess that) { 
        JCExpression array = trExpr(that.getExpression());
//        checkForNull(array,that.pos,trueLiteral,null);
        
        JCExpression index = trExpr(that.getIndex());
        checkArrayAccess(array,index,that.pos);
        
        JCIdent arrayID = getArrayIdent(that.type);
        result = new JmlBBArrayAccess(arrayID,array,index,that.pos,that.type);
    }
    
    protected void checkForNull(JCExpression objTrans, int pos, JCExpression precondition, Label label) {
        //if (objTrans == thisId) return; // 'this' is always non-null
        JCExpression c = precondition == trueLiteral ? condition : makeBinary(JCTree.AND,condition,precondition,condition.pos);
        JCExpression e = makeBinary(JCTree.NE,objTrans,nullLiteral,pos);
        e = makeJmlBinary(JmlToken.IMPLIES,c,e,pos);
        addAssert(label != null ? label : inSpecExpression?Label.UNDEFINED_NULL:Label.POSSIBLY_NULL,
                e,pos,currentBlock.statements,pos,log.currentSourceFile());
    }
    
    protected void checkForZero(JCExpression objTrans, int pos, JCExpression precondition, Label label) {
        //if (objTrans == thisId) return; // 'this' is always non-null
        JCExpression c = precondition == trueLiteral ? condition : makeBinary(JCTree.AND,condition,precondition,condition.pos);
        JCExpression e = makeBinary(JCTree.NE,objTrans,zeroLiteral,pos);
        e = makeJmlBinary(JmlToken.IMPLIES,c,e,pos);
        addAssert(label != null ? label : inSpecExpression?Label.UNDEFINED_DIV0:Label.POSSIBLY_DIV0,
                e,pos,currentBlock.statements,pos,log.currentSourceFile());
    }
    
    protected void checkTrue(int pos, JCExpression assertion, Label label) {
        //if (objTrans == thisId) return; // 'this' is always non-null
        JCExpression e = makeJmlBinary(JmlToken.IMPLIES,condition,assertion,pos);
        addAssert(label,e,pos,currentBlock.statements,pos,log.currentSourceFile());
    }
    
    protected void checkArrayAccess(JCExpression arrayTrans, JCExpression indexTrans, int pos) {
        
        JCExpression index = indexTrans;
        
        // Require  that.index is not negative
        JCExpression e = makeBinary(JCTree.GE,index,zeroLiteral,index.pos);
        e = makeJmlBinary(JmlToken.IMPLIES,condition,e,e.pos);
        addAssert(inSpecExpression?Label.UNDEFINED_NEGATIVEINDEX:Label.POSSIBLY_NEGATIVEINDEX,
                e,pos,currentBlock.statements,pos,log.currentSourceFile());
        
        // Require  that.index is not too large
        e = new JmlBBFieldAccess(lengthIdent,arrayTrans);
        e.pos = pos;
        e.type = syms.intType;
        e = makeBinary(JCTree.LT,index,e,index.pos);
        e = makeJmlBinary(JmlToken.IMPLIES,condition,e,e.pos);
        addAssert(inSpecExpression?Label.UNDEFINED_TOOLARGEINDEX:Label.POSSIBLY_TOOLARGEINDEX,
                e,pos,currentBlock.statements,pos,log.currentSourceFile());
    }
    
    public void visitSelect(JCFieldAccess that) {
        Symbol sym = that.sym;
        if (sym == null) {
            log.noticeWriter.println("NULL SYM IN SELECT: " + that.name); // FIXME
        } else if (sym.isStatic()) {  // FIXME - isStatic is not correct for JML fields in interfaces
            // FIXME - is there something predefined to compare against?
            if (sym.toString().equals("class")) {
                // Class literal
                Type ty = trType(that.selected.type);
                addClassPredicate(ty);
                JCExpression now = factory.at(that.pos).Literal(TypeTags.CLASS,ty);
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
            //checkForNull(selected,that.pos,trueLiteral,null);

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
            if (owner != null && owner instanceof ClassSymbol && !vsym.isStatic() &&  // FIXME isStatic not correct forJML fields in interfaces
                    vsym.name != names._this) {
                // This is a field reference without the default this. prefix
                // We need to make it a JCFieldAccess with a 'this'
                
                // FIXME - is there a symbol for this?
                JCIdent thisIdX = factory.Ident(names._this);
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
            } else if (vsym.name == names._this) {
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
                // Don't translate this type - it is treated like Java
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
            addAssume(pos,Label.ASSIGNMENT,expr,newstatements,false);
//            JmlStatementExpr assume = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
//            newstatements.add(assume); 
            return left;
        } else if (left instanceof JCArrayAccess) {
            JCIdent arr = getArrayIdent(right.type);
            JCExpression ex = ((JCArrayAccess)left).indexed;
            JCIdent nid = newArrayIncarnation(right.type,pos);
            JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,((JCArrayAccess)left).index,right);
            expr.pos = pos;
            expr.type = restype;

            // FIXME - set line and source
            addAssume(pos,Label.ASSIGNMENT,expr,newstatements,false);
//            JmlStatementExpr assume = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
//            newstatements.add(assume); 
            newIdentIncarnation(heapVar,pos);
            return left;
        } else if (left instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)left;
            JCIdent oldfield = newIdentUse((VarSymbol)fa.sym,pos);
            JCIdent newfield = newIdentIncarnation(oldfield,pos);
            JCExpression expr = new JmlBBFieldAssignment(newfield,oldfield,fa.selected,right);
            expr.pos = pos;
            expr.type = restype;

            // FIXME - set line and source
            addAssume(pos,Label.ASSIGNMENT,expr,newstatements,false);
//            JmlStatementExpr assume = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
//            newstatements.add(assume); 
            newIdentIncarnation(heapVar,pos);
            return left;
        } else {
            log.noticeWriter.println("INCARNATION NOT IMPLERMENTED - visitAssign");
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
        currentBlock.statements.add(comment(that));
        JCIdent lhs = newIdentIncarnation(that,that.getPreferredPosition());
        if (that.init != null) {
            // Create and store the new lhs incarnation before translating the
            // initializer because the initializer is in the scope of the newly
            // declared variable.  Actually if there is such a situation, it 
            // will likely generate an error about use of an uninitialized variable.
            JCExpression init = trJavaExpr(that.init);
            JCBinary expr = makeBinary(JCBinary.EQ,lhs,init,that.pos);
            addAssume(that.pos,Label.ASSIGNMENT,expr,newstatements,false);
//            JmlStatementExpr assume = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
//            newstatements.add(assume);       
        }
    }
    
    public void visitSynchronized(JCSynchronized that)   { 
        // FIXME - for now ignore any synchronization
        trExpr(that.getExpression());  // just in case there are side-effects
        that.body.accept(this);
    }
    
    List<Map<Symbol,Type>> typeargsStack = new LinkedList<Map<Symbol,Type>>();
    Map<Symbol,Type> typeargs = new HashMap<Symbol,Type>();
    public void pushTypeArgs() {
        typeargsStack.add(0,typeargs);
        typeargs = new HashMap<Symbol,Type>();
    }
    public void popTypeArgs() {
        typeargs = typeargsStack.remove(0);
    }
    public void pushTypeArgs(Type type) {
        if (type.getTypeArguments() != null && type.getTypeArguments().size() != 0) {
            pushTypeArgs();
            Iterator<Type> args = type.getTypeArguments().iterator();
            Iterator<TypeSymbol> params = type.tsym.getTypeParameters().iterator();
            while (params.hasNext()) {
                typeargs.put(params.next(),args.next());
            }
        }
    }
    public void popTypeArgs(Type type) {
        if (type.getTypeArguments() != null && type.getTypeArguments().size() != 0) {
            popTypeArgs();
        }
    }
    
    public Type trType(Type type) {
        if (type instanceof Type.TypeVar) {
            Type t = typeargs.get(type.tsym);
            type = t != null ? t : ((Type.TypeVar)type).getUpperBound(); // FIXME - what about the other bounds?
        }
        return type;
    }
    
    public void visitNewClass(JCNewClass that) {
        // FIXME - ignoring enclosing expressions; ignoring anonymous classes
        
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
        JCIdent id = newAuxIdent("$$new"+pos+"$",that.type,pos,false);
        JCIdent prevId = currentThisId;
        VarMap prevOldMap = oldMap;
        JCExpression prevResultVar = resultVar;
        
        try {
            
            Symbol.MethodSymbol sym = (MethodSymbol)that.constructor;
            JmlSpecs.MethodSpecs mspecs = specs.getSpecs(sym);
            if (mspecs == null) {
                mspecs = JmlSpecs.defaultSpecs(0); // FIXME - is this OK
//                Log.instance(context).error("jml.internal","Unexpected failure to find specifications (even an empty spec) for method " + sym.owner + "." + sym);
//                throw new JmlInternalError();
            } 
            
            if (sym.params == null && sym.erasure_field != null) {
                log.noticeWriter.println("BINARY GENERIC NOT IMPLEMENTED - exiting " + sym);
                throw new RuntimeException();
            }

            // Evaluate all of the arguments and assign them to new variables
            decl = mspecs.cases.decl;
            int dpos = decl == null ? pos : decl.pos;
            int i = 0;
            if (sym.params != null) for (VarSymbol vd  : sym.params) {
                JCExpression expr = that.args.get(i++);
                JCIdent pid = newIdentIncarnation(vd,pos);
                addAssume(expr.pos,Label.ARGUMENT,makeBinary(JCTree.EQ,pid,trExpr(expr),expr.pos));
            }
            
            if (type.getTypeArguments() != null) {
                pushTypeArgs();
                Iterator<Type> arg = type.getTypeArguments().iterator();
                Iterator<Type> param = sym.type.asMethodType().getTypeArguments().iterator();
                while (arg.hasNext() && param.hasNext()) { // FIXME - look into this - for constructors at least there may not be any type arguments
                    typeargs.put(param.next().tsym,arg.next());
                }
            }

            // FIXME - observed that for the Object() constructor sym != mspecs.decl.sym ?????

            // Define a new thisId before translating the precondition
            currentThisId = id;
            resultVar = currentThisId;
            
            isHelper = isHelper(sym);
            mi = getMethodInfo(sym);
            for (JmlMethodClauseExpr pre: mi.requiresPredicates) {   // FIXME - need to put the composite precondition here
                addAssert(Label.PRECONDITION,trExpr(pre.expression),dpos,newstatements,pos,pre.source());
            }


            // Save the current incarnation map, so that instances of \old in the
            // postconditions of the called method are mapped to values just before
            // the havoc of assigned variables (and not to the values at the beginning
            // of the method being translated).
            oldMap = currentMap.copy();

            // Now make a new incarnation value for anything in the assignables list,
            // effectively making its value something legal but undefined.
            // FIXME - if we do this, then we have to redo any field initializations, etc.
            // FIXME - do we have the default right
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
                            log.noticeWriter.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                        }
                    } else if (sr instanceof JmlStoreRefKeyword) {
                        if (((JmlStoreRefKeyword)sr).token == JmlToken.BSNOTHING) {
                            // OK
                        } else {
                            log.noticeWriter.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                        }
                    } else {
                        log.noticeWriter.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                    }
                }
            }
            
            Type typeToConstruct = that.clazz.type;
            // FIXME - should really only do this translation when in a specification
            typeToConstruct = trType(typeToConstruct);
            addClassPredicate(typeToConstruct);

            JCIdent oldalloc = newIdentUse(allocSym,pos);
            JCIdent alloc = newIdentIncarnation(allocSym,pos);

            // assume <oldalloc> < <newalloc>
            JCExpression ee = makeBinary(JCTree.LT,oldalloc,alloc,pos);
            addAssume(pos,Label.SYN,ee);

            // assume <newid> != null;
            ee = makeBinary(JCTree.NE,id,nullLiteral,pos);
            addAssume(pos,Label.SYN,ee);

            // assume \typeof(<newid>) <: <declared type>
            ee = factory.at(pos).JmlMethodInvocation(JmlToken.BSTYPEOF,com.sun.tools.javac.util.List.<JCExpression>of(id));
            ee.type = syms.classType;
            JCLiteral lit = makeTypeLiteral(typeToConstruct,pos); // FIXME - type arguments?
            ee = makeBinary(JCTree.EQ,ee,lit,pos);
            addAssume(pos,Label.SYN,ee);
            
            // assume <newid>.alloc = <newalloc>
            ee = new JmlBBFieldAccess(allocIdent,id);  // FIXME pos, factory
            ee.pos = pos;
            ee.type = syms.intType;
            ee = makeBinary(JCTree.EQ,ee,alloc,pos);
            addAssume(pos,Label.SYN,ee);

            for (JmlMethodClauseExpr post: mi.ensuresPredicates) {
                addAssume(pos,Label.POSTCONDITION,trSpecExpr(post.expression,post.source()));
            }
            if (!isHelper) {
                for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e,inv.source());
                    addAssume(pos,Label.INVARIANT,e);
                }
                for (JmlTypeClauseExpr inv : classInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trSpecExpr(e,inv.source());
                    addAssume(pos,Label.INVARIANT,e);
                }
            }
            // Take out the temporary variables for the arguments
            if (sym.params != null) for (VarSymbol vd  : sym.params) {
                currentMap.remove(vd);
            }
            if (that.type.getTypeArguments() != null) {
                popTypeArgs();
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
        
        int pos = that.pos;
        
        // assume <oldalloc> < <newalloc>
        JCIdent oldalloc = newIdentUse(allocSym,pos);
        JCIdent alloc = newIdentIncarnation(allocSym,pos);
        JCExpression e = makeBinary(JCTree.LT,oldalloc,alloc,pos);
        addAssume(pos,Label.SYN,e);
        
        // assume <newarray> != null;
        JCIdent newarray = newAuxIdent("$$newarray$"+pos+"$",that.type,pos,false);
        e = makeBinary(JCTree.NE,newarray,nullLiteral,pos);
        addAssume(pos,Label.ARRAY_INIT,e);
        
        // assume <newarray>.alloc = <newalloc>
        e = new JmlBBFieldAccess(allocIdent,newarray);
        e.pos = pos;
        e.type = syms.intType;
        e = makeBinary(JCTree.EQ,e,alloc,pos);
        addAssume(pos,Label.SYN,e);
        
        List<JCExpression> dims = that.dims;
        int ndims = dims.size();
        Type arrayType = that.type;
        
        ListBuffer<JCExpression> types = ListBuffer.<JCExpression>lb();
        JCExpression intTypeTree = factory.at(pos).TypeIdent(TypeTags.INT);
        intTypeTree.type = syms.intType;
        //ListBuffer<Name> inames = ListBuffer.<Name>lb();
        ListBuffer<JCVariableDecl> idecls = ListBuffer.<JCVariableDecl>lb();
        JCExpression range = trueLiteral;
        JCExpression access = null;
        
        if (newelems == null) {
            // no initializer, one or more dimensions given
            // FIXME - need to set the last elements to null
            
            int ind;
            JCExpression prevLen = null;
            for (ind = 0; ind<ndims; ind++) {

                JCExpression len = trExpr(that.dims.get(ind));
                if (ind == 0) {
                    // <newarray>.length == <len>
                    e = new JmlBBFieldAccess(lengthIdent,newarray);
                    e.pos = pos;
                    e.type = syms.intType;
                    e = makeBinary(JCTree.EQ,e,trExpr(len),pos);
                    access = newarray;
                    prevLen = len;
                } else {
                    // (forall (i1::int ...) <range> => (...( <newarray> i1 ) i2 ) ... in ).length == <len> )
                    types.append(intTypeTree);
                    Name nm = names.fromString("i"+ind);
                    JCIdent id = factory.at(pos).Ident(nm);
                    id.type = syms.intType;
                    //inames.append(nm);
                    idecls.append(makeVariableDecl(id.name,syms.intType,pos));
                    range = makeBinary(JCTree.AND, range,
                                makeBinary(JCTree.AND,
                                      makeBinary(JCTree.LE,zeroLiteral,id,pos),
                                      makeBinary(JCTree.LT,id,prevLen,pos),
                                      pos),
                                pos);
                    arrayType = ((ArrayType)arrayType).elemtype;
                    JCIdent arraysID = getArrayIdent(arrayType);
                    access = new JmlBBArrayAccess(arraysID,access,id);
                    access.pos = pos;
                    access.type = arrayType;
                    JCExpression predicate = new JmlBBFieldAccess(lengthIdent,access);
                    predicate.pos = pos;
                    predicate.type = syms.intType;
                    predicate = makeBinary(JCTree.AND,
                                        makeBinary(JCTree.NE,access,nullLiteral,pos),
                                        makeBinary(JCTree.EQ,predicate,trExpr(len),pos),pos);
                    e = factory.at(pos).JmlQuantifiedExpr(JmlToken.BSFORALL,idecls,range,predicate);
                    e.type = syms.booleanType;
                }
                addAssume(pos,Label.ARRAY_INIT,e);
            }
            // (forall (i1::int ...) (...( <newarray> i1 ) i2 ) ... in ) != null )
            arrayType = ((ArrayType)arrayType).elemtype;
            if (arrayType instanceof ArrayType) {
                types.append(intTypeTree);
                Name nm = names.fromString("i"+ind);
                JCIdent id = factory.at(pos).Ident(nm);
                id.type = syms.intType;
                //inames.append(nm);
                idecls.append(makeVariableDecl(id.name,syms.intType,pos));
                JCIdent arraysID = getArrayIdent(arrayType);
                access = new JmlBBArrayAccess(arraysID,access,id);
                access.pos = pos;
                access.type = arrayType;
                e = makeBinary(JCTree.EQ,access,nullLiteral,pos);
                e = factory.at(pos).JmlQuantifiedExpr(JmlToken.BSFORALL,idecls,trueLiteral,e);
                e.type = syms.booleanType;
                addAssume(pos,Label.ARRAY_INIT,e);
            }

        } else {
            // an initializer, but no dimensions given

            int num = newelems.size();
            JCExpression len = makeLiteral(num,pos);

            // <newarray>.length == <len>
            e = new JmlBBFieldAccess(lengthIdent,newarray);
            e.pos = pos;
            e.type = syms.intType;
            e = makeBinary(JCTree.EQ,e,trExpr(len),pos);
            addAssume(pos,Label.ARRAY_INIT,e);

            int i = 0;
            for (JCExpression ee: newelems) {
                // create an assumption about each element of the new array, 
                // given the initializer value (which might be a new array itself)
                JCLiteral lit = makeLiteral(i++,ee.pos);
                e = new JmlBBArrayAccess(getArrayIdent(ee.type),newarray,lit);
                e.pos = ee.pos;
                e.type = ee.type;
                e = makeBinary(JCTree.EQ,e,ee,ee.pos);
                addAssume(ee.pos,Label.ARRAY_INIT,e);
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
        currentBlock.statements.add(comment(that));
        // This includes ghost local declarations
        // FIXME ??? ghost and model field declarations? // FIXME ??? java declarations?
        // FIXME - need to add various field specs tests
        JCIdent vd = newIdentIncarnation(that,that.pos);
        if (that.init != null) {
            int p = that.init.pos;
            boolean prevInSpecExpression = inSpecExpression;
            try {
                if (Utils.instance(context).isJML(that.mods)) inSpecExpression = true;
                JCExpression ninit = trJavaExpr(that.init);
                addAssume(p,Label.ASSIGNMENT,makeBinary(JCTree.EQ,vd,ninit,p));
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
                    log.noticeWriter.println("EXCEPTION VAR IS NULL");
                    result = null;
                } else {
                    result = newIdentUse((VarSymbol)exceptionVar.sym,that.pos);
                }
                break;

            case BSINDEX:
            case BSVALUES:
                if (that.info == null) {
                    log.error(that.pos,"esc.internal.error","No loop index found for this use of " + that.token.internedName());
                    result = null;
                } else {
                    result = newIdentUse((VarSymbol)that.info,that.pos);
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
                ListBuffer<JCVariableDecl> decls = ListBuffer.<JCVariableDecl>lb();
                for (JCVariableDecl d: that.decls) {
                    JCIdent id = newIdentUse(d.sym,0);
                    JCVariableDecl dd = factory.at(d.pos).VarDef(d.mods,id.name,d.vartype,null);
                    dd.type = d.type;
                    decls.append(dd);
                }
                JCExpression range = trExpr(that.range);
                condition = makeBinary(JCTree.AND,condition,range,condition.pos);
                JCExpression predicate = trExpr(that.predicate);
                JmlQuantifiedExpr now = factory.at(that.pos).JmlQuantifiedExpr(op,decls,range,predicate);
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
        JCIdent id = newAuxIdent(n,that.type,that.pos,false);
        JCExpression e = makeBinary(JCTree.EQ,id,trExpr(that.expression),that.pos);
        addAssume(that.getStartPosition(),Label.LBL,e);
        result = id;
    }
    
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        switch (that.token) {
            case BSNOTMODIFIED:
                // Allows multiple arguments; they may be store-refs with wildcards (FIXME)
                JCExpression combined = null;
                for (JCExpression a : that.list){
                    // FIXME - there is an issue with condition - how do we evaluate if old(e) is well-defined?
                    //  defined as  arg == \old(arg)
                    int pos = that.pos;
                    JCExpression e = trExpr(a);
                    VarMap prevMap = currentMap;
                    currentMap = oldMap;
                    try {
                        // FIXME - what happens if not_modifieds are nested, or within an old
                        //extraEnv = true;
                        JCExpression ee = trExpr(a);
                        ee = makeBinary(JCTree.EQ,e,ee,pos);
                        if (combined == null) combined = ee;
                        else combined = makeBinary(JCTree.AND,combined,ee,pos);
                    } finally {
                        currentMap = prevMap;
                        //extraEnv = false;
                    }
                }
                result = combined;
                break;

            default: notImpl(that);
        }
    }
    
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
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) { notImpl(that); }
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
        log.noticeWriter.println("YES THIS IS CALLED - visitClassDef");
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
        log.noticeWriter.println("YES THIS IS CALLED - visitJMLMethodDecl");
        //convertMethodBody(that.body); // FIXME - do the proof?? // Is it ever called? in local classes?
    }
    

    // FIXME - this will go away
    public static class VarFinder extends JmlTreeScanner {
        
        private Set<JCIdent> vars; // FIXME - change to a collection?
        
        public VarFinder() {}
        
        public static Set<JCIdent> findVars(BasicProgram program) {
            VarFinder vf = new VarFinder();
            Set<JCIdent> v = new HashSet<JCIdent>();
            for (JCExpression def : program.definitions()) {
                vf.find(def,v);
            }
            for (BasicBlock b : program.blocks()) {
                for (JCStatement st: b.statements()) {
                    vf.find(st,v);
                }
            }
            return v;
        }
        
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
            if (that == null) return v;
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
            if (that == null) return v;
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
        if (sym == null) return null;
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
    protected @Nullable JmlClassInfo computeClassInfo(@NonNull ClassSymbol csym) {
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
            // This can also happen for nested/inner classes of binary classes that
            // do not have specs.
            
            
            // This should not happen - every class referenced is loaded, 
            // even binary files.  If there is no source and no specs, then
            // the typespecs will have essentially null
            // innards, but the object should be there.
            // If this point is reached, some class somehow escaped being loaded.
            Log.instance(context).error("jml.internal","No typespecs for class " + csym);
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
        classInfo.superclassInfo = (csym == syms.objectType.tsym || csym.isInterface() ) ? null : getClassInfo(type.tsym);

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
        
        @NonNull Writer w;
        
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
        public String trace(@NonNull Context context, @NonNull JCMethodDecl decl, @NonNull ICounterexample s) {
            Tracer t = new Tracer(context,s);
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

        /** Translates the given position information into source, line and column information 
         * @param pos the position information to translate
         * @return A String containing human-readable source location information
         */
        public String getPosition(int pos) { // TODO - check about the second argument of getColumnNumber
            return log.currentSourceFile().getName() + ":" + log.currentSource().getLineNumber(pos) + " (col " + log.currentSource().getColumnNumber(pos,false) + "): ";
        }
        
        /** The constructor for this class
         * @param context the compilation context
         * @param s the counterexample information
         */
        protected Tracer(@NonNull Context context, @NonNull ICounterexample s) {
            this.context = context;
            ce = s;
            log = Log.instance(context);
            w = new StringWriter();
        }
        
        // CAUTION: The Strings in use in these visit methods correspond to the
        // encoding used in the BasicBlocker methods.  The BasicBlocker encodes
        // variables using combinations of variable name, declaration position,
        // and incarnation position.  These are reflected in the counterexample 
        // information and we need to match that as we interpret the counterexample
        // information in these methods.
        
        // FIXME - this implementation needs fleshing out
        
        public void visitMethodDef(JCMethodDecl that) {
            try {
                w.append("START METHOD " + that.sym + "\n");
                for (JCVariableDecl param: that.params) {
                    String s = param.name + "$" + param.pos + "$0";
                    String value = ce.get(s);
                    w.append("Parameter value: " + param.name + " = " + (value == null ? "<unused>" : value) + "\n");
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
                if (value == null) w.append(getPosition(that.pos) + "!!!  Could not find value for branch ("+s+")\n");
                else {
                    w.append(getPosition(that.pos) + "Branch condition value: " + value + "\n");
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
                    JCIdent id = (JCIdent)that.lhs;
                    String s = id.name + "$" + ((VarSymbol)id.sym).pos + "$" + that.pos;
                    String value = ce.get(s);
                    if (value == null) w.append(getPosition(that.pos) + "!!!  Could not find value for variable ("+s+")\n");
                    else w.append(getPosition(that.pos) + "Assignment: " + id.name + " = " + value + "\n");
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
                        w.append(getPosition(that.finalizer.pos) + "Executing finally block\n");
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
            String s = "$$result";
            String value = ce.get(s);
            try {
                if (that.expr != null) {
                    if (value == null) w.append(getPosition(that.pos) + "!!!  Could not find return value ("+s+")\n");
                    else w.append(getPosition(that.pos) + "Executed return: value = " + value + "\n");
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
    

    /** This class converts a counterexample into more readable information;
     * it uses the basic program form rather than using the Java AST. */
    public static class TracerBB extends JmlTreeScanner {
        
        /** The counterexample information */
        ICounterexample ce;
        
        boolean showSubexpressions;
        
        /** The log for output */
        @NonNull Log log;
        
        /** The program being traced */
        BasicProgram program;
        
        /** The compilation context */
        @NonNull Context context;
        
        Writer w;
        
        /** The prover that was used to create the counterexample */
        IProver prover;
        
        Symtab syms;
        
        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
        private static class ReturnException extends RuntimeException {
            private static final long serialVersionUID = -3475328526478936978L;}

        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
        private static class ExException extends RuntimeException {
            private static final long serialVersionUID = -5610207201211221750L;}
        
        /** Outputs the counterexample information in more readable form
         * @param context the compilation context
         * @param program the program whose counterexample information is to be printed 
         * @param ce the counterexample information to translate
         * @param prover the prover from which the counterexample information came
         */
        public static String trace(@NonNull Context context, @NonNull BasicProgram program, @NonNull ICounterexample ce, IProver prover) {
            String s = null;
            try {
                s = (new TracerBB(context)).trace(program,ce,prover);
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
        
        /** Translates the given position information into source, line and column information 
         * @param pos the position information to translate
         * @return A String containing human-readable source location information
         */
        public String getPosition(int pos) {  // TODO - check about the second argument of getColumnNumber
            return log.currentSourceFile().getName() + ":" + log.currentSource().getLineNumber(pos) + " (col " + log.currentSource().getColumnNumber(pos,false) + "): \t";
        }
        
        /** The constructor for this class
         * @param context the compilation context
         */
        protected TracerBB(@NonNull Context context) {
            this.context = context;
            log = Log.instance(context);
            syms = Symtab.instance(context);
            w = new StringWriter();
            showSubexpressions = JmlOptionName.isOption(context,JmlOptionName.SUBEXPRESSIONS) || true;
        }
        
        //@ ensures this.program != null && this.ce != null;
        //@ ensures this.program != program && this.ce != ce;
        public String trace(@NonNull BasicProgram program, ICounterexample ce, IProver prover) throws IOException {
            this.ce = ce;
            this.program = program;
            this.prover = prover;
            w = new StringWriter();
            w.append("COUNTEREXAMPLE TRACE \n\n");
            this.subexp = new Subexpressor(context,prover,w);
            
            for (JCVariableDecl vd: program.methodDecl.params) {
                String n = vd.name + "$" + vd.pos + "$0";
                String value = ce.get(n);
                w.append(getPosition(vd.pos) + "Parameter \t" +  n + " \t= " + (value==null?"?":value) + "\n");
            }
            
            if (showSubexpressions) prover.reassertCounterexample(ce);
            
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
            w.append("END\n");
            return w.toString();
        }
        

        
        // CAUTION: The Strings in use in these visit methods correspond to the
        // encoding used in the BasicBlocker methods.  The BasicBlocker encodes
        // variables using combinations of variable name, declaration position,
        // and incarnation position.  These are reflected in the counterexample 
        // information and we need to match that as we interpret the counterexample
        // information in these methods.
        
        protected boolean traceBlockStatements(BasicBlock b) throws IOException {
            w.append(" [ block " + b.id() + " ]\n");
            boolean sawFalseAssert = false;
            String pos=null, lastpos;
            for (JCStatement statement: b.statements) {
                if (!(statement instanceof JmlStatementExpr)) {
                    log.error(statement.pos,"esc.internal.error","Incorrect statement type in traceBlockStatements: " + statement.getClass());
                    continue;
                }
                JmlStatementExpr s = (JmlStatementExpr)statement;
                JCExpression expr = s.expression;
                if (expr instanceof JCIdent) {
                    Name nm = ((JCIdent)expr).name;
                    if (nm.toString().startsWith(BasicBlocker.ASSUMPTION_PREFIX)) {
                        for (JCExpression e : program.definitions) {
                            if (e instanceof JCBinary && ((JCBinary)e).lhs instanceof JCIdent && ((JCIdent)((JCBinary)e).lhs).name.equals(nm)) {
                                expr = ((JCBinary)e).rhs;
                            }
                        }
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
                            JCBinary bin = (JCBinary)expr;
                            if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
                            Name n = ((JCIdent)bin.lhs).name;
                            w.append(pos + "Assignment " + n + " = " + value((JCIdent)bin.lhs)
                                    + "  [" + bin.rhs + "]\n");
                            showSubexpressions(bin.rhs);

                        } else if (expr instanceof JmlBBArrayAssignment){
                            JmlBBArrayAssignment asg = (JmlBBArrayAssignment)expr;
                            JCExpression array = asg.args.get(2);
                            JCExpression index = asg.args.get(3);
                            JCExpression value = asg.args.get(4);
                            
                            List<String> results = subexp.getValues(array,index,value);
                            w.append(pos + "ArrayAssignment " 
                                    + results.get(0) + "[" + results.get(1) + "] = " + results.get(2)
                                    + "  [ (" + array + ")[" + index + "] = " + value + " ]\n");
                            showSubexpressions(array);
                            showSubexpressions(index);
                            showSubexpressions(value);
                        } else if (expr instanceof JmlBBFieldAssignment){
                            JmlBBFieldAssignment asg = (JmlBBFieldAssignment)expr;
                            JCExpression obj = asg.args.get(2);
                            JCIdent field = (JCIdent)asg.args.get(0);
                            JCExpression value = asg.args.get(3);
                            
                            List<String> results = subexp.getValues(obj,value);
                            w.append(pos + "FieldAssignment " 
                                    + results.get(0) + "." + field + " = " + results.get(1)
                                    + "  [ (" + obj + ")." + field + " = " + value + " ]\n");
                            showSubexpressions(obj);
                            showSubexpressions(value);

                        } else {
                            failure(label,expr);
                        }
                    } else if (label == Label.ARGUMENT) {
                        // Called methods and new object (called constructor) calls
                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
                        JCBinary bin = (JCBinary)expr;
                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
                        Name n = ((JCIdent)bin.lhs).name;
                        w.append(pos + "ArgumentEvaluation " + n + " = " + value((JCIdent)bin.lhs)
                                + "  [" + bin.rhs + "]\n");
                        showSubexpressions(bin.rhs);

                    } else if (label == Label.RECEIVER) {
                        // Called methods and new object (called constructor) calls
                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
                        JCBinary bin = (JCBinary)expr;
                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
                        Name n = ((JCIdent)bin.lhs).name;
                        w.append(pos + "ReceiverEvaluation " + n + " = " + value((JCIdent)bin.lhs)
                                + "  [" + bin.rhs + "]\n");
                        showSubexpressions(bin.rhs);
                    
                    } else if (label == Label.BRANCHC) {
                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
                        JCBinary bin = (JCBinary)expr;
                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
                        w.append(pos + label + " = " + value((JCIdent)bin.lhs)
                                + "  [" + bin.rhs + "]\n");
                        showSubexpressions(bin.rhs);
                        
                    } else if (label == Label.LBL) {
                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
                        JCBinary bin = (JCBinary)expr;
                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
                        JCIdent id = (JCIdent)bin.lhs;
                        String lbl = id.toString();
                        int k = lbl.lastIndexOf('$');
                        lbl = lbl.substring(k+1);
                        w.append(pos + label + ": " + lbl + " = " + value(id)
                                + "  [" + bin.rhs + "]\n");
                        showSubexpressions(bin.rhs);
                        
                    } else if (label == Label.SWITCH_VALUE) {
                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
                        JCBinary bin = (JCBinary)expr;
                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
                        w.append(pos + "switch value = " + value((JCIdent)bin.lhs)
                                + "  [" + bin.rhs + "]\n");
                        showSubexpressions(bin.rhs);
                        
                    } else if (label == Label.SYN) {  // FIXME - rename the SYN types that are wanted
                        if (expr instanceof JCBinary) {
                            JCExpression lhs = ((JCBinary)expr).lhs;
                            if (lhs instanceof JCIdent) {
                                String value = ce.get(((JCIdent)lhs).name.toString());
                                w.append(pos + "Syn " + lhs + " = " + value + "\n");
                            } else {
                                w.append(pos + "Syn " + expr + "\n");
                            }
                        } else {
                            w.append(pos + "Syn " + expr + "\n");
                        }
                    } else if (label == Label.EXPLICIT_ASSUME) {
                        if (expr instanceof JCIdent) {
                            // This will happen for tracked assumptions
                            Name n = ((JCIdent)expr).name;
                            String value = ce.get(n.toString());
                            w.append(pos + label + " " + n + " = " + value + "\n");
                            JCExpression e = findDefinition(n);
                            if (e != null) showSubexpressions(e);
                        } else {
                            w.append(pos + label + " " + expr + "\n");
                            showSubexpressions(expr);
                        }
                    } else if (label == Label.DSA) {
                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
                        JCBinary bin = (JCBinary)expr;
                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
                        if (!(bin.rhs instanceof JCIdent)) { failure(label,expr); continue; }
                        w.append(lastpos + label + " = " + value((JCIdent)bin.lhs)
                                + "  [" + bin.rhs + "]\n");
                        // no subexpressions
                    } else if (label == Label.RETURN) {
                        w.append(pos + "Executing return statement\n");
                    } else if (label == Label.TERMINATION) {
                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
                        JCBinary bin = (JCBinary)expr;
                        if (!(bin.lhs instanceof JCBinary)) { failure(label,expr); continue; }
                        bin = (JCBinary)bin.lhs;
                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
                        String v = value((JCIdent)bin.lhs);
                        if (v.equals("0")) {
                            String rv = bin.lhs.toString().replace("terminationVar","result");
                            String vv = valueNull(rv);
                            w.append(pos + "Called method returned normally [" + bin.lhs + "=" + v +"]"+ (vv==null?"":", return value = " + vv + " ["+rv+"]\n"));
                        } else {
                            String rv = bin.lhs.toString().replace("terminationVar","exception");
                            String vv = subexp.getType(rv);
                            w.append(pos + "Called method exited with an exception [" + bin.lhs + "=" + v +"]"
                                    + (vv==null?"":", exception type = "+vv) + "\n");
                        }
                    } else if (label == Label.METHODAXIOM) {
                        // Just print the axiom - don't try to evaluate it
                        w.append(pos + label + " " + expr + "\n");
                    } else if (label == Label.ARRAY_INIT) {
                        // Just print the expression - don't try to evaluate it
                        w.append(pos + label + " " + expr + "\n");
                    } else if (label == Label.BRANCHT || label == Label.BRANCHE || label == Label.HAVOC) {
                        // skip
                    } else {
                        w.append(pos + label + " " + expr + "\n");
                        showSubexpressions(expr);
                    }
                } else if (s.token == JmlToken.ASSERT) {
                    String value = null;
                    String name = null;
                    if (expr instanceof JCIdent) {
                        name = ((JCIdent)expr).toString();
                        value = ce.get(name);
                        JCExpression e = findDefinition(((JCIdent)expr).name);
                        if (e != null) expr = e;
                    }
                    w.append(pos + "Assert [" + label + "] "
                            + (value == null? "" : value)
                            + "   [" + expr + "]\n");
                    showSubexpressions(expr);
                    if ("false".equals(value)) {
                        sawFalseAssert = true;
                        return false;  // FIXME (do we want this?) - abrupt return here if we quit the trace reporting upon the first false assertion
                    }
                } else if (s.token == JmlToken.COMMENT) {
                    w.append(pos);
                    w.append("Comment: // ");
                    w.append(((JCLiteral)s.expression).value.toString());
                    w.append("\n");
                } else {
                    log.error(pos,"esc.internal.error","Incorrect token type in traceBlockStatements: " + s.token.internedName());
                }
            }
            return !sawFalseAssert;
        }
        
        public JCExpression findDefinition(Name name) {
            for (JCExpression e: program.definitions) {
                if (!(e instanceof JCBinary)) continue;
                JCBinary bin = (JCBinary)e;
                if (!(bin.lhs instanceof JCIdent)) continue;
                JCIdent id = (JCIdent)bin.lhs;
                if (id.name != name) continue;
                return bin.rhs;
            }
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
            log.warning("jml.internal.notsobad","Unable to interpret counterexample trace.  A " + label + " statement has unexpected structure: " + expr);
        }
        
        Subexpressor subexp;
        
        public void showSubexpressions(JCExpression expr) {
            if (showSubexpressions) try { subexp.walk(expr); } catch (IOException e) {}
        }
    }
    
    static int count = 1000000;
    public static class Subexpressor extends JmlTreeScanner {
        
        Context context;
        IProver prover;
        JmlTree.Maker factory;
        Names names;
        Symtab syms;
        final String prefix = "X$$$";
        StringBuilder builder;
        List<JCBinary> exprs = new LinkedList<JCBinary>();
        Map<String,JCExpression> requests = new HashMap<String,JCExpression>();
        Writer w;
        
        public void walk(JCExpression expr) throws IOException {
            exprs.clear();
            requests.clear();
            scan(expr);
            IProverResult res = null;
            try {
                for (JCExpression e: exprs) {
                    prover.assume(e);
                }
                res = prover.check(true);
            } catch (ProverException ex) {
                w.append(ex.toString());
                w.append("\n");
                return;
            }
            if (res == null) {
                throw new RuntimeException("ERROR: no additional information available");
            } else if (!res.isSat()) {
                throw new RuntimeException("ERROR: no longer satisfiable");
            } else {
                ICounterexample nce = res.counterexample();
                for (JCBinary bin: exprs) {
                    JCIdent id = (JCIdent)bin.lhs;
                    String value = nce.get(id.toString());
                    if (value == null) value = "?";
                    w.append("                                " + value + "\t = " + bin.rhs + "\n");
                }
            }
        }
        
        public List<String> getValues(JCExpression... exprlist) throws IOException {
            IProverResult res = null;
            List<JCIdent> ids = new LinkedList<JCIdent>();
            try {
                for (JCExpression e: exprlist) {
                    JCIdent id = newIdent(e);
                    JCExpression ex = factory.Binary(JCTree.EQ,id,e);
                    ex.type = syms.booleanType;
                    ids.add(id);
                    prover.assume(ex);
                }
                res = prover.check(true);
            } catch (ProverException ex) {
                w.append(ex.toString()); w.append("\n");
                return null;
            }
            if (res == null) {
                w.append("ERROR: no additional information available\n");
            } else if (!res.isSat()) {
                w.append("ERROR: no longer satisfiable\n");
            } else {
                ICounterexample nce = res.counterexample();
                List<String> out = new LinkedList<String>();
                for (JCIdent id: ids) {
                    String value = nce.get(id.name.toString());
                    if (value == null) value = "?";
                    out.add(value);
                }
                prover.reassertCounterexample(nce);
                return out;
            }
            return null;
        }

        public String getType(String eid) {
            try {
                JCIdent expr = factory.Ident(Names.instance(context).fromString(eid));
                expr.type = syms.objectType;
                JCExpression e = factory.at(0).JmlMethodInvocation(JmlToken.BSTYPEOF,expr);
                e.type = syms.classType;
                JCIdent id = newIdent(e);
                JCExpression ex = factory.Binary(JCTree.EQ,id,e);
                ex.type = syms.booleanType;
                prover.assume(ex);
                IProverResult res = prover.check(true);
                if (res == null) {
                    w.append("ERROR: no additional information available\n");
                } else if (!res.isSat()) {
                    w.append("ERROR: no longer satisfiable\n");
                } else {
                    ICounterexample nce = res.counterexample();
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
        
        public Subexpressor(Context context, IProver prover, Writer w) {
            this.context = context;
            this.prover = prover;
            this.factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
            this.names = Names.instance(context);
            this.syms = Symtab.instance(context);
            this.w = w;
            //builder = new StringBuilder();
            
        }
        
        public void request(JCExpression expr) {
            JCIdent id = newIdent(expr);
            requests.put(id.name.toString(),expr);
            JCBinary bin = (factory.Binary(JCTree.EQ,id,expr));
            bin.type = syms.booleanType;
            exprs.add(bin);
        }
        
        public JCIdent newIdent(JCExpression expr)  {
            Type t = expr.type;
//            if (expr instanceof JCIdent && !((JCIdent)expr).sym.isStatic()) {
//                // non-static fields are type (REF -> t)
//            }
            Name n = names.fromString(prefix + (++count));
            JCIdent id = factory.Ident(n);
            id.type = t;
            return id;
        }
        
        public void scan(JCTree that) {
            super.scan(that);
//            if (that instanceof JCIdent &&
//                    ((JCIdent)that).sym != null &&
//                    ((JCIdent)that).sym.owner != null &&
//                    !((JCIdent)that).sym.isStatic()) return;  // These are maps that we don't handle for now - I think they just come up in HAVOC assumptions - FIXME
            if (that instanceof JCExpression &&
                    !(that instanceof JCParens) &&
                    !(that instanceof JCLiteral)) request((JCExpression)that);
        }

        public void scanNoRequest(JCTree that) {
            super.scan(that);
        }

        public void visitApply(JCMethodInvocation tree) {
            scanNoRequest(tree.meth);
            scan(tree.args);
        }
        
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree) {
            // do not scan the subexpressions of a quantified expression
        }
    }
    
    public static class Counter extends JmlTreeScanner {
        
        int nodes = 0;  // nodes
        int assumes = 0;
        int asserts = 0;
        int blocks = 0;
        int statements = 0;
        int paths = 0;
        int maxBlockNodes = 0;
        
        public void count(BasicBlock b) {
            for (JCTree t: b.statements()) t.accept(this);
            nodes += b.statements().size();
        }
        
        public static int counts(BasicBlock b) {
            return counts(b.statements());
        }
        
        public static int counts(List<JCStatement> sts) {
            Counter c = new Counter();
            for (JCTree t: sts) t.accept(c);
            return c.nodes + sts.size();
        }
        
        static public Counter count(BasicProgram b) {
            Counter c = new Counter();
            int max = 0;
            for (BasicBlock bb: b.blocks()) {
                int c1 = c.nodes;
                c.count(bb);
                if (c.nodes - c1 > max) max = c.nodes - c1;
            }
            c.maxBlockNodes = max;
            for (JCTree t: b.definitions()) t.accept(c);
            for (JCTree t: b.background()) t.accept(c);
            c.blocks = b.blocks().size();
            return c;
        }
        
        static public int countx(BasicProgram b) {
            Counter c = new Counter();
            for (JCTree t: b.definitions()) t.accept(c);
            for (JCTree t: b.background()) t.accept(c);
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
            maxBlockNodes = maxBlockNodes < c.maxBlockNodes ? c.maxBlockNodes : maxBlockNodes;
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
            return "    " + blocks + " blocks; " + nodes + " nodes; " + maxBlockNodes + " max; " + assumes + " assumes; " + asserts + " asserts; " ;
        }
        
    }

    private ClassSymbol pureAnnotationSymbol = null;
    public boolean isPure(Symbol symbol) {
        if (pureAnnotationSymbol == null) {
            pureAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotation.Pure"));
        }
        return symbol.attribute(pureAnnotationSymbol)!=null;
    }

}
