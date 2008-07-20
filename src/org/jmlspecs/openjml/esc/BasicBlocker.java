package org.jmlspecs.openjml.esc; // FIXME - change package

import static org.jmlspecs.openjml.JmlToken.BSPRE;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;


import org.jmlspecs.openjml.JmlInternalError;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.esc.JmlEsc.JmlClassInfo;

import org.jmlspecs.annotations.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.EndPosParser;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Parser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

import java.util.List;

import javax.tools.JavaFileObject;

public class BasicBlocker extends JmlTreeScanner {

    /** The context key for the parser factory. */
    protected static final Context.Key<BasicBlocker> basicBlockerKey =
        new Context.Key<BasicBlocker>();

    /** Get the Factory instance for this context. */
    public static BasicBlocker instance(Context context) {
        BasicBlocker instance = context.get(basicBlockerKey);
        if (instance == null)
            instance = new BasicBlocker(context);
        return instance;
    }
    // TODO - should we make this class registerable?
    public BasicBlocker(Context context) {
        this.context = context;
        factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
        this.names = Name.Table.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        
//        this.attr = (JmlAttr)JmlAttr.instance(context);
        trueLiteral = factory.Literal(TypeTags.BOOLEAN,1);
        falseLiteral = factory.Literal(TypeTags.BOOLEAN,0);
        nullLiteral = factory.Literal(TypeTags.BOT,0);
        
        allocName = names.fromString("$$alloc");
        allocIdent = factory.Ident(allocName);
        allocSym = new VarSymbol(0,allocName,syms.intType,null);

        lengthName = names.fromString("length$0");
        lengthIdent = factory.Ident(lengthName);
        lengthSym = new VarSymbol(0,lengthName,syms.intType,null);

        thisId = newAuxIdent("this",syms.objectType,0); // FIXME - object type?
    }
    
    /** The compilation context */
    @NonNull Context context;
    
    /** The specifications database for this compilation context, initialized in the constructor */
    @NonNull JmlSpecs specs;
    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull Symtab syms;
    
    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull protected Name.Table names;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull JmlTree.Maker factory;
    
    /** visit methods that emit statements put them here */
    List<JCStatement> newstatements;
    
    /** Place to put new definitions, such as the equalities defining auxiliary variables */
    List<JCExpression> newdefs;
    
    /** List of blocks yet to be processed (from conventional program to basic program state) */
    java.util.List<BasicBlock> blocksToDo;
    
    /** List of blocks completed processing - in basic state, though not necessarily DSA */
    java.util.List<BasicBlock> blocksCompleted;
    
    /** A map of names to blocks */
    java.util.Map<String,BasicBlock> lookup;
    
    /** A holding spot for the conditional return block of a program under normal termination */
    protected BasicBlock condReturnBlock;
    
    /** A holding spot for the return block of a program under normal termination */
    protected BasicBlock returnBlock;
    
    /** A holding spot for the last block of a program when there is an exception */
    protected BasicBlock exceptionBlock;
    
    /** A variable to hold the block currently being processed */
    protected BasicBlock currentBlock;
    
    /** Ordered list of statements from the current block that are yet to be processed into basic program form */
    private List<JCStatement> remainingStatements;
    
    /** Holds an AST node for a boolean true literal, initialized in the constructor */
    @NonNull final protected JCLiteral trueLiteral;
    
    /** Holds an AST node for a boolean false literal, initialized in the constructor */
    @NonNull final protected JCLiteral falseLiteral;
    
    /** Holds an AST node for a null literal, initialized in the constructor */
    @NonNull final protected JCLiteral nullLiteral;
    
    /** Name of a synthesized object field holding the allocation time of the object, initialized in the constructor */
    protected Name allocName;
    /** Identifier of a synthesized object field holding the allocation time of the object, initialized in the constructor */
    protected JCIdent allocIdent;
    /** Symbol of a synthesized object field holding the allocation time of the object, initialized in the constructor */
    protected VarSymbol allocSym;

    /** Name of a synthesized object field holding the length of an array object, initialized in the constructor */
    protected Name lengthName;
    /** Identifier of a synthesized object field holding the length of an array object, initialized in the constructor */
    protected JCIdent lengthIdent;
    /** Symbol of a synthesized object field holding the length of an array object, initialized in the constructor */
    protected VarSymbol lengthSym;
    
    @NonNull protected Map<VarSymbol,Integer> oldMap = new HashMap<VarSymbol,Integer>();

    @NonNull protected JCIdent thisId;
    
    JmlClassInfo classInfo;
    
    protected JCIdent resultVar = null;
    protected JCIdent exceptionVar;
    protected JCIdent allocVar;
    protected JCIdent stateVar;
    protected JCIdent returningVar;
    
    protected JCIdent assumeCheckCountVar;
    protected int assumeCheckCount; 
    
    /** Holds the result of any of the visit methods that produce JCExpressions, since the visitor
     * template used here does not have a return value.  [We could have used the templated visitor,
     * but other methods do not need to return anything, we don't need the additional parameter,
     * and that visitor is complicated by the use of interfaces for the formal parameters.]
     */
    private JCExpression result;
    
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
    
    protected Map<BasicBlock,Map<VarSymbol,Integer>> blockmaps = new HashMap<BasicBlock,Map<VarSymbol,Integer>>();
    
    protected Map<BasicBlock,Map<VarSymbol,Integer>> labelmaps = new HashMap<BasicBlock,Map<VarSymbol,Integer>>();
    
    protected Map<VarSymbol,Integer> currentMap;
    
    protected void notImpl(JCTree that) {
        System.out.println("NOT IMPLEMENTED: BasicBlocker - " + that.getClass());
    }
    
    protected void shouldNotBeCalled(JCTree that) {
        Log.instance(context).error("esc.BasicBlocker.internal",that.getClass());
        throw new JmlInternalError();
    }
    
    protected <T extends JCExpression> T copyInfo(T newnode, T oldnode) {
        newnode.type = oldnode.type;
        // FIXME - store end information?
        return newnode;
    }
    
    protected <T extends JCIdent> T copyInfo(T newnode, T oldnode) {
        newnode.type = oldnode.type;
        newnode.sym = oldnode.sym;
        // FIXME - store end information?
        return newnode;
    }
    
    
    protected Name encodedName(VarSymbol sym, int usePosition) {
        return names.fromString(sym.getQualifiedName() + (sym.pos == -1 ? "$" : ("$" + sym.pos + "$")) + usePosition);
    }
    
    /** Creates an identifier nodes for a new incarnation of the variable, that is,
     * when the variable is assigned to.
     * @param id the old identifier, giving the root name, symbol and type
     * @param usePosition the position (and incarnation number) of the new variable
     * @return the new identifier
     */
    protected JCIdent newIdentIncarnation(JCIdent id, int usePosition) {
        JCIdent n = factory.at(usePosition).Ident(encodedName((VarSymbol)id.sym,usePosition));
        copyInfo(n,id);
        currentMap.put((VarSymbol)id.sym,usePosition);
        return n;
    }
    
    protected JCIdent newArrayIncarnation(Type componentType, int usePosition) {
        String s = "arrays$" + encodeType(componentType);
        JCIdent id = arrayIdMap.get(s);
        if (id == null) {
            id = factory.Ident(names.fromString(s));
            id.pos = 0;
            id.type = componentType;
            id.sym = new VarSymbol(0,id.name,id.type,null);
            arrayIdMap.put(s,id);
        }
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
     */
    protected JCIdent newIdentUse(VarSymbol sym, int useposition, int incarnation) {
        JCIdent n = factory.at(useposition).Ident(encodedName(sym,incarnation));
        n.sym = sym;
        n.type = sym.type;
        // FIXME - end information?
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
     * then it would be the position of the actual parameter expresssion.
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
    
    /** Creates a new variable representing an auxiliary variable, not a
     * program variable, for use within the program; this is a one-time
     * defined variable - it may not be assigned to again.  The variable will
     * have no associated symbol.
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
    
    protected void startBlock(@NonNull BasicBlock b) {
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
        lookup.put(b.name,b);
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
    
    protected void replaceFollows(@NonNull BasicBlock before, @NonNull BasicBlock after) {
        for (BasicBlock b: before.succeeding) {
            b.preceding.remove(before);
        }
        before.succeeding.clear();
        follows(before,after);
    }
    
    /** This utility method converts an expression from AST to BasicProgram
     * form (which may mean no change at all); the method may have side-effects
     * in creating new statements (in newstatements).  The returned expression
     * node is expected to have position, type and symbol information set.
     * @param expr the expression to convert
     * @return the converted expression
     */
    public JCExpression trExpr(JCExpression expr) {
        if (expr == null) return null;
        expr.accept(this);
        return result;
    }
    
    /** Static entry point that converts an AST (the block of a method) into basic block form
     * 
     * @param context the compilation context
     * @param tree the block of a method
     * @return
     */
    public static @NonNull BasicProgram convertToBasicBlocks(@NonNull Context context, 
            @NonNull JCMethodDecl tree, JmlMethodSpecs denestedSpecs, JmlClassInfo classInfo) {
        BasicBlocker blocker = instance(context); // FIXME new BasicBlocker(context);
        return blocker.convertMethodBody(tree,denestedSpecs,classInfo);
    }

    /** Converts the top-level block of a method into the elements of a BasicProgram */
    public BasicProgram convertMethodBody(JCMethodDecl tree, JmlMethodSpecs denestedSpecs, JmlClassInfo classInfo) {
        this.classInfo = classInfo;
        newdefs = new LinkedList<JCExpression>();
        blocksToDo = new LinkedList<BasicBlock>();
        blocksCompleted = new ArrayList<BasicBlock>();
        lookup = new java.util.HashMap<String,BasicBlock>();
        if (tree.getReturnType() != null) {
            resultVar = newAuxIdent("$$result",tree.getReturnType().type,0); 
        }
        returningVar = newAuxIdent("$$returning",syms.booleanType,0);
        exceptionVar = newAuxIdent("$$exception",syms.exceptionType,0);
        allocVar = newAuxIdent("$$alloc",syms.intType,0); // FIXME - would this be better as its own uninterpreted type?
        stateVar = newAuxIdent("$$state",syms.intType,0); // FIXME - would this be better as its own uninterpreted type?
        assumeCheckCountVar = newAuxIdent("$$assumeCheckCount",syms.intType,0);
        assumeCheckCount = 0;
        
        JCBlock block = tree.getBody();
        condReturnBlock = new BasicBlock(COND_RETURN_BLOCK_NAME);
        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,returningVar);
        condReturnBlock.statements.add(asm);
        returnBlock = new BasicBlock(RETURN_BLOCK_NAME);
        follows(condReturnBlock,returnBlock);
        exceptionBlock = new BasicBlock(EXCEPTION_BLOCK_NAME);
        JCExpression e = factory.Binary(JCTree.NE,exceptionVar,nullLiteral);
        e.type = syms.booleanType;
        asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);
        exceptionBlock.statements.add(asm);
        BasicBlock startBlock = new BasicBlock(START_BLOCK_NAME);
        
        // Put all the program statements in the Body Block
        BasicBlock bodyBlock = new BasicBlock(BODY_BLOCK_NAME);
        // First a couple key statements
        e = factory.Unary(JCTree.NOT,returningVar);
        e.type = syms.booleanType;
        asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);
        bodyBlock.statements.add(asm);
        e = factory.Binary(JCTree.EQ,exceptionVar,nullLiteral);
        e.type = syms.booleanType;
        asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);
        bodyBlock.statements.add(asm);
        // Then the program
        bodyBlock.statements.addAll(block.getStatements());
        follows(startBlock,bodyBlock);
        follows(bodyBlock,returnBlock); // implicit, unconditional return
        
        // Put the blocks in the todo list
        blocksToDo.add(0,exceptionBlock);
        blocksToDo.add(0,returnBlock);
        blocksToDo.add(0,condReturnBlock);
        blocksToDo.add(0,bodyBlock);
        
        // Handle the start block a little specially
        // It does not have any statements in it
        startBlock(startBlock);
        addPreconditions(startBlock,tree,denestedSpecs);
        completed(currentBlock);

        // Pick a block to do and process it
        while (!blocksToDo.isEmpty()) {
            processBlock(blocksToDo.remove(0));
        }
        addPostconditions(returnBlock,tree,denestedSpecs);
        
        // Make the BasicProgram
        BasicProgram program = new BasicProgram();
        program.startId = START_BLOCK_NAME;
        program.blocks.addAll(blocksCompleted);
        program.definitions = newdefs;
        program.assumeCheckVar = assumeCheckCountVar;
        
        // Now do DSA pass
        //doDSA(program);
        
        // Find all the variables so they can be declared if necessary
        Set<JCIdent> vars = new HashSet<JCIdent>();
        for (BasicBlock bb : blocksCompleted) {
            VarFinder.findVars(bb.statements,vars);
        }
        for (JCExpression ex : newdefs) {
            VarFinder.findVars(ex,vars);
        }
        Collection<JCIdent> decls = program.declarations;
        Set<Name> varnames = new HashSet<Name>();
        for (JCIdent id: vars) {
            if (varnames.add(id.getName())) decls.add(id);
        }
        return program;
    }
    
    public void processBlock(BasicBlock block) {
        startBlock(block);
        //System.out.println("CONVERTING " + currentBlock.name);
        processBlockStatements(true);
    }
    
    public void processBlockStatements(boolean complete) {
        while (!remainingStatements.isEmpty()) {
            JCStatement s = remainingStatements.remove(0);
            s.accept(this);
        }
        if (complete) completed(currentBlock);
    }
    
    ClassSymbol helperAnnotationSymbol = null;
    public boolean isHelper(Symbol symbol) {
        if (helperAnnotationSymbol == null) {
            helperAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.Helper"));
        }
        return symbol.attribute(helperAnnotationSymbol)!=null;

    }

    
    protected void addPreconditions(BasicBlock b, JCMethodDecl tree, JmlMethodSpecs specs) {
        boolean isStatic = tree.mods != null && (tree.mods.flags & Flags.STATIC) != 0;
        boolean isConstructor = tree.getReturnType() == null;
        boolean isHelper = isHelper(tree.sym);
        if (!isConstructor && !isHelper) {
            for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                JCExpression e = inv.expression;
                e = trExpr(e);
                JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.INVARIANT,e);
                b.statements.add(asm);
            }
            if (!isStatic) {
                for (JmlTypeClauseExpr inv : classInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.INVARIANT,e);
                    b.statements.add(asm);
                }
            }
        }
        JmlMethodInfo mi = getMethodInfo(tree);

        for (JCExpression pre: mi.requiresPredicates) {
            JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.PRECONDITION,trExpr(pre));
            b.statements.add(asm);
        }
//        if (specs != null) {
//            boolean isConstructor = tree.getReturnType() == null;
//            boolean isHelper = isHelper(tree.sym);
//
//            // FIXME _ need class stuff
////          if (!isConstructor && !isHelper) {
////              if (!isStatic) for (Expr c: classInfo.invariants) {
////                  sps = M.Specification(Specification.SpecType.REQUIRES,c,true,sps,c.loc());
////              }
////              for (Expr c: classInfo.staticinvariants) {
////                  sps = M.Specification(Specification.SpecType.REQUIRES,c,true,sps,c.loc());
////              }
////          }
//
//            JCExpression pre = specs.cases.size() == 0 ? trueLiteral : falseLiteral;
//            int num = 0;
//            for (JmlSpecificationCase spc: specs.cases) {
//                JCExpression spre = trueLiteral;
//                for (JmlMethodClause c: spc.clauses) {
//                    if (c.token == JmlToken.REQUIRES) {
//                        num++;
//                        spre = factory.Binary(JCTree.AND,spre,trExpr(((JmlMethodClauseExpr)c).expression));
//                    }
//                }
//                pre = factory.Binary(JCTree.OR,pre,spre);
//            }
//            if (pre != trueLiteral) {
//                JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.PRECONDITION,pre);
//                newstatements.add(asm);
//            }
//            
            // Need definedness checks?  FIXME

    }
    
    boolean useAuxDefinitions = true;

//    protected void addAssert(Label label, JCExpression that, List<JCStatement> statements, int usepos) {
//        addAssert(label,that,that.pos,statements,usepos);
//    }
    
    protected JCExpression addAssert(Label label, JCExpression that, int declpos, List<JCStatement> statements, int usepos) {
        JmlStatementExpr st;
        if (useAuxDefinitions) {
            String n = "assert$" + usepos + "$" + label + "$" + declpos;
            JCExpression id = newAuxIdent(n,syms.booleanType,that.getStartPosition());
            JCExpression expr = factory.at(that.pos).Binary(JCTree.EQ,id,that);
                    // FIXME - start and end?
            newdefs.add(expr);
            that = id;
        }
        st = factory.JmlExpressionStatement(JmlToken.ASSERT,label,that);
        st.pos = that.pos; // FIXME - start and end?
        st.optionalExpression = null;
        st.type = null; // FIXME - is this right?
        // FIXME - what about source and line?
        statements.add(st);
        return that;
    }
    
    // non-tracked
    protected void addAssume(Label label, JCExpression that, List<JCStatement> statements, boolean useAuxDefinition) {
//        String n = "assert$" + label + "$" + that.pos;
//        JCExpression id = new AuxVarDSA(names.fromString(n),syms.booleanType,that);
//        JCExpression expr = factory.Binary(JCTree.EQ,id,that);
//        if (useAuxDefinitions) {
//            newdefs.add(expr);
//        } else {
//            JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,expr);
//            statements.add(st);
//        }
        if (useAuxDefinition) {
            
        }
        that.type = syms.booleanType;
        JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,that);
        st.pos = that.pos;
        statements.add(st);
    }
    
    static public String encodeType(Type t) {   // FIXME String? char? void? unsigned?
        if (t instanceof ArrayType) {
            return "array$" + encodeType(((ArrayType)t).getComponentType());
        } else if (!t.isPrimitive()) {
            return "REF";
        } else if (t.tag == TypeTags.INT || t.tag == TypeTags.SHORT || t.tag == TypeTags.LONG || t.tag == TypeTags.BYTE) {
            return "int";
        } else if (t.tag == TypeTags.BOOLEAN) {
            return "bool";
        } else if (t.tag == TypeTags.FLOAT || t.tag == TypeTags.DOUBLE) {
            return "real";
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
            newdefs.add(factory.at(newexpr.pos).Binary(JCTree.EQ,vd,newexpr));
        } else {
            JmlTree.JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,factory.at(newexpr.pos).Binary(JCTree.EQ,vd,newexpr));
            asm.pos = expr.getStartPosition();  // FIXME - start and end position?
            currentBlock.statements.add(asm);
        }
        return vd;
    }
    
    protected void addPostconditions(BasicBlock b, JCMethodDecl tree, JmlMethodSpecs denestedSpecs) {
        currentBlock = b;
        currentMap = blockmaps.get(b);
        List<JCStatement> statements = b.statements;
        JmlMethodInfo mi = getMethodInfo(tree);
        for (JCExpression post: mi.ensuresPredicates) {
            addAssert(Label.POSTCONDITION,trExpr(post),post.getStartPosition(),statements,tree.pos);
        }
        boolean isStatic = tree.mods != null && (tree.mods.flags & Flags.STATIC) != 0;
        boolean isConstructor = tree.getReturnType() == null;
        boolean isHelper = isHelper(tree.sym);
        if (!isHelper) {
            for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                JCExpression e = inv.expression;
                e = trExpr(e);
                addAssert(Label.INVARIANT,e,inv.expression.getStartPosition(),statements,tree.pos);
            }
            if (!isStatic) {
                for (JmlTypeClauseExpr inv : classInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssert(Label.INVARIANT,e,inv.expression.getStartPosition(),statements,tree.pos);
                }
            }
            if (!isConstructor) {
                for (JmlTypeClauseConstraint inv : classInfo.staticconstraints) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssert(Label.CONSTRAINT,e,inv.expression.getStartPosition(),statements,tree.pos);
                }
                if (!isStatic) {
                    for (JmlTypeClauseConstraint inv : classInfo.constraints) {
                        JCExpression e = inv.expression;
                        e = trExpr(e);
                        addAssert(Label.CONSTRAINT,e,inv.expression.getStartPosition(),statements,tree.pos);
                    }
                }
            } else {
                for (JmlTypeClauseExpr inv : classInfo.initiallys) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssert(Label.INVARIANT,e,inv.expression.getStartPosition(),statements,tree.pos);
                }
            }
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
//                        ProgVarDSA pold = new ProgVarDSA(sym,-1);
//
//                        pold.incarnation = i;
//                        ProgVarDSA pnew = new ProgVarDSA(sym,-1);
//                        pnew.incarnation = max;
                        // No position information for these nodes
                        // Type information put in, though I don't know that we need it
                        JCIdent pold = newIdentUse(sym,0,i);
                        JCIdent pnew = newIdentUse(sym,0,max);
                        JCBinary eq = factory.at(0).Binary(JCTree.EQ,pnew,pold);
                        eq.type = syms.booleanType;
                        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,eq);
                        b.statements.add(asm);
                        m.put(sym,max);
                    }
                }
                newMap.put(sym,max);
            }
        }
        return newMap;
    }
    
//    public void doDSA(BasicProgram program) {
//        DSA dsa = new DSA();
//        Map<BasicBlock,Map<String,Integer>> maps = new HashMap<BasicBlock,Map<String,Integer>>();
//        Map<String,VarSymbol> typeMap = new HashMap<String,VarSymbol>();
//        List<BasicBlock> blocksToDo = new LinkedList<BasicBlock>();
//        blocksToDo.add(program.startBlock());
//
//        while (!blocksToDo.isEmpty()) {
//            BasicBlock block = blocksToDo.remove(0);
//            Map<String,Integer> incMap = maps.get(block);
//            if (incMap != null) continue;
//            Iterator<BasicBlock> before = block.preceding.iterator();
//            while (before.hasNext()) {
//                BasicBlock t = before.next();
//                if (maps.get(t) == null) {
//                    if (block != null) {
//                        blocksToDo.add(0,block);
//                        block = null;
//                    }
//                    blocksToDo.add(0,t);
//                }
//            }
//            if (block == null) continue;
//            // All previous blocks have been done (all have maps)
//            incMap = new HashMap<String,Integer>();
//            if (block.preceding.size() == 0) {
//                // keep the empty one
//            } else if (block.preceding.size() == 1) {
//                incMap.putAll(maps.get(block.preceding.get(0))); 
//            } else {
//                List<Map<String,Integer>> all = new LinkedList<Map<String,Integer>>();
//                Map<String,Integer> combined = new HashMap<String,Integer>();
//                for (BasicBlock b : block.preceding) {
//                    Map<String,Integer> m = maps.get(b);
//                    all.add(m);
//                    combined.putAll(m);
//                }
//                for (String s: combined.keySet()) {
//                    int max = -1;
//                    for (Map<String,Integer> m: all) {
//                        Integer i = m.get(s);
//                        if (i != null && i > max) max = i;
//                    }
//                    for (BasicBlock b: block.preceding) {
//                        Map<String,Integer> m = maps.get(b);
//                        Integer i = m.get(s);
//                        if (i == null) i = 0;
//                        if (i < max) {
//                            VarSymbol sym = typeMap.get(s);
//                            ProgVarDSA pold = new ProgVarDSA(sym,-1);
//                            pold.incarnation = i;
//                            ProgVarDSA pnew = new ProgVarDSA(sym,-1);
//                            pnew.incarnation = max;
//                            JCBinary eq = factory.Binary(JCTree.EQ,pnew,pold);
//                            JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,eq);
//                            b.statements.add(asm);
//                        }
//                    }
//                    incMap.put(s,max);
//                }
//            }
//            maps.put(block,incMap);
//            for (JCStatement st: block.statements()) {
//                dsa.assignIncarnations(st,incMap);
//                if (st instanceof JmlStatementExpr
//                        && ((JmlStatementExpr)st).token == JmlToken.ASSUME
//                        && ((JmlStatementExpr)st).label == Label.ASSIGNMENT) {
//                    JCExpression e = ((JmlStatementExpr)st).expression;
//                    JCExpression lhs;
//                    if (e instanceof JCBinary) {
//                        lhs = ((JCBinary)e).getLeftOperand();
//                    } else if (e instanceof JmlBinary) {
//                        lhs = ((JmlBinary)e).getLeftOperand();
//                    } else {
//                        System.out.println("UNEXPECTED " + e.getClass());
//                        continue;
//                    }
//                    if (lhs instanceof AuxVarDSA) continue;
//                    if (lhs instanceof JCIdent) {
//                        System.out.println("UNEXPECTED-B " + lhs.getClass());
//                        continue;
//                    }
//                    if (!(lhs instanceof ProgVarDSA)) {
//                        System.out.println("UNEXPECTED-B " + lhs.getClass());
//                        continue;
//                    }
//                    String root = ((ProgVarDSA)lhs).root();
//                    typeMap.put(root,((ProgVarDSA)lhs).sym);
//                    ((ProgVarDSA)lhs).incarnation = st.pos;
//                    incMap.put(root,st.pos);
//                }
//            }
//
//            blocksToDo.addAll(block.succeeding());
//        }
//    }
    
//    static public class DSA extends JmlTreeScanner {
//
//        Map<String,Integer> map;
//        Map<String,Integer> prestateMap = new HashMap<String,Integer>();
//        
//        public void assignIncarnations(JCTree tree, Map<String,Integer> map) {
//            this.map = map;
//            tree.accept(this);
//        }
//
//        public void visitProgVarDSA(ProgVarDSA that) {
//            Integer i = map.get(that.root());
//            if (i == null) 
//                that.incarnation = 0;
//            else
//                that.incarnation = i;
//            super.visitProgVarDSA(that);
//        }
//
//        public void visitAuxVarDSA(AuxVarDSA that) {
//            if (that.definition != null) that.definition.accept(this);
//            super.visitAuxVarDSA(that);
//        }
//
//        public void visitIdent(JCIdent that) {
//            System.out.println("UNEXPECTED IDENTIFIER (DSA) " + that.toString());
//            super.visitIdent(that);
//        }
//        
//        public void visitJmlFunction(JmlFunction that) {
//            if (that.token != JmlToken.BSOLD && that.token != JmlToken.BSPRE) {
//                super.visitJmlFunction(that);
//                return;
//            }
//            // Get appropriate incarnation map
//            // For pre-state this is an empty map
//            Map<String,Integer> prev = map;
//            try {
//                map = prestateMap;
//                super.visitJmlFunction(that);
//            } finally {
//                map = prev;
//            }
//        }
//
//        public void visitApply(JCMethodInvocation that) {
//            Map<String,Integer> prev = map;
//            try {
//                if (that.meth instanceof JmlFunction) {
//                    // FIXME - get the right map for labelled old and pre
//                    // FIXME - are there any other tokens to worry about?
//                    map = prestateMap;
//                } 
//                super.visitApply(that);
//            } finally {
//                map = prev;
//            }
//        }
//
//    }

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

    JmlMethodInfo getMethodInfo(JCMethodDecl method) {
        JmlMethodInfo mi = methodInfoMap.get(method.sym);
        if (mi == null) {
            mi = computeMethodInfo(method);
            methodInfoMap.put(method.sym,mi);
        }
        return mi;
    }


    // FIXME - when run standalone (not in Eclipse), this method is called with the Object constructor 
    // as its argument, but with method.sym == null - is this because it is Binary?  is it not seeing the specs?
    JmlMethodInfo computeMethodInfo(JCMethodDecl method) {
        JmlMethodInfo mi = new JmlMethodInfo(method);
        JmlMethodSpecs denestedSpecs = method.sym == null ? null : specs.getDenestedSpecs(method.sym);
        System.out.println("SPECS FOR " + method.getName() + " " + (denestedSpecs != null) + " " + method.sym);
        System.out.println(denestedSpecs == null ? "     No denested Specs" : denestedSpecs.toString("   "));
        // FIXME - what to do if trExpr actullay produces some new statements?
        List<JCStatement> prev = newstatements;
        newstatements = new LinkedList<JCStatement>();
        if (denestedSpecs != null) {
            // preconditions
            JCExpression pre = denestedSpecs.cases.size() == 0 ? trueLiteral : falseLiteral;
            int num = 0;
            for (JmlSpecificationCase spc: denestedSpecs.cases) {
                JCExpression spre = trueLiteral;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.REQUIRES) {
                        num++;
                        JCExpression e = (((JmlMethodClauseExpr)c).expression);
                        spre = factory.Binary(JCTree.AND,spre,e);
                        spre.pos = e.pos;
                    }
                }
                pre = factory.Binary(JCTree.OR,pre,spre);
                pre.pos = spre.pos;
            }
            if (pre != trueLiteral) {
                mi.requiresPredicates.add(pre);
            }
            // postconditions
            for (JmlSpecificationCase spc: denestedSpecs.cases) {
                JCExpression spre = trueLiteral;
                for (JmlMethodClause c: spc.clauses) {
                    // FIXME - need definedness checks ??
                    if (c.token == JmlToken.REQUIRES) spre = factory.Binary(JCTree.AND,spre,(((JmlMethodClauseExpr)c).expression));
                }
                JCExpression nspre = factory.Apply(null,factory.JmlFunction(JmlToken.BSOLD),com.sun.tools.javac.util.List.of(spre));
                nspre.type = spre.type;
                spre = nspre;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.ENSURES) {
                        JCExpression post = factory.JmlBinary(JmlToken.IMPLIES,spre,(((JmlMethodClauseExpr)c).expression));
                        post.pos = ((JmlMethodClauseExpr)c).expression.getStartPosition();
                        // FIXME - need definedness checks ??
                        mi.ensuresPredicates.add(post);
                    } else if (c.token == JmlToken.ASSIGNABLE) {
                        JmlMethodClauseAssignable mod = (JmlMethodClauseAssignable)c;
                        // spre is the precondition under which the store-refs are modified
                        List<JCTree> list = mod.list; // store-ref expressions
                        mi.assignables.add(new JmlMethodInfo.Entry(spre,list));
                    }
                }
            }
        }
        newstatements = prev;
        return mi;
    }


    // Statement nodes to be implemented
    
    public void visitBlock(JCBlock that) {
        List<JCStatement> s = that.getStatements();
        if (s != null) remainingStatements.addAll(0,s);
    }
    
    public void visitDoLoop(JCDoWhileLoop that)          { notImpl(that); }
    
    /* while (B) S;
     * becomes
     * LoopStart: - is actually the end of the current Block
     *   assert loop invariants
     *   havoc any loop modified variables
     *   assume loop invariants
     *   compute loop condition
     *   goto LoopBody, LoopEnd
     * LoopBody:
     *   assume B
     *   compute decreasing, check that it is > 0
     *   S
     *   goto LoopContinue
     * LoopContinue:  <-- all continues go here
     *   assert loop invariants
     *   check that decreasing is less
     * LoopEnd:
     *   assume !B 
     *   goto LoopBreak
     * LoopBreak: <-- all breaks go here
     *   assert loop invariants 
     *   goto rest...
     */
    public void visitJmlWhileLoop(JmlWhileLoop that)  { 
        int pos = that.pos;
        BasicBlock bloopBody = new BasicBlock("LoopBody" + pos);
        BasicBlock bloopContinue = new BasicBlock("LoopContinue" + pos);
        BasicBlock bloopEnd = new BasicBlock("LoopEnd" + pos);
        BasicBlock bloopBreak = new BasicBlock("LoopBreak" + pos);
        String restName = "afterWhile" + pos;

        // Now create an (unprocessed) block for everything that follows the
        // if statement
        BasicBlock brest = new BasicBlock(restName,currentBlock);// it gets all the followers of the current block
        List<JCStatement> temp = brest.statements;
        brest.statements = remainingStatements; // it gets all of the remaining statements
        remainingStatements = temp;
        blocksToDo.add(0,brest); // push it on the front of the to do list

        // Finish out the current block with the loop initialization
        addLoopInvariants(JmlToken.ASSERT,that.loopSpecs,that.getStartPosition());
        {
            // Now havoc needed variables
            List<JCExpression> targets = TargetFinder.findVars(that.body,null);
            TargetFinder.findVars(that.cond,targets);
            // synthesize a modifies list
            int wpos = that.body.pos;
            for (JCExpression e: targets) {
                if (e instanceof JCIdent) {
                    newIdentIncarnation((JCIdent)e,wpos);
                } else {
                    System.out.println("UNIMPLEMENTED HAVOC IN LOOP " + e.getClass());
                }
            }
        }
        addLoopInvariants(JmlToken.ASSUME,that.loopSpecs,that.getStartPosition());
        for (JmlStatementLoop loopspec: that.loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                String dec = "decreases" + "$" + loopspec.getStartPosition();
                addAuxVariable(dec,syms.longType,loopspec.expression,false);
            }
        }
        String loopTestVarName = "loopCondition"  
            + "$" + that.cond.getStartPosition() + "$" + that.cond.getStartPosition(); // FIXME - end position?
        JCIdent loopTest = addAuxVariable(loopTestVarName,syms.booleanType,that.cond,false);
        completed(currentBlock);
        BasicBlock bloopStart = currentBlock;
        follows(bloopStart,bloopBody);
        follows(bloopStart,bloopEnd);

        // Create the loop body block
        startBlock(bloopBody);
        addAssume(Label.LOOP,loopTest,bloopBody.statements,false);
        for (JmlStatementLoop loopspec: that.loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                int p = loopspec.getStartPosition();
                String dec = "decreases" + "$" + p;
                JCIdent v = newAuxIdent(dec,syms.longType,p);
                JCExpression e = factory.at(p).Binary(JCTree.GT,v,factory.Literal(TypeTags.INT,0));
                addAssert(Label.LOOP_DECREASES_NEGATIVE,e,p,currentBlock.statements,that.body.getStartPosition()); // FIXME - track which continue is causing a problem?
            }
        }
        remainingStatements.add(that.body);
        follows(bloopBody,bloopContinue);
        processBlockStatements(true);
        
        // Create a loop continue block
        startBlock(bloopContinue);
        // Check that loop invariants are still established
        addLoopInvariants(JmlToken.ASSERT,that.loopSpecs,that.body.getStartPosition()); // FIXME - use end position?
        // Check that loop variants are decreasing
        for (JmlStatementLoop loopspec: that.loopSpecs) {
            if (loopspec.token == JmlToken.DECREASES) {
                String dec = "decreases" + "$" + loopspec.getStartPosition();
                JCIdent id = newAuxIdent(dec,syms.longType,loopspec.getStartPosition());
                JCExpression newexpr = trExpr(loopspec.expression);
                JCExpression e = factory.Binary(JCTree.LT,newexpr,id);
                addAssert(Label.LOOP_DECREASES,e,loopspec.pos,currentBlock.statements,that.body.getStartPosition()); // FIXME - track which continue is causing a problem?
            }
        }
        completed(bloopContinue);
        
        // Create the LoopEnd block
        startBlock(bloopEnd);
        follows(bloopEnd,bloopBreak);
        JCExpression neg = factory.at(loopTest.pos).Unary(JCTree.NOT,loopTest);
            // FIXME - start and end position
        addAssume(Label.LOOP,neg,currentBlock.statements,false);
        completed(bloopEnd);
        
        // fill in the LoopBreak block
        startBlock(bloopBreak);
        follows(bloopBreak,brest);
        addLoopInvariants(JmlToken.ASSERT,that.loopSpecs,that.body.getStartPosition()+1); // FIXME _ use end position - keep different from Continue
        completed(bloopBreak);

        // Go on processing the loop body
        currentBlock = null;
        newstatements = null;
    }
    
    protected void addLoopInvariants(JmlToken t, java.util.List<JmlStatementLoop> loopSpecs, int usepos) {
        for (JmlStatementLoop loopspec: loopSpecs) {
            if (loopspec.token == JmlToken.LOOP_INVARIANT) {
                JCExpression e = trExpr(loopspec.expression);
                if (t == JmlToken.ASSUME) addAssume(Label.LOOP_INVARIANT,e,currentBlock.statements,false);
                else addAssert(Label.LOOP_INVARIANT,e,loopspec.pos,currentBlock.statements,usepos);
            }
        }
    }

    public void visitWhileLoop(JCWhileLoop that)         { 
        // This is a loop with no specs
        int pos = that.pos;
        String loopStart = "LoopStart" + pos;
        String loop = "LoopBody" + pos;
        String loopContinue = "LoopContinue" + pos;
        String loopEnd = "LoopEnd" + pos;
        String loopBreak = "LoopBreak" + pos;
        String restName = "afterLoop" + pos;

        // Now create an (unprocessed) block for everything that follows the
        // if statement
        BasicBlock b = new BasicBlock(restName,currentBlock);// it gets all the followers of the current block
        List<JCStatement> temp = b.statements;
        b.statements = remainingStatements; // it gets all of the remaining statements
        remainingStatements = temp;
        blocksToDo.add(0,b); // push it on the front of the to do list
        BasicBlock brest = b;

    }
    
    public void visitForLoop(JCForLoop that)             { notImpl(that); }
    public void visitForeachLoop(JCEnhancedForLoop that) { notImpl(that); }
    public void visitLabelled(JCLabeledStatement that)   { notImpl(that); }
    
    public void visitSwitch(JCSwitch that)               { 
        int pos = that.pos;
        JCExpression switchExpression = that.selector;
        List<JCCase> cases = that.cases;
        
        // Create the ending block name
        String endBlock = "switchEnd" + pos;
        
        try {
            breakStack.addFirst(that);

            // We create a new auxiliary variable to hold the switch value, so 
            // we can track its value and so the subexpression does not get
            // replicated.  We add an assumption about its value and add it to
            // list of new variables
            String switchName = ("$switchExpression" + pos 
                    + "$" + that.getStartPosition() + "$" + that.getStartPosition()); // FIXME - use end position
            JCExpression newexpr = trExpr(switchExpression);
            JCIdent vd = newAuxIdent(switchName,switchExpression.type,newexpr.pos);
            JmlTree.JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,factory.Binary(JCTree.EQ,vd,newexpr));
            asm.pos = switchExpression.pos;
            newstatements.add(asm);
            BasicBlock switchStart = currentBlock;

            // Now create an (unprocessed) block for everything that follows the
            // switch statement
            BasicBlock b = new BasicBlock(endBlock,currentBlock);// it gets all the followers of the current block
            List<JCStatement> temp = b.statements;
            b.statements = remainingStatements; // it gets all of the remaining statements
            remainingStatements = temp;
            blocksToDo.add(0,b); // push it on the front of the to do list
            BasicBlock brest = b;

            // Now we need to make blocks, processing them as we go, for all of the case statements
            // Note that there might be nesting of other switch statements etc.
            java.util.LinkedList<BasicBlock> blocks = new java.util.LinkedList<BasicBlock>();
            BasicBlock prev = null;
            JCExpression defaultCond = falseLiteral;
            JmlTree.JmlStatementExpr defaultAsm = null;
            for (JCCase caseStatement: cases) {
                JCExpression caseValue = caseStatement.getExpression();
                List<JCStatement> stats = caseStatement.getStatements();
                String caseName = ("$case" + caseStatement.pos 
                        + "$" + that.getStartPosition() + "$" + that.getStartPosition()); // FIXME - use end position
                BasicBlock blockForTest = new BasicBlock(caseName);
                follows(switchStart,blockForTest);
                JCBinary eq = caseValue == null ? null : factory.Binary(JCTree.EQ,vd,caseValue);
                asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,eq);
                asm.pos = switchExpression.pos;
                blockForTest.statements.add(asm);
                if (caseValue == null) defaultAsm = asm;
                else defaultCond = factory.Binary(JCTree.OR,eq,defaultCond);
                blocks.add(blockForTest);
                boolean fallthrough = stats.isEmpty() || !(stats.get(stats.size()-1) instanceof JCBreak);
                if (prev == null) {
                    // statements can go in the same block
                    blockForTest.statements.addAll(stats);
                    if (!fallthrough) follows(blockForTest,brest);
                    prev = fallthrough ? blockForTest : null;
                } else {
                    // since there is fall-through, the statements need to go in their own block
                    String caseStats = ("$caseStats" + caseStatement.pos 
                            + "$" + that.getStartPosition() + "$" + that.getStartPosition()); // FIXME - use end position
                    BasicBlock blockForStats = new BasicBlock(caseStats);
                    blockForStats.statements.addAll(stats);
                    follows(blockForTest,blockForStats);
                    follows(prev,blockForStats);
                    if (!fallthrough) follows(blockForStats,brest);
                    blocks.add(blockForStats);
                    prev = fallthrough ?  blockForStats : null;
                }
            }
            if (prev != null) follows(prev,brest);
            if (defaultAsm != null) {
                JCExpression eq = factory.Unary(JCTree.NOT,defaultCond);
                defaultAsm.expression = eq;
            }
            // push all of the blocks onto the to do list
            while (!blocks.isEmpty()) {
                blocksToDo.add(0,blocks.removeLast());
            }
        } finally {
            breakStack.removeFirst();
        }
        
        
    }
    
    public void visitCase(JCCase that)                   { shouldNotBeCalled(that); } // FIXME - change error message - should never get here since case is handled in switch
    
    protected java.util.Deque<JCTry> tryStack = new java.util.LinkedList<JCTry>();

    public void visitTry(JCTry that) {
        // Create an (unprocessed) block for everything that follows the
        // try statement
        BasicBlock b = new BasicBlock("afterTry" + that.pos,currentBlock);// it gets all the followers of the current block
        List<JCStatement> temp = b.statements;
        b.statements = remainingStatements; // it gets all of the remaining statements
        remainingStatements = temp;
        blocksToDo.add(0,b); // push it on the front of the to do list
        BasicBlock brest = b;
        remainingStatements.add(0,that.getBlock()); // push on the front of the list
        JCExpression e = factory.Unary(JCTree.NOT,returningVar);
        e.type = syms.booleanType;
        JmlTree.JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e); 
        brest.statements.add(0,asm);
        
        try {
            // We make an empty finally block if the try statement does not
            // have one, just to simplify things
            tryStack.addFirst(that);
            JCBlock finallyStat = that.getFinallyBlock();
            int pos = that.pos;
            String finallyBlockName = "finally" + pos;
            BasicBlock finallyBlock = new BasicBlock(finallyBlockName,currentBlock);// it gets all the followers of the current block
            if (finallyStat != null) finallyBlock.statements.add(finallyStat); // it gets all of the remaining statements
            blocksToDo.add(0,finallyBlock); // push it on the front of the to do list
            follows(currentBlock,finallyBlock);
            follows(finallyBlock,brest);
            follows(finallyBlock,condReturnBlock);
            lookup.put(finallyBlock.name,finallyBlock);
                
                // FIXME - have to handle exceptions going someplace else
            int i = 0;
            for (JCCatch catcher: that.catchers) {
                String catchBlockName = "catch" + catcher.pos;
                BasicBlock catchBlock = new BasicBlock(catchBlockName);
                catchBlock.statements.add(catcher.getBlock()); // it gets all of the remaining statements
                blocksToDo.add(i++,catchBlock); // push it on the front of the to do list
                follows(catchBlock,finallyBlock);
            }
            
            // Do the processing here
            processBlockStatements(false);
        } finally {
            tryStack.removeFirst();
        }
    }
    
    public void visitCatch(JCCatch that) { 
        shouldNotBeCalled(that); 
    }
    
    public void visitConditional(JCConditional that) { 
        JCExpression cond = trExpr(that.cond);
        JCExpression truepart = trExpr(that.truepart);
        JCExpression falsepart = trExpr(that.falsepart);
        JCConditional now = factory.Conditional(cond,truepart,falsepart);
        now.type = that.type;
        now.pos = that.pos;
        result = now;
    }
    
    public void visitIf(JCIf that) {
        // Create a bunch of block names
        String thenName = "then" + that.pos;
        String elseName = "else" + that.pos;
        String restName = "afterIf" + that.pos;
        
        // We create a new auxiliary variable to hold the branch condition, so 
        // we can track its value and so the subexpression does not get
        // replicated.  We add an assumption about its value and add it to
        // list of new variables
        String condName = ("branchCondition" + that.pos 
                + "$" + that.getStartPosition() + "$" + that.getStartPosition()); // FIXME - use end position
        JCIdent vd = newAuxIdent(condName,syms.booleanType,that.cond.pos);
        JCExpression newexpr = factory.at(that.cond.pos).Binary(JCTree.EQ,vd,that.cond);
        newexpr.type = syms.booleanType;
        JmlTree.JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,trExpr(newexpr));
        asm.pos = that.pos;
        newstatements.add(asm);
        
        // Now create an (unprocessed) block for everything that follows the
        // if statement
        BasicBlock b = new BasicBlock(restName,currentBlock);// it gets all the followers of the current block
        List<JCStatement> temp = b.statements;
        b.statements = remainingStatements; // it gets all of the remaining statements
        remainingStatements = temp;
        blocksToDo.add(0,b); // push it on the front of the to do list
        BasicBlock brest = b;
        
        // Now make the else block, also unprocessed
        b = new BasicBlock(elseName);
        JCExpression c = factory.Unary(JCTree.NOT,vd);
        //c = addAuxVariable("auxE"+that.cond.pos,syms.booleanType,c,true);
        JmlTree.JmlStatementExpr t = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.BRANCHE,c);
        t.pos = that.cond.pos + 1;
        b.statements.add(t);
        if (that.elsepart != null) b.statements.add(that.elsepart);
        blocksToDo.add(0,b);
        follows(b,brest);
        follows(currentBlock,b);
        
        // Now make the then block, also still unprocessed
        b = new BasicBlock(thenName);
        c = vd;
        //c = addAuxVariable("auxT"+that.cond.pos,syms.booleanType,c,true);
        t = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.BRANCHT,c);
        t.pos = that.cond.pos;
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
    
    protected java.util.Deque<JCStatement> breakStack = new java.util.LinkedList<JCStatement>();
    
    public void visitBreak(JCBreak that) { 
        if (breakStack.isEmpty()) {
            // ERROR - FIXME
        } else if (breakStack.peekFirst() instanceof JCSwitch) {
            // Don't need to do anything.  If the break is not at the end of a block,
            // the compiler would not have passed this.  If it is at the end of a block
            // the logic in handling JCSwitch has taken care of everything.
            
            // FIXME - for safety, check and warn if there are any remaining statements in the block
        } else {
            // Some kind of loop
        }
    }
    
    public void visitContinue(JCContinue that)           { notImpl(that); }
    
    public void visitReturn(JCReturn that)               {
        if (that.getExpression() != null) {
            JCExpression res = trExpr(that.getExpression());
            JCExpression now = factory.Binary(JCTree.EQ,resultVar,res);
            JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,now);
            newstatements.add(asm);
        }
        JCIdent id = newIdentIncarnation(returningVar,that.pos);
        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,id);
        newstatements.add(asm);
        if (tryStack.isEmpty()) {
            replaceFollows(currentBlock,returnBlock);
        } else {
            String s = "finally" + tryStack.peekFirst().pos;
            BasicBlock finallyBlock = lookup.get(s);
            replaceFollows(currentBlock,finallyBlock);
        }
        // FIXME check and warn if there are remaining statements
    }
    public void visitThrow(JCThrow that)                 { notImpl(that); }
    
    public void visitAssert(JCAssert that) { 
        JCExpression cond = trExpr(that.cond);
        JCExpression detail = trExpr(that.detail);
        // FIXME - what to do with detail
        // FIXME - for now turn cond into a JML assertion
        // FIXME - need a label for the assert statement
        // FIXME - set line and source
        addAssert(Label.EXPLICIT_ASSERT, cond, that.cond.getStartPosition(), newstatements, that.cond.getStartPosition());
    }
    
    //protected Deque<HashMap<VarSymbol,Integer>> oldstack = new LinkedList<HashMap<VarSymbol,Integer>>();
    //protected Deque<JCIdent> retstack = new LinkedList<JCIdent>();
    
    public void visitApply(JCMethodInvocation that)      { 
        if (!(that.meth instanceof JmlFunction)) {

            JCExpression now;
            JCExpression obj;
            MethodSymbol msym;
            if (that.meth instanceof JCIdent) {
                obj = thisId;
                now = trExpr(that.meth);
                msym = (MethodSymbol)((JCIdent)now).sym;
            } else if (that.meth instanceof JCFieldAccess) {
                JCFieldAccess fa = (JCFieldAccess)that.meth;
                obj = trExpr( fa.selected );
                msym = (MethodSymbol)(fa.sym);
            } else {
                // FIXME - not implemented
                msym = null;
                obj = null;
            }
        
            // FIXME - translate typeargs

            ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
            for (JCExpression arg: that.args) {
                JCExpression n = trExpr(arg);
                newargs.append(n);
            }

            // FIXME - concerned that the position here is not after the
            // positions of all of the arguments
            result = insertMethodCall(that.pos,msym,obj,newargs.toList());
            return;
        }
        JmlToken token = ((JmlFunction)that.meth).token;
        
        if (token == JmlToken.BSOLD) {
            Map<VarSymbol,Integer> prev = currentMap;
            currentMap = oldMap; //oldstack.isEmpty() ? new HashMap<VarSymbol,Integer>()
                                 //   : oldstack.peekFirst();
            try {
                // There is only one argument to translate
                result = trExpr(that.args.get(0));
            } finally {
                currentMap = prev;
            }
            return;
        } else {
            System.out.println("JmlFunction not implemented " + token.internedName());
        }
        return;
    }
    
    public JCIdent insertMethodCall(int pos, MethodSymbol sym, JCExpression obj, List<JCExpression> args) {
        Map<VarSymbol,Integer> prevOldMap = oldMap;
        JCIdent prevThisId = thisId;
        JCIdent retId = sym.type == null ? null : newAuxIdent("$$result$"+pos,sym.type,pos);
        JCIdent prevResultVar = resultVar;
        
        try {
            JmlMethodSpecs mspecs = specs.getSpecs(sym);
            if (mspecs == null) {
                System.out.println("NO SPECS FOR METHOD CALL");
            } else {
                
                JCExpression expr;
                // Note: need to do all of the expression translation before
                // we assign the new thisId
                if (obj != null) obj = trExpr(obj);
                
                // Evaluate all of the arguments and assign them to a new variable
                JmlMethodDecl decl = mspecs.decl;
                int i = 0;
                for (JCVariableDecl vd  : decl.params) {
                    expr = args.get(i++);
                    JCIdent id = newIdentIncarnation(vd,pos);
                    // FIXME - end information?  use copyInfo?
                    expr = factory.at(id.pos).Binary(JCTree.EQ,id,expr);
                    expr.type = syms.booleanType; // FIXME - start end? source line?
                    JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
                    newstatements.add(st);
                }
                
                thisId = newAuxIdent("this$"+pos,syms.objectType,pos); // FIXME - object type?
                if (obj != null) {
                    expr = factory.at(obj.pos).Binary(JCTree.EQ,thisId,obj);
                    expr.type = syms.booleanType; // FIXME - start end? source line?
                    JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
                    newstatements.add(st);
                }

                boolean isStatic = decl.mods != null && (decl.mods.flags & Flags.STATIC) != 0;
                boolean isConstructor = false; // FIXME - what about super calls within constructors
                boolean isHelper = isHelper(decl.sym);
                if (!isConstructor && !isHelper) {
                    for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                        JCExpression e = inv.expression;
                        e = trExpr(e);
                        addAssert(Label.INVARIANT,e,inv.pos,newstatements,pos);
                    }
                    if (!isStatic) {
                        for (JmlTypeClauseExpr inv : classInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trExpr(e);
                            addAssert(Label.INVARIANT,e,inv.pos,newstatements,pos);
                        }
                    }
                }
                if (isConstructor && !isHelper) {
                    for (JmlTypeClauseExpr inv : classInfo.initiallys) {
                        JCExpression e = inv.expression;
                        e = trExpr(e);
                        addAssert(Label.INVARIANT,e,inv.pos,newstatements,pos);
                    }
                }
                JmlMethodInfo mi = getMethodInfo(decl);
                for (JCExpression pre: mi.requiresPredicates) {
                    addAssert(Label.PRECONDITION,trExpr(pre),decl.pos,newstatements,pos);
                }

                oldMap = new HashMap<VarSymbol,Integer>(currentMap);

                for (JmlMethodInfo.Entry entry: mi.assignables) {
                    // What to do with preconditions?  FIXME
                            for (JCTree sr: entry.storerefs) {
                                if (sr instanceof JCIdent) {
                                    JCIdent id = (JCIdent)sr;
                                    newIdentIncarnation(id,pos+1); // new incarnation
                                } else {
                                    System.out.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                                }
                            }
                }
                
                resultVar = retId;
                for (JCExpression post: mi.ensuresPredicates) {
                    addAssume(Label.POSTCONDITION,trExpr(post),newstatements,false);
                }
                resultVar = prevResultVar;
                
                if (!isHelper) {
                    for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                        JCExpression e = inv.expression;
                        e = trExpr(e);
                        addAssume(Label.INVARIANT,e,newstatements,false);
                    }
                    if (!isStatic) {
                        for (JmlTypeClauseExpr inv : classInfo.invariants) {
                            JCExpression e = inv.expression;
                            e = trExpr(e);
                            addAssume(Label.INVARIANT,e,newstatements,false);
                        }
                    }
                    if (!isConstructor) {
                        for (JmlTypeClauseConstraint inv : classInfo.staticconstraints) {
                            JCExpression e = inv.expression;
                            e = trExpr(e);
                            addAssume(Label.CONSTRAINT,e,newstatements,false);
                        }
                        if (!isStatic) {
                            for (JmlTypeClauseConstraint inv : classInfo.constraints) {
                                JCExpression e = inv.expression;
                                e = trExpr(e);
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
            thisId = prevThisId;
            resultVar = prevResultVar;
            result = retId;
        }
//        } else if (meth instanceof JCFieldAccess) {
//            Log.instance(context).warning("jml.unimplemented.construct","meth.getClass() in insertMethodCall - JCFieldAccess");
//        } else {
//            Log.instance(context).warning("jml.unimplemented.construct","meth.getClass() in insertMethodCall " + meth.getClass());
//        }
        return retId;
    }
    
    public void visitSkip(JCSkip that)                   {
        // do nothing
    }
    public void visitJmlStatement(JmlStatement that) {
        // Just do all the JML statements as if they were Java statements, 
        // since they are part of specifications
        that.statement.accept(this);
    }
    
    public void visitJmlStatementLoop(JmlStatementLoop that)       { notImpl(that); }
    public void visitJmlStatementSpec(JmlStatementSpec that)       { notImpl(that); }
    
    public void visitJmlStatementExpr(JmlStatementExpr that) { 
        JmlStatementExpr now;
        if (that.token == JmlToken.ASSUME || that.token == JmlToken.ASSERT) {
            JCExpression expr = trExpr(that.expression);
            JCExpression opt = trExpr(that.optionalExpression);
            if (that.token == JmlToken.ASSERT) {
                expr = addAssert(that.label,expr,that.pos,newstatements,that.pos);
            }
//            if (expr == that.expression && opt == that.optionalExpression)
//                now = that;
//            else {
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
                        newdefs.add(factory.at(that.pos).Binary(JCTree.EQ,id,trueLiteral));

//                        String restName = "blockA" + that.pos;
//                        // Now create an (unprocessed) block for everything that follows the
//                        // if statement
//                        BasicBlock b = new BasicBlock(restName,currentBlock);// it gets all the followers of the current block
//                        List<JCStatement> temp = b.statements;
//                        b.statements = remainingStatements; // it gets all of the remaining statements
//                        remainingStatements = temp;
//                        blocksToDo.add(0,b); // push it on the front of the to do list
//                        follows(currentBlock,b);
//                        return;
                    } else {
                        //expr = addAuxVariable("assume"+expr.pos,syms.booleanType,expr,true);
                        now = factory.JmlExpressionStatement(that.token,that.label,expr);
                        now.optionalExpression = opt;
                        now.pos = that.pos;
                        now.type = that.type;   
                    }
                } else {
                    now = factory.JmlExpressionStatement(that.token,that.label,expr);
                    now.optionalExpression = opt;
                    now.pos = that.pos;
                    now.type = that.type;
                }
 //           }
            currentBlock.statements.add(now);
            if (that.token == JmlToken.ASSUME && (that.label == Label.EXPLICIT_ASSUME 
                    || that.label == Label.BRANCHT || that.label == Label.BRANCHE)) {
                int pos = now.pos;
                String n = "assumeCheck$" + that.pos + "$" + that.label.toString();
                JCExpression count = factory.Literal(TypeTags.INT,that.pos);
                JCExpression e = factory.at(pos).Binary(JCTree.NE,assumeCheckCountVar,count);
                JCExpression id = newAuxIdent(n,syms.booleanType,e.pos);
                e = factory.at(pos).JmlBinary(JmlToken.EQUIVALENCE,id,e);
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
            JCExpression expr = factory.Literal(TypeTags.BOOLEAN,Boolean.FALSE);
            expr.pos = that.pos; // FIXME - start and end position?
            addAssert(Label.UNREACHABLE,expr,that.pos,currentBlock.statements,that.getStartPosition());
        } else {
            // ERROR - FIXME
        }
    }
    public void visitJmlStatementDecls(JmlStatementDecls that)     { notImpl(that); }
    public void visitJmlForLoop(JmlForLoop that)                   { notImpl(that); }
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that)   { notImpl(that); }
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that)           { notImpl(that); }

    // Expression nodes to be implemented
    public void visitParens(JCParens that)               { 
        that.expr.accept(this);
        JCExpression expr = result;
        if (expr == that.expr) { result = that; return; }
        JCParens now = factory.Parens(expr);
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
            JCExpression e = factory.at(that.pos).Binary(op,arg,factory.at(that.pos).Literal(TypeTags.INT,1));
            result = doAssignment(arg,e,that.pos);
            if (tag == JCTree.POSTDEC || tag == JCTree.POSTINC) result = arg;
            return;
        }
        if (arg == that.arg) { result = that; return; }
        JCUnary now = factory.Unary(that.getTag(),arg);
        now.operator = that.operator;
        now.type = that.type;
        now.pos = that.pos;
        result = now;
    }
    
    public void visitBinary(JCBinary that)               { 
        JCExpression left = trExpr(that.lhs);
        JCExpression right = trExpr(that.rhs);
        if (left == that.lhs && right == that.rhs) { result = that; return; }
        JCBinary now = factory.Binary(that.getTag(),left,right);
        now.operator = that.operator;
        now.type = that.type;
        now.pos = that.pos;
        result = now;
    }
    
    public void visitTypeCast(JCTypeCast that)           { notImpl(that); }
    public void visitTypeTest(JCInstanceOf that)         { notImpl(that); }
    
    public void visitIndexed(JCArrayAccess that)         { 
        JCExpression array = trExpr(that.getExpression());
        JCExpression index = trExpr(that.getIndex());
        JCIdent arrayID = getArrayIdent(that.type);
        JCArrayAccess now = new JmlBBArrayAccess(arrayID,array,index);
        now.pos = that.pos;
        now.type = that.type;
        result = now;
    }
    
    public void visitSelect(JCFieldAccess that) {
        Symbol sym = that.sym;
        if (sym == null) {
            System.out.println("NULL SYM IN SELECT: " + that.name);
        } else if (sym.isStatic()) {
            VarSymbol vsym = (VarSymbol)that.sym;
            JCIdent now = newIdentUse(vsym,that.pos);
            now.type = that.type;
            result = now;
        } else if (sym instanceof VarSymbol){
            JCExpression selected = trExpr(that.selected);
            Name field = that.name;

            VarSymbol vsym = (VarSymbol)sym;
            JCIdent id = newIdentUse(vsym,that.pos);

            JCFieldAccess now = new JmlBBFieldAccess(id,selected,field,sym);
            now.pos = that.pos;
            now.type = that.type;
            result = now;
        } else if (sym instanceof MethodSymbol) {
            // FIXME - should not get here
        } else {
            // FIXME - don't know what this could be
        }
    }
    
    public void visitIdent(JCIdent that)                 { 
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
                JCIdent thisId = factory.Ident(names.fromString("this"));
                thisId.pos = that.pos;
                VarSymbol v = new VarSymbol(0,thisId.name,owner.type,owner);
                v.pos = 0;
                thisId.sym = v;
                thisId.type = owner.type;
                JCFieldAccess now = factory.Select(thisId,vsym.name);
                now.pos = that.pos;
                now.type = that.type;
                now.sym = vsym;
                result = trExpr(now);
            } else if (vsym.toString().equals("this")) {
                result = thisId;
            } else {
                result = newIdentUse(vsym,that.pos);
            }
        } else {
            result = that;
        }
    }
    
    public void visitLiteral(JCLiteral that) { 
        // numeric, boolean, character, String, null
        // FIXME - not sure about characters or String
        result = that;
    }
    
    public void visitAssign(JCAssign that) { 
        JCExpression left = trExpr(that.lhs);
        JCExpression right = trExpr(that.rhs);
        result = doAssignment(left,right,that.pos);
    }
    
    // FIXME - embedded assignments to array elements are not implemented; no warning either
    
    protected JCExpression doAssignment(JCExpression left, JCExpression right, int pos) {
        if (left instanceof JCIdent) {
            JCIdent id = (JCIdent)left;
            left = newIdentIncarnation(id,pos);
            JCBinary expr = factory.at(pos).Binary(JCBinary.EQ,left,right);
            expr.type = syms.booleanType;

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
            expr.type = syms.booleanType;

            // FIXME - set line and source
            JmlStatementExpr assume = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
            newstatements.add(assume); 
            return left;
        } else if (left instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)left;
            Name name = fa.name;
            JCIdent oldfield = newIdentUse((VarSymbol)fa.sym,pos);
            JCIdent newfield = newIdentIncarnation(oldfield,pos);
            JCExpression expr = new JmlBBFieldAssignment(newfield,oldfield,fa.selected,right);
            expr.pos = pos;
            expr.type = syms.booleanType;

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
    // FIXME - need to handle most of these specially
    public void visitAssignop(JCAssignOp that) { 
        JCExpression left = trExpr(that.lhs);
        JCExpression right = trExpr(that.rhs);
        int op = that.getTag() - JCTree.ASGOffset;
        JCExpression e = factory.at(that.pos).Binary(op,left,right);
        result = doAssignment(left,e,that.pos);
    }


    // TBD
    public void visitVarDef(JCVariableDecl that)         { 
        JCIdent lhs = newIdentUse((VarSymbol)that.sym,that.getPreferredPosition(),that.getPreferredPosition());
        if (that.init != null) {
            // Create and store the new lhs incarnation before translating the
            // initializer because the initializer is in the scope of the newly
            // declared variable.
            JCExpression init = trExpr(that.init);
            JCBinary expr = factory.at(that.pos).Binary(JCBinary.EQ,lhs,init);
            expr.type = syms.booleanType;
            // FIXME - set line and source
            JmlStatementExpr assume = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
                // also source and line?  FIXME
            newstatements.add(assume);       
        }
    }
    public void visitSynchronized(JCSynchronized that)   { 
        // FIXME - for now ignore any synchronization
        // FIXME - should we at least evaluate the lock for side effects?
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
        
        Symbol.MethodSymbol sym = (MethodSymbol)that.constructor;
        JmlMethodSpecs mspecs = specs.getSpecs(sym);
        if (mspecs == null) {
            System.out.println("NO SPECS FOR METHOD CALL");
        } 
        int pos = that.pos;

        if (mspecs != null) {
            // Evaluate all of the arguments and assign them to a new variable
            decl = mspecs.decl;
            int i = 0;
            for (JCVariableDecl vd  : decl.params) {
                JCExpression expr = that.args.get(i++);
                JCIdent pid = newIdentIncarnation(vd,pos);
                // FIXME - end information?  use copyInfo?
                expr = factory.at(pid.pos).Binary(JCTree.EQ,pid,expr);
                expr.type = syms.booleanType; // FIXME - start end? source line?
                JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
                newstatements.add(st);
            }

            isHelper = isHelper(decl.sym);
            mi = getMethodInfo(decl);
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
        Map<VarSymbol,Integer> prevOldMap = oldMap;
        oldMap = currentCopy;

        if (mspecs != null) {

            // Now make a new incarnation value for anything in the assignables list,
            // effectively making its value something legal but undefined.
            for (JmlMethodInfo.Entry entry: mi.assignables) {
                // What to do with preconditions?  FIXME
                for (JCTree sr: entry.storerefs) {
                    if (sr instanceof JCIdent) {
                        JCIdent pid = (JCIdent)sr;
                        newIdentIncarnation(pid,pos+1); // new incarnation
                    } else {
                        System.out.println("UNIMPLEMENTED STORE REF " + sr.getClass());
                    }
                }
            }
        }

        JCIdent oldalloc = newIdentUse((VarSymbol)allocVar.sym,pos);
        JCIdent alloc = newIdentIncarnation(allocVar,pos);
        JCExpression ee = factory.at(pos).Binary(JCTree.LT,oldalloc,alloc);
        addAssume(Label.SYN,ee,newstatements,false);
        ee = new JmlBBFieldAccess(allocIdent,id,allocName,allocSym);
        ee.type = syms.intType;
        ee = factory.at(pos).Binary(JCTree.EQ,ee,alloc);
        ee.type = syms.booleanType;
        addAssume(Label.SYN,ee,newstatements,false);
        ee = factory.at(pos).Binary(JCTree.NE,id,nullLiteral);
        ee.type = syms.booleanType;
        addAssume(Label.SYN,ee,newstatements,false);

        if (mspecs != null) {
            for (JCExpression post: mi.ensuresPredicates) {
                addAssume(Label.POSTCONDITION,trExpr(post),newstatements,false);
            }
            if (!isHelper) {
                for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssume(Label.INVARIANT,e,newstatements,false);
                }
                for (JmlTypeClauseExpr inv : classInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssume(Label.INVARIANT,e,newstatements,false);
                }
            }
            // Take out the temporary variables for the arguments
            for (JCVariableDecl vd  : decl.params) {
                currentMap.remove((VarSymbol)vd.sym);
            }
        }
        oldMap = prevOldMap;
        result = id;
    }
    
    public void visitNewArray(JCNewArray that) { //that.dims, elems, elemtype
        JCIdent oldalloc = newIdentUse((VarSymbol)allocVar.sym,that.pos);
        JCIdent alloc = newIdentIncarnation(allocVar,that.pos);
        JCExpression e = factory.at(that.pos).Binary(JCTree.LT,oldalloc,alloc);
        addAssume(Label.SYN,e,newstatements,false);
        
        JCIdent id = newAuxIdent("$$newarray"+that.pos+"$",that.type,that.pos);
        e = new JmlBBFieldAccess(allocIdent,id,allocName,allocSym);
        e.type = syms.intType;
        e = factory.at(that.pos).Binary(JCTree.EQ,e,alloc);
        addAssume(Label.SYN,e,newstatements,false);
        
        List<JCExpression> dims = that.dims;
        
        JCExpression len;
        if (dims.size() != 0) {
            len = that.dims.get(0);
        } else {
            len = factory.Literal(TypeTags.INT,that.elems.size());
            len.type = syms.intType;
        }
            // FIXME - only handling one-D arrays // FIXME - how to encode element types
        e = new JmlBBFieldAccess(lengthIdent,id,lengthName,lengthSym);
        e.type = syms.intType;
        e = factory.at(that.pos).Binary(JCTree.EQ,e,trExpr(len));
        addAssume(Label.SYN,e,newstatements,false);
        
        if (that.elems != null) {
                int i = 0;
                for (JCExpression ee: that.elems) {
                    JCLiteral lit = factory.at(ee.pos).Literal(TypeTags.INT,i++);
                    lit.type = syms.intType;
                    e = new JmlBBArrayAccess(getArrayIdent(ee.type),id,lit); // FIXME - fix the type
                    e.type = ee.type; // FIXME - actually this is the type of the initializer, which may need conversion
                    e = factory.at(ee.pos).Binary(JCTree.EQ,e,trExpr(ee));
                    e.type = syms.booleanType;
                    addAssume(Label.SYN,e,newstatements,false);
                }
        }
        
        result = id;
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
    
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        //VarDSA vd = new ProgVarDSA((VarSymbol)(that.sym), that.pos);
        JCIdent vd = newIdentIncarnation(that,that.pos);
        if (that.init != null) {
            JCExpression init = trExpr(that.init);
            JmlTree.JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,factory.at(that.init.pos).Binary(JCTree.EQ,vd,init));
            asm.pos = that.init.pos;
            newstatements.add(asm);
            // FIXME - check all new asserts and assumes for location info
        }
    }
    public void visitJmlSingleton(JmlSingleton that) { 
        switch (that.token) {
            case BSRESULT:
                //methodInfo.resultUsed = true;
                if (resultVar == null) {
                    throw new RuntimeException();
                } else {
                    result = resultVar;
                }
                break;

            case INFORMAL_COMMENT:
                result = trueLiteral;
                break;
                
            case BSLOCKSET:
            case BSSAME:
            case BSNOTSPECIFIED:
            case BSNOTHING:
            case BSEVERYTHING:
                Log.instance(context).error(that.pos, "jml.unimplemented.construct",that.token.internedName(),"JmlRac.visitJmlSingleton");
                // FIXME - recovery possible?
                break;

            default:
                Log.instance(context).error(that.pos, "jml.unknown.construct",that.token.internedName(),"JmlRac.visitJmlSingleton");
            // FIXME - recovery possible?
                break;
        }
        //result = that; // TODO - can all of these be present in a basic block?
    }
    
    public void visitJmlFunction(JmlFunction that) {
        switch (that.token) {
            case BSOLD :
            case BSPRE :
                // Handling of incarnation occurs later
                result = that; 
                break;
                
            case BSTYPEOF :
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
            case BSTYPELC :
                System.out.println("NOT IMPLEMENTED TOKEN " + that.token.internedName());
                break;

            default:
                System.out.println("UNKNOWN TOKEN " + that.token.internedName());
        }


        
    }

    public void visitJmlBinary(JmlBinary that) { 
        that.lhs.accept(this);
        JCExpression left = result;
        that.rhs.accept(this);
        JCExpression right = result;
        if (left == that.lhs && right == that.rhs) { result = that; return; }
        JmlBinary now = factory.JmlBinary(that.op,left,right); // FIXME - end position infor for all new nodes?
        now.op = that.op;
        now.type = that.type;
        now.pos = that.pos;
        result = now;
    }
    
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that)     { notImpl(that); }
    public void visitJmlSetComprehension(JmlSetComprehension that) { notImpl(that); }
    
    public void visitJmlLblExpression(JmlLblExpression that) {
        String n = "$$" + that.token.toString().substring(2) + "$" + that.pos + "$" + that.label;
        JCIdent id = newAuxIdent(n,that.type,that.pos);
        JCExpression e = factory.at(that.pos).Binary(JCTree.EQ,id,trExpr(that.expression));
        e.type = syms.booleanType;
        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,e);
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
        scan(that.defs); // FIXME - is this ever called for top level class; is it write for a class definition statement?
    }
    
    @Override
    public void visitMethodDef(JCMethodDecl that)        { notImpl(that); }
    //public void visitJmlClassDecl(JmlClassDecl that) ; // OK to inherit
 
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        System.out.println("YES THIS IS CALLED - visitJMLMethodDecl");
        //convertMethodBody(that.body); // FIXME - do the proof?? // Is it ever called? in local classes?
    }
    

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
    
    public static class TargetFinder extends JmlTreeScanner {
        
        private List<JCExpression> vars;
        
        public TargetFinder() {}
        
        public static List<JCExpression> findVars(List<? extends JCTree> that, List<JCExpression> v) {
            TargetFinder vf = new TargetFinder();
            return vf.find(that,v);
        }
        
        public static List<JCExpression> findVars(JCTree that, List<JCExpression> v) {
            TargetFinder vf = new TargetFinder();
            return vf.find(that,v);
        }
        
        public List<JCExpression> find(List<? extends JCTree> that, List<JCExpression> v) {
            if (v == null) vars = new ArrayList<JCExpression>();
            else vars = v;
            for (JCTree t: that) t.accept(this);
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

    } 
    
}
