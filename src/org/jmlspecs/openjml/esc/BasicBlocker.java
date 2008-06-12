package org.jmlspecs.openjml.esc; // FIXME - change package

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;


import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicProgram.AuxVarDSA;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.esc.BasicProgram.ProgVarDSA;
import org.jmlspecs.openjml.esc.BasicProgram.VarDSA;
import org.jmlspecs.openjml.esc.JmlEsc.JmlClassInfo;

import org.jmlspecs.annotations.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.jvm.ClassReader;
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
        factory = (JmlTree.JmlFactory)JmlTree.Maker.instance(context);
        this.names = Name.Table.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
//        this.attr = (JmlAttr)JmlAttr.instance(context);
        trueLiteral = factory.Literal(TypeTags.BOOLEAN,1);
        falseLiteral = factory.Literal(TypeTags.BOOLEAN,0);
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
    @NonNull JmlTree.JmlFactory factory;
    
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
    
    /** A holding spot for the last block of a program */
    protected BasicBlock returnBlock;
    
    /** A variable to hold the block currently being processed */
    protected BasicBlock currentBlock;
    
    /** Ordered list of statements from the current block that are yet to be processed into basic program form */
    private List<JCStatement> remainingStatements;
    
    /** A class-wide counter, so that unique numbers can be obtained */
    protected int blockNumber = 0;
    
    /** Holds an AST node for a boolean true literal, initialized in the constructor */
    @NonNull final protected JCLiteral trueLiteral;
    
    /** Holds an AST node for a boolean false literal, initialized in the constructor */
    @NonNull final protected JCLiteral falseLiteral;
    
    JmlClassInfo classInfo;
    
    protected AuxVarDSA resultVar;
    
    protected AuxVarDSA assumeCheckCountVar;
    protected int assumeCheckCount; 
    
    /** Holds the result of any of the visit methods that produce JCExpressions, since the visitor
     * template used here does not have a return value.  [We could have used the templated visitor,
     * but other methods do not need to return anything, we don't need the additional parameter,
     * and that visitor is complicated by the use of interfaces for the formal parameters.]
     */
    private JCExpression result;
    
    /** Standard name for the block that starts the body */
    public static final @NonNull String BODY_BLOCK_NAME = "bodyBegin";
    
    /** Standard name for the starting block of the program (just has the preconditions) */
    public static final @NonNull String START_BLOCK_NAME = "Start";
    
    /** Standard name for the last block, whether or not a value is returned */
    public static final @NonNull String RETURN_BLOCK_NAME = "returnBlock";
    
    protected void notImpl(JCTree that) {
        System.out.println("NOT IMPLEMENTED: BasicBlocker - " + that.getClass());
    }
    
    /** Files away a completed block, adding it to the blocksCompleted list and
     * to the lookup Map.
     * @param b the completed block
     */
    protected void completed(@NonNull BasicBlock b) {
        blocksCompleted.add(b);
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
     * in creating new statements (in newstatements).
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
        if (tree.getReturnType() != null) resultVar = new AuxVarDSA(names.fromString("$$result"),tree.getReturnType().type,null); 
        assumeCheckCountVar = new AuxVarDSA(names.fromString("$$assumeCheckCount"),syms.intType,null);
        assumeCheckCount = 0;
        blockNumber = 0;
        
        JCBlock block = tree.getBody();
        returnBlock = new BasicBlock(RETURN_BLOCK_NAME);
        BasicBlock startBlock = new BasicBlock(START_BLOCK_NAME);
        
        // Put all the program statements in the Body Block
        BasicBlock bodyBlock = new BasicBlock(BODY_BLOCK_NAME);
        bodyBlock.statements.addAll(block.getStatements());
        blocksToDo.add(0,returnBlock);
        blocksToDo.add(0,bodyBlock);
        follows(startBlock,bodyBlock);
        follows(bodyBlock,returnBlock);
        
        // Handle the start block a little specially
        // It does not have any statements in it
        currentBlock = startBlock;
        newstatements = currentBlock.statements = new ArrayList<JCStatement>();
        addPreconditions(startBlock,tree,denestedSpecs);
        completed(currentBlock);

        // Pick a block to do and process it
        while (!blocksToDo.isEmpty()) {
            currentBlock = blocksToDo.remove(0);
            //System.out.println("CONVERTING " + currentBlock.name);
            remainingStatements = currentBlock.statements;
            newstatements = currentBlock.statements = new ArrayList<JCStatement>();
            while (!remainingStatements.isEmpty()) {
                JCStatement s = remainingStatements.remove(0);
                s.accept(this);
            }
            System.out.println("newstatements-Z " + newstatements.size() + " " + currentBlock.statements.size());

            completed(currentBlock);
        }
        addPostconditions(returnBlock,tree,denestedSpecs);
        
        // Make the BasicProgram
        BasicProgram program = new BasicProgram();
        program.startId = START_BLOCK_NAME;
        program.blocks.addAll(blocksCompleted);
        program.definitions = newdefs;
        program.assumeCheckVar = assumeCheckCountVar;
        
        // Now do DSA pass
        doDSA(program);
        
        // Find all the variables so they can be declared if necessary
        Set<VarDSA> vars = new HashSet<VarDSA>();
        for (BasicBlock bb : blocksCompleted) {
            VarFinder.findVars(bb.statements,vars);
        }
        for (JCExpression ex : newdefs) {
            VarFinder.findVars(ex,vars);
        }
        program.declarations.addAll(vars);
        return program;
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
        if (isConstructor && !isHelper) {
            for (JmlTypeClauseExpr inv : classInfo.initiallys) {
                JCExpression e = inv.expression;
                e = trExpr(e);
                JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.PRECONDITION,e);
                b.statements.add(asm);
            }
        }
        JmlMethodInfo mi = getMethodInfo(tree);

        for (JCExpression pre: mi.requiresPredicates) {
            JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.PRECONDITION,pre);
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
    
    protected void addAssert(Label label, JCExpression that, List<JCStatement> statements) {
        if (useAuxDefinitions) {
            String n = "assert$" + label + "$" + that.pos;
            JCExpression id = new AuxVarDSA(names.fromString(n),syms.booleanType,that);
            JCExpression expr = factory.Binary(JCTree.EQ,id,that);
            newdefs.add(expr);
            JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSERT,label,id);
            statements.add(st);
        } else {
            JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSERT,label,that);
            statements.add(st);
        }
        System.out.println("AddAssert " + statements.size());
    }
    
    // non-tracked
    protected void addAssume(Label label, JCExpression that, List<JCStatement> statements) {
//        String n = "assert$" + label + "$" + that.pos;
//        JCExpression id = new AuxVarDSA(names.fromString(n),syms.booleanType,that);
//        JCExpression expr = factory.Binary(JCTree.EQ,id,that);
//        if (useAuxDefinitions) {
//            newdefs.add(expr);
//        } else {
//            JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,expr);
//            statements.add(st);
//        }
        JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,label,that);
        statements.add(st);
        System.out.println("AddAssume " + statements.size());
    }
    
    protected void addPostconditions(BasicBlock b, JCMethodDecl tree, JmlMethodSpecs denestedSpecs) {
        List<JCStatement> statements = b.statements;
        JmlMethodInfo mi = getMethodInfo(tree);
        for (JCExpression post: mi.ensuresPredicates) {
            // ensures predicates are already translated
            addAssert(Label.POSTCONDITION,post,statements);
        }
        boolean isStatic = tree.mods != null && (tree.mods.flags & Flags.STATIC) != 0;
        boolean isConstructor = tree.getReturnType() == null;
        boolean isHelper = isHelper(tree.sym);
        if (!isHelper) {
            for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                JCExpression e = inv.expression;
                e = trExpr(e);
                addAssert(Label.INVARIANT,e,statements);
            }
            if (!isStatic) {
                for (JmlTypeClauseExpr inv : classInfo.invariants) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssert(Label.INVARIANT,e,statements);
                }
            }
            if (!isConstructor) {
                for (JmlTypeClauseConstraint inv : classInfo.staticconstraints) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssert(Label.CONSTRAINT,e,statements);
                }
                if (!isStatic) {
                    for (JmlTypeClauseConstraint inv : classInfo.constraints) {
                        JCExpression e = inv.expression;
                        e = trExpr(e);
                        addAssert(Label.CONSTRAINT,e,statements);
                    }
                }
            }
        }
    }
    
    public void doDSA(BasicProgram program) {
        DSA dsa = new DSA();
        Map<BasicBlock,Map<String,Integer>> maps = new HashMap<BasicBlock,Map<String,Integer>>();
        Map<String,VarSymbol> typeMap = new HashMap<String,VarSymbol>();
        List<BasicBlock> blocksToDo = new LinkedList<BasicBlock>();
        blocksToDo.add(program.startBlock());

        while (!blocksToDo.isEmpty()) {
            BasicBlock block = blocksToDo.remove(0);
            Map<String,Integer> incMap = maps.get(block);
            if (incMap != null) continue;
            Iterator<BasicBlock> before = block.preceding.iterator();
            while (before.hasNext()) {
                BasicBlock t = before.next();
                if (maps.get(t) == null) {
                    if (block != null) {
                        blocksToDo.add(0,block);
                        block = null;
                    }
                    blocksToDo.add(0,t);
                }
            }
            if (block == null) continue;
            // All previous blocks have been done (all have maps)
            incMap = new HashMap<String,Integer>();
            if (block.preceding.size() == 0) {
                // keep the empty one
            } else if (block.preceding.size() == 1) {
                incMap.putAll(maps.get(block.preceding.get(0))); 
            } else {
                List<Map<String,Integer>> all = new LinkedList<Map<String,Integer>>();
                Map<String,Integer> combined = new HashMap<String,Integer>();
                for (BasicBlock b : block.preceding) {
                    Map<String,Integer> m = maps.get(b);
                    all.add(m);
                    combined.putAll(m);
                }
                for (String s: combined.keySet()) {
                    int max = -1;
                    for (Map<String,Integer> m: all) {
                        Integer i = m.get(s);
                        if (i != null && i > max) max = i;
                    }
                    for (BasicBlock b: block.preceding) {
                        Map<String,Integer> m = maps.get(b);
                        Integer i = m.get(s);
                        if (i == null) i = 0;
                        if (i < max) {
                            VarSymbol sym = typeMap.get(s);
                            ProgVarDSA pold = new ProgVarDSA(sym,-1);
                            pold.incarnation = i;
                            ProgVarDSA pnew = new ProgVarDSA(sym,-1);
                            pnew.incarnation = max;
                            JCBinary eq = factory.Binary(JCTree.EQ,pnew,pold);
                            JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,eq);
                            b.statements.add(asm);
                        }
                    }
                    incMap.put(s,max);
                }
            }
            maps.put(block,incMap);
            for (JCStatement st: block.statements()) {
                dsa.assignIncarnations(st,incMap);
                if (st instanceof JmlStatementExpr
                        && ((JmlStatementExpr)st).token == JmlToken.ASSUME
                        && ((JmlStatementExpr)st).label == Label.ASSIGNMENT) {
                    JCExpression e = ((JmlStatementExpr)st).expression;
                    JCExpression lhs;
                    if (e instanceof JCBinary) {
                        lhs = ((JCBinary)e).getLeftOperand();
                    } else if (e instanceof JmlBinary) {
                        lhs = ((JmlBinary)e).getLeftOperand();
                    } else {
                        System.out.println("UNEXPECTED " + e.getClass());
                        continue;
                    }
                    if (lhs instanceof AuxVarDSA) continue;
                    if (lhs instanceof JCIdent) {
                        System.out.println("UNEXPECTED-B " + lhs.getClass());
                        continue;
                    }
                    if (!(lhs instanceof ProgVarDSA)) {
                        System.out.println("UNEXPECTED-B " + lhs.getClass());
                        continue;
                    }
                    String root = ((ProgVarDSA)lhs).root();
                    typeMap.put(root,((ProgVarDSA)lhs).sym);
                    ((ProgVarDSA)lhs).incarnation = st.pos;
                    incMap.put(root,st.pos);
                }
            }

            blocksToDo.addAll(block.succeeding());
        }
    }
    
    static public class DSA extends JmlTreeScanner {

        Map<String,Integer> map;
        Map<String,Integer> prestateMap = new HashMap<String,Integer>();
        
        public void assignIncarnations(JCTree tree, Map<String,Integer> map) {
            this.map = map;
            tree.accept(this);
        }

        public void visitProgVarDSA(ProgVarDSA that) {
            Integer i = map.get(that.root());
            if (i == null) 
                that.incarnation = 0;
            else
                that.incarnation = i;
            super.visitProgVarDSA(that);
        }

        public void visitAuxVarDSA(AuxVarDSA that) {
            if (that.definition != null) that.definition.accept(this);
            super.visitAuxVarDSA(that);
        }

        public void visitIdent(JCIdent that) {
            System.out.println("UNEXPECTED IDENTIFIER (DSA) " + that.toString());
            super.visitIdent(that);
        }
        
        public void visitJmlFunction(JmlFunction that) {
            if (that.token != JmlToken.BSOLD && that.token != JmlToken.BSPRE) {
                super.visitJmlFunction(that);
                return;
            }
            // Get appropriate incarnation map
            // For pre-state this is an empty map
            Map<String,Integer> prev = map;
            try {
                map = prestateMap;
                super.visitJmlFunction(that);
            } finally {
                map = prev;
            }
        }

        public void visitApply(JCMethodInvocation that) {
            Map<String,Integer> prev = map;
            try {
                if (that.meth instanceof JmlFunction) {
                    // FIXME - get the right map for labelled old and pre
                    // FIXME - are there any other tokens to worry about?
                    map = prestateMap;
                } 
                super.visitApply(that);
            } finally {
                map = prev;
            }
        }

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


    
    JmlMethodInfo computeMethodInfo(JCMethodDecl method) {
        JmlMethodInfo mi = new JmlMethodInfo(method);
        JmlMethodSpecs denestedSpecs = method.sym == null ? null : specs.getDenestedSpecs(method.sym);
        System.out.println("SPECS FOR " + method.getName());
        System.out.println(denestedSpecs.toString("   "));
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
                        JCExpression e = trExpr(((JmlMethodClauseExpr)c).expression);
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
                    if (c.token == JmlToken.REQUIRES) spre = factory.Binary(JCTree.AND,spre,trExpr(((JmlMethodClauseExpr)c).expression));
                }
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.ENSURES) {
                        JCExpression post = factory.JmlBinary(JmlToken.IMPLIES,spre,trExpr(((JmlMethodClauseExpr)c).expression));
                        post.pos = ((JmlMethodClauseExpr)c).expression.getStartPosition();
                        // FIXME - need definedness checks ??
                        mi.ensuresPredicates.add(post);
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
    public void visitWhileLoop(JCWhileLoop that)         { notImpl(that); }
    public void visitForLoop(JCForLoop that)             { notImpl(that); }
    public void visitForeachLoop(JCEnhancedForLoop that) { notImpl(that); }
    public void visitLabelled(JCLabeledStatement that)   { notImpl(that); }
    public void visitSwitch(JCSwitch that)               { notImpl(that); }
    public void visitCase(JCCase that)                   { notImpl(that); }
    public void visitTry(JCTry that)                     { notImpl(that); }
    public void visitCatch(JCCatch that)                 { notImpl(that); }
    public void visitConditional(JCConditional that)     { notImpl(that); }
    
    public void visitIf(JCIf that) {
        // Create a bunch of block names
        String thenName = "then" + (blockNumber);
        String elseName = "else" + (blockNumber);
        String restName = "block" + (++blockNumber);
        
        // We create a new auxiliary variable to hold the branch condition, so 
        // we can track its value and so the subexpression does not get
        // replicated.  We add an assumption about its value and add it to
        // list of new variables
        Name condName = names.fromString("branchCondition" + (++blockNumber) 
                + "$" + that.getStartPosition() + "$" + that.getStartPosition()); // FIXME - use end position
        JCExpression newexpr = trExpr(that.cond);
        VarDSA vd = new AuxVarDSA(condName,syms.booleanType,newexpr);
        JmlTree.JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.SYN,factory.Binary(JCTree.EQ,vd,newexpr));
        asm.pos = that.cond.pos;
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
        JmlTree.JmlStatementExpr t = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.BRANCHE,c);
        t.pos = that.cond.pos + 1;
        b.statements.add(t);
        if (that.elsepart != null) b.statements.add(that.elsepart);
        blocksToDo.add(0,b);
        follows(b,brest);
        follows(currentBlock,b);
        
        // Now make the then block, also still unprocessed
        b = new BasicBlock(thenName);
        t = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.BRANCHT,vd);
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
    
    public void visitBreak(JCBreak that)                 { notImpl(that); }
    public void visitContinue(JCContinue that)           { notImpl(that); }
    public void visitReturn(JCReturn that)               {
        JCExpression res = trExpr(that.getExpression());
        JCExpression now = factory.Binary(JCTree.EQ,resultVar,res);
        JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,now);
        newstatements.add(asm);
        replaceFollows(currentBlock,returnBlock);
        // FIXME check and warn if there are remaining statements
    }
    public void visitThrow(JCThrow that)                 { notImpl(that); }
    
    public void visitAssert(JCAssert that) { 
        that.cond.accept(this);
        JCExpression cond = result;
        that.detail.accept(this);
        JCExpression detail = result;
        // FIXME - what to do with detail
        // FIXME - for now turn cond into a JML assertion
        // FIXME - need a label for the assert statement
        // FIXME - set line and source
        JmlStatementExpr assertion = factory.JmlExpressionStatement(JmlToken.ASSERT, Label.EXPLICIT_ASSERT, cond);
        newstatements.add(assertion); 
    }
    
    public void visitApply(JCMethodInvocation that)      { 
        JmlToken token = null;
        if (that.meth instanceof JmlFunction) token = ((JmlFunction)that.meth).token;
        JCExpression now = trExpr(that.meth);
        
        // FIXME - translate typeargs
        
        ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
        boolean changed = now != that.meth;
        for (JCExpression arg: that.args) {
            JCExpression n = trExpr(arg);
            newargs.append(n);
            if (n != arg) changed = true;
        }
        
        if (!(now instanceof JmlFunction)) {
            insertMethodCall(now,newargs.toList());
            return;
        }
            
        if (!changed) { result = that; return; }
        result = factory.Apply(that.typeargs,now,newargs.toList());   
        return;
    }
    
    public void insertMethodCall(JCExpression meth, List<JCExpression> args) {
        if (meth instanceof JCIdent) {
            MethodSymbol sym = (MethodSymbol)((JCIdent)meth).sym;
            JmlMethodSpecs mspecs = specs.getSpecs(sym);
            if (mspecs == null) {
                System.out.println("NO SPECS FOR METHOD CALL");
            } else {
            JmlMethodDecl decl = mspecs.decl;
            int i = 0;
            for (JCVariableDecl vd  : decl.params) {
                Name n = vd.name;
                JCExpression expr = args.get(i++);
                String s = n + "$" + vd.getPreferredPosition();
                JCExpression id = new ProgVarDSA(vd.sym,expr.getStartPosition());
                //setStartEnd(id,expr); // FIXME
                expr = factory.Binary(JCTree.EQ,id,expr);
                JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
                newstatements.add(st);
                
            }
            System.out.println("newstatements-B " + newstatements.size());
            
            boolean isStatic = decl.mods != null && (decl.mods.flags & Flags.STATIC) != 0;
            boolean isConstructor = decl.getReturnType() == null;
            boolean isHelper = isHelper(decl.sym);
            if (!isConstructor && !isHelper) {
                for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssert(Label.INVARIANT,e,newstatements);
                }
                if (!isStatic) {
                    for (JmlTypeClauseExpr inv : classInfo.invariants) {
                        JCExpression e = inv.expression;
                        e = trExpr(e);
                        addAssert(Label.INVARIANT,e,newstatements);
                    }
                }
            }
            if (isConstructor && !isHelper) {
                for (JmlTypeClauseExpr inv : classInfo.initiallys) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssert(Label.PRECONDITION,e,newstatements);
                }
            }
            System.out.println("newstatements-C " + newstatements.size());
            JmlMethodInfo mi = getMethodInfo(decl);
            for (JCExpression pre: mi.requiresPredicates) {
                addAssert(Label.PRECONDITION,pre,newstatements);
            }
            System.out.println("newstatements-D " + newstatements.size());
            
            // FIXME - havoc from modifies
            
            for (JCExpression post: mi.ensuresPredicates) {
                // ensures predicates are already translated
                addAssume(Label.POSTCONDITION,post,newstatements);
            }
            System.out.println("newstatements-E " + newstatements.size());
            if (!isHelper) {
                for (JmlTypeClauseExpr inv : classInfo.staticinvariants) {
                    JCExpression e = inv.expression;
                    e = trExpr(e);
                    addAssume(Label.INVARIANT,e,newstatements);
                }
                if (!isStatic) {
                    for (JmlTypeClauseExpr inv : classInfo.invariants) {
                        JCExpression e = inv.expression;
                        e = trExpr(e);
                        addAssume(Label.INVARIANT,e,newstatements);
                    }
                }
                if (!isConstructor) {
                    for (JmlTypeClauseConstraint inv : classInfo.staticconstraints) {
                        JCExpression e = inv.expression;
                        e = trExpr(e);
                        addAssume(Label.CONSTRAINT,e,newstatements);
                    }
                    if (!isStatic) {
                        for (JmlTypeClauseConstraint inv : classInfo.constraints) {
                            JCExpression e = inv.expression;
                            e = trExpr(e);
                            addAssume(Label.CONSTRAINT,e,newstatements);
                        }
                    }
                }
            }
            System.out.println("newstatements-F " + newstatements.size());
            }
            

        } else if (meth instanceof JCFieldAccess) {
            Log.instance(context).warning("jml.unimplemented.construct","meth.getClass() in insertMethodCall");
            
        } else {
            Log.instance(context).warning("jml.unimplemented.construct","meth.getClass() in insertMethodCall");
        }
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
                String n = "assert$" + that.label + "$" + that.pos;
                JCExpression id = new AuxVarDSA(names.fromString(n),syms.booleanType,expr);
                expr = factory.JmlBinary(JmlToken.EQUIVALENCE,id,expr);
                JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
                newstatements.add(st);
                expr = id;
            }
            if (expr == that.expression && opt == that.optionalExpression)
                now = that;
            else {
                now = factory.JmlExpressionStatement(that.token,that.label,expr);
                now.optionalExpression = opt;
                now.pos = that.pos;
                now.type = that.type;
            }
            currentBlock.statements.add(now);
            if (that.token == JmlToken.ASSUME && (that.label == Label.EXPLICIT_ASSUME 
                    || that.label == Label.BRANCHT || that.label == Label.BRANCHE)) {
                int c = ++assumeCheckCount;
                String n = "assumeCheck$" + that.pos + "$" + that.label.toString();
                JCExpression count = factory.Literal(TypeTags.INT,that.pos);
                JCExpression e = factory.Binary(JCTree.NE,assumeCheckCountVar,count);
                JCExpression id = new AuxVarDSA(names.fromString(n),syms.booleanType,e);
                e = factory.JmlBinary(JmlToken.EQUIVALENCE,id,e);
                JCStatement st = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSUME_CHECK,e);
                newstatements.add(st);
                st = factory.JmlExpressionStatement(JmlToken.ASSERT,Label.ASSUME_CHECK,id);
                newstatements.add(st);
            }

        } else if (that.token == JmlToken.UNREACHABLE) {
            JCExpression expr = factory.Literal(TypeTags.BOOLEAN,Boolean.FALSE);
            now = factory.JmlExpressionStatement(JmlToken.ASSERT,Label.UNREACHABLE,expr);
            now.optionalExpression = null;
            now.pos = that.pos;
            now.type = null; // FIXME - is this what it should be?
            currentBlock.statements.add(now);
        } else {
            // ERROR - FIXME
        }
    }
    public void visitJmlStatementDecls(JmlStatementDecls that)     { notImpl(that); }
    public void visitJmlForLoop(JmlForLoop that)                   { notImpl(that); }
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that)   { notImpl(that); }
    public void visitJmlWhileLoop(JmlWhileLoop that)               { notImpl(that); }
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
    public void visitIndexed(JCArrayAccess that)         { notImpl(that); }
    public void visitSelect(JCFieldAccess that)          { notImpl(that); }
    
    public void visitIdent(JCIdent that)                 { 
        if (that.sym instanceof VarSymbol) {
            result = new ProgVarDSA((VarSymbol)that.sym, that.pos);
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
        // FIXME - fix this if the lhs is complicated
        that.lhs.accept(this);
        JCExpression left = result;
        that.rhs.accept(this);
        JCExpression right = result;
        JCBinary expr = factory.Binary(JCBinary.EQ,left,right);
        expr.type = syms.booleanType;
        expr.pos = that.pos;

        // FIXME - need a label for the assume statement
        // FIXME - set line and source
        JmlStatementExpr assume = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,expr);
        assume.pos = that.pos; // also source and line?  FIXME
        newstatements.add(assume);       
    }
    
    public void visitAssignop(JCAssignOp that) { 
        notImpl(that);
//        that.lhs.accept(this);
//        JCExpression left = result;
//        that.rhs.accept(this);
//        JCExpression right = result;
//        if (left == that.lhs && right == that.rhs) { result = that; return; }
//        JCAssignOp now = factory.Assignop(that.operator.kind,left,right);
//        now.operator = that.operator;
//        now.type = that.type;
//        now.pos = that.pos;
//        result = now;
    }


    // TBD
    public void visitVarDef(JCVariableDecl that)         { 
        if (that.init != null) {
            that.init.accept(this);
            JCExpression lhs = factory.Ident(that.name);
            JCAssign a = factory.Assign(lhs,result); // FIXME - needs position information
            JCExpressionStatement s = factory.Exec(a);
            newstatements.add(s);
        }
    }
    public void visitSynchronized(JCSynchronized that)   { notImpl(that); }
    public void visitNewClass(JCNewClass that)           { notImpl(that); }
    public void visitNewArray(JCNewArray that)           { notImpl(that); }
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
        VarDSA vd = new ProgVarDSA((VarSymbol)(that.sym), that.pos);
        if (that.init != null) {
            that.init.accept(this);
            JCExpression init = result;
//            JCIdent v = factory.Ident(that.name);
//            v.sym = that.sym;
            JmlTree.JmlStatementExpr asm = factory.JmlExpressionStatement(JmlToken.ASSUME,Label.ASSIGNMENT,factory.Binary(JCTree.EQ,vd,init));
            asm.pos = that.init.pos;
            newstatements.add(asm);
            // FIXME - check all new asserts and assumes for location info
        }
    }
    public void visitJmlSingleton(JmlSingleton that) { 
        switch (that.token) {
            case BSRESULT:
                //methodInfo.resultUsed = true;
                result = resultVar;
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
    public void visitJmlLblExpression(JmlLblExpression that)       { notImpl(that); }
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
    public void visitTopLevel(JCCompilationUnit that)    { notImpl(that); }
    public void visitImport(JCImport that)               { notImpl(that); }
    public void visitJmlCompilationUnit(JmlCompilationUnit that)   { notImpl(that); }
    public void visitJmlRefines(JmlRefines that)                   { notImpl(that); }
    public void visitJmlImport(JmlImport that)                     { notImpl(that); }

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
    
    @Override
    public void visitAuxVarDSA(AuxVarDSA that) {
        result = that;
    }

    @Override
    public void visitProgVarDSA(ProgVarDSA that) {
        result = that;
    }


    
    public static class VarFinder extends JmlTreeScanner {
        
        private Set<VarDSA> vars; // FIXME - change to a collection?
        
        public VarFinder() {}
        
        public static Set<VarDSA> findVars(List<? extends JCTree> that, Set<VarDSA> v) {
            VarFinder vf = new VarFinder();
            return vf.find(that,v);
        }
        
        public static Set<VarDSA> findVars(JCTree that, Set<VarDSA> v) {
            VarFinder vf = new VarFinder();
            return vf.find(that,v);
        }
        
        public Set<VarDSA> find(List<? extends JCTree> that, Set<VarDSA> v) {
            if (v == null) vars = new HashSet<VarDSA>();
            else vars = v;
            for (JCTree t: that) t.accept(this);
            return vars;
        }
        
        public Set<VarDSA> find(JCTree that, Set<VarDSA> v) {
            if (v == null) vars = new HashSet<VarDSA>();
            else vars = v;
            that.accept(this);
            return vars;
        }
        
        public void visitIdentifier(JCIdent that) {
            System.out.println("OOPS IDENTIFIER " + that.sym);
            //vars.add((VarSymbol)that.sym);
        }
        public void visitProgVarDSA(ProgVarDSA that) {
            vars.add(that);
        }
        public void visitAuxVarDSA(AuxVarDSA that) {
            vars.add(that);
        }
    }
    
}
