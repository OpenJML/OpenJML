package org.jmlspecs.openjml.esc;


import static com.sun.tools.javac.code.TypeTags.CLASS;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.DiagnosticPositionSES;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
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
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCWildcard;
import com.sun.tools.javac.tree.JCTree.LetExpr;
import com.sun.tools.javac.tree.JCTree.TypeBoundKind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

public class JmlAssertionAdder extends JmlTreeScanner {
    
    public Map<String,DiagnosticPositionSES> positionMap = new HashMap<String,DiagnosticPositionSES>();
    
    protected JCMethodDecl methodDecl = null;
    
    protected Context context;
    protected Log log;
    protected JmlSpecs specs;
    final protected JmlTree.Maker M;
    final protected Names names;
    final protected Symtab syms;
    
    final protected JmlExpressionRewriter jmlrewriter = new JmlExpressionRewriter();
    
    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    @NonNull protected JmlTreeUtils treeutils;
    

    final protected String resultString = "RESULT";
    final protected Name resultName;
    protected Symbol resultSym = null;
    static final public String terminationString = "TERMINATION";
    final protected Name terminationName;
    protected Symbol terminationSym = null;

    final protected String tmp = "tmp";

    protected LinkedList<ListBuffer<JCStatement>> statementStack = new LinkedList<ListBuffer<JCStatement>>();
    protected ListBuffer<JCStatement> currentStatements;
    protected int count;
    JCExpression eresult;
    protected boolean esc ; // if false, then translating for rac
    
    public JCBlock convertMethodBody(JCMethodDecl decl) {
        JCMethodDecl prev = methodDecl;
        try {
            this.methodDecl = decl;
            return convert(decl);
        } catch (RuntimeException e) {
            Log.instance(context).error("jml.internal.notsobad",e.getMessage());
            return null;
        } finally {
            methodDecl = prev;
        }
    }
    
    public JmlAssertionAdder(Context context, boolean esc) {
        this.context = context;
        this.esc = esc;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.resultName = names.fromString(resultString);
        this.terminationName = names.fromString(terminationString);
        this.count = 0;
    }
    
    /** The creates the overall framework for the block:
     * <PRE> 
         preconditions
         try {
            method body
         } finally {
            postconditions
         }
        </PRE>
     * <P>
     * The converted method body is a new block with the following characteristics:
     * <UL>
     * <LI>control flow statements are still present: if-then-else, switch
     * <LI>expressions in Java code are decomposed into individual operations, with temporaries. This is so that
     * (a) it is easy to add any assertions prior to a specific operation
     * (b) it is straightforward to handle any operation with side-effects, even in the context of
     * short-circuit operations
     * <LI>assertions are added in for any checks that are desired (see the list below)
     * <LI>specification expressions are not decomposed into individual operations, since all the
     * sub-expressions are supposed to be pure; however, additional assertions are added before any
     * specification expression that checks that the specification expression is well-defined - TODO
     * <LI>conditional and short-circuit expressions (in Java code) are converted into if-then-else statements;
     * again, this is to simplify handling of side-effects in sub-expressions - TODO for short-circuit
     * <LI>all identifiers are made unique by combining the name with location information; but no
     * conversions for single-assignment are performed - TODO
     * </UL>
     * <P>
     * These operations are converted: 
     * <UL>
     * <LI>JML equivalence to boolean =
     * <LI>JML inequivalence to boolean !=
     * <LI>JML reverse implies (p <== q) to (p || !q)
     * <LI>assignments with operations are decomposed into the operation and the assignment
     * </UL>
     * <LI>These operations are retained:
     * <UL>
     * <LI>assignment
     * <LI>integer and floating +, -, *, /
     * <LI>== and !=
     * <LI>comparison operations (integer and floating)
     * </UL>
     * <LI>TODO: mod, integer division, shift operations, bit operations, JML implies, JML subtype,
     * instanceof, short-circuit boolean operations
     * <LI>TODO: handle method calls
     * <LI>TODO: handle method calls in specifications
     * <LI>TODO: new Object, new Array expressions
     * <LI>TODO: quantifier and set comprehension expressions
     * <LI>TODO: \fresh operation
     * <LI>TODO: \nonnullelements
     * </UL>
     * <P>
     * These assumptions and checks are added in:
     * <UL>
     * <LI>assume the method preconditions, including null method parameters
     * <LI>assume any class invariants, including null field declarations
     * <LI>assert the method postconditions
     * <LI>assume any explicit assumption
     * <LI>assert any explicit assertion
     * <LI>assert the method exceptional postconditions - TODO
     * <LI>check for null-dereference on each field access
     * <LI>check for null-dereference on each array access - TODO
     * <LI>check for index out of bounds on each array access - TODO
     * <LI>check for assignment of null to any non-null variable or field
     * <LI>check for out of range arithmetic operations - TODO
     * </UL>
     * 
     * @param decl method being converted
     * @returna JCBlock with all assumptions, assertions, added declarations
     */
    public JCBlock convert(JCMethodDecl decl) {
        ListBuffer<JCStatement> initialStatements = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> outerFinalizeStats = new ListBuffer<JCStatement>();
        if (decl.restype != null && decl.restype.type.tag != TypeTags.VOID) {
            JCVariableDecl d = treeutils.makeVarDef(decl.restype.type,resultName,decl.sym,null);
            resultSym = d.sym;
            initialStatements.add(d);
        }
        JCVariableDecl d = treeutils.makeVarDef(syms.intType,terminationName,decl.sym,null);
        terminationSym = d.sym;
//        initialStatements.add(d);
        
        // Give parameters unique names
        for (JCVariableDecl param : decl.params) {
            Name n = uniqueName(param.sym);
            param.name = n;
        }
        
        addPrePostConditions(decl, initialStatements,outerFinalizeStats);
        ListBuffer<JCStatement> bodyStatements = new ListBuffer<JCStatement>();
        currentStatements = bodyStatements;
        decl.body.accept(this);
        JCBlock b = M.at(decl.body.pos).Block(0, bodyStatements.toList());
        JCTry outerTryStatement = M.Try(b,List.<JCCatch>nil(),
                M.Block(0, outerFinalizeStats.toList()));
        initialStatements.add(outerTryStatement);
        return M.at(decl.pos).Block(0,initialStatements.toList());
    }
    
    protected void push() {
        statementStack.add(0,currentStatements);
        currentStatements = new ListBuffer<JCStatement>();
    }
    
    protected void pop() {
        currentStatements = statementStack.removeFirst();
    }
    
    protected JCBlock popBlock(long flags, int pos) {
        JCBlock b = M.at(pos).Block(flags, currentStatements.toList());
        pop();
        return b;
    }
    
    protected void addStat(JCStatement stat) {
        currentStatements.add(stat);
    }
    
    protected JCVariableDecl makeDeclaration(Name nm, JCExpression vartype, /*@Nullable*/ JCExpression init) {
        return M.VarDef(M.Modifiers(0), nm, vartype, init);
    }
    
    /** This generates a JmlExpressionStatement comment statement with the given string as
     * text; the statement is not added to any statement list
     */
    public JmlStatementExpr comment(int pos, String s) {
        return M.at(pos).JmlExpressionStatement(JmlToken.COMMENT,null,M.Literal(s));
    }
    
    /** This generates a comment statement whose content is the
     * given JCTree, pretty-printed; the statement is not added to any statement list
     */
    public JmlStatementExpr comment(JCTree t) {
        return comment(t.pos,JmlPretty.write(t,false));
    }
    
    public void copyEndPosition(JCTree newnode, JCTree srcnode) {
        Map<JCTree,Integer> z = log.currentSource().getEndPosTable();
        if (z != null && srcnode != null) { // srcnode can be null when processing a switch statement
            int end = srcnode.getEndPosition(z);
            if (end != Position.NOPOS) z.put(newnode, end);
        }
    }

    int precount = 0;
    final String prePrefix = "Pre_";
    final String assertPrefix = "ASSERT_";
    protected int assertCount = 0;
    
    /** Adds an assertion, in which the referenced clause might be in another file */
    public void addAssertOther(JmlMethodClause clause, Label label, JCExpression ex, ListBuffer<JCStatement> stats) {
        DiagnosticSource dsource = log.currentSource();
        log.useSource(clause.sourcefile);
        int end = log.currentSource().getEndPosTable().get(clause);
        DiagnosticPositionSES pos = new DiagnosticPositionSES(clause.getStartPosition(),end,log.currentSource());
        log.useSource(dsource.getFile());
        String assertID = assertPrefix + (++assertCount);
        Name assertname = names.fromString(assertID);
        JCVariableDecl decl = treeutils.makeVarDef(syms.booleanType,assertname,null,ex);
        stats.add(decl);
        stats.add(treeutils.makeAssert(clause.pos,label,treeutils.makeIdent(clause.pos,decl.sym)));
        //positionMap.put(assertID, pos);
    }
    
    /** Adds an assertion - the referenced location is within the text of the file containing the method */ 
    public void addAssert(JCTree location, Label label, JCExpression ex, ListBuffer<JCStatement> stats) {
        int start = location.getStartPosition();
        Integer end = log.currentSource().getEndPosTable().get(location);
        DiagnosticPositionSES pos = new DiagnosticPositionSES(start,end==null?start:end,log.currentSource());
        String assertID = assertPrefix + (++assertCount);
        Name assertname = names.fromString(assertID);
        JCVariableDecl decl = treeutils.makeVarDef(syms.booleanType,assertname,null,ex);
        stats.add(decl);
        stats.add(treeutils.makeAssert(location.pos,label,treeutils.makeIdent(location.pos,decl.sym)));
        //positionMap.put(assertID, pos);
    }
    
    /** Adds an assertion - the referenced location is within the text of the file containing the method */ 
    public void addAssertStart(JCTree location, Label label, JCExpression ex, ListBuffer<JCStatement> stats) {
        int start = location.getStartPosition();
        Integer end = log.currentSource().getEndPosTable().get(location);
        DiagnosticPositionSES pos = new DiagnosticPositionSES(start,end==null?start:end,log.currentSource());
        String assertID = assertPrefix + (++assertCount);
        Name assertname = names.fromString(assertID);
        JCVariableDecl decl = treeutils.makeVarDef(syms.booleanType,assertname,null,ex);
        stats.add(decl);
        stats.add(treeutils.makeAssert(start,label,treeutils.makeIdent(location.pos,decl.sym)));
        //positionMap.put(assertID, pos);
    }
    
    public void addAssumeEqual(int pos, Label label, JCExpression ex, JCExpression exx, ListBuffer<JCStatement> stats) {
        stats.add(treeutils.makeAssume(pos,label,treeutils.makeBinary(pos,JCTree.EQ,ex,exx)));
    }
    
    public void addAssume(int pos, Label label, JCExpression ex, ListBuffer<JCStatement> stats) {
        stats.add(treeutils.makeAssume(pos,label,ex));
    }
    
    Map<Symbol,JCVariableDecl> preparams = new HashMap<Symbol,JCVariableDecl>();
    
    public void addPrePostConditions(JCMethodDecl decl, ListBuffer<JCStatement> initialStats, ListBuffer<JCStatement> ensureStats) {
        currentStatements = initialStats;
        JmlMethodSpecs denestedSpecs = decl.sym == null ? null : JmlSpecs.instance(context).getDenestedSpecs(decl.sym);
        for (JCVariableDecl d: decl.params) {
            if (specs.isNonNull(d.sym, (Symbol.ClassSymbol)d.sym.owner.owner)) { // FIXME - needs to go through jmlrewriter ?
                addAssume(d.pos,Label.NULL_CHECK,treeutils.makeBinary(d.pos,JCTree.NE, treeutils.makeIdent(d.pos, d.sym), treeutils.nulllit), initialStats);
            }
            JCVariableDecl dd = treeutils.makeVariableDecl(M.Name("PRE_"+d.name.toString()), d.type, 
                    M.Ident(d.name), decl.pos);
            preparams.put(d.sym,dd);
            addStat(dd);
        }
        for (JmlSpecificationCase scase : denestedSpecs.cases) {
            JCIdent preident = null;
            JCExpression preexpr = null;
            for (JmlMethodClause clause : scase.clauses) {
                switch (clause.token) {
                    case REQUIRES:
                        currentStatements = initialStats;
                        JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                        ex = jmlrewriter.translate(ex);
                        if (preexpr == null) preexpr = ex;
                        else preexpr = treeutils.makeAnd(ex.pos, preexpr, ex);
                        break;
                    default:
                }
            }
            if (preexpr == null) {
                preexpr = treeutils.trueLit; // FIXME - make a copy
            }
            Name prename = names.fromString(prePrefix + precount);
            JCVariableDecl d = treeutils.makeVarDef(syms.booleanType, prename, decl.sym, preexpr);
            preident = treeutils.makeIdent(preexpr.pos, d.sym);
            initialStats.add(d);
            initialStats.add(treeutils.makeAssume(preexpr.pos,Label.PRECONDITION,preident));

            for (JmlMethodClause clause : scase.clauses) {
                switch (clause.token) {
                    case ENSURES:
                        currentStatements = ensureStats;
                        JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                        ex = jmlrewriter.translate(ex,true);
                        //JCExpression exx = treeutils.makeUnary(clause.pos, JCTree.NOT, preident);
                        ex = treeutils.makeJmlBinary(clause.pos, JmlToken.IMPLIES, preident, ex);
                        // FIXME - if the clause is synthetic, the source file may be null
                        addAssertOther(clause,Label.POSTCONDITION,ex,ensureStats);
                        break;
                        
                    default:
                }
            }
        }
    }

    /** This class holds a summary of specification and other useful data about a method.
     * It is only used during BasicBlock, but it is computed and cached on first request
     * (within the compilation context). The 'computeMethodInfo' call fills in the details.
     */
    static public class JmlMethodInfo {
        /** Creates an unitialized instance from a method declaration */
        public JmlMethodInfo(JCMethodDecl d, Context context) { 
            this.decl = d; 
            this.owner = d.sym; 
            this.source = ((JmlMethodDecl)d).sourcefile;
            findOverrides(owner,context);
        }
        /** Creates an uninitialized instance from a method symbol */
        public JmlMethodInfo(MethodSymbol msym, Context context) { 
            this.decl = null; 
            this.owner = msym; 
            this.source = null;
            findOverrides(owner,context);
        }
        /** The symbol for this method */
        MethodSymbol owner;
        /** The declaration for this method, if there is one */
        /*@Nullable*/ JCMethodDecl decl;
        /** The JmlClassInfo stucture for the containing class */
        JmlClassInfo classInfo;
        /** The file in which the method is declared and implemented */
        JavaFileObject source;
        /** The name used as the result of the method - filled in during translation */
        String resultName;
        /** Whether the result is used - filled in during translation */
        boolean resultUsed = false;
        //FIXME
        JCExpression exceptionDecl;
        VarSymbol exceptionLocal;
        
        /** A list of all the forall predicates */ // FIXME - how interacts with spec cases
        java.util.List<JCVariableDecl> foralls = new LinkedList<JCVariableDecl>();
        /** A list of all the old predicates */ // FIXME - how interacts with spec cases
        ListBuffer<JCVariableDecl> olds = new ListBuffer<JCVariableDecl>();
        /** A list of the one combined requires predicate */ // FIXME - combined across inheritance?
        java.util.List<JmlMethodClauseExpr> requiresPredicates = new LinkedList<JmlMethodClauseExpr>();
        /** A list of desugared ensures predicates (i.e. in the form \old(precondition) ==> postcondition )*/
        java.util.List<JmlMethodClauseExpr> ensuresPredicates = new LinkedList<JmlMethodClauseExpr>();
        /** A list of desugared signals predicates (i.e. in the form \old(precondition) ==> postcondition )*/
        java.util.List<JmlMethodClauseExpr> exPredicates = new LinkedList<JmlMethodClauseExpr>();
        /** A list of desugared signals_only predicates (i.e. in the form \old(precondition) ==> postcondition )*/
        java.util.List<JmlMethodClauseExpr> sigPredicates = new LinkedList<JmlMethodClauseExpr>();
        /** A list of desugared diverges predicates (i.e. in the form \old(precondition) ==> postcondition )*/
        java.util.List<JmlMethodClauseExpr> divergesPredicates = new LinkedList<JmlMethodClauseExpr>();
        
        /** A structure holding information about desugared assignable clauses */
        public static class Entry {
            public Entry(JCExpression pre, java.util.List<JCExpression> list) {
                this.pre = pre;
                this.storerefs = list;
            }
            /** The precondition guarding this list of assignables */ // FIXME - with \old?
            public JCExpression pre;
            /** A list of storerefs for a particular spec case */
            public java.util.List<JCExpression> storerefs;
        }
        
        /** A list of assignable clause information */
        java.util.List<Entry> assignables = new LinkedList<Entry>();
        
        /** A list of overridden methods from super classes */
        java.util.List<MethodSymbol> overrides = new LinkedList<MethodSymbol>();
        
        /** A list of overridden methods from super interfaces */
        java.util.List<MethodSymbol> interfaceOverrides = new LinkedList<MethodSymbol>();
        
        protected void findOverrides(MethodSymbol sym, Context context) {
            MethodSymbol msym = sym;
            Types types = Types.instance(context);
            for (Type t = types.supertype(msym.owner.type); t.tag == CLASS; t = types.supertype(t)) {
                TypeSymbol c = t.tsym;
                Scope.Entry e = c.members().lookup(msym.name);
                while (e.scope != null) {
                    if (msym.overrides(e.sym, (TypeSymbol)msym.owner, types, false)) {
                        msym = (MethodSymbol)e.sym;
                        if (msym != null) overrides.add(msym);
                        break;
                    }
                    e = e.next();
                }
            }
            
        }

    }
    
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
        JmlMethodSpecs denestedSpecs = msym == null ? null : JmlSpecs.instance(context).getDenestedSpecs(msym);
        if (JmlEsc.escdebug) log.noticeWriter.println("SPECS FOR " + msym.owner + " " + msym + " " + (denestedSpecs != null));
        if (JmlEsc.escdebug) log.noticeWriter.println(denestedSpecs == null ? "     No denested Specs" : ("   " + denestedSpecs.toString())); // FIXME - bad indenting

//        List<JCStatement> prev = newstatements;
//        newstatements = new LinkedList<JCStatement>();
//        if (denestedSpecs != null) {
//            // preconditions
//            JCExpression pre = denestedSpecs.cases.size() == 0 ? treeutils.makeBooleanLiteral(mspecs.cases.decl==null?0:mspecs.cases.decl.pos,true) : null;
//            int num = 0;
//            JavaFileObject source = null;
//            for (JmlSpecificationCase spc: denestedSpecs.cases) {
//                treetrans.pushSource(spc.sourcefile);
//                if (source == null) source = spc.sourcefile;
//                
//                for (JmlMethodClause c: spc.clauses) {
//                    if (c.token == JmlToken.FORALL) {
//                        JmlMethodClauseDecl d = (JmlMethodClauseDecl)c;
//                        for (JCVariableDecl stat: d.decls) {
//                            JCVariableDecl newstat = treetrans.translate(stat);
//                            mi.foralls.add(newstat);
//                        }
//                    } else if (c.token == JmlToken.OLD) {
//                        JmlMethodClauseDecl d = (JmlMethodClauseDecl)c;
//                        for (JCVariableDecl stat: d.decls) {
//                            JCVariableDecl newstat = treetrans.translate(stat);
//                            mi.olds.append(newstat);
//                        }
//                    }
//                }
//                JCExpression spre = null;
//                for (JmlMethodClause c: spc.clauses) {
//                    if (c.token == JmlToken.REQUIRES) {
//                        num++;
//                        JCExpression e = treetrans.translate((((JmlMethodClauseExpr)c).expression));
//                        e.pos = c.pos;
//                        copyEndPosition(e,c); // FIXME - these lines should be part of translate
//                        if (spre == null) {
//                            spre = e;
//                        } else {
//                            spre = treeutils.makeBinary(spre.pos,JCTree.AND,spre,e);
//                            copyEndPosition(spre,e);
//                        }
//                    }
//                }
//                if (spre == null) {
//                    spre = treeutils.makeBooleanLiteral(spc.pos,true);
//                    copyEndPosition(spre,spc);
//                }
//                if (pre == null) pre = spre;
//                else {
//                    pre = treeutils.makeBinary(pre.pos,JCTree.BITOR,pre,spre);
//                    copyEndPosition(pre,spre);
//                }
//                treetrans.popSource();
//            }{
//                JmlMethodClauseExpr p = factory.at(pre.pos).JmlMethodClauseExpr(JmlToken.REQUIRES,pre);
//                p.sourcefile = source != null ? source : log.currentSourceFile();
//                if (num == 1) copyEndPosition(p,pre);
//                mi.requiresPredicates.add(p);  // Just one composite precondition for all of the spec cases
//            }
//            
//            // postconditions
//            for (JmlSpecificationCase spc: denestedSpecs.cases) {
//                JCExpression spre = null;
//                for (JmlMethodClause c: spc.clauses) {
//                    if (c.token == JmlToken.REQUIRES) {
//                        if (spre == null) {
//                            JCExpression cexpr = ((JmlMethodClauseExpr)c).expression;
//                            spre = treetrans.translate((cexpr));
//                            copyEndPosition(spre,cexpr); // FIXME _ included in translate?
//                        } else {
//                            int pos = spre.getStartPosition();
//                            JCExpression cexpr = ((JmlMethodClauseExpr)c).expression;
//                            spre = treeutils.makeBinary(pos,JCTree.AND,spre,treetrans.translate((cexpr)));
//                            copyEndPosition(spre,cexpr);
//                        }
//                    }
//                }
//                if (spre == null) {
//                    spre = treeutils.makeBooleanLiteral(Position.NOPOS, true);
//                    // FIXME - fix position?
//                }
//                // FIXME - set startpos for JmlMethodInvocation
//                JCExpression nspre = factory.at(spre.getStartPosition()).JmlMethodInvocation(JmlToken.BSOLD,com.sun.tools.javac.util.List.of(spre));
//                copyEndPosition(nspre,spre);
//                nspre.type = spre.type;
//                spre = nspre;
//                for (JmlMethodClause c: spc.clauses) {
//                    if (c.token == JmlToken.ENSURES) {
//                        JCExpression e = treetrans.translate(((JmlMethodClauseExpr)c).expression);
//                        copyEndPosition(e,((JmlMethodClauseExpr)c).expression); // FIXME - fold into translate
//                        JCExpression post = treeutils.makeJmlBinary(e.getStartPosition(),JmlToken.IMPLIES,spre,e);
//                        copyEndPosition(post,e);// FIXME - fold into translate; wathc out for different source files
//                        JmlMethodClauseExpr p = factory.at(c.pos).JmlMethodClauseExpr(JmlToken.ENSURES,post);
//                        p.sourcefile = c.source();
//                        copyEndPosition(p,c);
//                        int sp1 = post.getStartPosition();
//                        int ep1 = post.getEndPosition(log.currentSource().getEndPosTable());
//                        int sp2 = spre.getStartPosition();
//                        int ep2 = spre.getEndPosition(log.currentSource().getEndPosTable());
//                        int sp3 = e.getStartPosition();
//                        int ep3 = e.getEndPosition(log.currentSource().getEndPosTable());
//                        mi.ensuresPredicates.add(p);
//                    } else if (c.token == JmlToken.ASSIGNABLE) {
//                        JmlMethodClauseStoreRef mod = (JmlMethodClauseStoreRef)c;
//                        // spre is the precondition under which the store-refs are modified
//                        List<JCExpression> list = mod.list; // store-ref expressions
//                        mi.assignables.add(new JmlMethodInfo.Entry(spre,list));
//                    } else if (c.token == JmlToken.SIGNALS) {
//                        // FIXME - what if there is no variable? - is there one already inserted or is it null?
//                        JmlMethodClauseSignals mod = (JmlMethodClauseSignals)c;
//                        JCExpression e = treetrans.translate(mod.expression);
//                        copyEndPosition(e,mod.expression); // FIXME - fold into translate
//                        boolean isFalse = (e instanceof JCLiteral) && ((JCLiteral)e).value.equals(0);
//                        // If vardef is null, then there is no declaration in the signals clause (e.g. it is just false).
//                        // We use the internal \exception token instead; we presume the type is java.lang.Exception 
//                        JCExpression post = treeutils.makeJmlBinary(e.getStartPosition(),JmlToken.IMPLIES,spre,e);
//                        copyEndPosition(post,e);// FIXME - fold into translate; wathc out for different source files
//                        if (!isFalse) {
//                            if (mod.vardef != null) {
//                                JCIdent id = treeutils.makeIdent(mod.vardef.pos,mod.vardef.sym);
//                                e = makeNNInstanceof(id,c.pos, mod.vardef.type, mod.vardef.pos);
//                                post = treeutils.makeJmlBinary(c.pos,JmlToken.IMPLIES,e,post);
//                            } else {
//                                JCExpression id = factory.at(c.pos).JmlSingleton(JmlToken.BSEXCEPTION);
//                                e = makeNNInstanceof(id,c.pos, syms.exceptionType, c.pos);
//                                post = treeutils.makeJmlBinary(c.pos,JmlToken.IMPLIES,e,post);
//                            }
//                            copyEndPosition(post,mod.expression);
//                        }
//                        JmlMethodClauseExpr p = factory.at(c.pos).JmlMethodClauseExpr(JmlToken.SIGNALS,post);
//                        copyEndPosition(p,c);
//                        p.sourcefile = c.source();
//                        // expression is    pre ==> post
//                        // or               (\typeof(exVar) <: ExTYPE) ==> (pre ==> post)
//                        mi.exPredicates.add(p);
//                    } else if (c.token == JmlToken.DIVERGES) {
//                        JCExpression e = treetrans.translate(((JmlMethodClauseExpr)c).expression);
//                        JCExpression post = treeutils.makeJmlBinary(e.getStartPosition(),JmlToken.IMPLIES,spre,e);
//                        JmlMethodClauseExpr p = factory.at(post.pos).JmlMethodClauseExpr(JmlToken.DIVERGES,post);
//                        p.sourcefile = c.source();
//                        mi.divergesPredicates.add(p);
//                    } else if (c.token == JmlToken.SIGNALS_ONLY) {
//                        JCExpression post = makeSignalsOnly((JmlMethodClauseSignalsOnly)c);
//                        JmlMethodClauseExpr p = factory.at(post.pos).JmlMethodClauseExpr(JmlToken.SIGNALS,post);
//                        p.sourcefile = c.source();
//                        mi.sigPredicates.add(p);
//                    }
//                    // FIXME - is signals_only desugared or handled here?
//                    // FIXME - we are ignoring forall old when duration working_space callable accessible measured_by captures
//                }
//            }
//        }
//        newstatements = prev;
        return mi;
    }
    

    // VISITOR METHODS

    @Override
    public void visitTopLevel(JCCompilationUnit that) {
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitImport(JCImport that) {
        // FIXME - can these happen in an anonymous class expression
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitClassDef(JCClassDecl that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());

    }

    @Override
    public void visitMethodDef(JCMethodDecl that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());

    }

    @Override
    public void visitVarDef(JCVariableDecl that) {
        scan(that.init);
        JCExpression init = that.init == null ? null : eresult;
        // FIXME - need to make a unique symbol
        JCVariableDecl stat = M.at(that.pos).VarDef(that.sym,init);
        addStat(stat);
    }

    @Override
    public void visitSkip(JCSkip that) {
        addStat(that); // using the same statement - no copying
                        // Caution - JML statements are subclasses of JCSkip
    }

    @Override
    public void visitBlock(JCBlock that) {
        push();
        scan(that.stats);
        JCBlock block = popBlock(that.flags,that.pos);
        addStat(block);
    }

    @Override
    public void visitDoLoop(JCDoWhileLoop that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitWhileLoop(JCWhileLoop that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitForLoop(JCForLoop that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitForeachLoop(JCEnhancedForLoop that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitLabelled(JCLabeledStatement that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitSwitch(JCSwitch that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitCase(JCCase that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitSynchronized(JCSynchronized that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitTry(JCTry that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitCatch(JCCatch that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitConditional(JCConditional that) {
        that.cond.accept(this);
        JCExpression cond = eresult;
        Name ifname = names.fromString("conditionalResult" + (++count));
        JCVariableDecl vdecl = treeutils.makeVarDef(that.type, ifname, null, null);
        currentStatements.add(vdecl);
        push();
        scan(that.truepart);
        addAssumeEqual(that.truepart.pos, Label.ASSIGNMENT, 
                  treeutils.makeIdent(that.truepart.pos, vdecl.sym), eresult, currentStatements);
        JCBlock trueblock = popBlock(0,that.truepart.pos);
        push();
        scan(that.falsepart);
        addAssumeEqual(that.falsepart.pos, Label.ASSIGNMENT, 
                treeutils.makeIdent(that.falsepart.pos, vdecl.sym), eresult, currentStatements);
        JCStatement stat = M.If(cond, trueblock, popBlock(0,that.falsepart.pos));
        currentStatements.add(stat);
        eresult = treeutils.makeIdent(that.pos, vdecl.sym);
    }

    @Override
    public void visitIf(JCIf that) {
        scan(that.cond);
        JCExpression cond = eresult;
        push();
        scan(that.thenpart);
        JCBlock thenpart = popBlock(0,that.thenpart.pos);
        push();
        scan(that.elsepart);
        JCBlock elsepart = popBlock(0,that.elsepart.pos);
        addStat(M.at(that.pos).If(cond,thenpart,elsepart));
    }

    @Override
    public void visitExec(JCExpressionStatement that) {
        addStat(comment(that));
        scan(that.getExpression());
        JCExpression arg = eresult;
        JCStatement stat = M.at(that.pos).Exec(arg);
        addStat(stat);
    }

    @Override
    public void visitBreak(JCBreak that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitContinue(JCContinue that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitReturn(JCReturn that) {
        JCExpression arg = null;
        JCExpression retValue = that.getExpression();
        if (retValue != null) {
            scan(retValue);
            arg = eresult;
            JCIdent resultid = M.at(that.pos).Ident(resultSym);
            M.at(that.pos);
            JCStatement stat = M.Exec(M.Assign(resultid,arg)); // FIXME - needs position
            addStat(stat);
            arg = resultid;
        }
        JCStatement stat = M.at(that.pos).Return(arg);
        addStat(stat);
    }

    @Override
    public void visitThrow(JCThrow that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitAssert(JCAssert that) {
        // TODO: This automatically converts a Java assert statement to a JML one - is that what we always want?
        addStat(comment(that));
        scan(that.getCondition());
        addAssertStart(that.getCondition(),Label.EXPLICIT_ASSERT,eresult,currentStatements);
        scan(that.getDetail());
    }

    @Override
    public void visitApply(JCMethodInvocation that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitNewClass(JCNewClass that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitNewArray(JCNewArray that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitParens(JCParens that) {
        scan(that.getExpression());
        JCExpression arg = eresult;
        eresult = M.at(that.pos).Parens(arg);
        eresult.setType(that.type);
    }

    @Override
    public void visitAssign(JCAssign that) {
        if (that.lhs instanceof JCIdent) {
            JCIdent id = (JCIdent)that.lhs;
            scan(that.lhs);
            JCExpression lhs = eresult;
            scan(that.rhs);
            JCExpression rhs = eresult;
            if (specs.isNonNull(id.sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(that.pos, rhs, treeutils.nulllit);
                addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e, currentStatements);
            }
            JCExpression assign = treeutils.makeAssign(that.pos,  lhs, rhs);
            addStat(M.Exec(assign));
            eresult = lhs;
            
        } else if (that.lhs instanceof JCFieldAccess) {
            // FIXME - needs a declaration of the new array
            JCFieldAccess fa = (JCFieldAccess)(that.lhs);
            scan(fa.selected);
            JCFieldAccess newfa = M.at(fa.pos).Select(eresult, fa.name);
            newfa.sym = fa.sym;
            newfa.type = fa.type;
            scan(that.rhs);
            JCExpression rhs = eresult;
            if (specs.isNonNull(fa.sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nulllit);
                addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e, currentStatements);
            }
            JCExpression assign = treeutils.makeAssign(that.pos,newfa, rhs);
            eresult = assign;
           
        } else if (that.lhs instanceof JCArrayAccess) {
            JCArrayAccess aa = (JCArrayAccess)(that.lhs);
            scan(aa.indexed);
            scan(aa.index);
            scan(that.rhs);
            System.out.println("NOT IMPLEMENTED");
        } else {
            System.out.println("NOT IMPLEMENTED");
           
        }
        // FIXME - not complete
    }

    @Override
    public void visitAssignop(JCAssignOp that) {
        JCExpression lhs = that.lhs;
        JCExpression rhs = that.rhs;
        int op = that.getTag();
        if (op <= JCTree.BITAND_ASG) op += (JCTree.BITXOR - JCTree.BITXOR_ASG);
        else op += (JCTree.PLUS - JCTree.PLUS_ASG);
        if (lhs instanceof JCIdent) {
            scan(lhs);
            lhs = eresult;
            scan(rhs);
            rhs = eresult;
            scan(treeutils.makeBinary(that.pos,op ,lhs,rhs));
            rhs = eresult;
            if (specs.isNonNull(((JCIdent)lhs).sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(that.pos, rhs, treeutils.nulllit);
                addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e, currentStatements);
            }
            addStat(M.Exec(treeutils.makeAssign(that.pos, lhs, rhs)));
            eresult = lhs;
        } else if (lhs instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)lhs;
            scan(fa.selected);
            lhs = eresult;
            scan(rhs);
            rhs = eresult;
            if (specs.isNonNull(fa.sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nulllit);
                addAssert(that, Label.POSSIBLY_NULL_ASSIGNMENT, e, currentStatements);
            }
            lhs = M.at(fa.pos).Select(lhs, fa.sym);
            lhs.type = fa.type;
            eresult = treeutils.makeAssign(that.pos, lhs, 
                    treeutils.makeBinary(that.pos,op ,lhs,rhs));
        } else if (lhs instanceof JCArrayAccess) {
            JCArrayAccess aa = (JCArrayAccess)lhs;
            scan(aa.indexed);
            lhs = eresult;
            scan(aa.index);
            JCExpression index = eresult;
            scan(rhs);
            rhs = eresult;
            lhs = M.at(aa.pos).Indexed(lhs, index);
            lhs.type = aa.type;
            // FIXME - add checks
            eresult = treeutils.makeAssign(that.pos, lhs, 
                    treeutils.makeBinary(that.pos,op ,lhs,rhs));
        } else {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }
    }

    @Override
    public void visitUnary(JCUnary that) {
        scan(that.getExpression());
        JCExpression arg = eresult;
        JCExpression expr = M.at(that.pos).Unary(that.getTag(),arg);
        expr.setType(that.type);
        Name n = M.Name(tmp + (++count));
        JCVariableDecl d = M.VarDef(M.Modifiers(0), n, M.Type(that.type), expr);
        currentStatements.add(d);
        eresult = M.at(that.pos).Ident(n);
        eresult.setType(that.type);
        // FIXME - check arithmetic error
    }

    @Override
    public void visitBinary(JCBinary that) {
        scan(that.lhs);
        JCExpression lhs = eresult;
        scan(that.rhs);
        JCExpression rhs = eresult;
        if (that.getTag() == JCTree.DIV) {
            JCExpression nonzero = treeutils.makeBinary(that.pos, JCTree.NE, rhs, treeutils.makeIntLiteral(that.rhs.pos, 0));
            addAssert(that,Label.POSSIBLY_DIV0,nonzero,currentStatements);
        }
        // FIXME - add checks for numeric overflow
        JCExpression bin = M.at(that.pos).Binary(that.getTag(),lhs,rhs);
        bin.setType(that.type);
        Name n = M.Name(tmp + (++count));
        JCVariableDecl d = M.VarDef(M.Modifiers(0), n, M.Type(that.type), bin);
        currentStatements.add(d);
        eresult = M.at(that.pos).Ident(n);
        eresult.setType(that.type);
        
        // FIXME - do this differently for short-circuit operations
    }

    @Override
    public void visitTypeCast(JCTypeCast that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitTypeTest(JCInstanceOf that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitIndexed(JCArrayAccess that) {
        scan(that.indexed);
        JCExpression indexed = eresult;
        JCExpression nonnull = treeutils.makeBinary(that.indexed.pos, JCTree.NE, indexed, 
                treeutils.nulllit);
        addAssert(that,Label.POSSIBLY_NULL,nonnull,currentStatements);

        scan(that.index);
        JCExpression index = eresult;
        JCExpression compare = treeutils.makeBinary(that.index.pos, JCTree.LE, treeutils.zero, 
                index);
        addAssert(that,Label.POSSIBLY_NEGATIVEINDEX,compare,currentStatements);
        JCExpression length = treeutils.makeLength(that.indexed.pos,indexed);
        compare = treeutils.makeBinary(that.pos, JCTree.LT, index, 
                length);
        addAssert(that,Label.POSSIBLY_TOOLARGEINDEX,compare,currentStatements);

        JCArrayAccess aa = M.at(that.pos).Indexed(indexed,index);
        aa.setType(that.type);
        Name n = M.Name(tmp + (++count));
        JCVariableDecl d = M.VarDef(M.Modifiers(0), n, M.Type(that.type), aa);
        currentStatements.add(d);
        eresult = M.at(that.pos).Ident(n);
        eresult.setType(that.type);
    }

    @Override
    public void visitSelect(JCFieldAccess that) {
        scan(that.selected);
        JCExpression selected = eresult;
        // Check that the selected expression is not null
        JCExpression nonnull = treeutils.makeNeqObject(that.pos, selected, 
                treeutils.nulllit);
        addAssert(that,Label.POSSIBLY_NULL,nonnull,currentStatements);
        JCFieldAccess fa = M.at(that.pos).Select(selected,that.name);
        fa.sym = that.sym;
        fa.setType(that.type);
        Name n = M.Name(tmp + (++count));
        JCVariableDecl d = M.VarDef(M.Modifiers(0), n, M.Type(that.type), fa); // FIXME - should this have a syumbol? use treeutils?
        currentStatements.add(d);
        eresult = M.at(that.pos).Ident(n);
        eresult.setType(that.type);
    }
    
    Map<Symbol,Name> newnames = new HashMap<Symbol,Name>();

    public Name uniqueName(Symbol sym) {
        Name n = newnames.get(sym);
        if (n == null) {
            String s = sym.name.toString();// + "__" + (++count); // FIXME - Temporarily just use the same name, but will need to fix this
            n = names.fromString(s);
            newnames.put(sym,n);
        }
        return n;
    }
    @Override
    public void visitIdent(JCIdent that) {
        JCIdent id = treeutils.makeIdent(that.pos,that.sym);
        Name n = uniqueName(that.sym);
        id.name = n;
        eresult = id;
    }

    @Override
    public void visitLiteral(JCLiteral that) {
        eresult = treeutils.makeDuplicateLiteral(that.pos, that);
    }

    @Override
    public void visitTypeIdent(JCPrimitiveTypeTree that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitTypeArray(JCArrayTypeTree that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitTypeApply(JCTypeApply that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitTypeParameter(JCTypeParameter that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitWildcard(JCWildcard that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitTypeBoundKind(TypeBoundKind that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitAnnotation(JCAnnotation that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitModifiers(JCModifiers that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitErroneous(JCErroneous that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitLetExpr(LetExpr that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlBinary(JmlBinary that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlChoose(JmlChoose that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlGroupName(JmlGroupName that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlImport(JmlImport that) {
        // TODO Auto-generated method stub
        // FIXME - can this occur in an anonymous expression
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlSingleton(JmlSingleton that) {
        switch (that.token) {
            case BSRESULT:
                if (resultSym == null) {
                    throw new RuntimeException(); // FIXME - do something more informative - should not ever get here
                } else {
                    eresult = treeutils.makeIdent(that.pos, resultSym);
                }
                break;

            case INFORMAL_COMMENT:
                eresult = treeutils.makeBooleanLiteral(that.pos,true);
                break;
                
//            case BSEXCEPTION:
//                if (exceptionVar == null) {
//                    // FIXME -error
//                    log.noticeWriter.println("EXCEPTION VAR IS NULL");
//                    result = null;
//                } else {
//                    result = newIdentUse((VarSymbol)exceptionVar.sym,that.pos);
//                }
//                break;
//
//            case BSINDEX:
//            case BSVALUES:
//                if (that.info == null) {
//                    log.error(that.pos,"esc.internal.error","No loop index found for this use of " + that.token.internedName());
//                    result = null;
//                } else {
//                    result = newIdentUse((VarSymbol)that.info,that.pos);
//                }
//                break;
//                
//            case BSLOCKSET:
//            case BSSAME:
//            case BSNOTSPECIFIED:
//            case BSNOTHING:
//            case BSEVERYTHING:
//                Log.instance(context).error(that.pos, "jml.unimplemented.construct",that.token.internedName(),"BasicBlocker.visitJmlSingleton");
//                // FIXME - recovery possible?
//                break;

            default:
                Log.instance(context).error(that.pos, "jml.unknown.construct",that.token.internedName(),"BasicBlocker.visitJmlSingleton");
            // FIXME - recovery possible?
                break;
        }
        //result = that; // TODO - can all of these be present in a basic block?
        //toLogicalForm.put(that,result);
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


    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlStatement(JmlStatement that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        switch (that.token) {
            case ASSERT:
                addStat(comment(that));
                JCExpression e = jmlrewriter.translate(that.expression);
                addAssertStart(that,Label.EXPLICIT_ASSERT,e,currentStatements);
                break;
            case ASSUME:
                addStat(comment(that));
                JCExpression ee = jmlrewriter.translate(that.expression);
                addAssume(that.expression.pos,Label.EXPLICIT_ASSUME,ee,currentStatements);
                break;
            case COMMENT:
                addStat(that);
                break;
            default:
                log.error("jml.internal","Unknown token type in JmlAssertionAdder.visitJmlStatementExpr: " + that.token.internedName());
                break;
        }
    }

    @Override
    public void visitJmlStatementLoop(JmlStatementLoop that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        scan(that.init);
        JCExpression init = that.init == null ? null : eresult;
        // FIXME - need to make a unique symbol
        JmlVariableDecl stat = M.at(that.pos).VarDef(that.sym,init);
        addStat(stat);
    }

    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        // TODO Auto-generated method stub
        throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }
    
    /** This class rewrites (making a full copy) JML expressions (but not Java statements and expressions).
     * Since JML expressions are pure (at least have no visible side-effects), we do not dismember expressions
     * into individual subexpressions as we do for expressions in Java statements. However, we do issue 
     * JML assert statements that check whether the JML expression being translated is well-defined; also
     * identifiers are changed in the same as as they are changed for Java expressions.
     * <P>
     * This class is purposely not static, so it can use the context of the enclosing Java rewriter.
     */
    // TODO - this expression rewriter would be better off with a visitor that returned a value from the visit/scan/accept methods
    public class JmlExpressionRewriter extends JmlTreeScanner {
        
        JCExpression condition;
        boolean isPostcondition;
        JCExpression ejmlresult;
        
        JCExpression translate(JCExpression that, boolean isPostcondition) {
            this.isPostcondition = isPostcondition;
            this.condition = treeutils.trueLit;
            this.ejmlresult = null; // Just so it is initialized in case assignment is forgotten
            that.accept(this);
            return ejmlresult;
        }
        
        JCExpression translate(JCExpression that) {
            this.isPostcondition = false;
            this.condition = treeutils.trueLit;
            this.ejmlresult = null; // Just so it is initialized in case assignment is forgotten
            that.accept(this);
            return ejmlresult;
        }

        // VISITOR METHODS

        @Override
        public void visitTopLevel(JCCompilationUnit that) {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitImport(JCImport that) {
            // FIXME - can these happen in an anonymous class expression
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitClassDef(JCClassDecl that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());

        }

        @Override
        public void visitMethodDef(JCMethodDecl that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());

        }

        @Override
        public void visitVarDef(JCVariableDecl that) {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//            scan(that.init);
//            JCExpression init = that.init == null ? null : eresult;
//            // FIXME - need to make a unique symbol
//            JCVariableDecl stat = M.at(that.pos).VarDef(that.sym,init);
//            addStat(stat);
        }

        @Override
        public void visitSkip(JCSkip that) {
            //addStat(that); // using the same statement - no copying
                            // Caution - JML statements are subclasses of JCSkip
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitBlock(JCBlock that) {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//            push();
//            scan(that.stats);
//            JCBlock block = popBlock(that.flags,that.pos);
//            addStat(block);
        }

        @Override
        public void visitDoLoop(JCDoWhileLoop that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitWhileLoop(JCWhileLoop that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitForLoop(JCForLoop that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitForeachLoop(JCEnhancedForLoop that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitLabelled(JCLabeledStatement that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitSwitch(JCSwitch that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitCase(JCCase that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitSynchronized(JCSynchronized that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitTry(JCTry that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitCatch(JCCatch that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitConditional(JCConditional that) {
            that.cond.accept(this);
            JCExpression cond = ejmlresult;
            JCExpression prev = condition;
            try {
                condition = treeutils.makeAnd(that.pos, prev, cond);
                that.truepart.accept(this);
                JCExpression truepart = ejmlresult;
                condition = treeutils.makeAnd(that.pos, prev, treeutils.makeNot(that.falsepart.pos, cond));
                that.falsepart.accept(this);
                JCExpression falsepart = ejmlresult;
                ejmlresult = M.at(that.pos).Conditional(cond,truepart,falsepart);
            } finally {
                condition = prev;
            }
        }

        @Override
        public void visitIf(JCIf that) {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//            scan(that.cond);
//            JCExpression cond = ejmlresult;
//            push();
//            scan(that.thenpart);
//            JCBlock thenpart = popBlock(0,that.thenpart.pos);
//            push();
//            scan(that.elsepart);
//            JCBlock elsepart = popBlock(0,that.elsepart.pos);
//            addStat(M.at(that.pos).If(cond,thenpart,elsepart));
        }

        @Override
        public void visitExec(JCExpressionStatement that) {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//           addStat(comment(that));
//            scan(that.getExpression());
//            JCExpression arg = ejmlresult;
//            JCStatement stat = M.at(that.pos).Exec(arg);
//            addStat(stat);
        }

        @Override
        public void visitBreak(JCBreak that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitContinue(JCContinue that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitReturn(JCReturn that) {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//            JCExpression retValue = that.getExpression();
//            JCExpression arg = null;
//            if (retValue != null) {
//                scan(retValue);
//                arg = ejmlresult;
//            }
//            if (esc) {
//                M.at(that.pos);
////                JCStatement stat = M.JmlExpressionStatement(JmlToken.ASSUME,Label.RETURN,
////                        M.Binary(JCTree.EQ,M.Ident(terminationSym),M.Literal(that.pos)));
////                addStat(stat);
//                if (arg != null) {
//                    JCStatement stat = M.JmlExpressionStatement(JmlToken.ASSUME,Label.RETURN,
//                            M.Binary(JCTree.EQ,M.Ident(resultName),arg));
//                    addStat(stat);
//                }
//            } else {
//                if (retValue != null) {
//                    M.at(that.pos);
//                    arg = M.Assign(M.Ident(resultName), arg);
//                }
//            }
//            JCStatement stat = M.at(that.pos).Return(arg);
//            addStat(stat);
        }

        @Override
        public void visitThrow(JCThrow that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitAssert(JCAssert that) {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//            // TODO: This automatically converts a Java assert statement to a JML one - is that what we always want?
//            addStat(comment(that));
//            scan(that.getCondition());
//            addAssertStart(that.getCondition(),Label.EXPLICIT_ASSERT,ejmlresult,currentStatements);
//            scan(that.getDetail());
        }

        @Override
        public void visitApply(JCMethodInvocation that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitNewClass(JCNewClass that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitNewArray(JCNewArray that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitParens(JCParens that) {
            scan(that.getExpression());
            ejmlresult = M.at(that.pos).Parens(ejmlresult);
            ejmlresult.setType(that.type);
        }

        @Override
        public void visitAssign(JCAssign that) {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitAssignop(JCAssignOp that) {
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitUnary(JCUnary that) {
            scan(that.getExpression());
            JCExpression arg = ejmlresult;
            JCExpression expr = treeutils.makeUnary(that.pos,that.getTag(),arg);
            ejmlresult = expr;
            // FIXME - check arithmetic error
        }

        @Override
        public void visitBinary(JCBinary that) {
            scan(that.lhs);
            JCExpression lhs = ejmlresult;
            JCExpression rhs;
            int tag = that.getTag();
            if (tag == JCTree.AND) {
                JCExpression prev = condition;
                try {
                    condition = treeutils.makeAnd(that.lhs.pos, condition, lhs);
                    scan(that.rhs);
                    rhs = ejmlresult;
                } finally {
                    condition = prev;
                }
            } else if (tag == JCTree.OR) { 
                JCExpression prev = condition;
                try {
                    condition = treeutils.makeAnd(that.lhs.pos, condition, treeutils.makeNot(that.lhs.pos,lhs));
                    scan(that.rhs);
                    rhs = ejmlresult;
                } finally {
                    condition = prev;
                }
            } else if (tag == JCTree.DIV) {
                scan(that.rhs);
                rhs = ejmlresult;
                JCExpression nonzero = treeutils.makeBinary(that.pos, JCTree.NE, rhs, treeutils.makeIntLiteral(that.rhs.pos, 0));
                addAssert(that,Label.UNDEFINED_DIV0,treeutils.makeImplies(that.pos, condition, nonzero),currentStatements);
            } else {
                scan(that.rhs);
                rhs = ejmlresult;
            }
            // FIXME - add checks for numeric overflow
            // FIXME - change condition for short-circuit ops
            JCExpression bin = treeutils.makeBinary(that.pos,that.getTag(),lhs,rhs);
            ejmlresult = bin;
            
        }

        @Override
        public void visitTypeCast(JCTypeCast that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitTypeTest(JCInstanceOf that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitIndexed(JCArrayAccess that) {
            scan(that.indexed);
            JCExpression indexed = ejmlresult;
            JCExpression nonnull = treeutils.makeBinary(that.indexed.pos, JCTree.NE, indexed, 
                    treeutils.nulllit);
            nonnull = treeutils.makeAnd(that.pos, condition, nonnull);
            addAssert(that,Label.UNDEFINED_NULL,nonnull,currentStatements);

            scan(that.index);
            JCExpression index = ejmlresult;
            JCExpression compare = treeutils.makeBinary(that.index.pos, JCTree.LE, treeutils.zero, 
                    index);
            compare = treeutils.makeAnd(that.pos, condition, compare);
            addAssert(that,Label.UNDEFINED_NEGATIVEINDEX,compare,currentStatements);
            
            JCExpression length = treeutils.makeLength(that.indexed.pos,indexed);
            compare = treeutils.makeBinary(that.pos, JCTree.LT, index, 
                    length);
            compare = treeutils.makeAnd(that.pos, condition, compare);
            addAssert(that,Label.UNDEFINED_TOOLARGEINDEX,compare,currentStatements);

            JCArrayAccess aa = M.at(that.pos).Indexed(indexed,index);
            aa.setType(that.type);
            ejmlresult = aa;
        }

        @Override
        public void visitSelect(JCFieldAccess that) {
            scan(that.selected);
            JCExpression selected = ejmlresult;
            // Check that the selected expression is not null
            JCExpression nonnull = treeutils.makeNeqObject(that.pos, selected, 
                    treeutils.nulllit);
            nonnull = treeutils.makeAnd(that.pos, condition, nonnull);
            addAssert(that,Label.UNDEFINED_NULL,nonnull,currentStatements);
            
            JCFieldAccess fa = M.at(that.pos).Select(selected,that.name);
            fa.sym = that.sym;
            fa.setType(that.type);
            
            ejmlresult = fa;
        }
        
        @Override
        public void visitIdent(JCIdent that) {
            JCVariableDecl decl;
            if (isPostcondition && (decl=preparams.get(that.sym)) != null) {
                JCIdent id = treeutils.makeIdent(that.pos,decl.sym);
                ejmlresult = id;            
            } else {
                JCIdent id = treeutils.makeIdent(that.pos,that.sym);
                Name n = uniqueName(that.sym);
                id.name = n;
                ejmlresult = id;
            }
        }

        @Override
        public void visitLiteral(JCLiteral that) {
            // Note that that.typetag can be different from that.type.tag - e.g for null values
            ejmlresult = treeutils.makeDuplicateLiteral(that.pos, that);
        }

        @Override
        public void visitTypeIdent(JCPrimitiveTypeTree that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitTypeArray(JCArrayTypeTree that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitTypeApply(JCTypeApply that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitTypeParameter(JCTypeParameter that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitWildcard(JCWildcard that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitTypeBoundKind(TypeBoundKind that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitAnnotation(JCAnnotation that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitModifiers(JCModifiers that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitErroneous(JCErroneous that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitLetExpr(LetExpr that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlBinary(JmlBinary that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlChoose(JmlChoose that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlClassDecl(JmlClassDecl that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlCompilationUnit(JmlCompilationUnit that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlForLoop(JmlForLoop that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlGroupName(JmlGroupName that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlImport(JmlImport that) {
            // TODO Auto-generated method stub
            // FIXME - can this occur in an anonymous expression
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlLblExpression(JmlLblExpression that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodDecl(JmlMethodDecl that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlMethodSpecs(JmlMethodSpecs that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlSetComprehension(JmlSetComprehension that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlSingleton(JmlSingleton that) {
            switch (that.token) {
                case BSRESULT:
                    if (resultSym == null) {
                        throw new RuntimeException(); // FIXME - do something more informative - should not ever get here
                    } else {
                        ejmlresult = treeutils.makeIdent(that.pos, resultSym);
                    }
                    break;

                case INFORMAL_COMMENT:
                    ejmlresult = treeutils.makeBooleanLiteral(that.pos,true);
                    break;
                    
//                case BSEXCEPTION:
//                    if (exceptionVar == null) {
//                        // FIXME -error
//                        log.noticeWriter.println("EXCEPTION VAR IS NULL");
//                        result = null;
//                    } else {
//                        result = newIdentUse((VarSymbol)exceptionVar.sym,that.pos);
//                    }
//                    break;
    //
//                case BSINDEX:
//                case BSVALUES:
//                    if (that.info == null) {
//                        log.error(that.pos,"esc.internal.error","No loop index found for this use of " + that.token.internedName());
//                        result = null;
//                    } else {
//                        result = newIdentUse((VarSymbol)that.info,that.pos);
//                    }
//                    break;
//                    
//                case BSLOCKSET:
//                case BSSAME:
//                case BSNOTSPECIFIED:
//                case BSNOTHING:
//                case BSEVERYTHING:
//                    Log.instance(context).error(that.pos, "jml.unimplemented.construct",that.token.internedName(),"BasicBlocker.visitJmlSingleton");
//                    // FIXME - recovery possible?
//                    break;

                default:
                    Log.instance(context).error(that.pos, "jml.unknown.construct",that.token.internedName(),"BasicBlocker.visitJmlSingleton");
                // FIXME - recovery possible?
                    break;
            }
            //result = that; // TODO - can all of these be present in a basic block?
            //toLogicalForm.put(that,result);
        }
        
//        public void visitJmlFunction(JmlFunction that) {
//            switch (that.token) {
//                case BSOLD :
//                case BSPRE :
//                    // Handling of incarnation occurs later
//                    result = that; 
//                    break;
//                    
//                case BSTYPEOF :
//                case BSELEMTYPE :
//                case BSNONNULLELEMENTS :
//                case BSMAX :
//                case BSFRESH :
//                case BSREACH :
//                case BSSPACE :
//                case BSWORKINGSPACE :
//                case BSDURATION :
//                case BSISINITIALIZED :
//                case BSINVARIANTFOR :
//                case BSNOWARN:
//                case BSNOWARNOP:
//                case BSWARN:
//                case BSWARNOP:
//                case BSBIGINT_MATH:
//                case BSSAFEMATH:
//                case BSJAVAMATH:
//                case BSNOTMODIFIED:
//                case BSTYPELC:
//                    Log.instance(context).error("esc.not.implemented","Not yet implemented token in BasicBlocker: " + that.token.internedName());
//                    result = trueLiteral; // FIXME - may not even be a boolean typed result
//                    break;
    //
//                default:
//                    Log.instance(context).error("esc.internal.error","Unknown token in BasicBlocker: " + that.token.internedName());
//                    result = trueLiteral; // FIXME - may not even be a boolean typed result
//            }
//        }


        @Override
        public void visitJmlSpecificationCase(JmlSpecificationCase that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlStatement(JmlStatement that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlStatementDecls(JmlStatementDecls that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlStatementExpr(JmlStatementExpr that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//            switch (that.token) {
//                case ASSERT:
//                    addStat(comment(that));
//                    scan(that.expression);
//                    addAssertStart(that,Label.EXPLICIT_ASSERT,ejmlresult,currentStatements);
//                    break;
//                case ASSUME:
//                    addStat(comment(that));
//                    scan(that.expression);
//                    addAssume(that.expression.pos,Label.EXPLICIT_ASSUME,ejmlresult,currentStatements);
//                    break;
//                case COMMENT:
//                    addStat(that);
//                    break;
//                default:
//                    log.error("jml.internal","Unknown token type in JmlAssertionAdder.visitJmlStatementExpr: " + that.token.internedName());
//                    break;
//            }
        }

        @Override
        public void visitJmlStatementLoop(JmlStatementLoop that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlStatementSpec(JmlStatementSpec that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

        @Override
        public void visitJmlVariableDecl(JmlVariableDecl that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//            scan(that.init);
//            JCExpression init = that.init == null ? null : ejmlresult;
//            // FIXME - need to make a unique symbol
//            JmlVariableDecl stat = M.at(that.pos).VarDef(that.sym,init);
//            addStat(stat);
        }

        @Override
        public void visitJmlWhileLoop(JmlWhileLoop that) {
            // TODO Auto-generated method stub
            throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
        }

    }
}
