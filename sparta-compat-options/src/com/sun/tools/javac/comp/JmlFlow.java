/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.*;
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

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBreak;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCContinue;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;

/**
 * This extends Flow to add flow checks to specifications.  Flow checks for:<BR>
 * uninitialized variables<BR>
 * assignments to final variables<BR>
 * unreachable statements<BR>
 * forward references<BR>
 * fall-through in cases<BR>
 * improper use of checked exceptions<BR>
 * exception never thrown in try<BR>
 * redundant cast <BR>
 * The JML additions just make sure that ghost fields, model methods and model classes
 * are visited by the flow tree walker.
 *
 * @author David Cok
 */  // FIXME - I think we need to implement the JML visit methods in order to do checks within JML expressions?
// FIXME - these might apply to JML clauses: redundant cast, forward references, uninit variables

public class JmlFlow extends Flow implements IJmlVisitor {

    /** Registers a singleton factory for JmlFlow against the flowKey; the factory
     * produces a singleton (per context) instance of JmlFlow
     * @param context the context in which to register the instance
     */
    public static void preRegister(final Context context) {
        context.put(Flow.flowKey, new Context.Factory<Flow>() {
            Flow instance = null;
            public Flow make(Context context) { 
                if (instance == null) instance = new JmlFlow(context);
                return instance;
            }
        });
    }
        
    /** The compilation context of this instance */
    protected Context context;
    
    /** This is a stack of the declarations occurring in JML quantifier expressions,
     * possible nested (and therefore stacked).
     */
    protected java.util.List<List<JCVariableDecl>> quantDeclStack = new java.util.LinkedList<List<JCVariableDecl>>();
    
    /** A constructor, but use instance() to generate new instances of this class. */
    protected JmlFlow(Context context) {
        super(context);
        this.context = context;
    }
    
    // Instead of overriding visitClassDef (which does a lot of processing), a hook
    // (moreClassDef) was added into the middle of its implementation; this hook does
    // nothing in the base class, but is overridden below to do additional processing.
    /** Overridden to be sure that ghost/model declarations within the class are
     * visited by the flow checker.
     */
    @Override
    public void moreClassDef(JCClassDecl tree) {
        // Do nothing if the class is not attibuted
        if (tree.sym == null) return;
        // Do nothing if the class is already instrumented for RAC
        if (Utils.instance(context).isInstrumented(tree.mods.flags)) return;
        
        // Do nothing if the class has no specs (i.e., is binary)
        JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(tree.sym);
        if (tspecs == null) return;
        
        JavaFileObject prev = Log.instance(context).currentSourceFile();
        try {
            // Do Flow processing on each JML clause of the class declaration
            for (JmlTypeClause c : tspecs.clauses) {
                if (c instanceof JmlTypeClauseDecl) {
                    JCTree d = ((JmlTypeClauseDecl)c).decl;
                    Log.instance(context).useSource(c.source());
                    if (c.modifiers != null && (c.modifiers.flags & Flags.SYNTHETIC) != 0) {
                        continue;
                    }
                    d.accept(this);
                }
            }
        } finally {
            Log.instance(context).useSource(prev);
        }
    }
    
    // FIXME - should the continues statement target be changed? Perhaps when it is attributed?
    // FIXME - do the same for break statements?
    // MAINTENANCE: copied from Flow.resolveContinues
    /** Resolve all continues of this statement. */
    @Override
    boolean resolveContinues(JCTree tree) {
        boolean result = false;
        List<PendingExit> exits = pendingExits.toList();
        pendingExits = new ListBuffer<PendingExit>();
        for (; exits.nonEmpty(); exits = exits.tail) {
            PendingExit exit = exits.head;
            if (exit.tree.getTag() == JCTree.CONTINUE &&
                    ((JCContinue) exit.tree).target == tree) {
                    inits.andSet(exit.inits);
                    uninits.andSet(exit.uninits);
                    result = true;
            } else if (exit.tree.getTag() == JCTree.CONTINUE &&
                    tree instanceof JmlEnhancedForLoop &&
                    ((JCContinue) exit.tree).target == ((JmlEnhancedForLoop)tree).internalForLoop) {
                            inits.andSet(exit.inits);
                            uninits.andSet(exit.uninits);
                            result = true;
            } else {
                pendingExits.append(exit);
            }
        }
        return result;
    }

    /** Resolve all breaks of this statement. */
    @Override
    boolean resolveBreaks(JCTree tree,
                          ListBuffer<PendingExit> oldPendingExits) {
        boolean result = false;
        List<PendingExit> exits = pendingExits.toList();
        pendingExits = oldPendingExits;
        for (; exits.nonEmpty(); exits = exits.tail) {
            PendingExit exit = exits.head;
            if (exit.tree.getTag() == JCTree.BREAK &&
                    ((JCBreak) exit.tree).target == tree) {
                    inits.andSet(exit.inits);
                    uninits.andSet(exit.uninits);
                    result = true;
            } else if (exit.tree.getTag() == JCTree.BREAK &&
                    tree instanceof JmlEnhancedForLoop &&
                    ((JCBreak) exit.tree).target == ((JmlEnhancedForLoop)tree).internalForLoop) {
                            inits.andSet(exit.inits);
                            uninits.andSet(exit.uninits);
                            result = true;
            } else {
                pendingExits.append(exit);
            }
        }
        return result;
    }

    
    //// These are implemented
    
    /** This is overridden in order to handle JML method call-like features (e.g. \typeof) */
    @Override
    public void visitApply(JCMethodInvocation tree) {
        if (tree.meth == null) return;
        if (tree.meth.type == null) {
            // FIXME - need to do this just because we don't have full attribution in trEnhancedForLoop
            scanExpr(tree.meth);
            scanExprs(tree.args);
        } else {
            super.visitApply(tree);
        }
        // Ignore JML functions (FIXME - should we make this a JmlTreeScanner and do lots more checks?)
    }

    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        visitMethodDef(that);
    }

    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        visitApply(that);
    }

    @Override
    public void visitJmlBinary(JmlBinary that) {
        scan(that.lhs);
        scan(that.rhs);
    }
    
    @Override
    public void visitJmlChoose(JmlChoose that) {
        scan(that.orBlocks);
        scan(that.elseBlock);
    }

    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        visitClassDef(that);
    }

    @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        visitTopLevel(that);
    }

    @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        visitDoLoop(that);
    }

    @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        visitForeachLoop(that);
    }

    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        visitForLoop(that);
    }
    

    @Override
    public void visitJmlImport(JmlImport that) {
        visitImport(that);
    }

    @Override
    public void visitJmlSingleton(JmlSingleton that) {
        // nothing to do
    }

    @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        scan(that.expression);
    }

    @Override
    public void visitJmlStatement(JmlStatement that) {
        scan(that.statement);
    }

    @Override
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        for (JCStatement s: that.list) {
            scan(s);
        }
    }

    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        scanExpr(that.expression);
        scanExpr(that.optionalExpression);
    }

    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) {
        scan(that.storerefs);
    }

    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        visitVarDef(that);
    }

    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        visitWhileLoop(that);
    }
    
    @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        // No action to take
    }

    @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        // FIXME - check array dimensions?
    }

    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        quantDeclStack.add(0,that.decls);
        if (that.racexpr != null) {
            scanExpr(that.racexpr);
        } else {
            scanExpr(that.range);
            scanExpr(that.value);
        }
        quantDeclStack.remove(0);
    }
    
    @Override
    public void visitIdent(JCIdent that) {
        for (List<JCVariableDecl> list: quantDeclStack) {
            for (JCVariableDecl decl: list) {
                if (decl.sym.equals(that.sym)) return;
            }
        }
        super.visitIdent(that);
    }

    @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        // FIXME: Skipping set comprehension
    }

    @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        // Is called, but nothing to check
    }

    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        // FIXME: skipping store-ref expressions
        // we could call scanExpr on each expression, but we have to watch for special expressions
    }

    //// These are not implemented

    @Override
    public void visitJmlGroupName(JmlGroupName that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlGroupNameg");
    }

    @Override
    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseCallable");
    }

    @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseConditional");
    }

    @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseDecl");
    }

    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseExpr");
    }

    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseGroup");
    }

    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseSigOnly");
    }

    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseSignals");
    }

    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseStoreRef");
    }

    @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodSpecs");
    }

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlSpecificationCase");
    }

    @Override
    public void visitJmlStatementLoop(JmlStatementLoop that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStatementLoop");
    }

    @Override
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
//        scan(that.expression);
//        scan(that.lo);
//        scan(that.hi);
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStoreRefArrayRange");
    }

    @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseConditional");
    }

    @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseConstraint");
    }

    @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseDecl");
    }

    @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseExpr");
    }

    @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseIn");
    }

    @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseInitializer");
    }

    @Override
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseMaps");
    }

    @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseMonitorsFor");
    }

    @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseRepresents");
    }

    public void visitJmlMethodSig(JmlMethodSig that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlConstraintMethodSig");
    }

    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlModelProgramStatement");
    }
}