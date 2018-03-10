/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.TreeMaker;
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

public class JmlFlow extends Flow  {

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
    
    
    /** A constructor, but use instance() to generate new instances of this class. */
    protected JmlFlow(Context context) {
        super(context);
        this.context = context;
    }
    
    class JmlAliveAnalyzer extends AliveAnalyzer implements IJmlVisitor {
        
        /** This is a stack of the declarations occurring in JML quantifier expressions,
         * possible nested (and therefore stacked).
         */
        protected java.util.List<List<JCVariableDecl>> quantDeclStack = new java.util.LinkedList<List<JCVariableDecl>>();
       
      
        //// These are implemented
        
        /** This is overridden in order to handle JML method call-like features (e.g. \typeof) */
        @Override
        public void visitApply(JCMethodInvocation tree) {
                super.visitApply(tree);
        }

        @Override
        public void visitJmlMethodDecl(JmlMethodDecl that) {
            JavaFileObject prev = Log.instance(context).useSource(that.sourcefile);
            try {
                visitMethodDef(that);
            } finally {
                Log.instance(context).useSource(prev);
            }
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
        public void visitJmlBlock(JmlBlock that) {
            scan(that.stats);
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
        public void visitJmlLabeledStatement(JmlLabeledStatement that) {
//            scan(that.extraStatements.toList());
            scan(that.body);
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
        public void visitJmlStatementShow(JmlStatementShow that) {
            scan(that.expressions);
        }

        @Override
        public void visitJmlStatementDecls(JmlStatementDecls that) {
            for (JCStatement s: that.list) {
                scan(s);
            }
        }

        @Override
        public void visitJmlStatementExpr(JmlStatementExpr that) {
            // nothing to do for this checker
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
        public void visitJmlInlinedLoop(JmlInlinedLoop that) {
            // FIXME - do nothing?
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
            // nothing to do for this checker
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
            // No need to scan the specs
            if (that.statements != null) {
                scan(that.statements);
            }
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
        public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStatementLoop");
        }

        @Override
        public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStatementLoop");
        }

        @Override
        public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
//            scan(that.expression);
//            scan(that.lo);
//            scan(that.hi);
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStoreRefArrayRange");
        }

        @Override
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseConditional");
        }

        @Override
        public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseConstraint");
        }

        @Override
        public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseDecl");
        }

        @Override
        public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseExpr");
        }

        // FIXME - ignoring many calls that used to be errors. This has not been thought through -- e.g. why
        // the errors started appearing and if any checks ought to be performed.
        
        @Override
        public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseIn");
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
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseMonitorsFor");
        }

        @Override
        public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
            // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseRepresents");
        }

        public void visitJmlMethodSig(JmlMethodSig that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlConstraintMethodSig");
        }

        public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlModelProgramStatement");
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

            // All of these are added to the main AST
//            JavaFileObject prev = Log.instance(context).currentSourceFile();
//            try {
//                // Do Flow processing on each JML clause of the class declaration
//                for (JmlTypeClauseDecl c : tspecs.decls) {
//                        JCTree d = c.decl;
//                        Log.instance(context).useSource(c.source());
//                        if (c.modifiers != null && (c.modifiers.flags & Flags.SYNTHETIC) != 0) {
//                            continue;
//                        }
//                        d.accept(this);
//                }
//            } finally {
//                Log.instance(context).useSource(prev);
//            }
        }
        
        @Override
        protected boolean resolveJump(JCTree tree,
                        ListBuffer<PendingExit> oldPendingExits,
                        JumpKind jk) {
            boolean resolved = false;
            List<PendingExit> exits = pendingExits.toList();
            pendingExits = oldPendingExits;
            for (; exits.nonEmpty(); exits = exits.tail) {
                PendingExit exit = exits.head;
                if (exit.tree.hasTag(jk.treeTag) &&
                        jk.getTarget(exit.tree) == tree) {
                    exit.resolveJump();
                    resolved = true;
                } else if(exit.tree.hasTag(jk.treeTag) &&
                        jk.getTarget(exit.tree) == tree && tree instanceof JmlEnhancedForLoop && // JLS -- adapted to fit JDK8 programming style
                        jk.getTarget(exit.tree) == ((JmlEnhancedForLoop)tree).internalForLoop){
                    exit.resolveJump();
                    resolved = true;
                }
                
                else {
                    pendingExits.append(exit);
                }
            }
            return resolved;
        }

        /** Resolve all continues of this statement. */
        boolean resolveContinues(JCTree tree) {
            return resolveJump(tree, new ListBuffer<PendingExit>(), JumpKind.CONTINUE);
        }

        /** Resolve all breaks of this statement. */
        boolean resolveBreaks(JCTree tree, ListBuffer<PendingExit> oldPendingExits) {
            return resolveJump(tree, oldPendingExits, JumpKind.BREAK);
        }

        
        
    }
    
    class JmlAssignAnalyzer extends AssignAnalyzer implements IJmlVisitor {
        
        /** This is a stack of the declarations occurring in JML quantifier expressions,
         * possible nested (and therefore stacked).
         */
        protected java.util.List<List<JCVariableDecl>> quantDeclStack = new java.util.LinkedList<List<JCVariableDecl>>();
       
        
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
        public void visitJmlBlock(JmlBlock that) {
            scan(that.stats);
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

        public void visitJmlLabeledStatement(JmlLabeledStatement that) {
//            scan(that.extraStatements.toList());
            scan(that.body);
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
        public void visitJmlStatementShow(JmlStatementShow that) {
            scan(that.expressions);
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
        public void visitJmlInlinedLoop(JmlInlinedLoop that) {
            // No action to take
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
            // No need to scxan specs
            if (that.statements != null) {
                scan(that.statements);
            }
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
        public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStatementLoop");
        }

        @Override
        public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStatementLoop");
        }

        @Override
        public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
//            scan(that.expression);
//            scan(that.lo);
//            scan(that.hi);
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
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseExpr");
        }

        @Override
        public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseIn");
        }

        @Override
        public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseInitializer");
        }

        @Override
        public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseMaps");
        }

        @Override
        public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseMonitorsFor");
        }

        @Override
        public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseRepresents");
        }

        public void visitJmlMethodSig(JmlMethodSig that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlConstraintMethodSig");
        }

        public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlModelProgramStatement");
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
        
        
        
        @Override
        protected boolean resolveJump(JCTree tree,
                        ListBuffer<AssignAnalyzer.AssignPendingExit> oldPendingExits,
                        JumpKind jk) {
            boolean resolved = false;
            List<AssignAnalyzer.AssignPendingExit> exits = pendingExits.toList();
            pendingExits = oldPendingExits;
            for (; exits.nonEmpty(); exits = exits.tail) {
                PendingExit exit = exits.head;
                if (exit.tree.hasTag(jk.treeTag) &&
                        jk.getTarget(exit.tree) == tree) {
                    exit.resolveJump();
                    resolved = true;
                } else if(exit.tree.hasTag(jk.treeTag) &&
                        jk.getTarget(exit.tree) == tree && tree instanceof JmlEnhancedForLoop && // JLS -- adapted to fit JDK8 programming style
                        jk.getTarget(exit.tree) == ((JmlEnhancedForLoop)tree).internalForLoop){
                    exit.resolveJump();
                    resolved = true;
                }
                
                else {
                    pendingExits.append((AssignAnalyzer.AssignPendingExit) exit);
                }
            }
            return resolved;
        }

        /** Resolve all continues of this statement. */
        boolean resolveContinues(JCTree tree) {
            return resolveJump(tree, new ListBuffer<AssignAnalyzer.AssignPendingExit>(), JumpKind.CONTINUE);
        }

        /** Resolve all breaks of this statement. */
        boolean resolveBreaks(JCTree tree, ListBuffer<AssignAnalyzer.AssignPendingExit> oldPendingExits) {
            return resolveJump(tree, oldPendingExits, JumpKind.BREAK);
        }
        
        
       

    }
    
    class JmlFlowAnalyzer extends FlowAnalyzer implements IJmlVisitor {
        
        /** This is a stack of the declarations occurring in JML quantifier expressions,
         * possible nested (and therefore stacked).
         */
        protected java.util.List<List<JCVariableDecl>> quantDeclStack = new java.util.LinkedList<List<JCVariableDecl>>();
       
        
        //// These are implemented
        
        /** This is overridden in order to handle JML method call-like features (e.g. \typeof) */
        @Override
        public void visitApply(JCMethodInvocation tree) {
            // tree.meth is null for JML keyword calls
            if (tree.meth != null) super.visitApply(tree);
            else scan(tree.args);
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
        public void visitJmlBlock(JmlBlock that) {
            scan(that.stats);
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
        public void visitJmlLabeledStatement(JmlLabeledStatement that) {
//            scan(that.extraStatements.toList());
            scan(that.body);
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
        public void visitJmlStatementShow(JmlStatementShow that) {
            scan(that.expressions);
        }

        @Override
        public void visitJmlStatementDecls(JmlStatementDecls that) {
            for (JCStatement s: that.list) {
                scan(s);
            }
        }

        @Override
        public void visitJmlStatementExpr(JmlStatementExpr that) {
          // nothing to do for this checker
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
        public void visitJmlInlinedLoop(JmlInlinedLoop that) {
            // No action to take
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
            // nothing to do ofr this checker
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
            // No need to scan specs
            if (that.statements != null) {
                scan(that.statements);
            }
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
        public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStatementLoop");
        }

        @Override
        public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStatementLoop");
        }

        @Override
        public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
//            scan(that.expression);
//            scan(that.lo);
//            scan(that.hi);
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStoreRefArrayRange");
        }

        @Override
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseConditional");
        }

        @Override
        public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseConstraint");
        }

        @Override
        public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseDecl");
        }

        @Override
        public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseExpr");
        }

        @Override
        public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseIn");
        }

        @Override
        public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseInitializer");
        }

        @Override
        public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseMaps");
        }

        @Override
        public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseMonitorsFor");
        }

        @Override
        public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseRepresents");
        }

        public void visitJmlMethodSig(JmlMethodSig that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlConstraintMethodSig");
        }

        public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlModelProgramStatement");
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
       
        @Override
        protected boolean resolveJump(JCTree tree,
                        ListBuffer<FlowAnalyzer.FlowPendingExit> oldPendingExits,
                        JumpKind jk) {
            boolean resolved = false;
            List<FlowAnalyzer.FlowPendingExit> exits = pendingExits.toList();
            pendingExits = oldPendingExits;
            for (; exits.nonEmpty(); exits = exits.tail) {
                PendingExit exit = exits.head;
                if (exit.tree.hasTag(jk.treeTag) &&
                        jk.getTarget(exit.tree) == tree) {
                    exit.resolveJump();
                    resolved = true;
                } else if(exit.tree.hasTag(jk.treeTag) &&
                        jk.getTarget(exit.tree) == tree && tree instanceof JmlEnhancedForLoop && // JLS -- adapted to fit JDK8 programming style
                        jk.getTarget(exit.tree) == ((JmlEnhancedForLoop)tree).internalForLoop){
                    exit.resolveJump();
                    resolved = true;
                }
                
                else {
                    pendingExits.append((FlowPendingExit) exit);
                }
            }
            return resolved;
        }

        /** Resolve all continues of this statement. */
        boolean resolveContinues(JCTree tree) {
            return resolveJump(tree, new ListBuffer<FlowAnalyzer.FlowPendingExit>(), JumpKind.CONTINUE);
        }

        /** Resolve all breaks of this statement. */
        boolean resolveBreaks(JCTree tree, ListBuffer<FlowAnalyzer.FlowPendingExit> oldPendingExits) {
            return resolveJump(tree, oldPendingExits, JumpKind.BREAK);
        }
        
        
    }
        
    // Overridden to call JML versions of visitors
    @Override 
    public void analyzeTree(Env<AttrContext> env, TreeMaker make) {
        new JmlAliveAnalyzer().analyzeTree(env, make);
        new JmlAssignAnalyzer().analyzeTree(env);
        new JmlFlowAnalyzer().analyzeTree(env, make);
        new CaptureAnalyzer().analyzeTree(env, make);
    }

    
    
   
}