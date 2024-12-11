/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-17
 */
package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.Kinds.*;
import static com.sun.tools.javac.code.Kinds.Kind.*;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.MiscExpressions;
import org.jmlspecs.openjml.ext.StateExpressions;
import org.jmlspecs.openjml.visitors.IJmlVisitor;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Lint;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.Flow.SnippetAliveAnalyzer;
import com.sun.tools.javac.comp.Flow.SnippetBreakToAnalyzer;
import com.sun.tools.javac.resources.CompilerProperties.Errors;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

// FIXME: The following list needs review; also whether JML constructs contribute to or mitigate such errors
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
            public Flow make(Context context) { 
                return new JmlFlow(context);
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
         * possibly nested (and therefore stacked).
         */
        protected java.util.List<List<JCVariableDecl>> quantDeclStack = new java.util.LinkedList<List<JCVariableDecl>>();
       
      
        //// These are implemented
        
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
        	if (that.meth != null) {
        		visitApply(that);
        	} else {
        		that.args.forEach(a -> { if (a.type != null) scan(a); });
        	}
        }

        @Override
        public void visitJmlBinary(JmlBinary that) {
            scan(that.lhs);
            scan(that.rhs);
        }
        
        @Override
        public void visitJmlChained(JmlChained that) {
            scan(that.conjuncts.head.lhs);
            for (JCTree.JCBinary b: that.conjuncts) scan(b.rhs);
        }
        
//        @Override
//        public void visitBlock(JmlBlock that) {
//            scanStats(that.stats);
//        }
        
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
        

//      @Override
//      public void visitImport(JCImport that) {
//          super.visitImport(that);
//      }
        
        @Override
        public void visitJmlRange(JmlRange that) {
            scan(that.lo);
            scan(that.hi);
        }

        @Override
        public void visitJmlSingleton(JmlSingleton that) {
            // nothing to do
        }

        @Override
        public void visitLabelled(JCTree.JCLabeledStatement that) {
            scan(((JmlLabeledStatement)that).extraStatements.toList());
            super.visitLabelled(that);
        }

        @Override
        public void visitJmlLblExpression(JmlLblExpression that) {
            scan(that.expression);
        }

//      public void visitNewClass(JCNewClass that) {
//      super.visitNewClass(that);
//  }

        public void visitJmlMatchExpression(JmlMatchExpression that) {
            scan(that.expression);
            for (JmlMatchExpression.MatchCase c: that.cases) {
                scan(c.caseExpression);
                scan(c.value);
            }
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
            scan(that.list);
        }

        @Override
        public void visitJmlStatementExpr(JmlStatementExpr that) {
            scan(that.expression);
            scan(that.optionalExpression);
        }

        @Override
        public void visitJmlStatementHavoc(JmlStatementHavoc that) {
            scan(that.storerefs);
        }

        public void visitJmlTuple(JmlTuple that) {
            for (JCExpression e: that.values)
                scan(e);
        }
        
        @Override
        public void visitJmlVariableDecl(JmlVariableDecl that) {
        	try {
            visitVarDef(that);
        	} catch (Exception e) {
        		System.out.println("Exception visiting " + that);
        		throw e;
        	}
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
            // No action - cf. TreeScanner.visitTypeIdent
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

        @Override
        public void visitJmlStoreRef(JmlStoreRef that) {
            // FIXME - do need to do some scanning
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
            // Needed for old clauses
            for (JCVariableDecl d: that.decls) visitVarDef(d);
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseDecl");
        }

        @Override
        public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
//            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseExpr");
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
            scan(that.expression);
            scan(that.lo);
            if (that.lo != that.hi) scan(that.hi);
//            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStoreRefArrayRange");
        }

        @Override
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseConditional");
        }

        @Override
        public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
         // ignore call
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseConstraint");
        }

        @Override
        public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseDecl");
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
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlTypeClauseInitializer");
        }

        @Override
        public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
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
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlModelProgramStatement");
        }
        
     // Instead of overriding visitClassDef (which does a lot of processing), a hook
        // (moreClassDef) was added into the middle of its implementation; this hook does
        // nothing in the base class, but is overridden below to do additional processing.
        /** Overridden to be sure that ghost/model declarations within the class are
         * visited by the flow checker.
         */
        @Override
        public void moreClassDef(JCClassDecl tree) {
            // Do nothing if the class is not attributed
            if (tree.sym == null) return;
            
            // Do nothing if the class is already instrumented for RAC
            if (Utils.instance(context).isInstrumented(tree.mods.flags)) return;
            
            // Do nothing if the class has no specs (i.e., is binary)
//            JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(tree.sym);
//            if (tspecs == null) return;

            // FIXME - it appears we are doing nothing here - so why this method?
            
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
//            if (tree.meth == null) {
//                IJmlClauseKind k = ((JmlMethodInvocation)tree).kind;
//                if (k == StateExpressions.oldKind || k == MiscExpressions.freshKind || k == MiscExpressions.allocKind) {
//                    scanExpr(tree.args.get(0)); // A second argument is just a label, and not a regular identifier
//                    // FIXME - where do we check that the label is in scope
//                } else {
//                    scanExprs(tree.args);
//                }
//            } else if (tree.meth.type == null) {
//                // FIXME - need to do this just because we don't have full attribution in trEnhancedForLoop
//                scanExpr(tree.meth);
//                scanExprs(tree.args);
//            } else {
                super.visitApply(tree);
 //           }
        }

        @Override
        public void visitJmlMethodDecl(JmlMethodDecl that) {
            visitMethodDef(that);
        }

        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        	if (that.meth != null) {
        		visitApply(that);
        	} else {
        		that.args.forEach(a -> { if (a.type != null) scan(a); });
        	}
        }

        @Override
        public void visitJmlBinary(JmlBinary that) {
            scanExpr(that.lhs);
            scanExpr(that.rhs);
        }

        @Override
        public void visitJmlChained(JmlChained that) {
            scanExpr(that.conjuncts.head.lhs);
            for (JCTree.JCBinary b: that.conjuncts) scanExpr(b.rhs);
        }
        
//        @Override
//        public void visitBlock(JmlBlock that) {
//            scan(that.stats);
//        }
        
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
        

//      @Override
//      public void visitImport(JCImport that) {
//          super.visitImport(that);
//      }

        @Override
        public void visitJmlRange(JmlRange that) {
            scan(that.lo);
            scan(that.hi);
        }

        @Override
        public void visitJmlSingleton(JmlSingleton that) {
            // nothing to do
        }

        @Override
        public void visitLabelled(JCTree.JCLabeledStatement that) {
            scan(((JmlLabeledStatement)that).extraStatements.toList());
            super.visitLabelled(that);
        }
        
        public void visitSelect(JCFieldAccess tree) {
            if (tree.name == null) return; // this might be a x.* in a havoc statement
            super.visitSelect(tree);
        }
        
        public void visitJmlTuple(JmlTuple that) {
            for (JCExpression e: that.values)
                scanExpr(e);
        }
        

        @Override
        public void visitJmlLblExpression(JmlLblExpression that) {
            scanExpr(that.expression);
        }

//        public void visitNewClass(JCNewClass that) {
//            super.visitNewClass(that);
//        }

        public void visitJmlMatchExpression(JmlMatchExpression that) {
        	System.out.println("visitJmlMatchExpression");
            scanExpr(that.expression);
            for (JmlMatchExpression.MatchCase c: that.cases) {
                //scan(c.caseExpression);
                //scan(c.value); // FIXME - spurious nonn-initialized errors
            }
        }

        @Override
        public void visitJmlStatement(JmlStatement that) {
            scan(that.statement);
        }
        
        @Override
        public void visitJmlStatementShow(JmlStatementShow that) {
        	// pure expressions - no assignments
        }

        @Override
        public void visitJmlStatementDecls(JmlStatementDecls that) {
            scan(that.list);
        }

        @Override
        public void visitJmlStatementExpr(JmlStatementExpr that) {
        	// pure expressions - no assignments
        }

        @Override
        public void visitJmlStatementHavoc(JmlStatementHavoc that) {
            scan(that.storerefs);
        }

        @Override
        public void visitJmlVariableDecl(JmlVariableDecl that) {
            try {
                visitVarDef(that);
            } catch (Exception e) {
                System.out.println("Exception flow-checking " + that);
                e.printStackTrace(System.out);
            }
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
            // No action to take -- FIXME - should visit expressions? amnd elsewhere in this file?
        }

        @Override
        public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
            // FIXME - check array dimensions? and elsewhere in this file?
        }

        @Override
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
            quantDeclStack.add(0,that.decls);
            for (var d: that.decls) {
            	scan(d);
            	letInit(d.pos(), d.sym);
            }
            if (that.racexpr != null) {
                scanExpr(that.racexpr); // FIXME - do this elsewhere in this file also?
            } else {
                scanExpr(that.range);
                scanExpr(that.value);
                scanExprs(that.triggers);
            }
            quantDeclStack.remove(0);
        }
        
        Utils utils;
        
        @Override
        public void visitIdent(JCIdent that) {
            if (that.sym == null) System.out.println("NULL SYM FOR " + that);
//            for (List<JCVariableDecl> list: quantDeclStack) {
//                for (JCVariableDecl decl: list) {
//                    if (decl.sym.equals(that.sym)) return;
//                }
//            }
//            if (utils == null) utils = Utils.instance(context);
//            if (utils.isJML(that.sym.flags()) && utils.isJMLTop(that.sym.flags()) && (that.sym.flags() & Flags.HASINIT) != 0) {
//                // Skip check for initialization -- this is a JML declaration with an initializer
//                // so includes old clauses in spec cases
//                referenced(that.sym);
//            } else {
                super.visitIdent(that);
//            }
        }

        @Override
        void checkInit(DiagnosticPosition pos, VarSymbol sym) {
        	// A static final ghost field does not need to be initialized
            if (!(Utils.instance(context).isJML(sym.flags()) && Utils.isStatic(sym.flags()) && Utils.isFinal(sym.flags()))) {
            	super.checkInit(pos,sym);
            }
        }


        public void visitVarDef(JCVariableDecl tree) {
            super.visitVarDef(tree);
            if (tree.init == null) {
            	if (tree.type.toString().startsWith("org.jmlspecs.lang")) {
            		//if (tree.type instanceof org.jmlspecs.lang.IJmlPrimitiveType) { // package does not exist in first compilation round
            		letInit(tree.pos(), tree.sym);
            	}
            }
            
//                Lint lintPrev = lint;
//                lint = lint.augment(tree.sym);
//                try{
//                    boolean track = trackable(tree.sym);
//                    if (track && (tree.sym.owner.kind == MTH || tree.sym.owner.kind == VAR)) {
//                        newVar(tree);
//                    }
//                    if (tree.init != null || tree.type.toString().startsWith("org.jmlspecs.lang")) {
//                        scanExpr(tree.init);
//                        if (track) {
//                            letInit(tree.pos(), tree.sym);
//                        }
//                    } else {
//                    	System.out.println("NOT INIT " + tree.type.toString());
//                    }
//                } finally {
//                    lint = lintPrev;
//                }
        }


        @Override
        public void visitJmlSetComprehension(JmlSetComprehension that) {
            // FIXME: Skipping set comprehension - check elsewhere in this file also
        }

        @Override
        public void visitJmlStatementSpec(JmlStatementSpec that) {
            // No need to scxan specs
            scan(that.statements);
        }

        @Override
        public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
            // FIXME: skipping store-ref expressions
            // we could call scanExpr on each expression, but we have to watch for special expressions
        }
        
        @Override
        public void visitJmlStoreRef(JmlStoreRef that) {
            // FIXME - do need to do some scanning
        }

        //// These do nothing, if they are even needed

        @Override
        public void visitJmlGroupName(JmlGroupName that) {
        }

        @Override
        public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) {
        }

        @Override
        public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        }

        @Override
        public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
            for (JCVariableDecl d: that.decls) visitVarDef(d);
        }

        @Override
        public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        }

        @Override
        public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        }

        @Override
        public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        }

        @Override
        public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        }

        @Override
        public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        }

        @Override
        public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        }

        @Override
        public void visitJmlSpecificationCase(JmlSpecificationCase that) {
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
            scanExpr(that.expression);
            scanExpr(that.lo);
            if (that.lo != that.hi) scanExpr(that.hi);
//            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStoreRefArrayRange");
        }

        @Override
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        	// no need to analyze
        }

        @Override
        public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        	// no need to analyze
        }

        @Override
        public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        	// no need to analyze
        }

        @Override
        public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        	// no need to analyze
        }

        @Override
        public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        	// no need to analyze
        }

        @Override
        public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        	// no need to analyze
        }

        @Override
        public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        	// no need to analyze
        }

        @Override
        public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        	// no need to analyze
        }

        @Override
        public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        	// no need to analyze
        }

        public void visitJmlMethodSig(JmlMethodSig that) {
        	// no need to analyze
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
//            // Do nothing if the class is not attributed
//            if (tree.sym == null) return;
//            
//            // Do nothing if the class is already instrumented for RAC
//            if (Utils.instance(context).isInstrumented(tree.mods.flags)) return;
//            
//            // Do nothing if the class has no specs (i.e., is binary)
//            JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(tree.sym);
//            if (tspecs == null) return;
//            
//            JavaFileObject prev = Log.instance(context).currentSourceFile();
//            try {
//                // Do Flow processing on each JML clause of the class declaration
//                for (JmlTypeClause c : tspecs.clauses) {
//                    if (c instanceof JmlTypeClauseDecl) {
//                        JCTree d = ((JmlTypeClauseDecl)c).decl;
//                        Log.instance(context).useSource(c.source());
//                        if (c.modifiers != null && (c.modifiers.flags & Flags.SYNTHETIC) != 0) {
//                            continue;
//                        }
//                        d.accept(this);
//                    }
//                }
//            } finally {
//                Log.instance(context).useSource(prev);
//            }
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
        	if (that.meth != null) {
        		visitApply(that);
        	} else {
        		that.args.forEach(a -> { if (a.type != null) scan(a); });
        	}
        }

        @Override
        public void visitJmlBinary(JmlBinary that) {
            scan(that.lhs);
            scan(that.rhs);
        }
        
        @Override
        public void visitJmlChained(JmlChained that) {
            scan(that.conjuncts.head.lhs);
            for (JCTree.JCBinary b: that.conjuncts) scan(b.rhs);
        }
        
//        @Override
//        public void visitBlock(JmlBlock that) {
//            scan(that.stats);
//        }
        
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
        

//        @Override
//        public void visitImport(JCImport that) {
//            super.visitImport(that);
//        }

        @Override
        public void visitJmlRange(JmlRange that) {
            scan(that.lo);
            scan(that.hi);
        }

        @Override
        public void visitJmlSingleton(JmlSingleton that) {
            // nothing to do
        }

        @Override
        public void visitLabelled(JCTree.JCLabeledStatement that) {
            scan(((JmlLabeledStatement)that).extraStatements.toList());
            super.visitLabelled(that);
        }

        @Override
        public void visitJmlLblExpression(JmlLblExpression that) {
            scan(that.expression);
        }

//      public void visitNewClass(JCNewClass that) {
//      super.visitNewClass(that);
//  }

        public void visitJmlMatchExpression(JmlMatchExpression that) {
            scan(that.expression);
            for (JmlMatchExpression.MatchCase c: that.cases) {
                //scan(c.caseExpression);
                scan(c.value);
            }
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
            scan(that.list);
        }

        @Override
        public void visitJmlStatementExpr(JmlStatementExpr that) {
            scan(that.expression);
            scan(that.optionalExpression);
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
            // No action to take -- FIXME - review
        }

        @Override
        public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
            // FIXME - check array dimensions?
        }

        @Override
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
            // nothing to do for this checker -- FIXME - review
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

        public void visitJmlTuple(JmlTuple that) {
            for (JCExpression e: that.values)
                scan(e);
        }
        
        @Override
        public void visitJmlStatementSpec(JmlStatementSpec that) {
            // No need to scan specs
            scan(that.statements);
        }

        @Override
        public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
            // FIXME: skipping store-ref expressions
            // we could call scanExpr on each expression, but we have to watch for special expressions
        }

        @Override
        public void visitJmlStoreRef(JmlStoreRef that) {
            // FIXME - do need to do some scanning
        }


        //// These are not implemented

        @Override
        public void visitJmlGroupName(JmlGroupName that) {
        }

        @Override
        public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) {
        }

        @Override
        public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseConditional");
        }

        @Override
        public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
            for (JCVariableDecl d: that.decls) visitVarDef(d);
            //Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseDecl");
        }

        @Override
        public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
//            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlMethodClauseExpr");
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
            scan(that.expression);
            scan(that.lo);
            if (that.lo != that.hi) scan(that.hi);
//            Log.instance(context).error("jml.internal","Unexpected call of JmlFlow.visitJmlStoreRefArrayRange");
        }

        @Override
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        	// do nothing
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
        	// do nothing
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
    
            // FIXME - it seems we should do this flow processing, but will it muck up attributing specs on demand?
//            // Do nothing if the class has no specs (i.e., is binary)
//            JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).getSpecs(tree.sym);
////            if (tspecs == null) return;
//            
//            JavaFileObject prev = Log.instance(context).currentSourceFile();
//            try {
//                // Do Flow processing on each JML clause of the class declaration
//                for (JmlTypeClause c : tspecs.clauses) {
//                    if (c instanceof JmlTypeClauseDecl) {
//                        JCTree d = ((JmlTypeClauseDecl)c).decl;
//                        Log.instance(context).useSource(c.source());
//                        if (c.modifiers != null && (c.modifiers.flags & Flags.SYNTHETIC) != 0) {
//                            continue;
//                        }
//                        d.accept(this);
//                    }
//                }
//            } finally {
//                Log.instance(context).useSource(prev);
//            }
        }
    }
    
    public class JmlCaptureAnalyzer extends CaptureAnalyzer implements IJmlVisitor{
    	public void visitAnnotation(JCTree.JCAnnotation tree) {
    		// FIXME - we skip annotations because some of them crash in CaptureAnalyzer.visitIdent, as they do 
    		// not have sym set -- this is a bug of as yet undebugged cause
    		//System.out.println("ANNOT " + tree + " " + tree.type);
    		return;
    	}
    }
        
    // Overridden to call JML versions of visitors
    @Override 
    public void analyzeTree(Env<AttrContext> env, TreeMaker make) {
    	try {
    		new JmlAliveAnalyzer().analyzeTree(env, make);
    		new JmlAssignAnalyzer().analyzeTree(env, make);
    		new JmlFlowAnalyzer().analyzeTree(env, make);
    		new JmlCaptureAnalyzer().analyzeTree(env, make);
    	} catch (Exception e)  {
    		Utils.instance(context).unexpectedException(e, "FLOW");
    	}
    }
}