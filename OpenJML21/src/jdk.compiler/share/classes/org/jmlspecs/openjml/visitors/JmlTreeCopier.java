/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.visitors;

import java.io.IOException;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.JmlTree.JmlMatchExpression.MatchCase;
import static org.jmlspecs.openjml.ext.StateExpressions.*;
import static org.jmlspecs.openjml.ext.MiscExpressions.*;

import com.sun.source.tree.*;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeCopier;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;

/** This class extends TreeCopier to JML nodes.  It simply makes a deep copy of
 * the tree, including JML nodes and specs, without changing it.  CAUTION: Any 
 * new AST nodes or change to the fields of an AST node will require changes to
 * this code.
 * 
 * @author David Cok
 *
 */

// DESIGN NOTE: This class follows the design of TreeCopier, namely to create
// copies by using the factory and explicitly filling in the nodes that the
// factory methods do not initialize.  This is fragile against additions or
// removal of fields from AST nodes.
// Alternately we could have used clone methods, and let the AST classes themselves
// be responsible for copying themselves.  JCTree does define clone().  
// Using clone() would not have permitted using an alternate factory to create
// the copy of the tree (a piece of functionality we don't use), and it would be
// different from how TreeCopier is implemented.
// So we live with this design.

// FIXME - This class does not yet take care of the start and end position information;
// also links between declarations and symbols are not updated (e.g. the map from
// symbols to class declarations).  It may be the case that the AST will have to be 
// completely re-attributed and that it is not really possible to have copies
// of trees that really work

public class JmlTreeCopier extends TreeCopier<Void> implements JmlTreeVisitor<JCTree,Void> {
    
    protected Context context;
    
    /** The factory to be used to make new nodes */
    protected JmlTree.Maker M;
    
    protected JmlTreeUtils treeutils; 
    
    protected Log log;
    
    /** Creates a new copier, whose new nodes are generated from the given factory*/
    public JmlTreeCopier(Context context, JmlTree.Maker maker) {
        super(maker);
        this.M = maker;
        this.context = context;
        this.treeutils = JmlTreeUtils.instance(context);
        this.log = Log.instance(context);
    }
    
    /** A (overridable) factory method that returns a new (or derived) instance
     * of a JmlCopier object.
     */
    public JmlTreeCopier newCopier(JmlTree.Maker maker) {
        return new JmlTreeCopier(context,maker);
    }
    
    public void copyEndPos(JCTree dst, JCTree src, javax.tools.JavaFileObject jfo)  {
    	if (jfo != null) {
    		var prev = log.useSource(jfo);
    		treeutils.copyEndPosition(dst, src);
    		log.useSource(prev);
    	} else {
    		treeutils.copyEndPosition(dst, src);
    	}
    }
    
    public void copyEndPos(JCTree dst, JCTree src)  {
    	treeutils.copyEndPosition(dst, src);
    }
    
    /** Static method to create a copy of the given AST with the given factory */
    public static <T extends JCTree> T copy(JmlTree.Maker maker, /*@nullable*/ T that) {
        return new JmlTreeCopier(maker.context,maker).copy(that,null);
    }
    
    /** Deep copy of a list of nodes */
    public <T extends JCTree> ListBuffer<T> copy(/*@nullable*/ ListBuffer<T> trees, Void p) {
        if (trees == null) return null;
        ListBuffer<T> lb = new ListBuffer<T>();
        for (T tree: trees)
            lb.append(copy(tree, p));
        return lb;
    }

    /** Deep copy of a list of nodes */
    public <T extends JCTree> java.util.List<T> copy(/*@ nullable */ java.util.List<T> trees, Void p) {
        if (trees == null) return null;
        java.util.List<T> lb = new java.util.LinkedList<T>();
        for (T tree: trees)
            lb.add(copy(tree, p));
        return lb;
    }

    /** Deep copy of a list of nodes */
    public <T extends JCTree> com.sun.tools.javac.util.List<T> copy(/*@ nullable */ com.sun.tools.javac.util.List<T> trees, Void p) {
        if (trees == null) return null;
        ListBuffer<T> lb = new ListBuffer<T>();
        for (T tree: trees)
            lb.append(copy(tree, p));
        return lb.toList();
    }


    
    public void visitTree(JCTree that) {
        // FIXME - proper error message
        Log.instance(context).error("log.internal","A node type is not implemented in JmlTreeCopier: " + that.getClass());
    }
    

    public JCTree visitJmlChoose(JmlChoose that, Void p) {
        JmlChoose copy = M.at(that.pos).JmlChoose(that.keyword, that.clauseType, copy(that.orBlocks), copy(that.elseBlock));
        return copy;
    }

    public JCTree visitJmlClassDecl(JmlClassDecl that, Void p) {
        JmlClassDecl copy = (JmlClassDecl)super.visitClass(that,p);
        copy.toplevel = that.toplevel;
        copy.specsDecl = that.specsDecl;// FIXME - copy
        copy.typeSpecs = that.typeSpecs;// FIXME - copy
        copy.thisSymbol = that.thisSymbol;
        copy.type = that.type;
        copy.lineAnnotations = that.lineAnnotations;
        return copy;
    }

    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl)super.visitMethod(that,p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;// FIXME - copy
        copy.cases = copy(that.cases,p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined,p,this);
        copy.type = that.type;
        copy.isInitializer = that.isInitializer;
        return copy;
    }

    public JCTree visitJmlVariableDecl(JmlVariableDecl that, Void p) {
        JmlVariableDecl copy = (JmlVariableDecl)super.visitVariable(that,p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl; // FIXME - repoint to new reference?
        copy.fieldSpecs = that.fieldSpecs;
        copy.sym = that.sym;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlBinary(JmlBinary that, Void p) {
        JCExpression lhs = copy(that.lhs,p);
        JCExpression rhs = copy(that.rhs,p);
        JmlBinary r = M.at(that.pos).JmlBinary(that.op,lhs,rhs);
        r.type = that.type;
        return r;
    }
    
    @Override
    public JCTree visitJmlChained(JmlChained that, Void p) {
        JCExpression lhs = copy(that.conjuncts.head.lhs,p);
        ListBuffer<JCBinary> c = new ListBuffer<>();
        for (JCBinary b: that.conjuncts) {
            JCExpression rhs = copy(b.rhs);
            JCBinary r = M.at(b.pos).Binary(b.getTag(),lhs,rhs);
            r.operator = b.operator;
            r.type = b.type;
            c.add(r);
            lhs = rhs;
        }
        return M.at(that.pos).JmlChained(c.toList()).setType(that.type);
    }
    
    @Override
    public JCTree visitBlock(BlockTree node, Void p) {
        JmlBlock that = (JmlBlock)node;
        JmlBlock r = (JmlBlock)super.visitBlock(that,p).setType(that.type);
        r.endpos = that.endpos;
        r.sourcefile = that.sourcefile;
        r.isInitializerBlock = that.isInitializerBlock;
        r.specificationCases = copy(that.specificationCases);
        return r;
    }


    
    @Override
    public JCTree visitJmlConstraintMethodSig(JmlMethodSig that,
            Void p) {
        return M.at(that.pos).JmlConstraintMethodSig(
                copy(that.expression,p),
                copy(that.argtypes,p)).setType(that.type);
    }

    @Override
    public JCTree visitJmlDoWhileLoop(JmlDoWhileLoop that, Void p) {
        JmlDoWhileLoop r = M.at(that.pos).JmlDoWhileLoop(
                (JCDoWhileLoop)this.visitDoWhileLoop(that,p),
                copy(that.loopSpecs,p));
        // already done: r.type = that.type;
        r.split = that.split;
        return r;
    }

    @Override
    public JCTree visitJmlEnhancedForLoop(JmlEnhancedForLoop that, Void p) {
        JmlEnhancedForLoop r = M.at(that.pos).JmlEnhancedForLoop(
                (JCEnhancedForLoop)this.visitEnhancedForLoop(that,p),
                copy(that.loopSpecs,p));
        // already done: r.type = that.type;
        // FIXME - implementation, indexDecl, valuesDecl, iterDecl
        r.split = that.split;
        return r;
    }


    @Override
    public JCTree visitJmlForLoop(JmlForLoop that, Void p) {
        JmlForLoop r = M.at(that.pos).JmlForLoop(
                (JCForLoop)this.visitForLoop(that,p),
                copy(that.loopSpecs,p));
        // already done: r.type = that.type;
        r.split = that.split;
        return r;
    }

    @Override
    public JCTree visitJmlGroupName(JmlGroupName that, Void p) {
        JmlGroupName r = M.at(that.pos).JmlGroupName(copy(that.selection,p));
        r.sym = that.sym;
        r.type = that.type;
        return r;
    }

 
    @Override
    public JCTree visitJmlInlinedLoop(JmlInlinedLoop that, Void p) {
        JmlInlinedLoop copy = M.at(that.pos).JmlInlinedLoop(copy(that.loopSpecs));
        copy.type = that.type;
        return copy;
    }
    
    public JCTree visitLambda(JCLambda that, Void p) {
        JmlLambda copy = M.at(that.pos).JmlLambda(copy(that.params,p), copy(that.body,p), copy(((JmlLambda)that).jmlType,p));
        copy.type = that.type;
        copy.canCompleteNormally = that.canCompleteNormally;
        copy.paramKind = that.paramKind;
        copy.polyKind = that.polyKind;
        copy.target = that.target; // FIXME - should make new copies?
        copy.sourceLocation = ((JmlLambda)that).sourceLocation;
        return copy;
    }
    
    @Override
    public JCTree visitMemberReference(MemberReferenceTree that, Void p) {
    	var mref = (JCMemberReference)that;
    	var copy = (JCMemberReference)super.visitMemberReference(that,p);
    	copy.sym = mref.sym;
    	copy.type = mref.type;
    	return copy;
    }

    @Override
    public JCTree visitNewClass(NewClassTree tree, Void p) {
//            return super.visitNewClass(node,p).setType(((JCTree)node).type);
//            // FIXME - does not copy constructor, varargsElement, constructorType
        JmlNewClass that = (JmlNewClass)tree;
        JmlNewClass copy = M.at(that.pos).NewClass(
                copy(that.encl,p), copy(that.typeargs,p), copy(that.clazz,p), copy(that.args,p), copy(that.def,p));
        copy.type = that.type;
        copy.constructor = that.constructor;
        copy.constructorType = that.constructorType;
        // Not copying capturedExpressions
        return copy;
    }



    @Override
    public JCTree visitLabeledStatement(LabeledStatementTree tree, Void p) {
        var that = (JmlLabeledStatement)tree;
        return M.at(that.pos).JmlLabeledStatement(
                that.label,
                copy(that.extraStatements,p),
                copy(that.body,p)).setType(that.type);
     }

    @Override
    public JCTree visitJmlLblExpression(JmlLblExpression that, Void p) {
        return M.at(that.pos).JmlLblExpression(
                that.labelPosition,
                that.kind,
                that.label,
                copy(that.expression,p)).setType(that.type);
    }
    
    @Override
    public JCTree visitJmlMatchExpression(JmlMatchExpression that, Void p) {
        JmlMatchExpression cc = M.at(that.pos).JmlMatchExpression(
                copy(that.expression),that.cases);
        cc.setType(that.type);
        ListBuffer<JmlMatchExpression.MatchCase> newcases = new ListBuffer<>();
        for (JmlMatchExpression.MatchCase c: that.cases) {
            newcases.add(new JmlMatchExpression.MatchCase(copy(c.caseExpression), copy(c.value)));
        }
        cc.cases = newcases.toList();
        return cc;
    }
    
    // FIXME - missing copying end positions, here and probably elsewhere

    @Override
    public JCTree visitJmlMethodClauseCallable(JmlMethodClauseCallable that, Void p) {
        JmlMethodClauseCallable copy;
        if (that.keyword != null) {
            copy = M.at(that.pos).JmlMethodClauseCallable(that.keyword);
        } else {
            copy = M.at(that.pos).JmlMethodClauseCallable(copy(that.methodSignatures,p));
        }
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseBehaviors(JmlMethodClauseBehaviors that, Void p) {
        JmlMethodClauseBehaviors copy= M.at(that.pos).JmlMethodClauseBehaviors(that.command);
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseConditional(JmlMethodClauseConditional that, Void p) {
        JmlMethodClauseConditional copy = M.at(that.pos).JmlMethodClauseConditional(
                that.keyword,
                that.clauseKind,
                copy(that.expression,p),
                copy(that.predicate,p));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseDecl(JmlMethodClauseDecl that, Void p) {
        JmlMethodClauseDecl copy = M.at(that.pos).JmlMethodClauseDecl(
                that.keyword,
                that.clauseKind,
                copy(that.decls,p));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        JmlMethodClauseExpr copy = M.at(that.pos).JmlMethodClauseExpr(
                that.keyword,
                that.clauseKind,
                copy(that.expression,p));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseInvariants(JmlMethodClauseInvariants that, Void p) {
        JmlMethodClauseInvariants copy = M.at(that.pos).JmlMethodClauseInvariants(copy(that.expressions));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseGroup(JmlMethodClauseGroup that, Void p) {
        JmlMethodClauseGroup copy = M.at(that.pos).JmlMethodClauseGroup(
                copy(that.cases,p));
        copy.keyword = that.keyword;
        copy.clauseKind = that.clauseKind;
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseSignals(JmlMethodClauseSignals that, Void p) {
        JmlMethodClauseSignals copy = M.at(that.pos).JmlMethodClauseSignals(
                that.keyword,
                that.clauseKind,
                copy(that.vardef,p),
                copy(that.expression,p));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that, Void p) {
        JmlMethodClauseSignalsOnly copy = M.at(that.pos).JmlMethodClauseSignalsOnly(
                that.keyword,
                that.clauseKind,
                copy(that.list,p));
        copy.defaultClause = that.defaultClause;
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, Void p) {
        JmlMethodClauseStoreRef r = M.at(that.pos).JmlMethodClauseStoreRef(
                that.keyword,
                that.clauseKind,
                copy(that.list,p));
        r.sourcefile = that.sourcefile;
        r.setType(that.type);
        copyEndPos(r,that,r.sourcefile);
        return r;
    }

    @Override
    public JCTree visitJmlMethodInvocation(JmlMethodInvocation that, Void p) {
        // Don't use visitMethodInvocation, since it is designed just to produce
        // JCMethodInvocation nodes.  Normal method calls are JCMethodInvocations;
        // only special JML functions (e.g. \\nonnullelements) are JmlMethodInvocation
        // nodes.
        // CAUTION: if JCMethodInvocation adds fields, they have to be added here
//        JmlMethodInvocation copy = M.at(that.pos).JmlMethodInvocation(
//                that.kind,
//                copy(that.args,p));
//        copy.name = that.name;
//        copy.token = that.token;
//        copy.startpos = that.startpos;
//        copy.labelProperties = that.labelProperties;
//        copy.type = that.type;
//        copy.meth = copy(that.meth,p);
//        copy.typeargs = copy(that.typeargs,p);
//        copy.varargsElement = that.varargsElement; // FIXME - copy?
		if (that.kind == oldKind || that.kind == pastKind || that.kind == preKind || that.kind == freshKind
				|| that.kind == allocKind) {
			JCExpression arg0 = copy(that.args.get(0),p);
			JmlMethodInvocation m;
			if (that.args.size() > 1) {
				JCExpression arg1 = that.args.get(1);
				arg1 = M.at(arg1).Ident(((JCIdent) arg1).name);
				m = M.at(that).JmlMethodInvocation(that.kind, List.<JCExpression>of(arg0, arg1));
			} else {
				m = M.at(that).JmlMethodInvocation(that.kind, List.<JCExpression>of(arg0));
			}
			m.setType(that.type);
			m.token = that.token;
			m.labelProperties = that.labelProperties;
			m.startpos = that.startpos;
			m.varargsElement = that.varargsElement;
			// typeargs and meth are always null for a JML operation
			return m;
		} else {
			JmlMethodInvocation m;
			if (that.kind != null) {
				m = M.at(that).JmlMethodInvocation(that.kind, copy(that.args,p));
			} else if (that.token != null) {
				m = M.at(that).JmlMethodInvocation(that.token, copy(that.args,p));
			} else if (that.name != null) {
				m = M.at(that).JmlMethodInvocation(that.name, copy(that.args,p));
			} else {
				m = M.at(that).JmlMethodInvocation(copy(that.meth, p), copy(that.args,p));
			}
			m.setType(that.type);
			m.labelProperties = that.labelProperties;
			m.javaType = that.javaType;
			m.startpos = that.startpos;
			m.token = that.token;
			m.varargsElement = that.varargsElement;
			// typeargs and meth are always null for a
			return m;
		}
    }

    @Override
    public JCTree visitJmlMethodSpecs(JmlMethodSpecs that, Void p) {
        JmlMethodSpecs copy = M.at(that.pos).JmlMethodSpecs(copy(that.cases,p));
        copy.impliesThatCases = copy(that.impliesThatCases,p);
        copy.forExampleCases = copy(that.forExampleCases,p);
        copy.feasible = copy(that.feasible,p);
        copy.type = that.type;
        // FIXME - decl desugared
        // FICXME - endpos?
        return copy;
    }

    @Override
    public JCTree visitJmlModelProgramStatement(JmlModelProgramStatement that,
            Void p) {
        return M.at(that.pos).JmlModelProgramStatement(copy(that.item,p)).setType(that.type);
        // FIXME - end pos
    }

    @Override
    public JCTree visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that, Void p) {
        return M.at(that.pos).JmlPrimitiveTypeTree(that.token, that.jmlclausekind, that.typeName).setType(that.type);
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        JmlQuantifiedExpr q =  M.JmlQuantifiedExpr(
                that.kind,
                copy(that.decls,p),
                copy(that.range,p),
                copy(that.value,p));
        q.pos = that.pos;
        q.triggers = copy(that.triggers,p);
        q.racexpr = copy(that.racexpr,p);
        q.founddef = that.founddef;
        q.setType(that.type);
        return q;
    }

    @Override
    public JCTree visitJmlRange(JmlRange that, Void p) {
        JmlRange r = M.JmlRange(copy(that.lo), copy(that.hi));
        r.pos = that.pos;
        r.type = that.type;
        r.hiExclusive = that.hiExclusive;
        return r;
    }

    @Override
    public JCTree visitJmlSetComprehension(JmlSetComprehension that, Void p) {
        return M.JmlSetComprehension(
                copy(that.newtype,p),
                copy(that.variable,p),
                copy(that.predicate,p)).setType(that.type).setPos(that.pos);
    }

    @Override
    public JCTree visitJmlSingleton(JmlSingleton that, Void p) {
        JmlSingleton r = M.JmlSingleton(that.kind);
        r.pos = that.pos;
        r.type = that.type;
        r.info = that.info;
        return r;
    }

    @Override
    public JCTree visitJmlSpecificationCase(JmlSpecificationCase that, Void p) {
        JmlSpecificationCase copy = M.JmlSpecificationCase(
                copy(that.modifiers,p),
                that.code,
                that.token,
                that.also,
                copy(that.clauses,p),
                copy(that.block));
        copy.pos = that.pos;
        copy.block = copy(that.block,p);
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        copy.name = that.name;
        copyEndPos(copy,that,copy.sourcefile);
        return copy;
    }

    @Override
    public JCTree visitJmlStatement(JmlStatement that, Void p) {
        JmlStatement copy = M.JmlStatement(
                that.clauseType,
                copy(that.statement,p));
        copy.pos = that.pos;
        copy.type = that.type;
        return copy;
    }
    
    @Override
    public JCTree visitJmlStatementShow(JmlStatementShow that, Void p) {
        ListBuffer<JCExpression> expressions = new ListBuffer<>();
        for (JCExpression e: that.expressions) expressions.add( copy(e,p));
        JmlStatementShow copy = M.JmlStatementShow(
                that.clauseType,
                copy(that.expressions,p));
        copy.pos = that.pos;
        copy.type = that.type;
        return copy;
    }

    

    @Override
    public JCTree visitJmlStatementDecls(JmlStatementDecls that, Void p) {
        JmlStatementDecls copy = M.at(that.pos).JmlStatementDecls(
                copy(that.list,p));
        copy.token = that.token;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStatementExpr(JmlStatementExpr that, Void p) {
        JmlStatementExpr copy = M.at(that.pos).JmlExpressionStatement(
                that.keyword,
                that.clauseType,
                that.label,
                copy(that.expression,p));
        copy.optionalExpression = copy(that.optionalExpression,p);
        copy.associatedPos = that.associatedPos;
        copy.associatedClause = that.associatedClause;
        copy.source = that.source;
        copy.type = that.type;
        copyEndPos(copy,that,copy.source); // FIXME - should the log be set before all the sub-copies?
        return copy;
    }

    @Override
    public JCTree visitJmlStatementHavoc(JmlStatementHavoc that, Void p) {
    	var prev = log.useSource(that.source);
        JmlStatementHavoc copy = M.at(that.pos).JmlHavocStatement(
                copy(that.storerefs,p));
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlStatementLoopExpr(JmlStatementLoopExpr that, Void p) {
        JmlStatementLoopExpr copy = M.at(that.pos).JmlStatementLoopExpr(
                that.clauseType,
                copy(that.expression,p));
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStatementLoopModifies(JmlStatementLoopModifies that, Void p) {
    	var prev = log.useSource(that.source);
        JmlStatementLoopModifies copy = M.at(that.pos).JmlStatementLoopModifies(
                that.clauseType,
                copy(that.storerefs,p));
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        JmlStatementSpec sp = M.at(that.pos).JmlStatementSpec(
                copy(that.statementSpecs,p));
        sp.exports = copy(that.exports, p);
        sp.label = that.label;
        sp.setType(that.type);
        return sp;
    }

    @Override
    public JCTree visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that, Void p) {
//        JmlStoreRefArrayRange copy = M.at(that.pos).JmlStoreRefArrayRange(
//                copy(that.expression,p),
//                copy(that.lo,p),
//                copy(that.hi,p));
//        copy.type = that.type;
//        return copy;
    	return null;
    }

    @Override
    public JCTree visitJmlStoreRefKeyword(JmlStoreRefKeyword that, Void p) {
//        JmlStoreRefKeyword copy = M.at(that.pos).JmlStoreRefKeyword(
//                that.kind);
//        copy.type = that.type;
//        return copy;
    	return null;
    }

    @Override
    public JCTree visitJmlStoreRefListExpression(JmlStoreRefListExpression that, Void p) {
        JmlStoreRefListExpression copy = M.at(that.pos).JmlStoreRefListExpression(
                that.token,
                copy(that.list,p));
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStoreRef(JmlStoreRef that, Void p) {
        JmlStoreRef copy = M.at(that.pos).JmlStoreRef(
                that.isEverything,
                that.local,
                copy(that.expression,p),
                copy(that.receiver,p),
                copy(that.range,p),
                that.field,
                that.originalStoreRef
                );
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTuple(JmlTuple that, Void p) {
        JmlTuple copy = M.at(that.pos).JmlTuple(
                copy(that.values,p));
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseConditional(JmlTypeClauseConditional that, Void p) {
    	var prev = log.useSource(that.source);
        JmlTypeClauseConditional copy = M.at(that.pos).JmlTypeClauseConditional(
                copy(that.modifiers,p),
                that.clauseType,
                copy(that.identifier,p),
                copy(that.expression,p));
        copy.source = that.source;
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that, Void p) {
    	var prev = log.useSource(that.source);
        JmlTypeClauseConstraint copy = M.at(that.pos).JmlTypeClauseConstraint(
                copy(that.modifiers,p),
                copy(that.expression,p),
                copy(that.sigs,p));
        copy.clauseType = that.clauseType;
        copy.source = that.source;
        copy.type = that.type;
        copy.notlist = that.notlist;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseDecl(JmlTypeClauseDecl that, Void p) {
    	var prev = log.useSource(that.source);
        JmlTypeClauseDecl copy = M.at(that.pos).JmlTypeClauseDecl(
                copy(that.decl,p));
        copy.clauseType = that.clauseType;
        copy.modifiers = copy(that.modifiers,p);
        copy.source = that.source;
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseExpr(JmlTypeClauseExpr that, Void p) {
    	var prev = log.useSource(that.source);
        JmlTypeClauseExpr copy = M.at(that.pos).JmlTypeClauseExpr(
                copy(that.modifiers,p),
                that.keyword,
                that.clauseType,
                copy(that.expression,p));
        copy.source = that.source;
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseIn(JmlTypeClauseIn that, Void p) {
    	var prev = log.useSource(that.source);
        JmlTypeClauseIn copy = M.at(that.pos).JmlTypeClauseIn(
                copy(that.list,p));
        copy.clauseType = that.clauseType;
        copy.source = that.source;
        copy.modifiers = copy(that.modifiers,p);
        copy.parentVar = that.parentVar; // FIXME - does this need repointing to the new copy
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that, Void p) {
    	var prev = log.useSource(that.source);
        JmlTypeClauseInitializer copy = M.at(that.pos).JmlTypeClauseInitializer(
                that.clauseType,null);
        copy.modifiers = copy(that.modifiers,p);
        copy.specs = copy(that.specs,p);
        copy.source = that.source;
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseMaps(JmlTypeClauseMaps that, Void p) {
    	var prev = log.useSource(that.source);
        JmlTypeClauseMaps copy = M.at(that.pos).JmlTypeClauseMaps(
                copy(that.expressions,p),
                copy(that.list,p));
        copy.clauseType = that.clauseType;
        copy.modifiers = copy(that.modifiers,p);
        copy.source = that.source;
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that, Void p) {
    	var prev = log.useSource(that.source);
        JmlTypeClauseMonitorsFor copy = M.at(that.pos).JmlTypeClauseMonitorsFor(
                copy(that.modifiers,p),
                copy(that.identifier,p),
                copy(that.list,p));
        copy.clauseType = that.clauseType;
        copy.source = that.source;
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that, Void p) {
    	var prev = log.useSource(that.source);
        JmlTypeClauseRepresents copy = M.at(that.pos).JmlTypeClauseRepresents(
                copy(that.modifiers,p),
                copy(that.ident,p),
                that.suchThat,
                copy(that.expression,p));
        copy.clauseType = that.clauseType;
        copy.source = that.source;
        copy.type = that.type;
        copyEndPos(copy,that);
        log.useSource(prev);
        return copy;
    }

    @Override
    public JCTree visitJmlWhileLoop(JmlWhileLoop that, Void p) {
        JmlWhileLoop r = M.at(that.pos).JmlWhileLoop(
                (JmlWhileLoop)this.visitWhileLoop(that,p),
                copy(that.loopSpecs,p));
        // already done: r.type = that.type;
        r.split = that.split;
        return r;
    }
    
    // We have to reimplement all the JCTree nodes because we want the type
    // information copied
    
    @Override
    public JCTree visitAnnotation(AnnotationTree node, Void p) {
    	var prev = node instanceof JmlAnnotation ? log.useSource(((JmlAnnotation)node).sourcefile) : null;
        JmlAnnotation a = (JmlAnnotation)super.visitAnnotation(node,p);
        a.setType(((JCAnnotation)node).type);
        if (node instanceof JmlAnnotation) {
        	a.sourcefile = ((JmlAnnotation)node).sourcefile;
        	a.kind = ((JmlAnnotation)node).kind;
            copyEndPos(a,(JCTree)node);
        }
        if (prev != null) log.useSource(prev);
        return a;
    }

    @Override
    public JCTree visitAssert(AssertTree node, Void p) {
        return super.visitAssert(node,p).setType(((JCAssert)node).type);
    }

    @Override
    public JCTree visitAssignment(AssignmentTree node, Void p) {
        return super.visitAssignment(node,p).setType(((JCAssign)node).type);
    }

    public JCTree visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        JCTree t = super.visitCompoundAssignment(node,p).setType(((JCAssignOp)node).type);
        ((JCAssignOp)t).operator = ((JCAssignOp)node).operator;
        return t;
    }

    public JCTree visitBinary(BinaryTree node, Void p) {
        JCTree t = super.visitBinary(node,p).setType(((JCBinary)node).type);
        ((JCBinary)t).operator = ((JCBinary)node).operator;
        return t;
    }

     public JCTree visitBreak(BreakTree node, Void p) {
        return super.visitBreak(node,p).setType(((JCBreak)node).type);
        // FIXME - need to repoint reference to target
    }

    public JCTree visitCase(CaseTree node, Void p) {
        return super.visitCase(node,p).setType(((JCCase)node).type);
    }

    public JCTree visitCatch(CatchTree node, Void p) {
        return super.visitCatch(node,p).setType(((JCCatch)node).type);
    }

    public JCTree visitClass(ClassTree node, Void p) {
        JCTree t = super.visitClass(node,p).setType(((JCClassDecl)node).type);
        ((JCClassDecl)t).sym = ((JCClassDecl)node).sym;
        return t;
    }

    public JCTree visitConditionalExpression(ConditionalExpressionTree node, Void p) {
        return super.visitConditionalExpression(node,p).setType(((JCConditional)node).type);
    }

    public JCTree visitContinue(ContinueTree node, Void p) {
        return super.visitContinue(node,p).setType(((JCContinue)node).type);
        // FIXME - need to repoint reference to target
    }

    public JCTree visitDoWhileLoop(DoWhileLoopTree node, Void p) {
        return super.visitDoWhileLoop(node,p).setType(((JCDoWhileLoop)node).type);
    }

    public JCTree visitErroneous(ErroneousTree node, Void p) {
        return super.visitErroneous(node,p).setType(((JCErroneous)node).type);
    }

    public JCTree visitExpressionStatement(ExpressionStatementTree node, Void p) {
        return super.visitExpressionStatement(node,p).setType(((JCExpressionStatement)node).type);
    }

    public JCTree visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
        return super.visitEnhancedForLoop(node,p).setType(((JCEnhancedForLoop)node).type);
    }

    public JCTree visitForLoop(ForLoopTree node, Void p) {
        return super.visitForLoop(node,p).setType(((JCForLoop)node).type);
    }

    public JCTree visitIdentifier(IdentifierTree node, Void p) {
        JCIdent id = (JCIdent)super.visitIdentifier(node,p).setType(((JCTree)node).type);
        id.sym = ((JCIdent)node).sym;
        return id;
    }

    public JCTree visitIf(IfTree node, Void p) {
        JCTree t = super.visitIf(node,p).setType(((JCTree)node).type);
        ((JmlIfStatement)t).split = ((JmlIfStatement)node).split;
        return t;
    }

    @Override
    public JCTree visitImport(ImportTree node, Void p) {
        JmlImport copy = (JmlImport)super.visitImport(node,p).setType(((JCTree)node).type);
        copy.isModel = ((JmlImport)node).isModel;
        // already done: copy.type = that.type;
        return copy;
    }
    
    public JCTree visitLambdaExpression(LambdaExpressionTree node, Void p) {
        return super.visitLambdaExpression(node,p).setType(((JCTree)node).type);
    }
    
    public JCTree visitArrayAccess(ArrayAccessTree node, Void p) {
        if (node instanceof JmlBBArrayAccess) {
            JmlBBArrayAccess n = (JmlBBArrayAccess)node;
            JmlBBArrayAccess nn = new JmlBBArrayAccess(copy(n.arraysId),copy(n.indexed),copy(n.index),n.pos,n.type);
            return nn;
        } else {
            return super.visitArrayAccess(node,p).setType(((JCTree)node).type);
        }
    }

    public JCTree visitLiteral(LiteralTree node, Void p) {
        return super.visitLiteral(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitMethod(MethodTree node, Void p) {
        JCTree t = super.visitMethod(node,p).setType(((JCTree)node).type);
        ((JCMethodDecl)t).sym = ((JCMethodDecl)node).sym;
        return t;
    }

    public JCTree visitMethodInvocation(MethodInvocationTree node, Void p) {
        JCMethodInvocation copy = (JCMethodInvocation)super.visitMethodInvocation(node,p).setType(((JCTree)node).type);
        copy.varargsElement = ((JCMethodInvocation)node).varargsElement; // FIXME - copy? - should be in super class
        return copy;
    }

    public JCTree visitModifiers(ModifiersTree node, Void p) {
        JmlModifiers copy = (JmlModifiers) super.visitModifiers(node,p).setType(((JCTree)node).type);
        copy.pos = ((JCModifiers)node).pos;
        copy.jmlmods = ((JmlModifiers)node).jmlmods;
        copy.anyModsInJava = ((JmlModifiers)node).anyModsInJava;
        return copy;
    }

    public JCTree visitNewArray(NewArrayTree node, Void p) {
        return super.visitNewArray(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitParenthesized(ParenthesizedTree node, Void p) {
        return super.visitParenthesized(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitReturn(ReturnTree node, Void p) {
        return super.visitReturn(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitMemberSelect(MemberSelectTree node, Void p) {
    	var fa = (JCFieldAccess)node;
    	JCTree t;
//		if (fa.sym != null) {
	        t = super.visitMemberSelect(node,p).setType(((JCTree)node).type);
	        ((JCFieldAccess)t).sym = fa.sym;
//		} else { // s can be null if we are visiting a package name  // FIXME - why do we need this if the super class doesn't
//			t = treeutils.makeSelect(fa.pos, fa.selected, fa.name).setType(fa.type);
//		}
		treeutils.copyEndPosition(t, fa);
        return t;
    }

    public JCTree visitEmptyStatement(EmptyStatementTree node, Void p) {
        return super.visitEmptyStatement(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitSwitch(SwitchTree node, Void p) {
        JCTree t = super.visitSwitch(node,p).setType(((JCTree)node).type);
        ((JmlSwitchStatement)t).split = ((JmlSwitchStatement)node).split;
        return t;
    }

    public JCTree visitSynchronized(SynchronizedTree node, Void p) {
        return super.visitSynchronized(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitThrow(ThrowTree node, Void p) {
        return super.visitThrow(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitCompilationUnit(CompilationUnitTree node, Void p) {
    	JmlCompilationUnit that = (JmlCompilationUnit)node;
        JmlCompilationUnit copy = (JmlCompilationUnit)super.visitCompilationUnit(that,p);
        copy.pid = copy(that.pid, p); // FIXME - point to the copied decl
        copy.sourcefile = that.sourcefile;
        copy.specsCompilationUnit = that == that.specsCompilationUnit ? copy : copy(that.specsCompilationUnit);
        copyEndPos(copy,(JCTree)node,copy.sourcefile);
//       copy.mode = that.mode;
//        copy.parsedTopLevelModelTypes = that.parsedTopLevelModelTypes; // FIXME - copy
//        copy.specsTopLevelModelTypes = that.specsTopLevelModelTypes;// FIXME - copy
        copy.type = that.type;
        return copy;
    }

    public JCTree visitModifiers(JCModifiers node, Void p) {
        var copy = (JmlModifiers)super.visitModifiers(node,p);
        for (var t: ((JmlModifiers)node).jmlmods) {
        	copy.add(t.copy());
        }
        copy.anyModsInJava = ((JmlModifiers)node).anyModsInJava;
        return copy;
    }

    public JCTree visitTry(TryTree node, Void p) {
        return super.visitTry(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitParameterizedType(ParameterizedTypeTree node, Void p) {
        return super.visitParameterizedType(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitArrayType(ArrayTypeTree node, Void p) {
        return super.visitArrayType(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitTypeCast(TypeCastTree node, Void p) {
        return super.visitTypeCast(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitPrimitiveType(PrimitiveTypeTree node, Void p) {
        return super.visitPrimitiveType(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitTypeParameter(TypeParameterTree node, Void p) {
        return super.visitTypeParameter(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitInstanceOf(InstanceOfTree node, Void p) {
        return super.visitInstanceOf(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitUnary(UnaryTree node, Void p) {
        JCTree t = super.visitUnary(node,p).setType(((JCTree)node).type);
        ((JCUnary)t).operator = ((JCUnary)node).operator;
        return t;
    }

    public JCTree visitVariable(VariableTree node, Void p) {
        JCTree t = super.visitVariable(node,p).setType(((JCTree)node).type);
        ((JCVariableDecl)t).sym = ((JCVariableDecl)node).sym;
        return t;
    }

    public JCTree visitWhileLoop(WhileLoopTree node, Void p) {
        return super.visitWhileLoop(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitWildcard(WildcardTree node, Void p) {
        return super.visitWildcard(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitOther(Tree node, Void p) {
        return super.visitOther(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitLetExpr(LetExpr that, Void p) {
        LetExpr let = (that instanceof JmlLetExpr) ?  M.JmlLetExpr(copy(that.defs,p), copy(that.expr,p), ((JmlLetExpr)that).explicit): M.LetExpr(copy(that.defs,p), copy(that.expr,p));
        let.pos = that.pos;
        let.type = that.type;
        return let;
    }
}
