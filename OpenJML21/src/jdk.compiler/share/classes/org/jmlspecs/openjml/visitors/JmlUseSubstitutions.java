package org.jmlspecs.openjml.visitors;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.ext.Operators;
import org.jmlspecs.openjml.ext.SetStatement;

import static org.jmlspecs.openjml.ext.RecommendsClause.*;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

public class JmlUseSubstitutions extends JmlTreeTranslator {
    
    final public Context context;

    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    final public JmlTreeUtils treeutils;

    /** Cached value of the symbol table */
    final public Symtab syms;

    /** Cached value of the Types tool */
    final public Types types;

    /** Cached value of the Log tool */
    final public Log log;

    /** Cached value of the AST node factory */
    final public JmlTree.Maker M;
    
    /** Cached value of JmlSpecs */
    final public JmlSpecs specs;
    
    /** Cached value of JmlSpecs */
    final public JmlTreeMatch matcher;
    
    /** Cached value of Utils */
    final public Utils utils;
    
    JmlTreeSubstitute subst;
    
    public JCExpression exprPrecondition  = null;
    public JCExpression exprHead  = null;
    public JCExpression exprTail  = null;

    public JmlUseSubstitutions(Context context) {
        copy = false;
        this.context = context;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.matcher = new JmlTreeMatch(context);
        this.utils = Utils.instance(context);
    }
    
    @SuppressWarnings("unchecked")
	@Override
    public JCTree translate(JCTree tree) {
        if (exprHead != null && tree != null && matcher.matches(tree,exprHead)) {
            // If exprHead is non null and matches the current tree, then we replace it with
            // exprTail. Then we set exprHead to null, so it is not used again.
            // That is we only do one substitution, whenever the next substitution is.
            // log.note(tree.pos, "jml.message", "Substituting here: " + exprHead.toString() + " with " + exprTail.toString() + " and precondition " + exprPrecondition.toString());
            if (matcher.assignOpMatch) {
                matcher.assignOpMatch = false;
                JCAssignOp t = (JCAssignOp)tree;
                return JmlTree.Maker.instance(context).at(tree.pos).Assign(t.lhs,exprTail);
            } else {
                exprPrecondition = null;
                exprHead = null;
                return exprTail;
            }
        } else {
            return super.translate(tree);
        }
    }
    
    @Override
    public void visitJmlStatement(JmlStatement that) {
        if (that.clauseType == SetStatement.setClause) {
            if (that.statement instanceof JCTree.JCExpressionStatement exec) {
                JCExpression expr = exec.expr;
                if (expr.type.getTag() == TypeTag.VOID
                    && expr instanceof JCTree.JCMethodInvocation apply
                    && JmlSpecs.instance(context).isSpecOKMethod((Symbol.MethodSymbol)TreeInfo.symbolFor(apply.meth))) {
                    //System.out.println("USING " + apply);
                    helper(that,expr);
                    return;
                }
            }
        }
        super.visitJmlStatement(that);
    }

    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        if (that.clauseType == useClause) {
            helper(that,that.expression);
        } else {
            super.visitJmlStatementExpr(that);
        }
    }
    
    public void helper(JCTree that, JCExpression expr) {
            if (expr instanceof JmlBinary imp && imp.op == Operators.impliesKind) {
                if (!(imp.rhs instanceof JCBinary && ((JCBinary)imp.rhs).getTag() == JCTree.Tag.EQ)) {
                    utils.error(expr, "jml.message", "Invalid kind of expression for a use statement; should be a lemma call, implication, or equality");
                    return;
                } else {
                    JCBinary eq = (JCBinary)imp.rhs;
                    exprPrecondition = imp.lhs;
                    exprHead = eq.lhs;
                    exprTail = eq.rhs;
                }
            } else if (expr instanceof JmlBinary bin && bin.op == Operators.equivalenceKind) {
                exprPrecondition = treeutils.trueLit;
                exprHead = bin.lhs;
                exprTail = bin.rhs;
            } else if (expr instanceof JCBinary bin && bin.getTag() == JCTree.Tag.EQ) {
                exprPrecondition = treeutils.trueLit;
                exprHead = bin.lhs;
                exprTail = bin.rhs;
            } else if (expr instanceof JCTree.JCMethodInvocation) {
                JCExpression meth = ((JCMethodInvocation)expr).meth;
                Symbol msym = treeutils.getSym(meth);
                if (!(msym instanceof Symbol.MethodSymbol)) {
                    utils.error(that,"jml.internal","No symbol found for " + meth.toString());
                    return;
                }

                JmlSpecs.MethodSpecs lemmaspecs = specs.getAttrSpecs((Symbol.MethodSymbol)msym);
                if (lemmaspecs == null) {
                    utils.error(that,"jml.internal","No symbol found for " + meth.toString());
                    return;
                }
                if (lemmaspecs.cases.cases.length() != 1) {
                    utils.error(that,"jml.message", "Only exactly one specification case is implemented for 'use' lemmas");
                    return;
                }
                List<JCVariableDecl> vd = lemmaspecs.cases.decl.params;
                Iterator<JCVariableDecl> iter = vd.iterator();
                Map<Object,JCExpression> replacements = new HashMap<>();
                for (JCExpression actualarg: ((JCMethodInvocation)expr).args) {
                    if (!iter.hasNext()) {
                        utils.error(that,"jml.message", "Mismatched argument lists");
                        return;
                    }
                    replacements.put(iter.next().sym, actualarg);
                }
                if (iter.hasNext()) {
                    utils.error(that,"jml.message", "Mismatched argument lists");
                    return;
                }
                subst = new JmlTreeSubstitute(context,M,replacements);

                exprPrecondition = exprHead = null;
                JmlSpecificationCase cs = lemmaspecs.cases.cases.head;
                for (JmlMethodClause cl: cs.clauses) {
                    IJmlClauseKind ct = cl.clauseKind;
                    if (ct == requiresClauseKind) {
                            expr = ((JmlMethodClauseExpr)cl).expression;
                            if (exprPrecondition != null) {
                                utils.error(cl,"jml.internal","Use lemmas currently implement only one requires clause");
                                return;
                            } else {
                                subst.replacements = replacements;
                                exprPrecondition = subst.copy(expr);
                            }
                    } else if (ct == ensuresClauseKind) {
                            expr = ((JmlMethodClauseExpr)cl).expression;
                            if (exprHead != null) {
                                utils.error(cl,"jml.internal","Use lemmas currently implement only one ensures clause");
                                return;
                            } else if (expr instanceof JCBinary && ((JCBinary)expr).getTag() == JCTree.Tag.EQ) {
                                JCBinary bin = (JCBinary)expr;
                                subst.replacements = replacements;
                                exprHead = subst.copy(bin.lhs);
                                exprTail = subst.copy(bin.rhs);
                            } else if (expr instanceof JmlBinary && ((JmlBinary)expr).op == Operators.impliesKind) {
                                JmlBinary bin = (JmlBinary)expr;
                                subst.replacements = replacements;
                                exprHead = subst.copy(bin.lhs);
                                exprTail = subst.copy(bin.rhs);
                            } else {
                                utils.error(cl,"jml.internal","Use lemma ensures clause must hold a == or ==> expression");
                                return;
                            }
                    } else {
                            utils.error(cl.sourcefile,cl,"jml.internal","Use lemmas currently implement only requires and ensures clauses: " + cl.keyword+ " in specs for " + msym.owner + "." + msym);
                            return;
                    }
//                    currentUse = M.at(that).JmlExpressionStatement(assertID, assertClause,Label.UNDEFINED_LEMMA,treeutils.trueLit);
//                    result = currentUse;
                }
                if (exprPrecondition != null && !treeutils.isTrueLit(exprPrecondition)) {
                    // Replace the use statement with the precondition check
                    result = M.at(that).JmlExpressionStatement(assertID, assertClause,Label.UNDEFINED_LEMMA,exprPrecondition);
                } else {
                    result = that;
                }
            } else {
                utils.error(expr, "jml.message", "Invalid kind of expression for a use statement; should be a lemma call, implication, or equality");
            }
    }
}
