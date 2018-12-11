package org.jmlspecs.openjml;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.walkers.JmlTreeMatch;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
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
    
    JmlTreeSubstitute subst;
    
    public JCExpression exprPrecondition  = null;
    public JCExpression exprHead  = null;
    public JCExpression exprTail  = null;
    public JmlStatementExpr currentUse = null;

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
    }
    
    @Override
    public JCTree translate(JCTree tree) {
        if (exprHead != null && tree != null && matcher.matches(tree,exprHead)) {
            // log.note(tree.pos, "jml.message", "Substituting here: " + exprHead.toString() + " with " + exprTail.toString() + " and precondition " + exprPrecondition.toString());
            currentUse = null;
            exprPrecondition = null;
            exprHead = null;
            return exprTail;
        } else {
            return super.translate(tree);
        }
    }

    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        if (that.token == DefaultJmlTokenKind.USE) {
            JCExpression expr = that.expression;
            if (expr instanceof JmlBinary && ((JmlBinary)expr).op == DefaultJmlTokenKind.IMPLIES) {
                JmlBinary imp = (JmlBinary)expr;
                if (!(imp.rhs instanceof JCBinary && ((JCBinary)imp.rhs).getTag() == JCTree.Tag.EQ)) {
                    log.error(expr, "jml.message", "Invalid kind of expression for a use statement; should be a lemma call, implication, or equality");
                    return;
                } else {
                    JCBinary eq = (JCBinary)imp.rhs;
                    exprPrecondition = imp.lhs;
                    exprHead = eq.lhs;
                    exprTail = eq.rhs;
                    currentUse = that;
                }
            } else if (expr instanceof JCBinary && ((JCBinary)expr).getTag() == JCTree.Tag.EQ) {
                JCBinary eq = (JCBinary)expr;
                exprPrecondition = treeutils.trueLit;
                exprHead = eq.lhs;
                exprTail = eq.rhs;
                currentUse = that;
            } else if (expr instanceof JCTree.JCMethodInvocation) {
                JCExpression meth = ((JCMethodInvocation)expr).meth;
                Symbol msym = treeutils.getSym(meth);
                if (!(msym instanceof Symbol.MethodSymbol)) {
                    log.error(that,"jml.internal","No symbol found for " + meth.toString());
                    return;
                }

                JmlSpecs.MethodSpecs lemmaspecs = specs.getSpecs((Symbol.MethodSymbol)msym);
                if (lemmaspecs == null) {
                    log.error(that,"jml.internal","No symbol found for " + meth.toString());
                    return;
                }
                if (lemmaspecs.cases.cases.length() != 1) {
                    log.error(that,"jml.message", "Only exactly one specification case is implemented for 'use' lemmas");
                    return;
                }
                List<JCVariableDecl> vd = lemmaspecs.cases.decl.params;
                Iterator<JCVariableDecl> iter = vd.iterator();
                Map<Object,JCExpression> replacements = new HashMap<>();
                for (JCExpression actualarg: ((JCMethodInvocation)expr).args) {
                    if (!iter.hasNext()) {
                        log.error(that,"jml.message", "Mismatched argument lists");
                        return;
                    }
                    replacements.put(iter.next().sym, actualarg);
                }
                if (iter.hasNext()) {
                    log.error(that,"jml.message", "Mismatched argument lists");
                    return;
                }
                subst = new JmlTreeSubstitute(context,M,replacements);

                exprPrecondition = exprHead = null;
                JmlSpecificationCase cs = lemmaspecs.cases.cases.head;
                for (JmlMethodClause cl: cs.clauses) {
                    switch ((DefaultJmlTokenKind) cl.token) {
                        case REQUIRES:
                            expr = ((JmlMethodClauseExpr)cl).expression;
                            if (exprPrecondition != null) {
                                log.error(cl,"jml.internal","Use lemmas currently implement only one requires clause");
                                return;
                            } else {
                                subst.replacements = replacements;
                                exprPrecondition = subst.copy(expr);
                            }
                            break;
                        case ENSURES:
                            expr = ((JmlMethodClauseExpr)cl).expression;
                            if (exprHead != null) {
                                log.error(cl,"jml.internal","Use lemmas currently implement only one ensures clause");
                                return;
                            } else if (expr instanceof JCBinary && ((JCBinary)expr).getTag() == JCTree.Tag.EQ) {
                                JCBinary bin = (JCBinary)expr;
                                subst.replacements = replacements;
                                exprHead = subst.copy(bin.lhs);
                                exprTail = subst.copy(bin.rhs);
                            } else if (expr instanceof JmlBinary && ((JmlBinary)expr).op == DefaultJmlTokenKind.IMPLIES) {
                                JmlBinary bin = (JmlBinary)expr;
                                subst.replacements = replacements;
                                exprHead = subst.copy(bin.lhs);
                                exprTail = subst.copy(bin.rhs);
                            } else {
                                log.error(cl,"jml.internal","Use lemma ensures clause must hold a == or ==> expression");
                                return;
                            }
                            break;
                        default:
                            log.error(cl,"jml.internal","Use lemmas currently implement only requires and ensures clauses: " + cl.token.internedName());
                            return;
                    }
                    currentUse = that;
                    if (exprPrecondition == null) exprPrecondition = treeutils.trueLit;
                    result = M.at(that).JmlExpressionStatement(DefaultJmlTokenKind.ASSERT,Label.UNDEFINED_LEMMA,treeutils.trueLit);
                    result = currentUse;
                }
            } else {
                log.error(expr, "jml.message", "Invalid kind of expression for a use statement; should be a lemma call, implication, or equality");
            }
        } else {
            super.visitJmlStatementExpr(that);
        }
    }
}
