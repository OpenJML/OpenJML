/*
 * This file is part of the OpenJML project.
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.util.ArrayList;

import org.jmlspecs.openjml.JmlTree.JmlChained;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.TreeInfo;

/**
 * The lower and upper bounds that the range of a quantified expression places on its (single,
 * integral) variable x: the comparisons, among the conjuncts of the range, that have x alone on
 * one side and do not mention x on the other, as in 0 <= x < a.length (a chained comparison is
 * split into its conjuncts). Used for the well-definedness of \max and \min (is the range
 * empty?) and for the recursive functions that translate \sum, \product and \num_of (over which
 * interval of x?).
 */
public class IntegerRangeBounds {

    /** A bound on x: x >= expr (or x > expr, if strict) for a lower bound, x <= expr (x < expr) for an upper one */
    public record Bound(JCExpression expr, boolean strict) {}

    /** The lower bounds on x */
    public final java.util.List<Bound> lower = new ArrayList<>();

    /** The upper bounds on x */
    public final java.util.List<Bound> upper = new ArrayList<>();

    /** True if every conjunct of the range is one of the bounds, so the range is exactly
     * 'every lower bound <= x <= every upper bound'; false if there are other conjuncts */
    public boolean exact = true;

    /** The bounds that range places on x; range may be null (no bounds) */
    public static IntegerRangeBounds of(Symbol x, /*@ nullable */ JCExpression range) {
        IntegerRangeBounds b = new IntegerRangeBounds();
        if (range != null) b.addConjuncts(x, range);
        return b;
    }

    private void addConjuncts(Symbol x, JCExpression e) {
        e = TreeInfo.skipParens(e);
        if (e instanceof JCBinary b) {
            switch (b.getTag()) {
                case AND: case BITAND: // a chained comparison such as 0 <= x < n becomes 0 <= x & x < n
                    addConjuncts(x, b.lhs);
                    addConjuncts(x, b.rhs);
                    return;
                case LT: case LE: case GT: case GE:
                    if (addBound(x, b)) return;
                    break;
                default:
            }
        } else if (e instanceof JmlChained ch) {
            for (JCBinary b: ch.conjuncts) addConjuncts(x, b);
            return;
        } else if (e instanceof JCTree.JCLiteral lit && Boolean.TRUE.equals(lit.getValue())) {
            return;
        }
        exact = false;
    }

    /** Records the comparison c if it bounds x; returns false if it does not */
    private boolean addBound(Symbol x, JCBinary c) {
        JCExpression lhs = TreeInfo.skipParens(c.lhs), rhs = TreeInfo.skipParens(c.rhs);
        boolean xLeft = lhs instanceof JCIdent id && id.sym == x && !mentions(rhs, x);
        boolean xRight = rhs instanceof JCIdent id && id.sym == x && !mentions(lhs, x);
        if (xLeft == xRight) return false;
        JCExpression other = xLeft ? rhs : lhs;
        boolean strict = c.hasTag(JCTree.Tag.LT) || c.hasTag(JCTree.Tag.GT);
        boolean isUpper = (c.hasTag(JCTree.Tag.LT) || c.hasTag(JCTree.Tag.LE)) == xLeft; // x < other, or other > x
        (isUpper ? upper : lower).add(new Bound(other, strict));
        return true;
    }

    /** Whether e is a literal equal to the least or greatest value of int or long (possibly negated or
     * cast); the range of a quantified variable's type, conjoined to every range, gives such bounds,
     * which are too far apart for a recursive function over the range */
    public static boolean isTypeExtreme(JCExpression e) {
        while (e instanceof JCTree.JCTypeCast c) e = c.expr;
        if (e instanceof JCTree.JCUnary u && u.hasTag(JCTree.Tag.NEG)) e = u.arg;
        if (!(e instanceof JCTree.JCLiteral lit) || !(lit.getValue() instanceof Number n)) return false;
        long v = n.longValue();
        return v == Integer.MIN_VALUE || v == Integer.MAX_VALUE || v == Long.MIN_VALUE || v == Long.MAX_VALUE
                || v == -(long)Integer.MIN_VALUE;
    }

    /** Whether the bounds, apart from those of a type's range, bound x both below and above -- the
     * condition for translating \sum, \product and \num_of over x into a recursive function */
    public boolean boundsRecursion() {
        return lower.stream().anyMatch(b -> !isTypeExtreme(b.expr())) && upper.stream().anyMatch(b -> !isTypeExtreme(b.expr()));
    }

    /** Whether e mentions the variable sym */
    public static boolean mentions(JCExpression e, Symbol sym) {
        boolean[] found = { false };
        new JmlTreeScanner() {
            @Override
            public void visitIdent(JCIdent id) { if (id.sym == sym) found[0] = true; }
        }.scan(e);
        return found[0];
    }
}
