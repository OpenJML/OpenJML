package org.jmlspecs.openjml.esc;

import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;

import com.sun.tools.javac.code.TypeTag;

/** The --fpreal model of float and double: a value of the SMT sort |#FpReal#| is NaN, an infinity, a signed zero,
 * or a nonzero real (|#fpVal#| r). Arithmetic on reals is exact: there is no rounding, overflow or underflow, so
 * float and double share the sort. Each Java operation is a define-fun in the prelude that handles the special
 * values as IEEE 754 does. Two encodings of the sort are available (--fpreal-encoding): 'uf', with uninterpreted
 * sorts and functions and axioms, for solvers without datatypes; and 'datatype', an SMT datatype. In both, SMT
 * equality on the sort is identity of Java values (aside from NaN payloads). */
public class FpRealModel {

    final SMTTranslator tr;
    final boolean datatype;
    boolean declared = false;

    public static final String SORT = "|#FpReal#|";
    public static final String NAN = "|#fpNaN#|", PINF = "|#fpPInf#|", NINF = "|#fpNInf#|", PZERO = "|#fpPZero#|", NZERO = "|#fpNZero#|";
    public static final String VAL = "|#fpVal#|", VALUE = "|#fpValue#|";

    public FpRealModel(SMTTranslator tr, boolean datatype) {
        this.tr = tr;
        this.datatype = datatype;
    }

    public ISort sort() {
        declare();
        return tr.F.createSortExpression(tr.F.symbol(SORT));
    }

    IExpr sym(String s) {
        return tr.F.symbol(s);
    }

    IExpr app(String f, IExpr... args) {
        declare();
        return tr.F.fcn(tr.F.symbol(f), args);
    }

    void add(String command) {
        tr.startCommands.add(tr.command(tr.smt, command));
    }

    /** Adds the prelude to the script, once */
    protected void declare() {
        if (declared) return;
        declared = true;
        tr.addReal();
        String F = SORT;
        if (datatype) {
            // A finite value is |#fpFin#| r negz; it is built only as |#fpFin#| r false or as a zero, so every built
            // value meets the axiom below by construction (an axiom excluding a built junk value would also
            // apply to the junk term in an untaken ite branch). Equality with a constructor rather than a tester,
            // since cvc5 does not accept a quoted constructor name in (_ is C).
            add("(declare-datatypes ((" + F + " 0)) (((" + NAN + ") (" + PINF + ") (" + NINF + ") (|#fpFin#| (" + VALUE + " Real) (|#fpNegZ#| Bool)))))");
            add("(define-fun " + PZERO + " () " + F + " (|#fpFin#| 0.0 false))");
            add("(define-fun " + NZERO + " () " + F + " (|#fpFin#| 0.0 true))");
            add("(define-fun " + VAL + " ((r Real)) " + F + " (|#fpFin#| r false))");
            add("(define-fun |#fpIsNaN#| ((a " + F + ")) Bool (= a " + NAN + "))");
            add("(define-fun |#fpIsPInf#| ((a " + F + ")) Bool (= a " + PINF + "))");
            add("(define-fun |#fpIsNInf#| ((a " + F + ")) Bool (= a " + NINF + "))");
            add("(define-fun |#fpIsFin#| ((a " + F + ")) Bool (not (or (= a " + NAN + ") (= a " + PINF + ") (= a " + NINF + "))))");
            add("(define-fun |#fpIsPZero#| ((a " + F + ")) Bool (and (|#fpIsFin#| a) (= (" + VALUE + " a) 0.0) (not (|#fpNegZ#| a))))");
            add("(define-fun |#fpIsNZero#| ((a " + F + ")) Bool (and (|#fpIsFin#| a) (= (" + VALUE + " a) 0.0) (|#fpNegZ#| a)))");
            add("(define-fun |#fpIsVal#| ((a " + F + ")) Bool (and (|#fpIsFin#| a) (not (= (" + VALUE + " a) 0.0))))");
            // Only a zero has a sign flag, so SMT equality is identity
            add("(assert (forall ((a " + F + ")) (! (=> (|#fpIsVal#| a) (not (|#fpNegZ#| a))) :pattern ((|#fpNegZ#| a)) :pattern ((" + VALUE + " a)))))");
        } else {
            String K = "|#FpKind#|";
            String[] kinds = { "|#FP_NAN#|", "|#FP_PINF#|", "|#FP_NINF#|", "|#FP_PZERO#|", "|#FP_NZERO#|", "|#FP_VALUE#|" };
            add("(declare-sort " + F + " 0)");
            add("(declare-sort " + K + " 0)");
            for (String k: kinds) add("(declare-fun " + k + " () " + K + ")");
            add("(assert (distinct " + String.join(" ", kinds) + "))");
            add("(declare-fun |#fpKind#| (" + F + ") " + K + ")");
            add("(declare-fun " + VALUE + " (" + F + ") Real)");
            add("(declare-fun " + VAL + " (Real) " + F + ")");
            String[] consts = { NAN, PINF, NINF, PZERO, NZERO };
            for (int i = 0; i < consts.length; i++) {
                add("(declare-fun " + consts[i] + " () " + F + ")");
                add("(assert (= (|#fpKind#| " + consts[i] + ") " + kinds[i] + "))");
            }
            add("(assert (= (" + VALUE + " " + PZERO + ") 0.0))");
            add("(assert (= (" + VALUE + " " + NZERO + ") 0.0))");
            add("(define-fun |#fpIsNaN#| ((a " + F + ")) Bool (= (|#fpKind#| a) |#FP_NAN#|))");
            add("(define-fun |#fpIsPInf#| ((a " + F + ")) Bool (= (|#fpKind#| a) |#FP_PINF#|))");
            add("(define-fun |#fpIsNInf#| ((a " + F + ")) Bool (= (|#fpKind#| a) |#FP_NINF#|))");
            add("(define-fun |#fpIsPZero#| ((a " + F + ")) Bool (= (|#fpKind#| a) |#FP_PZERO#|))");
            add("(define-fun |#fpIsNZero#| ((a " + F + ")) Bool (= (|#fpKind#| a) |#FP_NZERO#|))");
            add("(define-fun |#fpIsVal#| ((a " + F + ")) Bool (= (|#fpKind#| a) |#FP_VALUE#|))");
            // |#fpVal#| r is the value r, for nonzero r
            add("(assert (forall ((r Real)) (! (=> (not (= r 0.0)) (and (|#fpIsVal#| (" + VAL + " r)) (= (" + VALUE + " (" + VAL + " r)) r))) :pattern ((" + VAL + " r)))))");
            // Every value has one of the kinds and is the constant or nonzero real of its kind, so SMT equality is identity
            add("(assert (forall ((a " + F + ")) (! (and (or (|#fpIsNaN#| a) (|#fpIsPInf#| a) (|#fpIsNInf#| a) (|#fpIsPZero#| a) (|#fpIsNZero#| a) (|#fpIsVal#| a))"
                    + " (=> (|#fpIsVal#| a) (not (= (" + VALUE + " a) 0.0)))"
                    + " (= a (ite (|#fpIsNaN#| a) " + NAN + " (ite (|#fpIsPInf#| a) " + PINF + " (ite (|#fpIsNInf#| a) " + NINF
                    + " (ite (|#fpIsPZero#| a) " + PZERO + " (ite (|#fpIsNZero#| a) " + NZERO + " (" + VAL + " (" + VALUE + " a)))))))))"
                    + " :pattern ((|#fpKind#| a)) :pattern ((" + VALUE + " a)))))");
        }
        String a = "((a " + F + "))", ab = "((a " + F + ") (b " + F + "))";
        // Derived predicates; a NaN has no sign
        add("(define-fun |#fpIsInf#| " + a + " Bool (or (|#fpIsPInf#| a) (|#fpIsNInf#| a)))");
        add("(define-fun |#fpIsZero#| " + a + " Bool (or (|#fpIsPZero#| a) (|#fpIsNZero#| a)))");
        add("(define-fun |#fpIsFinite#| " + a + " Bool (or (|#fpIsZero#| a) (|#fpIsVal#| a)))");
        add("(define-fun |#fpIsNeg#| " + a + " Bool (or (|#fpIsNInf#| a) (|#fpIsNZero#| a) (and (|#fpIsVal#| a) (< (" + VALUE + " a) 0.0))))");
        add("(define-fun |#fpXorNeg#| " + ab + " Bool (not (= (|#fpIsNeg#| a) (|#fpIsNeg#| b))))");
        // The finite value r, with the sign 'neg' if it is zero
        add("(define-fun |#fpOf#| ((r Real) (neg Bool)) " + F + " (ite (= r 0.0) (ite neg " + NZERO + " " + PZERO + ") (" + VAL + " r)))");
        add("(define-fun |#fpInfOf#| ((neg Bool)) " + F + " (ite neg " + NINF + " " + PINF + "))");
        add("(define-fun |#fpZeroOf#| ((neg Bool)) " + F + " (ite neg " + NZERO + " " + PZERO + "))");
        // Arithmetic
        add("(define-fun |#fpNeg#| " + a + " " + F + " (ite (|#fpIsNaN#| a) " + NAN + " (ite (|#fpIsPInf#| a) " + NINF + " (ite (|#fpIsNInf#| a) " + PINF
                + " (ite (|#fpIsPZero#| a) " + NZERO + " (ite (|#fpIsNZero#| a) " + PZERO + " (" + VAL + " (- (" + VALUE + " a)))))))))");
        add("(define-fun |#fpAdd#| " + ab + " " + F + " (ite (or (|#fpIsNaN#| a) (|#fpIsNaN#| b) (and (|#fpIsPInf#| a) (|#fpIsNInf#| b)) (and (|#fpIsNInf#| a) (|#fpIsPInf#| b))) " + NAN
                + " (ite (or (|#fpIsPInf#| a) (|#fpIsPInf#| b)) " + PINF + " (ite (or (|#fpIsNInf#| a) (|#fpIsNInf#| b)) " + NINF
                + " (|#fpOf#| (+ (" + VALUE + " a) (" + VALUE + " b)) (and (|#fpIsNZero#| a) (|#fpIsNZero#| b)))))))");
        add("(define-fun |#fpSub#| " + ab + " " + F + " (|#fpAdd#| a (|#fpNeg#| b)))");
        add("(define-fun |#fpMul#| " + ab + " " + F + " (ite (or (|#fpIsNaN#| a) (|#fpIsNaN#| b) (and (|#fpIsInf#| a) (|#fpIsZero#| b)) (and (|#fpIsZero#| a) (|#fpIsInf#| b))) " + NAN
                + " (ite (or (|#fpIsInf#| a) (|#fpIsInf#| b)) (|#fpInfOf#| (|#fpXorNeg#| a b))"
                + " (|#fpOf#| (* (" + VALUE + " a) (" + VALUE + " b)) (|#fpXorNeg#| a b)))))");
        add("(define-fun |#fpDiv#| " + ab + " " + F + " (ite (or (|#fpIsNaN#| a) (|#fpIsNaN#| b) (and (|#fpIsInf#| a) (|#fpIsInf#| b)) (and (|#fpIsZero#| a) (|#fpIsZero#| b))) " + NAN
                + " (ite (or (|#fpIsInf#| a) (|#fpIsZero#| b)) (|#fpInfOf#| (|#fpXorNeg#| a b))"
                + " (ite (or (|#fpIsInf#| b) (|#fpIsZero#| a)) (|#fpZeroOf#| (|#fpXorNeg#| a b))"
                + " (" + VAL + " (/ (" + VALUE + " a) (" + VALUE + " b)))))))");
        // Java's %: the quotient is truncated toward zero; the result has the sign of a
        add("(define-fun |#fpTrunc#| ((r Real)) Real (ite (>= r 0.0) (to_real (to_int r)) (- (to_real (to_int (- r))))))");
        add("(define-fun |#fpRem#| " + ab + " " + F + " (ite (or (|#fpIsNaN#| a) (|#fpIsNaN#| b) (|#fpIsInf#| a) (|#fpIsZero#| b)) " + NAN
                + " (ite (or (|#fpIsInf#| b) (|#fpIsZero#| a)) a"
                + " (|#fpOf#| (- (" + VALUE + " a) (* (" + VALUE + " b) (|#fpTrunc#| (/ (" + VALUE + " a) (" + VALUE + " b))))) (|#fpIsNeg#| a)))))");
        // Comparisons: Java's == (IEEE equality: NaN is unequal to everything, the zeros are equal) and <
        add("(define-fun |#fpEq#| " + ab + " Bool (and (not (|#fpIsNaN#| a)) (not (|#fpIsNaN#| b)) (ite (and (|#fpIsFinite#| a) (|#fpIsFinite#| b)) (= (" + VALUE + " a) (" + VALUE + " b)) (= a b))))");
        add("(define-fun |#fpLt#| " + ab + " Bool (and (not (|#fpIsNaN#| a)) (not (|#fpIsNaN#| b)) (or (and (|#fpIsNInf#| a) (not (|#fpIsNInf#| b))) (and (|#fpIsPInf#| b) (not (|#fpIsPInf#| a)))"
                + " (and (|#fpIsFinite#| a) (|#fpIsFinite#| b) (< (" + VALUE + " a) (" + VALUE + " b))))))");
        add("(define-fun |#fpLe#| " + ab + " Bool (or (|#fpLt#| a b) (|#fpEq#| a b)))");
        // Library methods
        add("(define-fun |#fpAbs#| " + a + " " + F + " (ite (|#fpIsNaN#| a) " + NAN + " (ite (|#fpIsInf#| a) " + PINF + " (ite (|#fpIsZero#| a) " + PZERO
                + " (" + VAL + " (ite (< (" + VALUE + " a) 0.0) (- (" + VALUE + " a)) (" + VALUE + " a)))))))");
        // floor, ceil and rint of a finite value; a zero result has the sign of the argument
        add("(define-fun |#fpFloorR#| ((r Real)) Real (to_real (to_int r)))");
        add("(define-fun |#fpRintR#| ((r Real)) Real (let ((f (|#fpFloorR#| r))) (ite (< (- r f) 0.5) f (ite (> (- r f) 0.5) (+ f 1.0) (ite (= (mod (to_int f) 2) 0) f (+ f 1.0))))))");
        add("(define-fun |#fpFloor#| " + a + " " + F + " (ite (|#fpIsVal#| a) (|#fpOf#| (|#fpFloorR#| (" + VALUE + " a)) (|#fpIsNeg#| a)) a))");
        add("(define-fun |#fpCeil#| " + a + " " + F + " (ite (|#fpIsVal#| a) (|#fpOf#| (- (|#fpFloorR#| (- (" + VALUE + " a)))) (|#fpIsNeg#| a)) a))");
        add("(define-fun |#fpRint#| " + a + " " + F + " (ite (|#fpIsVal#| a) (|#fpOf#| (|#fpRintR#| (" + VALUE + " a)) (|#fpIsNeg#| a)) a))");
        // a with the sign of b; a NaN sign argument counts as positive, as in StrictMath
        add("(define-fun |#fpCopySign#| " + ab + " " + F + " (ite (|#fpIsNeg#| b) (|#fpNeg#| (|#fpAbs#| a)) (|#fpAbs#| a)))");
        // NaN if either is; -0.0 is less than +0.0
        add("(define-fun |#fpMin#| " + ab + " " + F + " (ite (|#fpIsNaN#| a) a (ite (|#fpIsNaN#| b) b (ite (|#fpLt#| a b) a (ite (|#fpLt#| b a) b (ite (|#fpIsNeg#| a) a b))))))");
        add("(define-fun |#fpMax#| " + ab + " " + F + " (ite (|#fpIsNaN#| a) a (ite (|#fpIsNaN#| b) b (ite (|#fpLt#| a b) b (ite (|#fpLt#| b a) a (ite (|#fpIsNeg#| a) b a))))))");
    }

    /** The constant for the Java value d */
    public IExpr literal(double d) {
        declare();
        if (Double.isNaN(d)) return sym(NAN);
        if (Double.isInfinite(d)) return sym(d > 0 ? PINF : NINF);
        if (d == 0) return sym(Double.compare(d, 0.0) < 0 ? NZERO : PZERO);
        return app(VAL, real(d));
    }

    /** The exact value of the finite double d, as an SMT real */
    IExpr real(double d) {
        String s = new java.math.BigDecimal(d).abs().toPlainString();
        if (!s.contains(".")) s += ".0";
        IExpr e = tr.F.decimal(s);
        return d < 0 ? tr.F.fcn(tr.F.symbol("-"), e) : e;
    }

    /** The translation of a binary operation on float or double operands (already of the sort); ieee says whether
     * == and != are Java's (IEEE) comparisons rather than identity */
    public IExpr binary(com.sun.tools.javac.tree.JCTree.Tag op, boolean ieee, IExpr lhs, IExpr rhs) {
        switch (op) {
            case EQ: return ieee ? app("|#fpEq#|", lhs, rhs) : tr.F.fcn(tr.eqSym, lhs, rhs);
            case NE: return ieee ? tr.F.fcn(tr.notSym, app("|#fpEq#|", lhs, rhs)) : tr.F.fcn(tr.distinctSym, lhs, rhs);
            case LT: return app("|#fpLt#|", lhs, rhs);
            case LE: return app("|#fpLe#|", lhs, rhs);
            case GT: return app("|#fpLt#|", rhs, lhs);
            case GE: return app("|#fpLe#|", rhs, lhs);
            case PLUS: return app("|#fpAdd#|", lhs, rhs);
            case MINUS: return app("|#fpSub#|", lhs, rhs);
            case MUL: return app("|#fpMul#|", lhs, rhs);
            case DIV: return app("|#fpDiv#|", lhs, rhs);
            case MOD: return app("|#fpRem#|", lhs, rhs);
            default: return null;
        }
    }

    public IExpr neg(IExpr a) {
        return app("|#fpNeg#|", a);
    }

    /** The float or double for the real r (exact: \real and integral values convert without rounding) */
    public IExpr fromReal(IExpr r) {
        return app("|#fpOf#|", r, tr.F.symbol("false"));
    }

    /** The real value of a; unspecified (but a real) if a is NaN or infinite */
    public IExpr toReal(IExpr a) {
        return app(VALUE, a);
    }

    /** The float or double a converted to the integral type 'to' as Java converts it (JLS 5.1.3): NaN to 0, the
     * infinities to the extremes of the type, otherwise as a real is converted */
    public IExpr toIntegral(TypeTag to, IExpr a) {
        boolean isLong = to == TypeTag.LONG;
        IExpr r = tr.realToIntegral(to, toReal(a));
        if (!tr.useBV) {
            IExpr max = tr.F.symbol(isLong ? "|#max64#|" : "|#max32#|");
            IExpr min = tr.F.symbol(isLong ? "|#min64#|" : "|#min32#|");
            IExpr x = tr.F.fcn(tr.iteSym, app("|#fpIsNaN#|", a), tr.zero,
                    tr.F.fcn(tr.iteSym, app("|#fpIsPInf#|", a), max, tr.F.fcn(tr.iteSym, app("|#fpIsNInf#|", a), min, r)));
            return isLong || to == TypeTag.INT ? x : tr.narrowInt(to, x);
        }
        // Bit-vector integers: clamp the truncated value, then convert it
        int w = isLong ? 64 : 32;
        IExpr max = tr.numeral(isLong ? Long.MAX_VALUE : Integer.MAX_VALUE), min = tr.numeral(isLong ? Long.MIN_VALUE : Integer.MIN_VALUE);
        IExpr x = tr.F.fcn(tr.iteSym, app("|#fpIsNaN#|", a), tr.F.numeral(0),
                tr.F.fcn(tr.iteSym, tr.F.fcn(tr.F.symbol("or"), app("|#fpIsPInf#|", a), tr.F.fcn(tr.F.symbol(">"), r, max)), max,
                tr.F.fcn(tr.iteSym, tr.F.fcn(tr.F.symbol("or"), app("|#fpIsNInf#|", a), tr.F.fcn(tr.F.symbol("<"), r, min)), min, r)));
        IExpr bv = tr.intToBV(w, x);
        return isLong || to == TypeTag.INT ? bv : tr.castBV(to, TypeTag.INT, bv);
    }

    /** The float or double value of the integral expression e of type 'from' */
    public IExpr fromIntegral(TypeTag from, IExpr e) {
        if (tr.useBV) {
            // the signed (or, for char, unsigned) value of the bit-vector
            int w = tr.bits(from);
            IExpr nat = tr.F.fcn(tr.F.symbol("bv2nat"), e);
            if (from != TypeTag.CHAR) {
                IExpr negative = tr.F.fcn(tr.F.symbol("bvslt"), e, tr.integralConstant(from, 0));
                nat = tr.F.fcn(tr.iteSym, negative, tr.F.fcn(tr.F.symbol("-"), nat, tr.F.numeral(java.math.BigInteger.ONE.shiftLeft(w).toString())), nat);
            }
            e = nat;
        }
        return fromReal(tr.F.fcn(tr.F.symbol("to_real"), e));
    }

    boolean[] bitsDeclared = new boolean[2];
    int bitsCount = 0;

    /** The raw bit pattern (Float.floatToRawIntBits or Double.doubleToRawLongBits) of a. The bits of a non-NaN value
     * are a function of the value, with those of the infinities and zeros fixed; those of a NaN are only some NaN
     * pattern, separately at each occurrence (the index argument), since the model has one NaN (cf. #1047) */
    public IExpr rawBits(boolean isFloat, IExpr a) {
        declare();
        int k = isFloat ? 0 : 1;
        String raw = isFloat ? "|#fpRaw32#|" : "|#fpRaw64#|", bits = isFloat ? "|#fpBits32#|" : "|#fpBits64#|";
        if (!bitsDeclared[k]) {
            bitsDeclared[k] = true;
            TypeTag t = isFloat ? TypeTag.INT : TypeTag.LONG;
            String S = tr.useBV ? "(_ BitVec " + (isFloat ? 32 : 64) + ")" : "Int";
            String le = tr.useBV ? "bvsle" : "<=";
            java.util.function.LongFunction<String> c = v -> tr.integralConstant(t, v).toString();
            add("(declare-fun " + bits + " (" + SORT + ") " + S + ")");
            add("(declare-fun " + raw + " (" + SORT + " Int) " + S + ")");
            String pinf = c.apply(isFloat ? 0x7f800000 : 0x7ff0000000000000L), ninf = c.apply(isFloat ? 0xff800000 : 0xfff0000000000000L);
            String nzero = c.apply(isFloat ? 0x80000000 : 0x8000000000000000L);
            String b = "(" + bits + " x)", r = "(" + raw + " x k)";
            String range = tr.useBV ? "" : " (<= " + c.apply(isFloat ? Integer.MIN_VALUE : Long.MIN_VALUE) + " " + b + ") (<= " + b + " " + c.apply(isFloat ? Integer.MAX_VALUE : Long.MAX_VALUE) + ")";
            add("(assert (forall ((x " + SORT + ")) (! (and" + range + " (=> (|#fpIsPInf#| x) (= " + b + " " + pinf + ")) (=> (|#fpIsNInf#| x) (= " + b + " " + ninf + "))"
                    + " (=> (|#fpIsPZero#| x) (= " + b + " " + c.apply(0) + ")) (=> (|#fpIsNZero#| x) (= " + b + " " + nzero + "))) :pattern (" + b + "))))");
            // a NaN pattern: above +infinity, or (negative) above -infinity
            String nan = "(or (and (" + le + " " + c.apply(isFloat ? 0x7f800001 : 0x7ff0000000000001L) + " " + r + ") (" + le + " " + r + " " + c.apply(isFloat ? Integer.MAX_VALUE : Long.MAX_VALUE) + "))"
                    + " (and (" + le + " " + c.apply(isFloat ? 0xff800001 : 0xfff0000000000001L) + " " + r + ") (" + le + " " + r + " " + c.apply(-1) + ")))";
            add("(assert (forall ((x " + SORT + ") (k Int)) (! (ite (|#fpIsNaN#| x) " + nan + " (= " + r + " " + b + ")) :pattern (" + r + "))))");
        }
        return tr.F.fcn(tr.F.symbol(raw), a, tr.F.numeral(bitsCount++));
    }

    /** The translation of the java.lang.Double or Float method, or java.lang.Math or StrictMath method on float or
     * double arguments, 'name', if this model defines it exactly; or null */
    public /*@ nullable */ IExpr method(String owner, String name, List<IExpr> args) {
        boolean math = owner.equals("java.lang.Math") || owner.equals("java.lang.StrictMath");
        IExpr a = args.get(0);
        if (args.size() == 1) {
            if (math) {
                switch (name) {
                    case "abs": return app("|#fpAbs#|", a);
                    case "floor": return app("|#fpFloor#|", a);
                    case "ceil": return app("|#fpCeil#|", a);
                    case "rint": return app("|#fpRint#|", a);
                    default: return null;
                }
            }
            switch (name) {
                case "isNaN": return app("|#fpIsNaN#|", a);
                case "isInfinite": return app("|#fpIsInf#|", a);
                case "isFinite": return app("|#fpIsFinite#|", a);
                case "isPositiveZero": return app("|#fpIsPZero#|", a);
                case "isNegativeZero": return app("|#fpIsNZero#|", a);
                case "floatToRawIntBits": return rawBits(true, a);
                case "doubleToRawLongBits": return rawBits(false, a);
                default: return null;
            }
        } else if (args.size() == 2) {
            IExpr b = args.get(1);
            switch (name) {
                case "min": return app("|#fpMin#|", a, b);
                case "max": return app("|#fpMax#|", a, b);
                case "copySign": return math ? app("|#fpCopySign#|", a, b) : null;
                case "identical": return math ? null : tr.F.fcn(tr.eqSym, a, b);
                case "sum": return math ? null : app("|#fpAdd#|", a, b);
                case "compare": {
                    if (math) return null;
                    // Java's total order: -0.0 below +0.0, NaN equal to itself and above everything else
                    IExpr lt = tr.integralConstant(TypeTag.INT, -1), eq = tr.integralConstant(TypeTag.INT, 0), gt = tr.integralConstant(TypeTag.INT, 1);
                    IExpr nanA = app("|#fpIsNaN#|", a), nanB = app("|#fpIsNaN#|", b);
                    IExpr negA = app("|#fpIsNeg#|", a), negB = app("|#fpIsNeg#|", b);
                    var ite = tr.iteSym;
                    return tr.F.fcn(ite, nanA, tr.F.fcn(ite, nanB, eq, gt),
                            tr.F.fcn(ite, nanB, lt,
                            tr.F.fcn(ite, app("|#fpLt#|", a, b), lt,
                            tr.F.fcn(ite, app("|#fpLt#|", b, a), gt,
                            tr.F.fcn(ite, tr.F.fcn(tr.eqSym, negA, negB), eq, tr.F.fcn(ite, negA, lt, gt))))));
                }
                default: return null;
            }
        } else if (args.size() == 3 && math && name.equals("fma")) {
            // exact, as the real arithmetic is
            return app("|#fpAdd#|", app("|#fpMul#|", a, args.get(1)), args.get(2));
        }
        return null;
    }
}
