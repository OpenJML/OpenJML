package org.jmlspecs.openjml.ext;

import org.eclipse.jdt.annotation.Nullable;
import org.jmlspecs.openjml.IArithmeticMode;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.JmlType;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Names;

import org.jmlspecs.openjml.JmlOption;

abstract public class Arithmetic extends ExpressionExtension {
    
    
    public static enum Mode { MATH(false,false), SAFE(true,true), JAVA(true,false) ;
        
        private boolean wrapsAround;
        private boolean overflowWarnings;
        private Mode(boolean w, boolean o) {
            wrapsAround = w;
            overflowWarnings = o;
        }
        public boolean wrapsAround() { return wrapsAround;}
        public boolean overflowWarnings() { return overflowWarnings; }
    
    };
    
    public Arithmetic(Context context) {
        super(context);
        this.intType = Symtab.instance(context).intType;
    }
    
    Symbol codeBigintMath = null;
    Symbol codeSafeMath = null;
    Symbol codeJavaMath = null;
    Symbol specBigintMath = null;
    Symbol specJavaMath = null;
    Symbol specSafeMath = null;
    
    Type intType;
    
    boolean javaChecks;
    
    private void initModeSymbols() {
        if (codeBigintMath != null) return;
        ClassReader classReader = ClassReader.instance(context);
        Names names = Names.instance(context);
        specSafeMath = classReader.enterClass(names.fromString(Strings.jmlAnnotationPackage + ".SpecSafeMath"));
        specJavaMath = classReader.enterClass(names.fromString(Strings.jmlAnnotationPackage + ".SpecJavaMath"));
        specBigintMath = classReader.enterClass(names.fromString(Strings.jmlAnnotationPackage + ".SpecBigintMath"));
        codeSafeMath = classReader.enterClass(names.fromString(Strings.jmlAnnotationPackage + ".CodeSafeMath"));
        codeJavaMath = classReader.enterClass(names.fromString(Strings.jmlAnnotationPackage + ".CodeJavaMath"));
        codeBigintMath = classReader.enterClass(names.fromString(Strings.jmlAnnotationPackage + ".CodeBigintMath"));
    }
    
    public static boolean rac;
    
    public IArithmeticMode defaultArithmeticMode(Symbol sym, boolean jml) {
        initModeSymbols();
        if (!jml) {
            if (sym.attribute(codeBigintMath) != null) return Math.instance(context);
            if (sym.attribute(codeSafeMath) != null) return Safe.instance(context);
            if (sym.attribute(codeJavaMath) != null) return Java.instance(context);
            sym = sym.owner;
            if (!(sym instanceof Symbol.PackageSymbol)) return defaultArithmeticMode(sym,jml);
            String v = JmlOption.value(context,JmlOption.CODE_MATH);
            if ("java".equals(v)) return Java.instance(context);
            if ("safe".equals(v)) return Safe.instance(context);
            return Math.instance(context);
        } else {
            if (sym.attribute(specBigintMath) != null) return Math.instance(context);
            if (sym.attribute(specSafeMath) != null) return Safe.instance(context);
            if (sym.attribute(specJavaMath) != null) return Java.instance(context);
            sym = sym.owner;
            Arithmetic.Math.instance(context).rac = rac; // FIXME - HACK FOR NOW
            if (!(sym instanceof Symbol.PackageSymbol)) return defaultArithmeticMode(sym,jml);
            String v = JmlOption.value(context,JmlOption.SPEC_MATH);
            if ("java".equals(v)) return Java.instance(context);
            if ("safe".equals(v)) return Safe.instance(context);
            return Math.instance(context);
        }
    }
    
    public Type maxtype(JmlTypes jmltypes, Type lhs, Type rhs) {
        if (lhs.getTag() == TypeTag.CLASS) lhs = Types.instance(context).unboxedType(lhs); 
        if (rhs.getTag() == TypeTag.CLASS) rhs = Types.instance(context).unboxedType(rhs); 
        TypeTag lt = lhs.getTag();
        TypeTag rt = rhs.getTag(); // FIOXME - is the typetag UNKNOWN or NONE
        if (lt == TypeTag.UNKNOWN && lhs == jmltypes.REAL) return lhs;
        if (rt == TypeTag.UNKNOWN && rhs == jmltypes.REAL) return rhs;
        if (lt == TypeTag.UNKNOWN && lhs == jmltypes.BIGINT) {
            if (rt == TypeTag.DOUBLE || rt == TypeTag.FLOAT) return jmltypes.REAL;
            return lhs;
        }
        if (rt == TypeTag.UNKNOWN && rhs == jmltypes.BIGINT) {
            if (lt == TypeTag.DOUBLE || lt == TypeTag.FLOAT) return jmltypes.REAL;
            return rhs;
        }
        if (lt == TypeTag.DOUBLE) return lhs;
        if (rt == TypeTag.DOUBLE) return rhs;
        if (lt == TypeTag.FLOAT) return lhs; 
        if (rt == TypeTag.FLOAT) return rhs; 
        if (lt == TypeTag.LONG) return lhs; 
        if (rt == TypeTag.LONG) return rhs; 
        return intType;
    }

    
    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        checkOneArg(parser,e);
    }

    @Override
    public Type typecheck(JmlAttr attr, JCExpression expr,
            Env<AttrContext> env) {
        JmlMethodInvocation tree = (JmlMethodInvocation)expr;
        JmlTokenKind token = tree.token;
        
        // Expect one argument of any type, result type is the same type
        // The argument expression may contain JML constructs
        ListBuffer<Type> argtypesBuf = new ListBuffer<>();
        attr.attribArgs(tree.args, env, argtypesBuf);
        //attr.attribTypes(tree.typeargs, env);
        int n = tree.args.size();
        if (n != 1) {
            error(tree.pos(),"jml.one.arg",token.internedName(),n);
        }
        Type t = syms.errType;
        if (n > 0) {
            return tree.args.get(0).type;
        }
        return t;
    }
    /** Makes a expression appropriate to the given newtype and whether the translation
     *  is for rac or esc and whether it uses bit-vectors or not
     * @param rewriter the JmlAssertionAdder instance
     * @param that the original expression
     * @param arg the already translated argument
     * @param newtype the type in which to do the operation
     * @return
     */
    public JCExpression makeUnaryOp(JmlAssertionAdder rewriter, JCUnary that, Type newtype, boolean implementOverflow, boolean warnOverflow) {
        JCExpression arg = rewriter.convertExpr(that.getExpression());
        arg = rewriter.addImplicitConversion(arg,newtype,arg);
        JCTree.Tag optag = that.getTag();
        TypeTag typetag = that.type.getTag();
        JCExpression eresult = null;
//        if (arg instanceof JCLiteral) {
//            // NEG, POS, COMPL
//            Number n = (Number)((JCLiteral)arg).getValue();
//            if (typetag == TypeTag.INT) {
//                int v = n.intValue();
//                if (v != Integer.MIN_VALUE || optag != JCTree.Tag.NEG) {
//                    v = optag == JCTree.Tag.NEG ? -v : optag == JCTree.Tag.COMPL ? -1-v : v;
//                    return rewriter.treeutils.makeIntLiteral(that.pos,v);
//                }
//            } else if (typetag == TypeTag.LONG) {
//                long v = n.longValue();
//                if (v != Long.MIN_VALUE || optag != JCTree.Tag.NEG) {
//                    v = optag == JCTree.Tag.NEG ? -v : optag == JCTree.Tag.COMPL ? -1-v : v;
//                    return rewriter.treeutils.makeLongLiteral(that.pos,v);
//                }
//            }
//        }
        if (implementOverflow && !(arg instanceof JCLiteral)) {
            if (typetag == TypeTag.INT) {
                JCExpression maxlit = rewriter.treeutils.makeIntLiteral(arg, Integer.MAX_VALUE);
                JCExpression minlit = rewriter.treeutils.makeIntLiteral(arg, Integer.MIN_VALUE);
                JCExpression a = rewriter.makeBin(arg, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, minlit, rewriter.convertCopy(arg), newtype);
                JCExpression b = rewriter.makeBin(arg, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, rewriter.convertCopy(arg), maxlit, newtype);
                rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
            } else if (typetag == TypeTag.LONG) {
                JCExpression maxlit = rewriter.treeutils.makeLongLiteral(arg, Long.MAX_VALUE);
                JCExpression minlit = rewriter.treeutils.makeLongLiteral(arg, Long.MIN_VALUE);
                JCExpression a = rewriter.makeBin(arg, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, minlit, rewriter.convertCopy(arg), newtype);
                JCExpression b = rewriter.makeBin(arg, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, rewriter.convertCopy(arg), maxlit, newtype);
                rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
            }
        }
        if (warnOverflow && optag == JCTree.Tag.NEG && rewriter.jmltypes.isSameType(that.type,that.getExpression().type)) {
            if (typetag == TypeTag.INT) {
                JCExpression e = rewriter.treeutils.makeNot(arg.pos,rewriter.treeutils.makeEquality(arg.pos, rewriter.convertCopy(arg), rewriter.treeutils.makeIntLiteral(arg.pos, Integer.MIN_VALUE)));
                e = condition(rewriter,e);
                rewriter.addCheck(that,Label.ARITHMETIC_OP_RANGE,e,"(int negation)");
            } else if (typetag == TypeTag.LONG) {
                JCExpression e = rewriter.treeutils.makeNot(arg.pos,rewriter.treeutils.makeEquality(arg.pos, rewriter.convertCopy(arg), rewriter.treeutils.makeLit(arg.pos, that.type, Long.MIN_VALUE)));
                e = condition(rewriter,e);
                rewriter.addCheck(that,Label.ARITHMETIC_OP_RANGE,e,"(long negation)");
            }
        }
        if (rewriter.rac && rewriter.jmltypes.isJmlType(newtype)) {
            if (optag == JCTree.Tag.NEG){ 
                if (rewriter.jmltypes.isSameType(newtype, rewriter.jmltypes.BIGINT)) {
                    eresult = rewriter.treeutils.makeUtilsMethodCall(that.pos,"bigint_neg",rewriter.convertCopy(arg));
                }
                if (rewriter.jmltypes.isSameType(newtype, rewriter.jmltypes.REAL)) {
                    eresult = rewriter.treeutils.makeUtilsMethodCall(that.pos,"real_neg",rewriter.convertCopy(arg));
                }
            } else if (optag == JCTree.Tag.POS) {
                eresult = arg;
            } else if (optag == JCTree.Tag.COMPL) {
                // Assumed to be a bigint (not real) operation - equivalent to -1-x
                JCExpression e = rewriter.treeutils.makeUtilsMethodCall(that.pos,"bigint_neg",rewriter.convertCopy(arg));
                e = rewriter.treeutils.makeUtilsMethodCall(that.pos,"bigint_sub1",e);
                eresult = e;
            } else { 
                rewriter.log.error(that,"jml.internal","Unknown unary operation in Arithmetic.Java for JML type: " + that);
                eresult = arg;
            }
        } else {
            // Implement overflow when not using bit operations
            // RAC implements bit-limited arithmetic anyway, so don't need to do it here
            // If we have implicitly converted, which would be from a smaller type, then negate won't overflow
            if (optag == JCTree.Tag.POS) eresult = arg;
            else eresult = rewriter.treeutils.makeUnary(that.pos,optag,that.getOperator(),arg);
            if (implementOverflow && rewriter.esc && optag == JCTree.Tag.NEG && !rewriter.useBV && rewriter.jmltypes.isSameType(that.type,that.getExpression().type)) {
                // FIXME - when this was accidentally enabled for rac, the conditional expression did not work correctly; not sure why - perhaps shared ASTs?
                // result == (arg == MIN_VALUE ? MIN_VALUE : -arg) 
                if (typetag == TypeTag.INT) {
                    JCExpression lit = rewriter.treeutils.makeIntLiteral(that.pos, Integer.MIN_VALUE);
                    JCExpression eq = rewriter.treeutils.makeBinary(that.pos, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.convertCopy(arg), lit);
                    JCExpression conditional = rewriter.treeutils.makeConditional(that.pos, eq, lit, eresult);
                    eresult = conditional;
                } else if (typetag == TypeTag.LONG) {
                    JCExpression lit = rewriter.treeutils.makeLongLiteral(that.pos, Long.MIN_VALUE);
                    JCExpression eq = rewriter.treeutils.makeEquality(that.pos, rewriter.convertCopy(arg), lit);
                    JCExpression conditional = rewriter.treeutils.makeConditional(that.pos, eq, lit, eresult);
                    eresult = conditional;
                } else if (rewriter.jmltypes.isIntegral(that.type)) {
                    rewriter.log.error(that,"jml.internal","Unimplemented integral type in Arithmetic.Java: " + that.type);
                }
            }
        }
        return eresult;
    }
    
    public JCExpression condition(JmlAssertionAdder rewriter, JCExpression e) {
        return rewriter.conditionedAssertion(e, e);
    }
    
    public JCExpression makeBinaryOp(JmlAssertionAdder rewriter, JCBinary that, Type newtype, boolean implementOverflow, boolean checkOverflow, boolean alreadyConverted) {
        int p = that.pos;
        this.javaChecks = (rewriter.esc || (rewriter.rac && JmlOption.isOption(context,JmlOption.RAC_JAVA_CHECKS)));

        JCTree.Tag optag = that.getTag();
        if (newtype == null) newtype = that.type;
        
        JCExpression lhs = alreadyConverted ? that.getLeftOperand() : rewriter.convertExpr(that.getLeftOperand());
        JCExpression rhs = alreadyConverted ? that.getRightOperand() : rewriter.convertExpr(that.getRightOperand());

        // Need to do this operation before any implicit conversions, because those conversions may convert
        // to bigint or real, which complicates this test
        if (optag == JCTree.Tag.DIV || optag == JCTree.Tag.MOD) {
            @Nullable JCExpression nonzero = rewriter.nonZeroCheck(that,rhs);
            if (nonzero != null) rewriter.addJavaCheck(that,nonzero,
                    Label.POSSIBLY_DIV0, Label.UNDEFINED_DIV0, "java.lang.ArithmeticException");
        }
        
        
        if (!(rac && alreadyConverted)) {
            lhs = rewriter.addImplicitConversion(lhs,newtype,lhs);
            rhs = rewriter.addImplicitConversion(rhs,newtype,rhs);
        }
        
        // In MATH mode, the types can be promoted to \bigint or \real, even though the .type field is still smaller
        if (rewriter.jmltypes.isJmlType(lhs.type)) newtype = lhs.type;
        else if (rewriter.jmltypes.isJmlType(rhs.type)) newtype = rhs.type;
        
        if (implementOverflow && !rewriter.jmltypes.isJmlType(newtype)) {
            if (newtype.getTag() == TypeTag.INT) {
                JCExpression maxlit = rewriter.treeutils.makeIntLiteral(p, Integer.MAX_VALUE);
                JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                if (!(lhs instanceof JCLiteral)) {
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, minlit, rewriter.convertCopy(lhs), newtype);
                    JCExpression b = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, rewriter.convertCopy(lhs), maxlit, newtype);
                    rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
                }
                if (!(rhs instanceof JCLiteral)) {
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, minlit, rewriter.convertCopy(rhs), newtype);
                    JCExpression b = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, rewriter.convertCopy(rhs), maxlit, newtype);
                    rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
                }
            } else if (newtype.getTag() == TypeTag.LONG) {
                JCExpression maxlit = rewriter.treeutils.makeLongLiteral(p, Long.MAX_VALUE);
                JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                if (!(lhs instanceof JCLiteral)) {
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, minlit, rewriter.convertCopy(lhs), newtype);
                    JCExpression b = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, rewriter.convertCopy(lhs), maxlit, newtype);
                    rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
                }
                if (!(rhs instanceof JCLiteral)) {
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, minlit, rewriter.convertCopy(rhs), newtype);
                    JCExpression b = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, rewriter.convertCopy(rhs), maxlit, newtype);
                    rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
                }
            }
        }

        TypeTag typetag = newtype.getTag();
        
        boolean smtPredefined = true;
        // Check for overflows
        if (checkOverflow) {
            // The overflow checks have to work whether integers are eventually encoded as fixed length bit vectors or as mathematical values
            if (optag == JCTree.Tag.PLUS || optag == JCTree.Tag.MINUS) {
                // For + : a > 0 && b > 0 ==> a <= MAX - b; a < 0 && b < 0 ==> MIN - b <= a;
                // For - : a > 0 && b < 0 ==> a <= MAX + b; a < 0 && b > 0 ==> MIN + b <= a;
                JCTree.Tag optagn = optag == JCTree.Tag.PLUS ? JCTree.Tag.MINUS : JCTree.Tag.PLUS;
                String str = optag == JCTree.Tag.PLUS ? "sum" : "difference";
                if (newtype.getTag() == TypeTag.INT) {
                    Symbol sym = optag == JCTree.Tag.PLUS ? rewriter.treeutils.intminusSymbol : rewriter.treeutils.intplusSymbol;
                    JCExpression maxlit = rewriter.treeutils.makeIntLiteral(p, Integer.MAX_VALUE);
                    JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                    JCExpression zerolit = rewriter.treeutils.makeIntLiteral(p, 0);
                    // a == 0 < lhs ; b1 == 0 < rhs ; b2 == rhs < 0
                    // +) c == MAX - rhs ; d == lhs <= c == lhs <= (MAX - rhs) ; x == (a && b1) ==> d
                    // -) c == MAX + rhs ; d == lhs <= c == lhs <= (MAX + rhs) ; x == (a && b2) ==> d
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, zerolit, rewriter.convertCopy(lhs), newtype);
                    JCExpression b1 = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, zerolit, rewriter.convertCopy(rhs), newtype);
                    JCExpression b2 = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, rewriter.convertCopy(rhs), zerolit, newtype);
                    JCExpression b = optag == JCTree.Tag.PLUS ? b1 : b2;
                    JCExpression c = rewriter.makeBin(that,  optagn,  sym, maxlit, rewriter.convertCopy(rhs), newtype);
                    JCExpression d = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, rewriter.convertCopy(lhs), c, newtype);
                    JCExpression x = rewriter.treeutils.makeImplies(p, rewriter.treeutils.makeAnd(p,a,b), d);
                    assertIt(rewriter, that, "overflow in int " + str, x);
                    // a == lhs < 0 ; b1 == 0 < rhs ; b2 == rhs < 0
                    // +) c == MIN - rhs ; d == c <= lhs == (MIN - rhs) <= lhs; x == (a && b2) ==> d
                    // -) c == MIN + rhs ; d == c <= lhs == (MIN + rhs) <= lhs; x == (a && b1) ==> d
                    a = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, rewriter.convertCopy(lhs), zerolit, newtype);
                    b = optag == JCTree.Tag.PLUS ? b2 : b1;
                    c = rewriter.makeBin(that,  optagn,  sym, minlit, rewriter.convertCopy(rhs), newtype);
                    d = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, c, rewriter.convertCopy(lhs), newtype);
                    x = rewriter.treeutils.makeImplies(p, rewriter.treeutils.makeAnd(p,a,rewriter.convertCopy(b)), d);
                    assertIt(rewriter, that, "underflow in int " + str, x);
                } else if (newtype.getTag() == TypeTag.LONG) {
                    Symbol sym = optag == JCTree.Tag.PLUS ? rewriter.treeutils.longminusSymbol : rewriter.treeutils.longplusSymbol;
                    JCExpression maxlit = rewriter.treeutils.makeLongLiteral(p, Long.MAX_VALUE);
                    JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                    JCExpression zerolit = rewriter.treeutils.makeLongLiteral(p, 0L);
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, zerolit, rewriter.convertCopy(lhs), newtype);
                    JCExpression b1 = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, zerolit, rewriter.convertCopy(rhs), newtype);
                    JCExpression b2 = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, rewriter.convertCopy(rhs), zerolit, newtype);
                    JCExpression b = optag == JCTree.Tag.PLUS ? b1 : b2;
                    JCExpression c = rewriter.makeBin(that,  optagn,  sym, maxlit, rewriter.convertCopy(rhs), newtype);
                    JCExpression d = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, rewriter.convertCopy(lhs), c, newtype);
                    JCExpression x = rewriter.treeutils.makeImplies(p, rewriter.treeutils.makeAnd(p,a,b), d);
                    assertIt(rewriter, that, "overflow in long " + str, x);
                    a = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, rewriter.convertCopy(lhs), zerolit, newtype);
                    b = optag == JCTree.Tag.PLUS ? b2 : b1;
                    c = rewriter.makeBin(that,  optagn,  sym, minlit, rewriter.convertCopy(rhs), newtype);
                    d = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, c, rewriter.convertCopy(lhs), newtype);
                    x = rewriter.treeutils.makeImplies(p, rewriter.treeutils.makeAnd(p,a,rewriter.convertCopy(b)), d);
                    assertIt(rewriter, that, "underflow in long " + str, x);
                }
            } else if (optag == JCTree.Tag.MUL) {
                if (rewriter.useBV || rewriter.rac) {
                    if (newtype.getTag() == TypeTag.INT) {
                        // a = lhs * rhs ; b = a / lhs; c = lhs == 0 ; d = b == rhs; check = c || d = (lhs == 0) || (lhs*rhs)/lhs == rhs;
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, rewriter.treeutils.intmultiplySymbol, rewriter.convertCopy(lhs), rewriter.convertCopy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.DIV, rewriter.treeutils.intdivideSymbol, a, rewriter.convertCopy(lhs));
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.convertCopy(lhs), rewriter.treeutils.makeIntLiteral(p, 0));
                        JCExpression d = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, b, rewriter.convertCopy(rhs));
                        rewriter.addAssert(that, Label.ARITHMETIC_OP_RANGE, 
                                condition(rewriter, rewriter.treeutils.makeOr(p, c, d)), "int multiply overflow");
                    } else if (newtype.getTag() == TypeTag.LONG) {
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, rewriter.treeutils.longmultiplySymbol, rewriter.convertCopy(lhs), rewriter.convertCopy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.DIV, rewriter.treeutils.longdivideSymbol, a, rewriter.convertCopy(lhs));
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.convertCopy(lhs), rewriter.treeutils.makeLongLiteral(p, 0L));
                        JCExpression d = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, b, rewriter.convertCopy(rhs));
                        rewriter.addAssert(that, Label.ARITHMETIC_OP_RANGE, 
                                condition(rewriter, rewriter.treeutils.makeOr(p, c, d)), "long multiply overflow");
                    }
                } else if (smtPredefined) {
                    if (newtype.getTag() == TypeTag.INT) {
                        assertIt(rewriter, that, "int multiply overflow", 
                            rewriter.treeutils.makeJmlMethodInvocation(that,"|#mul32ok#|", syms.booleanType, lhs, rhs));
                    } else if (newtype.getTag() == TypeTag.LONG) {
                        assertIt(rewriter, that, "long multiply overflow", 
                                rewriter.treeutils.makeJmlMethodInvocation(that,"|#mul64ok#|", syms.booleanType, lhs, rhs));
                    }
                } else {
                    if (newtype.getTag() == TypeTag.INT) {
                        // check =  MIN <= lhs*rhs && lhs*rhs <= MAX
                        JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                        JCExpression maxlit = rewriter.treeutils.makeIntLiteral(p, Integer.MAX_VALUE);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, that.getOperator(), rewriter.convertCopy(lhs), rewriter.convertCopy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE,  minlit, a);
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE,  rewriter.convertCopy(a), maxlit);
                        assertIt(rewriter, that, "int multiply overflow", rewriter.treeutils.makeAnd(p, b, c));
                    } else if (newtype.getTag() == TypeTag.LONG) {
                        JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                        JCExpression maxlit = rewriter.treeutils.makeLongLiteral(p, Long.MAX_VALUE);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, that.getOperator(), rewriter.convertCopy(lhs), rewriter.convertCopy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE,  minlit, a);
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE,  rewriter.convertCopy(a), maxlit);
                        assertIt(rewriter, that, "long multiply overflow", rewriter.treeutils.makeAnd(p, b, c));
                    }
                }
            } else if (optag == JCTree.Tag.DIV) {
                // a/b overflows only if  a == min && b == -1
                {
                    if (newtype.getTag() == TypeTag.INT) {
                        JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                        JCExpression minusonelit = rewriter.treeutils.makeIntLiteral(p, -1);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.convertCopy(lhs), minlit);
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.convertCopy(rhs), minusonelit);
                        JCExpression x = rewriter.treeutils.makeNot(p, rewriter.treeutils.makeAnd(p, a, b));
                        assertIt(rewriter, that, "overflow in int divide", x);
                    } else if (newtype.getTag() == TypeTag.LONG) {
                        JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                        JCExpression minusonelit = rewriter.treeutils.makeLongLiteral(p, -1L);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.convertCopy(lhs), minlit);
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.convertCopy(rhs), minusonelit);
                        JCExpression x = rewriter.treeutils.makeNot(p, rewriter.treeutils.makeAnd(p, a, b));
                        assertIt(rewriter, that, "overflow in long divide", x);
                    }
                }
            } else if (optag == JCTree.Tag.MOD){
                // a%b is always OK
            } else {
                // FIXME: Possibly: shifts
                rewriter.log.error(that,"jml.internal","Operation not implemented in Arithmetic.makeBinaryOp: " + optag.toString());
            }
            
        }
        
        // Implement the operation, correcting for overflow if needed
        
        boolean isBigint = rewriter.jmltypes.isJmlTypeOrRepType(newtype);
        JCExpression bin;
        if (rewriter.rac && rewriter.jmltypes.isJmlType(newtype)) {
            bin = rewriter.makeBin(that,optag,that.getOperator(),lhs,rhs,newtype);
        } else {
            bin = rewriter.treeutils.makeBinary(p,optag,that.getOperator(),lhs,rhs);
            if (isBigint) bin.type = newtype;
            // Now we always will have mathematical values
            if (rewriter.esc && !rewriter.useBV && implementOverflow && !isBigint) {
                if (optag == JCTree.Tag.PLUS || optag == JCTree.Tag.MINUS) {
                    // ( result > MAX ? result + MIN + MIN : result < MIN ? result - MIN - MIN : result
                    if (typetag == TypeTag.INT) {
                        JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                        JCExpression maxlit = rewriter.treeutils.makeIntLiteral(p, Integer.MAX_VALUE);
                        // a = bin > MAX ; b = bin < MIN ; d = bin - MIN - MIN ; f = bin + MIN + MIN ; g = (bin>MAX) ? f : (bin<MIN) ? d : bin;
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, maxlit, rewriter.convertCopy(bin));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, rewriter.convertCopy(bin), minlit);
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.intminusSymbol, rewriter.convertCopy(bin), minlit);
                        JCExpression d = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.intminusSymbol, c, minlit);
                        JCExpression e = rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.treeutils.intplusSymbol, rewriter.convertCopy(bin), minlit);
                        JCExpression f = rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.treeutils.intplusSymbol, e, minlit);
                        JCExpression g = rewriter.treeutils.makeConditional(p, a, f, 
                                rewriter.treeutils.makeConditional(p, b, d, bin));
                        bin = g;
                    } else if (typetag == TypeTag.LONG) {
                        JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                        JCExpression maxlit = rewriter.treeutils.makeLongLiteral(p, Long.MAX_VALUE);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, maxlit, rewriter.convertCopy(bin));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, rewriter.convertCopy(bin), minlit);
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.longminusSymbol, rewriter.convertCopy(bin), minlit);
                        JCExpression d = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.longminusSymbol, c, minlit);
                        JCExpression e = rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.treeutils.longplusSymbol, rewriter.convertCopy(bin), minlit);
                        JCExpression f = rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.treeutils.longplusSymbol, e, minlit);
                        JCExpression g = rewriter.treeutils.makeConditional(p, a, f, 
                                rewriter.treeutils.makeConditional(p, b, d, bin));
                        bin = g;
                    }
                } else if (optag == JCTree.Tag.MUL) {
                    // Note all of this arithmetic will be done in unbounded integers in SMT  -- not quite true - currently auto does not do a retranalsation
                    // a = lhs * rhs;  b = min <= a; c = max <= a; ; e = b && c; longbin = (long)(lhs*rhs); pos = 0 <= a;
                    // f = ( longbin % biglit) ; fneg = f; big = f > max ; small = fneg < min; sub = f - biglit;
                    // posvalue =  big ? sub : f;
                    // negvalue = small ? fneg + biglit : fneg
                    // result = g = e ? bin : pos ? posvalue : negvalue;
                    if (smtPredefined) {
                        if (newtype.getTag() == TypeTag.INT) {
                            bin = rewriter.treeutils.makeJmlMethodInvocation(that,"|#mul32#|", syms.intType, lhs, rhs);
                        } else if (newtype.getTag() == TypeTag.LONG) {
                            bin = rewriter.treeutils.makeJmlMethodInvocation(that,"|#mul64#|", syms.longType, lhs, rhs);
                        }
                    } else if (typetag == TypeTag.INT) {
                        // The MOD here is Java %, which is negative if the dividend is negative
                        // DIV is OK here because it is exact
                        JCExpression zero = rewriter.treeutils.makeIntLiteral(p, 0);
                        JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                        JCExpression minlitL = rewriter.treeutils.makeLongLiteral(p, Integer.MIN_VALUE);
                        JCExpression maxlit = rewriter.treeutils.makeIntLiteral(p, Integer.MAX_VALUE);
                        JCExpression maxlitL = rewriter.treeutils.makeLongLiteral(p, Integer.MAX_VALUE);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, that.getOperator(), rewriter.convertCopy(lhs), rewriter.convertCopy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.intleSymbol,  minlit, rewriter.convertCopy(a));
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.intleSymbol,  rewriter.convertCopy(a), maxlit);
                        JCExpression e = rewriter.treeutils.makeAnd(p, b, c);
                        JCExpression longbin = rewriter.addImplicitConversion(that, syms.longType, rewriter.convertCopy(bin));
                        JCExpression pos = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.intleSymbol,  zero, rewriter.convertCopy(a));
                        JCExpression biglit = rewriter.treeutils.makeLongLiteral(p, (-2L)*Integer.MIN_VALUE);
                        JCExpression f = rewriter.treeutils.makeBinary(p, JCTree.Tag.MOD, 
                                rewriter.treeutils.findOpSymbol(JCTree.Tag.MOD,syms.longType), longbin, biglit);
                        JCExpression fneg = rewriter.treeutils.makeBinary(p, JCTree.Tag.MOD, 
                                rewriter.treeutils.findOpSymbol(JCTree.Tag.MOD,syms.longType), rewriter.convertCopy(longbin), biglit);
                        JCExpression big = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol,  maxlitL, rewriter.convertCopy(f));
                        JCExpression small = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol,  rewriter.convertCopy(fneg), minlitL);
                        JCExpression sub = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.intminusSymbol,  rewriter.convertCopy(f), biglit);
                        JCExpression posvalue = rewriter.treeutils.makeConditional(p, big, sub, rewriter.convertCopy(f));
                        posvalue = rewriter.addImplicitConversion(that, syms.intType, posvalue);
                        JCExpression negvalue = rewriter.treeutils.makeConditional(p, small, 
                                    rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.convertCopy(fneg), biglit), rewriter.convertCopy(fneg));
                        negvalue = rewriter.addImplicitConversion(that, syms.intType, negvalue);
                        JCExpression g = rewriter.treeutils.makeConditional(p, e, rewriter.convertCopy(bin), rewriter.treeutils.makeConditional(p, pos, posvalue, negvalue)); 
                        bin = g;
                    } else if (typetag == TypeTag.LONG) {
                        // a = lhs * rhs;  b = min <= a; c = max <= a; ; e = b && c; longbin = (long)(lhs*rhs); pos = 0 <= a;
                        // f = ( longbin % biglit) ; fneg = f; big = f > max ; small = fneg < min; sub = f - biglit;
                        // posvalue =  big ? sub : f;
                        // negvalue = small ? fneg + biglit : fneg
                        // result = g = e ? bin : pos ? posvalue : negvalue;
                        JCExpression zero = rewriter.treeutils.makeLongLiteral(p, 0L);
                        JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                        JCExpression maxlit = rewriter.treeutils.makeLongLiteral(p, Long.MAX_VALUE);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, that.getOperator(), lhs, rhs);
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.longleSymbol,  minlit, rewriter.convertCopy(a));
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.longleSymbol,  rewriter.convertCopy(a), maxlit);
                        JCExpression e = rewriter.treeutils.makeAnd(p, b, c);
                        JCExpression longbin = bin;
                        JCExpression pos = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.longleSymbol,  zero, rewriter.convertCopy(a));
                        JCExpression biglit = rewriter.treeutils.makeBinary(p,  JCTree.Tag.MUL,  
                                rewriter.treeutils.makeLongLiteral(p, -2L),
                                rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE));
                        JCExpression f = rewriter.treeutils.makeBinary(p, JCTree.Tag.MOD, 
                                rewriter.treeutils.findOpSymbol(JCTree.Tag.MOD,syms.longType), longbin, biglit);
                        JCExpression fneg = rewriter.treeutils.makeBinary(p, JCTree.Tag.MOD, 
                                        rewriter.treeutils.findOpSymbol(JCTree.Tag.MOD,syms.longType), 
                                        rewriter.convertCopy(longbin), 
                                        biglit);
                        JCExpression big = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol,  maxlit, rewriter.convertCopy(f));
                        JCExpression small = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol,  rewriter.convertCopy(fneg), minlit);
                        JCExpression sub = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.longminusSymbol,  rewriter.convertCopy(f), biglit);
                        JCExpression add = rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.treeutils.longplusSymbol, biglit, fneg);
                        JCExpression posvalue = rewriter.treeutils.makeConditional(p, big, sub, rewriter.convertCopy(f));
                        JCExpression negvalue = rewriter.treeutils.makeConditional(p, small, add, rewriter.convertCopy(fneg));
                        JCExpression g = rewriter.treeutils.makeConditional(p, e, bin, rewriter.treeutils.makeConditional(p, pos, posvalue, negvalue)); 
                        bin = g;
                    }
                } else if (optag == JCTree.Tag.DIV) {
                    if (typetag == TypeTag.INT) {
                        JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                        JCExpression minusonelit = rewriter.treeutils.makeIntLiteral(p, -1);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.convertCopy(lhs), minlit);
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.convertCopy(rhs), minusonelit);
                        JCExpression x = rewriter.treeutils.makeNot(p, rewriter.treeutils.makeAnd(p, a, b));
                        bin = rewriter.treeutils.makeConditional(p, x, bin, minlit);
                    } else if (typetag == TypeTag.LONG) {
                        JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                        JCExpression minusonelit = rewriter.treeutils.makeLongLiteral(p, -1L);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.convertCopy(lhs), minlit);
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.convertCopy(rhs), minusonelit);
                        JCExpression x = rewriter.treeutils.makeNot(p, rewriter.treeutils.makeAnd(p, a, b));
                        bin = rewriter.treeutils.makeConditional(p, x, bin, minlit);
                    }
                }
            }
        }
        
        return bin;

    }

    private void assertIt(JmlAssertionAdder rewriter, JCBinary that, String str,
            JCExpression x) {
        x = condition(rewriter, x);
        if (!rac) {
            JCTree.JCIdent id = rewriter.newTemp(x);
            rewriter.saveMapping(x,id);
        }
        rewriter.addCheck(that, Label.ARITHMETIC_OP_RANGE, x, str);
    }
    
    /** This implements the bigint (which is also real) mathematical mode */
    public static class Math extends Arithmetic implements IArithmeticMode {
        
        public Math(Context context) {
            super(context);
        }
        
        public static Math instance(Context context) {
            return instance(context,Math.class);
        }
        
        @Override
        public Mode mode() { return Mode.MATH; }
        
        /** Returns the appropriate mathematical type (\bigint or \real) given the input type */
        Type mathType(JmlAssertionAdder rewriter, Type t) {
            TypeTag tag = t.getTag();
            if (rewriter.jmltypes.isJmlType(t)) return t;
            if (rewriter.jmltypes.isIntegral(t)) return rewriter.jmltypes.BIGINT;
            if (tag == TypeTag.DOUBLE || tag == TypeTag.FLOAT) return rewriter.jmltypes.REAL;
            return t;
        }
        
        /** Rewrites unary operations; for NEG, the expression is
         *  promoted to the math type and negated; for PLUS and COMPL the
         *  expression type is unchanged. 
         */
        @Override
        public JCExpression rewriteUnary(JmlAssertionAdder rewriter, JCUnary that) {
            JCTree.Tag tag = that.getTag();
            JCExpression e;
            switch (tag) {
                case NEG: {
                    Type newtype = that.type;
                    if (rewriter.rac) newtype = mathType(rewriter,that.type);
                    e = makeUnaryOp(rewriter,that,newtype,false,false);
                    break;
                } 
                case POS:
                case COMPL: {
                    Type newtype = that.type; // No overflows possible - do not need to promote the type
                    e = makeUnaryOp(rewriter,that,newtype,false,false);
                    break;
                } 
                default:
                    e = null;
                    rewriter.log.error(that.pos, "jml.internal", "Unexpected operation in Arithmetic.Math.rewriteUnary");
            }
            return e;
        }
        
        @Override
        public JCExpression rewriteBinary(JmlAssertionAdder rewriter, JCBinary that, boolean alreadyConverted) {
            
            // Don't actually need to promote mod operations, but doing it for consistency
            Type newtype = that.type;
            if (rewriter.rac) newtype = mathType(rewriter,that.type);
            
            return makeBinaryOp(rewriter, that, newtype, false, false, alreadyConverted);

        }

    }

    public static class Safe extends Arithmetic implements IArithmeticMode {
        
        public Safe(Context context) {
            super(context);
        }
        
        public static Safe instance(Context context) {
            return instance(context,Safe.class);
        }
        
        @Override
        public Mode mode() { return Mode.SAFE; }

        @Override
        public JCExpression rewriteUnary(JmlAssertionAdder rewriter, JCUnary that) {
            return makeUnaryOp(rewriter, that, that.type, true, true);
        }
        
        @Override
        public JCExpression rewriteBinary(JmlAssertionAdder rewriter, JCBinary that, boolean alreadyConverted) {
            return makeBinaryOp(rewriter, that, null, true, true, alreadyConverted);
        }
        
    }

    public static class Java extends Arithmetic implements IArithmeticMode {

        public Java(Context context) {
            super(context);
        }
        
        public static Java instance(Context context) {
            return instance(context,Java.class);
        }
        
        @Override
        public Mode mode() { return Mode.JAVA; }

        @Override
        public JCExpression rewriteUnary(JmlAssertionAdder rewriter, JCUnary that) {
            return makeUnaryOp(rewriter, that, that.type, true, false);
        }
        
        @Override
        public JCExpression rewriteBinary(JmlAssertionAdder rewriter, JCBinary that, boolean alreadyConverted) {
            return makeBinaryOp(rewriter, that, null, true, false, alreadyConverted);
        }

    }

}
