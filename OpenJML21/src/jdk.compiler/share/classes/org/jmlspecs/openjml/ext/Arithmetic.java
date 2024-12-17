package org.jmlspecs.openjml.ext;

import java.lang.reflect.Constructor;

import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.IArithmeticMode;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlOptions;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree.JmlModifiers;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
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
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Names;

import org.jmlspecs.openjml.JmlOption;

abstract public class Arithmetic extends JmlExtension {
    
	public Context context;

    public void register(Context context) {
    	Math.instance(context);
    	Safe.instance(context);
    	Java.instance(context);
    }
    
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
        
    Type intType;
    
    boolean javaChecks;
        
    public boolean rac;
    
    public IArithmeticMode defaultArithmeticMode(Symbol sym, boolean jml) {
        Utils utils = Utils.instance(context);
        if (!jml) {
            if (utils.hasModifier(sym, Modifiers.CODE_BIGINT_MATH)) return Math.instance(context);
            if (utils.hasModifier(sym, Modifiers.CODE_SAFE_MATH)) return Safe.instance(context);
            if (utils.hasModifier(sym, Modifiers.CODE_JAVA_MATH)) return Java.instance(context);
            sym = sym.owner;
            if (!(sym instanceof Symbol.PackageSymbol)) return defaultArithmeticMode(sym,jml);
            String v = JmlOption.value(context,JmlOption.CODE_MATH);
            if ("java".equals(v)) return Java.instance(context);
            if ("safe".equals(v)) return Safe.instance(context);
            return Math.instance(context);
        } else {
            if (utils.hasModifier(sym, Modifiers.SPEC_BIGINT_MATH)) return Math.instance(context);
            if (utils.hasModifier(sym, Modifiers.SPEC_SAFE_MATH)) return Safe.instance(context);
            if (utils.hasModifier(sym, Modifiers.SPEC_JAVA_MATH)) return Java.instance(context);
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
        Type REAL = JmlPrimitiveTypes.realTypeKind.getType(context);
        Type BIGINT = JmlPrimitiveTypes.bigintTypeKind.getType(context);
        TypeTag lt = lhs.getTag();
        TypeTag rt = rhs.getTag();
        if (lhs.tsym == REAL.tsym) return lhs;
        if (rhs.tsym == REAL.tsym) return rhs;
        if (lhs.tsym == BIGINT.tsym) {
            if (rt == TypeTag.DOUBLE || rt == TypeTag.FLOAT) return REAL;
            return lhs;
        }
        if (lt == TypeTag.CLASS) lhs = Types.instance(context).unboxedType(lhs); 
        if (rt == TypeTag.CLASS) rhs = Types.instance(context).unboxedType(rhs); 
        if (rhs.tsym == BIGINT.tsym) {
            if (lt == TypeTag.DOUBLE || lt == TypeTag.FLOAT) return REAL;
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

    
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        checkOneArg(parser,e);
    }
    
    public void checkOneArg(JmlParser parser, JmlMethodInvocation e) {
    	if (e.args.size() != 1) {
    		org.jmlspecs.openjml.Utils.instance(context).error(e.pos, parser.getEndPos(e), "jml.one.arg", e.kind.keyword());
    	}
    }

    public static <T> T instance(Context context, Class<T> key) {
    	T s = context.get(key);
    	if (s == null) {
    		try {
    			Constructor<T> c = key.getConstructor();
    			s = c.newInstance();
    			((Arithmetic)s).context = context;
    			context.put(key, s);
    		} catch (Exception e) {
    			throw new RuntimeException(e);
    		}
    	}
    	return s;
    }

    public Type typecheck(JmlAttr attr, JCExpression expr,
            Env<AttrContext> env) {
        JmlMethodInvocation tree = (JmlMethodInvocation)expr;
        
        // Expect one argument of any type, result type is the same type
        // The argument expression may contain JML constructs
        ListBuffer<Type> argtypesBuf = new ListBuffer<>();
        attr.attribArgs(tree.args, env, argtypesBuf);
        //attr.attribTypes(tree.typeargs, env);
        int n = tree.args.size();
        if (n != 1) {
            Utils.instance(context).error(tree.pos,"jml.one.arg",tree.kind.keyword(),n);
        }
        Type t = Symtab.instance(context).errType;
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
        if (implementOverflow && !(arg instanceof JCLiteral)) {
            if (typetag == TypeTag.INT) {
                JCExpression maxlit = rewriter.treeutils.makeIntLiteral(arg, Integer.MAX_VALUE);
                JCExpression minlit = rewriter.treeutils.makeIntLiteral(arg, Integer.MIN_VALUE);
                JCExpression a = rewriter.makeBin(arg, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, minlit, rewriter.copy(arg), newtype);
                JCExpression b = rewriter.makeBin(arg, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, rewriter.copy(arg), maxlit, newtype);
                rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
            } else if (typetag == TypeTag.LONG) {
                JCExpression maxlit = rewriter.treeutils.makeLongLiteral(arg, Long.MAX_VALUE);
                JCExpression minlit = rewriter.treeutils.makeLongLiteral(arg, Long.MIN_VALUE);
                JCExpression a = rewriter.makeBin(arg, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, minlit, rewriter.copy(arg), newtype);
                JCExpression b = rewriter.makeBin(arg, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, rewriter.copy(arg), maxlit, newtype);
                rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
            }
        }
        if (warnOverflow && optag == JCTree.Tag.NEG && rewriter.jmltypes.isSameType(that.type,that.getExpression().type)) {
            if (typetag == TypeTag.INT) {
                JCExpression e = rewriter.treeutils.makeNot(arg.pos,rewriter.treeutils.makeEquality(arg.pos, rewriter.copy(arg), rewriter.treeutils.makeIntLiteral(arg.pos, Integer.MIN_VALUE)));
                e = condition(rewriter,e);
                checkIt(rewriter,that,"int negation",e);
            } else if (typetag == TypeTag.LONG) {
                JCExpression e = rewriter.treeutils.makeNot(arg.pos,rewriter.treeutils.makeEquality(arg.pos, rewriter.copy(arg), rewriter.treeutils.makeLit(arg.pos, that.type, Long.MIN_VALUE)));
                e = condition(rewriter,e);
                checkIt(rewriter,that,"long negation",e);
            }
        }
        if (rewriter.rac && rewriter.jmltypes.isJmlType(newtype)) {
            if (optag == JCTree.Tag.NEG) { 
                // Both BIGINT and REAL
                eresult = rewriter.treeutils.makeMethodInvocation(that,arg,Names.instance(context).fromString("negate"));
            } else if (optag == JCTree.Tag.POS) {
                eresult = arg;
            } else if (optag == JCTree.Tag.COMPL) {
                // Assumed to be a bigint (not real) operation - equivalent to -x-1
                JCExpression ty = rewriter.treeutils.makeType(that.getPreferredPosition(), rewriter.BIGINT);
                JCExpression e = rewriter.treeutils.makeMethodInvocation(that,arg,Names.instance(context).fromString("negate"));
                eresult = rewriter.treeutils.makeMethodInvocation(that,e,Names.instance(context).fromString("subtract"),
                        rewriter.treeutils.makeMethodInvocation(that,ty,Names.instance(context).of,
                                rewriter.treeutils.makeIntLiteral(that, 1)));
            } else { 
                Utils.instance(context).error(that,"jml.internal","Unknown unary operation in Arithmetic.Java for JML type: " + that);
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
                    JCExpression eq = rewriter.treeutils.makeBinary(that.pos, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.copy(arg), lit);
                    JCExpression conditional = rewriter.treeutils.makeConditional(that.pos, eq, lit, eresult);
                    eresult = conditional;
                } else if (typetag == TypeTag.LONG) {
                    JCExpression lit = rewriter.treeutils.makeLongLiteral(that.pos, Long.MIN_VALUE);
                    JCExpression eq = rewriter.treeutils.makeEquality(that.pos, rewriter.copy(arg), lit);
                    JCExpression conditional = rewriter.treeutils.makeConditional(that.pos, eq, lit, eresult);
                    eresult = conditional;
                } else if (rewriter.jmltypes.isIntegral(that.type)) {
                	Utils.instance(context).error(that,"jml.internal","Unimplemented integral type in Arithmetic.Java: " + that.type);
                }
            }
        }
        return eresult;
    }
    
    public JCExpression condition(JmlAssertionAdder rewriter, JCExpression e) {
        return rewriter.conditionedAssertion(e, e);
    }
    
    public JCExpression makeBinaryOp(JmlAssertionAdder rewriter, JCBinary that, Type newtype, boolean implementOverflow, boolean checkOverflow, boolean alreadyConverted) {
        var syms = Symtab.instance(context);
        var utils = Utils.instance(context);
    	int p = that.pos;
        this.javaChecks = (rewriter.esc || (rewriter.rac && JmlOption.isOption(context,JmlOption.RAC_JAVA_CHECKS)));

        JCTree.Tag optag = that.getTag();
        if (newtype == null) newtype = that.type;
        
        JCExpression lhs = alreadyConverted ? that.getLeftOperand() : rewriter.convertExpr(that.getLeftOperand());
        JCExpression rhs = alreadyConverted ? that.getRightOperand() : rewriter.convertExpr(that.getRightOperand());

        // Need to do this operation before any implicit conversions, because those conversions may convert
        // to bigint or real, which complicates this test
        if (optag == JCTree.Tag.DIV || optag == JCTree.Tag.MOD) {
            /*@nullable*/ JCExpression nonzero = rewriter.nonZeroCheck(that,rhs);
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
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, minlit, rewriter.copy(lhs), newtype);
                    JCExpression b = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, rewriter.copy(lhs), maxlit, newtype);
                    rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
                }
                if (!(rhs instanceof JCLiteral)) {
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, minlit, rewriter.copy(rhs), newtype);
                    JCExpression b = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, rewriter.copy(rhs), maxlit, newtype);
                    rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
                }
            } else if (newtype.getTag() == TypeTag.LONG) {
                JCExpression maxlit = rewriter.treeutils.makeLongLiteral(p, Long.MAX_VALUE);
                JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                if (!(lhs instanceof JCLiteral)) {
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, minlit, rewriter.copy(lhs), newtype);
                    JCExpression b = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, rewriter.copy(lhs), maxlit, newtype);
                    rewriter.addAssume(that, Label.IMPLICIT_ASSUME, rewriter.treeutils.makeAnd(that,a,b));
                }
                if (!(rhs instanceof JCLiteral)) {
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, minlit, rewriter.copy(rhs), newtype);
                    JCExpression b = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, rewriter.copy(rhs), maxlit, newtype);
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
                    OperatorSymbol sym = optag == JCTree.Tag.PLUS ? rewriter.treeutils.intminusSymbol : rewriter.treeutils.intplusSymbol;
                    JCExpression maxlit = rewriter.treeutils.makeIntLiteral(p, Integer.MAX_VALUE);
                    JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                    JCExpression zerolit = rewriter.treeutils.makeIntLiteral(p, 0);
                    // a == 0 < lhs ; b1 == 0 < rhs ; b2 == rhs < 0
                    // +) c == MAX - rhs ; d == lhs <= c == lhs <= (MAX - rhs) ; x == (a && b1) ==> d
                    // -) c == MAX + rhs ; d == lhs <= c == lhs <= (MAX + rhs) ; x == (a && b2) ==> d
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, zerolit, rewriter.copy(lhs), newtype);
                    JCExpression b1 = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, zerolit, rewriter.copy(rhs), newtype);
                    JCExpression b2 = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, rewriter.copy(rhs), zerolit, newtype);
                    JCExpression b = optag == JCTree.Tag.PLUS ? b1 : b2;
                    JCExpression c = rewriter.makeBin(that,  optagn,  sym, maxlit, rewriter.copy(rhs), newtype);
                    JCExpression d = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, rewriter.copy(lhs), c, newtype);
                    JCExpression x = rewriter.treeutils.makeImplies(p, rewriter.treeutils.makeAnd(p,a,b), d);
                    checkIt(rewriter, that, "overflow in int " + str, x);
                    // a == lhs < 0 ; b1 == 0 < rhs ; b2 == rhs < 0
                    // +) c == MIN - rhs ; d == c <= lhs == (MIN - rhs) <= lhs; x == (a && b2) ==> d
                    // -) c == MIN + rhs ; d == c <= lhs == (MIN + rhs) <= lhs; x == (a && b1) ==> d
                    a = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, rewriter.copy(lhs), zerolit, newtype);
                    b = optag == JCTree.Tag.PLUS ? b2 : b1;
                    c = rewriter.makeBin(that,  optagn,  sym, minlit, rewriter.copy(rhs), newtype);
                    d = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.intleSymbol, c, rewriter.copy(lhs), newtype);
                    x = rewriter.treeutils.makeImplies(p, rewriter.treeutils.makeAnd(p,a,rewriter.copy(b)), d);
                    checkIt(rewriter, that, "underflow in int " + str, x);
                } else if (newtype.getTag() == TypeTag.LONG) {
                    OperatorSymbol sym = optag == JCTree.Tag.PLUS ? rewriter.treeutils.longminusSymbol : rewriter.treeutils.longplusSymbol;
                    JCExpression maxlit = rewriter.treeutils.makeLongLiteral(p, Long.MAX_VALUE);
                    JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                    JCExpression zerolit = rewriter.treeutils.makeLongLiteral(p, 0L);
                    JCExpression a = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, zerolit, rewriter.copy(lhs), newtype);
                    JCExpression b1 = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, zerolit, rewriter.copy(rhs), newtype);
                    JCExpression b2 = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, rewriter.copy(rhs), zerolit, newtype);
                    JCExpression b = optag == JCTree.Tag.PLUS ? b1 : b2;
                    JCExpression c = rewriter.makeBin(that,  optagn,  sym, maxlit, rewriter.copy(rhs), newtype);
                    JCExpression d = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, rewriter.copy(lhs), c, newtype);
                    JCExpression x = rewriter.treeutils.makeImplies(p, rewriter.treeutils.makeAnd(p,a,b), d);
                    checkIt(rewriter, that, "overflow in long " + str, x);
                    a = rewriter.makeBin(that, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, rewriter.copy(lhs), zerolit, newtype);
                    b = optag == JCTree.Tag.PLUS ? b2 : b1;
                    c = rewriter.makeBin(that,  optagn,  sym, minlit, rewriter.copy(rhs), newtype);
                    d = rewriter.makeBin(that, JCTree.Tag.LE, rewriter.treeutils.longleSymbol, c, rewriter.copy(lhs), newtype);
                    x = rewriter.treeutils.makeImplies(p, rewriter.treeutils.makeAnd(p,a,rewriter.copy(b)), d);
                    checkIt(rewriter, that, "underflow in long " + str, x);
                }
            } else if (optag == JCTree.Tag.MUL) {
                if (rewriter.useBV || rewriter.rac) {
                    if (newtype.getTag() == TypeTag.INT) {
                        // a = lhs * rhs ; b = a / lhs; c = lhs == 0 ; d = b == rhs; check = c || d = (lhs == 0) || (lhs*rhs)/lhs == rhs;
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, rewriter.treeutils.intmultiplySymbol, rewriter.copy(lhs), rewriter.copy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.DIV, rewriter.treeutils.intdivideSymbol, a, rewriter.copy(lhs));
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.copy(lhs), rewriter.treeutils.makeIntLiteral(p, 0));
                        JCExpression d = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, b, rewriter.copy(rhs));
                        checkIt(rewriter,that, "int multiply overflow", 
                                condition(rewriter, rewriter.treeutils.makeOr(p, c, d)));
                    } else if (newtype.getTag() == TypeTag.LONG) {
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, rewriter.treeutils.longmultiplySymbol, rewriter.copy(lhs), rewriter.copy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.DIV, rewriter.treeutils.longdivideSymbol, a, rewriter.copy(lhs));
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.copy(lhs), rewriter.treeutils.makeLongLiteral(p, 0L));
                        JCExpression d = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, b, rewriter.copy(rhs));
                        checkIt(rewriter,that, "long multiply overflow", 
                                condition(rewriter, rewriter.treeutils.makeOr(p, c, d)));
                    }
                } else if (smtPredefined) {
                    if (newtype.getTag() == TypeTag.INT) {
                        checkIt(rewriter, that, "int multiply overflow", 
                            rewriter.treeutils.makeJmlMethodInvocation(that,"|#mul32ok#|", syms.booleanType, lhs, rhs));
                    } else if (newtype.getTag() == TypeTag.LONG) {
                        checkIt(rewriter, that, "long multiply overflow", 
                                rewriter.treeutils.makeJmlMethodInvocation(that,"|#mul64ok#|", syms.booleanType, lhs, rhs));
                    }
                } else {
                    if (newtype.getTag() == TypeTag.INT) {
                        // check =  MIN <= lhs*rhs && lhs*rhs <= MAX
                        JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                        JCExpression maxlit = rewriter.treeutils.makeIntLiteral(p, Integer.MAX_VALUE);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, that.getOperator(), rewriter.copy(lhs), rewriter.copy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE,  minlit, a);
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE,  rewriter.copy(a), maxlit);
                        checkIt(rewriter, that, "int multiply overflow", rewriter.treeutils.makeAnd(p, b, c));
                    } else if (newtype.getTag() == TypeTag.LONG) {
                        JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                        JCExpression maxlit = rewriter.treeutils.makeLongLiteral(p, Long.MAX_VALUE);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, that.getOperator(), rewriter.copy(lhs), rewriter.copy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE,  minlit, a);
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE,  rewriter.copy(a), maxlit);
                        checkIt(rewriter, that, "long multiply overflow", rewriter.treeutils.makeAnd(p, b, c));
                    }
                }
            } else if (optag == JCTree.Tag.DIV) {
                // a/b overflows only if  a == min && b == -1
                {
                    if (newtype.getTag() == TypeTag.INT) {
                        JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                        JCExpression minusonelit = rewriter.treeutils.makeIntLiteral(p, -1);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.copy(lhs), minlit);
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.copy(rhs), minusonelit);
                        JCExpression x = rewriter.treeutils.makeNot(p, rewriter.treeutils.makeAnd(p, a, b));
                        checkIt(rewriter, that, "overflow in int divide", x);
                    } else if (newtype.getTag() == TypeTag.LONG) {
                        JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                        JCExpression minusonelit = rewriter.treeutils.makeLongLiteral(p, -1L);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.copy(lhs), minlit);
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.copy(rhs), minusonelit);
                        JCExpression x = rewriter.treeutils.makeNot(p, rewriter.treeutils.makeAnd(p, a, b));
                        checkIt(rewriter, that, "overflow in long divide", x);
                    }
                }
            } else if (optag == JCTree.Tag.MOD){
                // a%b is always OK
            } else {
                // FIXME: Possibly: shifts
                utils.error(that,"jml.internal","Operation not implemented in Arithmetic.makeBinaryOp: " + optag.toString());
            }
            
        }
        
        // Implement the operation, correcting for overflow if needed
        
        boolean isBigint = newtype.tsym == rewriter.BIGINT.tsym;
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
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, maxlit, rewriter.copy(bin));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.intltSymbol, rewriter.copy(bin), minlit);
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.intminusSymbol, rewriter.copy(bin), minlit);
                        JCExpression d = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.intminusSymbol, c, minlit);
                        JCExpression e = rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.treeutils.intplusSymbol, rewriter.copy(bin), minlit);
                        JCExpression f = rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.treeutils.intplusSymbol, e, minlit);
                        JCExpression g = rewriter.treeutils.makeConditional(p, a, f, 
                                rewriter.treeutils.makeConditional(p, b, d, bin));
                        bin = g;
                    } else if (typetag == TypeTag.LONG) {
                        JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                        JCExpression maxlit = rewriter.treeutils.makeLongLiteral(p, Long.MAX_VALUE);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, maxlit, rewriter.copy(bin));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol, rewriter.copy(bin), minlit);
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.longminusSymbol, rewriter.copy(bin), minlit);
                        JCExpression d = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.longminusSymbol, c, minlit);
                        JCExpression e = rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.treeutils.longplusSymbol, rewriter.copy(bin), minlit);
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
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.MUL, that.getOperator(), rewriter.copy(lhs), rewriter.copy(rhs));
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.intleSymbol,  minlit, rewriter.copy(a));
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.intleSymbol,  rewriter.copy(a), maxlit);
                        JCExpression e = rewriter.treeutils.makeAnd(p, b, c);
                        JCExpression longbin = rewriter.addImplicitConversion(that, syms.longType, rewriter.copy(bin));
                        JCExpression pos = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.intleSymbol,  zero, rewriter.copy(a));
                        JCExpression biglit = rewriter.treeutils.makeLongLiteral(p, (-2L)*Integer.MIN_VALUE);
                        JCExpression f = rewriter.treeutils.makeBinary(p, JCTree.Tag.MOD, 
                                rewriter.treeutils.findBinOpSymbol(JCTree.Tag.MOD,syms.longType), longbin, biglit);
                        JCExpression fneg = rewriter.treeutils.makeBinary(p, JCTree.Tag.MOD, 
                                rewriter.treeutils.findBinOpSymbol(JCTree.Tag.MOD,syms.longType), rewriter.copy(longbin), biglit);
                        JCExpression big = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol,  maxlitL, rewriter.copy(f));
                        JCExpression small = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol,  rewriter.copy(fneg), minlitL);
                        JCExpression sub = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.intminusSymbol,  rewriter.copy(f), biglit);
                        JCExpression posvalue = rewriter.treeutils.makeConditional(p, big, sub, rewriter.copy(f));
                        posvalue = rewriter.addImplicitConversion(that, syms.intType, posvalue);
                        JCExpression negvalue = rewriter.treeutils.makeConditional(p, small, 
                                    rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.copy(fneg), biglit), rewriter.copy(fneg));
                        negvalue = rewriter.addImplicitConversion(that, syms.intType, negvalue);
                        JCExpression g = rewriter.treeutils.makeConditional(p, e, rewriter.copy(bin), rewriter.treeutils.makeConditional(p, pos, posvalue, negvalue)); 
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
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.longleSymbol,  minlit, rewriter.copy(a));
                        JCExpression c = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.longleSymbol,  rewriter.copy(a), maxlit);
                        JCExpression e = rewriter.treeutils.makeAnd(p, b, c);
                        JCExpression longbin = bin;
                        JCExpression pos = rewriter.treeutils.makeBinary(p, JCTree.Tag.LE, rewriter.treeutils.longleSymbol,  zero, rewriter.copy(a));
                        JCExpression biglit = rewriter.treeutils.makeBinary(p,  JCTree.Tag.MUL,  
                                rewriter.treeutils.makeLongLiteral(p, -2L),
                                rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE));
                        JCExpression f = rewriter.treeutils.makeBinary(p, JCTree.Tag.MOD, 
                                rewriter.treeutils.findBinOpSymbol(JCTree.Tag.MOD,syms.longType), longbin, biglit);
                        JCExpression fneg = rewriter.treeutils.makeBinary(p, JCTree.Tag.MOD, 
                                        rewriter.treeutils.findBinOpSymbol(JCTree.Tag.MOD,syms.longType), 
                                        rewriter.copy(longbin), 
                                        biglit);
                        JCExpression big = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol,  maxlit, rewriter.copy(f));
                        JCExpression small = rewriter.treeutils.makeBinary(p, JCTree.Tag.LT, rewriter.treeutils.longltSymbol,  rewriter.copy(fneg), minlit);
                        JCExpression sub = rewriter.treeutils.makeBinary(p, JCTree.Tag.MINUS, rewriter.treeutils.longminusSymbol,  rewriter.copy(f), biglit);
                        JCExpression add = rewriter.treeutils.makeBinary(p, JCTree.Tag.PLUS, rewriter.treeutils.longplusSymbol, biglit, fneg);
                        JCExpression posvalue = rewriter.treeutils.makeConditional(p, big, sub, rewriter.copy(f));
                        JCExpression negvalue = rewriter.treeutils.makeConditional(p, small, add, rewriter.copy(fneg));
                        JCExpression g = rewriter.treeutils.makeConditional(p, e, bin, rewriter.treeutils.makeConditional(p, pos, posvalue, negvalue)); 
                        bin = g;
                    }
                } else if (optag == JCTree.Tag.DIV) {
                    if (typetag == TypeTag.INT) {
                        JCExpression minlit = rewriter.treeutils.makeIntLiteral(p, Integer.MIN_VALUE);
                        JCExpression minusonelit = rewriter.treeutils.makeIntLiteral(p, -1);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.copy(lhs), minlit);
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.inteqSymbol, rewriter.copy(rhs), minusonelit);
                        JCExpression x = rewriter.treeutils.makeNot(p, rewriter.treeutils.makeAnd(p, a, b));
                        bin = rewriter.treeutils.makeConditional(p, x, bin, minlit);
                    } else if (typetag == TypeTag.LONG) {
                        JCExpression minlit = rewriter.treeutils.makeLongLiteral(p, Long.MIN_VALUE);
                        JCExpression minusonelit = rewriter.treeutils.makeLongLiteral(p, -1L);
                        JCExpression a = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.copy(lhs), minlit);
                        JCExpression b = rewriter.treeutils.makeBinary(p, JCTree.Tag.EQ, rewriter.treeutils.longeqSymbol, rewriter.copy(rhs), minusonelit);
                        JCExpression x = rewriter.treeutils.makeNot(p, rewriter.treeutils.makeAnd(p, a, b));
                        bin = rewriter.treeutils.makeConditional(p, x, bin, minlit);
                    }
                }
            }
        }
        
        return bin;

    }

    private void checkIt(JmlAssertionAdder rewriter, JCTree pos, String str,
            JCExpression x) {
        x = condition(rewriter, x);
        if (!rac) {
            JCTree.JCIdent id = rewriter.newTemp(x);
            rewriter.saveMapping(x,id);
        }
        String mode = JmlOption.value(context,JmlOption.ARITHMETIC);
        if (mode == null) { 
            rewriter.utils.warning(pos, "jml.internal", "Null arithmetic failure mode should have been corrected before reaching this point"); 
        } else switch (mode) {
            case "hard" -> rewriter.addAssert(pos, Label.ARITHMETIC_OP_RANGE, x, str);
            case "soft" -> rewriter.addCheck(pos, Label.ARITHMETIC_OP_RANGE, x, str);
            case "quiet" -> rewriter.addAssume(pos, Label.ARITHMETIC_OP_RANGE, x);
            default -> { rewriter.utils.warning(pos, "jml.internal", "Erroneous arithmetic failure mode should have been corrected before reaching this point: " + mode); }
        }
    }
    
    /** This implements the bigint (which is also real) mathematical mode */
    public static class Math extends Arithmetic implements IArithmeticMode {
        
        public static Math instance(Context context) {
            return instance(context,Math.class);
        }
        
        @Override
        public Mode mode() { return Mode.MATH; }
        
        /** Returns the appropriate mathematical type (\bigint or \real) given the input type */
        Type mathType(JmlAssertionAdder rewriter, Type t) {
            TypeTag tag = t.getTag();
            if (rewriter.jmltypes.isJmlType(t)) return t;
            if (rewriter.jmltypes.isIntegral(t)) return rewriter.BIGINT;
            if (tag == TypeTag.DOUBLE || tag == TypeTag.FLOAT) return rewriter.REAL;
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
