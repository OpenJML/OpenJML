package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IArithmeticMode;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.JmlType;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.ExpressionExtension;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Names;
import org.jmlspecs.openjml.JmlOption;

abstract public class Arithmetic extends ExpressionExtension {
    
    public static enum Mode { MATH, SAFE, JAVA };
    
    public Arithmetic(Context context) {
        super(context);
        this.intType = Symtab.instance(context).intType;
    }
    
    static public JmlToken[] tokens() { return new JmlToken[]{
            JmlToken.BSBIGINT_MATH, JmlToken.BSJAVAMATH, JmlToken.BSSAFEMATH}; }
    
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
            if (!(sym instanceof Symbol.PackageSymbol)) return defaultArithmeticMode(sym,jml);
            String v = JmlOption.value(context,JmlOption.SPEC_MATH);
//            if ("java".equals(v)) return Java.instance(context);
//            if ("safe".equals(v)) return Safe.instance(context);
//            return Math.instance(context);
            return Java.instance(context);
        }
    }
    
    public Type maxtype(JmlTypes jmltypes, Type lhs, Type rhs) {
        if (lhs.tag == TypeTags.CLASS) lhs = Types.instance(context).unboxedType(lhs); 
        if (rhs.tag == TypeTags.CLASS) rhs = Types.instance(context).unboxedType(rhs); 
        int lt = lhs.tag;
        int rt = rhs.tag;
        if (lt == TypeTags.UNKNOWN && lhs == jmltypes.REAL) return lhs;
        if (rt == TypeTags.UNKNOWN && rhs == jmltypes.REAL) return rhs;
        if (lt == TypeTags.UNKNOWN && lhs == jmltypes.BIGINT) {
            if (rt == TypeTags.DOUBLE || rt == TypeTags.FLOAT) return jmltypes.REAL;
            return lhs;
        }
        if (rt == TypeTags.UNKNOWN && rhs == jmltypes.BIGINT) {
            if (lt == TypeTags.DOUBLE || lt == TypeTags.FLOAT) return jmltypes.REAL;
            return rhs;
        }
        if (lt == TypeTags.DOUBLE) return lhs;
        if (rt == TypeTags.DOUBLE) return rhs;
        if (lt == TypeTags.FLOAT) return lhs; 
        if (rt == TypeTags.FLOAT) return rhs; 
        if (lt == TypeTags.LONG) return lhs; 
        if (rt == TypeTags.LONG) return rhs; 
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
        JmlToken token = tree.token;
        
        // Expect one argument of any type, result type is the same type
        // The argument expression may contain JML constructs
        attr.attribArgs(tree.args, env);
        attr.attribTypes(tree.typeargs, env);
        int n = tree.args.size();
        if (n != 1) {
            error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
        }
        Type t = syms.errType;
        if (n > 0) {
            return tree.args.get(0).type;
        }
        return t;
    }
    
    public JCExpression makeNeg(JmlAssertionAdder rewriter, JCUnary that, JCExpression arg, Type newtype) {
        JCExpression eresult = null;
        int tag = that.getTag();
        if (rewriter.rac && rewriter.jmltypes.isJmlType(newtype)) {
            if (tag == JCTree.NEG){ 
                if (newtype == rewriter.jmltypes.BIGINT) {
                    eresult = rewriter.treeutils.makeUtilsMethodCall(that.pos,"bigint_neg",arg);
                }
                if (newtype == rewriter.jmltypes.REAL) {
                    eresult = rewriter.treeutils.makeUtilsMethodCall(that.pos,"real_neg",arg);
                }
                if (rewriter.splitExpressions) eresult = rewriter.newTemp(eresult);
            } else if (tag == JCTree.PLUS) {
                eresult = arg;
            } else { 
                rewriter.log.error(that,"jml.internal","Unknown unary operation for JML type: " + that);
                eresult = arg;
            }
        } else {
            JCExpression e = rewriter.treeutils.makeUnary(that.pos,tag,that.getOperator(),arg);
            eresult = e;
        }
        return eresult;
    }
    
    public static class Math extends Arithmetic implements IArithmeticMode {
        
        public Math(Context context) {
            super(context);
        }
        
        public static Math instance(Context context) {
            return instance(context,Math.class);
        }
        
        @Override
        public Mode mode() { return Mode.MATH; }
        
        Type mathType(JmlAssertionAdder rewriter, Type t) {
            int tag = t.tag;
            if (rewriter.jmltypes.isJmlType(t)) return t;
            if (tag <= TypeTags.LONG) return rewriter.jmltypes.BIGINT;
            if (tag == TypeTags.DOUBLE || tag == TypeTags.FLOAT) return rewriter.jmltypes.REAL;
            return t;
        }
        
        @Override
        public JCExpression rewriteUnary(JmlAssertionAdder rewriter, JCUnary that) {
            int tag = that.getTag();
            JCExpression e;
            switch (tag) {
                case JCTree.NEG: {
                    Type newtype = mathType(rewriter,that.type);
                    JCExpression arg = rewriter.convertExpr(that.getExpression());
                    arg = rewriter.addImplicitConversion(arg,newtype,arg);
                    e = makeNeg(rewriter,that,arg,newtype);
                    break;
                } 
                case JCTree.PLUS:
                case JCTree.COMPL: {
                    Type newtype = that.type; // No overflows possible - do not need to promote the type
                    JCExpression arg = rewriter.convertExpr(that.getExpression());
                    arg = rewriter.addImplicitConversion(arg,newtype,arg);
                    e = rewriter.treeutils.makeUnary(that.pos,that.getTag(),that.getOperator(),arg);
                    break;
                } 
                default:
                    e = null;
                    rewriter.log.error(that.pos, "jml.internal", "Unexpected operation in Arithmetic.Math.rewriteUnary");
            }
            return e;
        }
        
        @Override
        public JCExpression rewriteBinary(JmlAssertionAdder rewriter, JCBinary that) {
            this.javaChecks = rewriter.esc || (rewriter.rac && JmlOption.isOption(context,JmlOption.RAC_JAVA_CHECKS));

            int op = that.getTag();
            Type newtype = that.type;
            if (newtype.tag == TypeTags.BOOLEAN) {
                newtype = maxtype(rewriter.jmltypes,that.getLeftOperand().type,that.getRightOperand().type);
            } else {
                newtype = rewriter.jmltypes.BIGINT;
            }
            
            JCExpression lhs = rewriter.convertExpr(that.getLeftOperand());
            lhs = rewriter.addImplicitConversion(lhs,newtype,lhs);
            JCExpression rhs = rewriter.convertExpr(that.getRightOperand());
            rhs = rewriter.addImplicitConversion(rhs,newtype,rhs);

            if (javaChecks) {
                if (op == JCTree.DIV || op == JCTree.MOD) {
                    JCExpression nonzero = rewriter.nonZeroCheck(that,rhs,newtype);
                    rewriter.addAssert(that,
                            rewriter.translatingJML ? Label.UNDEFINED_DIV0 : Label.POSSIBLY_DIV0,
                            rewriter.treeutils.makeImplies(that.pos, rewriter.condition, nonzero));
                }
            }

            JCExpression bin = rewriter.makeBin(that,op,that.getOperator(),lhs,rhs,newtype);
            return bin;
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
            JCExpression arg = rewriter.convertExpr(that.getExpression());
            arg = rewriter.addImplicitConversion(arg,that.type,arg);
            int tag = that.getTag();
            if (tag == JCTree.NEG) {
                if (that.type.tag == TypeTags.INT) {
                    JCExpression e = rewriter.treeutils.makeNot(arg.pos,rewriter.treeutils.makeEquality(arg.pos, arg, rewriter.treeutils.makeIntLiteral(arg.pos, Integer.MIN_VALUE)));
                    rewriter.addAssert(that,Label.ARITHMETIC_OP_RANGE,e);
                } else if (that.type.tag == TypeTags.LONG) {
                    JCExpression e = rewriter.treeutils.makeNot(arg.pos,rewriter.treeutils.makeEquality(arg.pos, arg, rewriter.treeutils.makeLit(arg.pos, that.type, Long.MIN_VALUE)));
                    rewriter.addAssert(that,Label.ARITHMETIC_OP_RANGE,e);
                }
            }
            JCExpression eresult = makeNeg(rewriter,that,arg,that.type);
            return eresult;
        }
        
        @Override
        public JCExpression rewriteBinary(JmlAssertionAdder rewriter, JCBinary that) {
            this.javaChecks = rewriter.esc || (rewriter.rac && JmlOption.isOption(context,JmlOption.RAC_JAVA_CHECKS));

            int op = that.getTag();
            Type newtype = that.type;
            if (newtype.tag == TypeTags.BOOLEAN) {
                newtype = maxtype(rewriter.jmltypes,that.getLeftOperand().type,that.getRightOperand().type);
            }
            
            JCExpression lhs = rewriter.convertExpr(that.getLeftOperand());
            lhs = rewriter.addImplicitConversion(lhs,newtype,lhs);
            JCExpression rhs = rewriter.convertExpr(that.getRightOperand());
            rhs = rewriter.addImplicitConversion(rhs,newtype,rhs);

            if (javaChecks) {
                if (op == JCTree.DIV || op == JCTree.MOD) {
                    JCExpression nonzero = rewriter.nonZeroCheck(that,rhs,newtype);
                    rewriter.addAssert(that,
                            rewriter.translatingJML ? Label.UNDEFINED_DIV0 : Label.POSSIBLY_DIV0,
                            rewriter.condition == null ? nonzero : rewriter.treeutils.makeImplies(that.pos, rewriter.condition, nonzero));
                }
            }
            
            if (op == JCTree.PLUS || op == JCTree.MINUS) {
                // For + : a > 0 && b > 0 ==> a <= MAX - b; a < 0 && b < 0 ==> MIN - b <= a;
                // For - : a > 0 && b < 0 ==> a <= MAX + b; a < 0 && b > 0 ==> MIN + b <= a;
                int opn = op == JCTree.PLUS ? JCTree.MINUS : JCTree.PLUS;
                String str = op == JCTree.PLUS ? "sum" : "difference";
                if (newtype.tag == TypeTags.INT) {
                    Symbol sym = op == JCTree.PLUS ? rewriter.treeutils.intminusSymbol : rewriter.treeutils.intplusSymbol;
                    JCExpression maxlit = rewriter.treeutils.makeIntLiteral(that.pos, Integer.MAX_VALUE);
                    JCExpression minlit = rewriter.treeutils.makeIntLiteral(that.pos, Integer.MIN_VALUE);
                    JCExpression zerolit = rewriter.treeutils.makeIntLiteral(that.pos, 0);
                    JCExpression a = rewriter.makeBin(that, JCTree.LT, rewriter.treeutils.intltSymbol, zerolit, lhs, newtype);
                    JCExpression b1 = rewriter.makeBin(that, JCTree.LT, rewriter.treeutils.intltSymbol, zerolit, rhs, newtype);
                    JCExpression b2 = rewriter.makeBin(that, JCTree.LT, rewriter.treeutils.intltSymbol, rhs, zerolit, newtype);
                    JCExpression b = op == JCTree.PLUS ? b1 : b2;
                    JCExpression c = rewriter.makeBin(that,  opn,  sym, maxlit, rhs, newtype);
                    JCExpression d = rewriter.makeBin(that, JCTree.LE, rewriter.treeutils.intleSymbol, lhs, c, newtype);
                    JCExpression x = rewriter.treeutils.makeImplies(that.pos, rewriter.treeutils.makeAnd(that.pos,a,b), d);
                    rewriter.addAssert(that, Label.ARITHMETIC_OP_RANGE, x, "overflow in int " + str);
                    a = rewriter.makeBin(that, JCTree.LT, rewriter.treeutils.intltSymbol, lhs, zerolit, newtype);
                    b = op == JCTree.PLUS ? b2 : b1;
                    c = rewriter.makeBin(that,  opn,  sym, minlit, rhs, newtype);
                    d = rewriter.makeBin(that, JCTree.LE, rewriter.treeutils.intleSymbol, c, lhs, newtype);
                    x = rewriter.treeutils.makeImplies(that.pos, rewriter.treeutils.makeAnd(that.pos,a,b), d);
                    rewriter.addAssert(that, Label.ARITHMETIC_OP_RANGE, x, "underflow in int " + str);
                } else if (newtype.tag == TypeTags.LONG) {
                    Symbol sym = op == JCTree.PLUS ? rewriter.treeutils.longminusSymbol : rewriter.treeutils.longplusSymbol;
                    JCExpression maxlit = rewriter.treeutils.makeLongLiteral(that.pos, Long.MAX_VALUE);
                    JCExpression minlit = rewriter.treeutils.makeLongLiteral(that.pos, Long.MIN_VALUE);
                    JCExpression zerolit = rewriter.treeutils.makeLongLiteral(that.pos, 0L);
                    JCExpression a = rewriter.makeBin(that, JCTree.LT, rewriter.treeutils.longltSymbol, zerolit, lhs, newtype);
                    JCExpression b1 = rewriter.makeBin(that, JCTree.LT, rewriter.treeutils.longltSymbol, zerolit, rhs, newtype);
                    JCExpression b2 = rewriter.makeBin(that, JCTree.LT, rewriter.treeutils.longltSymbol, rhs, zerolit, newtype);
                    JCExpression b = op == JCTree.PLUS ? b1 : b2;
                    JCExpression c = rewriter.makeBin(that,  opn,  sym, maxlit, rhs, newtype);
                    JCExpression d = rewriter.makeBin(that, JCTree.LE, rewriter.treeutils.longleSymbol, lhs, c, newtype);
                    JCExpression x = rewriter.treeutils.makeImplies(that.pos, rewriter.treeutils.makeAnd(that.pos,a,b), d);
                    rewriter.addAssert(that, Label.ARITHMETIC_OP_RANGE, x, "overflow in long " + str);
                    a = rewriter.makeBin(that, JCTree.LT, rewriter.treeutils.longltSymbol, lhs, zerolit, newtype);
                    b = op == JCTree.PLUS ? b2 : b1;
                    c = rewriter.makeBin(that,  opn,  sym, minlit, rhs, newtype);
                    d = rewriter.makeBin(that, JCTree.LE, rewriter.treeutils.longleSymbol, c, lhs, newtype);
                    x = rewriter.treeutils.makeImplies(that.pos, rewriter.treeutils.makeAnd(that.pos,a,b), d);
                    rewriter.addAssert(that, Label.ARITHMETIC_OP_RANGE, x, "underflow in long " + str);
                }
            } else if (op == JCTree.MUL) {
                // FIXME - not implemented
            } else if (op == JCTree.DIV) {
                // a/b overflows only if  a == min && b == -1
                if (newtype.tag == TypeTags.INT) {
                    JCExpression minlit = rewriter.treeutils.makeIntLiteral(that.pos, Integer.MIN_VALUE);
                    JCExpression minusonelit = rewriter.treeutils.makeIntLiteral(that.pos, -1);
                    JCExpression a = rewriter.treeutils.makeBinary(that.pos, JCTree.EQ, rewriter.treeutils.inteqSymbol, lhs, minlit);
                    JCExpression b = rewriter.treeutils.makeBinary(that.pos, JCTree.EQ, rewriter.treeutils.inteqSymbol, rhs, minusonelit);
                    JCExpression x = rewriter.treeutils.makeNot(that.pos, rewriter.treeutils.makeAnd(that.pos, a, b));
                    rewriter.addAssert(that, Label.ARITHMETIC_OP_RANGE, x, "overflow in int divide");
                } else if (newtype.tag == TypeTags.LONG) {
                    JCExpression minlit = rewriter.treeutils.makeLongLiteral(that.pos, Long.MIN_VALUE);
                    JCExpression minusonelit = rewriter.treeutils.makeLongLiteral(that.pos, -1L);
                    JCExpression a = rewriter.treeutils.makeBinary(that.pos, JCTree.EQ, rewriter.treeutils.longeqSymbol, lhs, minlit);
                    JCExpression b = rewriter.treeutils.makeBinary(that.pos, JCTree.EQ, rewriter.treeutils.longeqSymbol, rhs, minusonelit);
                    JCExpression x = rewriter.treeutils.makeNot(that.pos, rewriter.treeutils.makeAnd(that.pos, a, b));
                    rewriter.addAssert(that, Label.ARITHMETIC_OP_RANGE, x, "overflow in long divide");
                }
            } else if (op == JCTree.MOD){
                // a%b is always OK
            }

            JCExpression bin = rewriter.makeBin(that,op,that.getOperator(),lhs,rhs,newtype);
            return bin;
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
            JCExpression arg = rewriter.convertExpr(that.getExpression());
            arg = rewriter.addImplicitConversion(arg,that.type,arg);
            int tag = that.getTag();
            JCExpression eresult = null;
            if (rewriter.rac && rewriter.jmltypes.isJmlType(that.type)) {
                if (tag == JCTree.NEG){ 
                    if (that.type == rewriter.jmltypes.BIGINT) {
                        eresult = rewriter.treeutils.makeUtilsMethodCall(that.pos,"bigint_neg",arg);
                    }
                    if (that.type == rewriter.jmltypes.REAL) {
                        eresult = rewriter.treeutils.makeUtilsMethodCall(that.pos,"real_neg",arg);
                    }
                    if (rewriter.splitExpressions) eresult = rewriter.newTemp(eresult);
                } else if (tag == JCTree.PLUS) {
                    eresult = arg;
                } else if (tag == JCTree.COMPL) {
                    // Assumed to be a bigint operation - equivalent to -x-1
                    JCExpression e = rewriter.treeutils.makeUtilsMethodCall(that.pos,"bigint_neg",arg);
                    e = rewriter.treeutils.makeUtilsMethodCall(that.pos,"bigint_sub1",e);
                    eresult = e;
                } else { 
                    rewriter.log.error(that,"jml.internal","Unknown unary operation for JML type: " + that);
                    eresult = arg;
                }
            } else {
                JCExpression e = rewriter.treeutils.makeUnary(that.pos,tag,that.getOperator(),arg);
                eresult = e;
            }
            return eresult;
        }
        
        @Override
        public JCExpression rewriteBinary(JmlAssertionAdder rewriter, JCBinary that) {
            this.javaChecks = rewriter.esc || (rewriter.rac && JmlOption.isOption(context,JmlOption.RAC_JAVA_CHECKS));

            int op = that.getTag();
            Type newtype = that.type;
            if (newtype.tag == TypeTags.BOOLEAN) {
                newtype = maxtype(rewriter.jmltypes,that.getLeftOperand().type,that.getRightOperand().type);
            }
            
            JCExpression lhs = rewriter.convertExpr(that.getLeftOperand());
            lhs = rewriter.addImplicitConversion(lhs,newtype,lhs);
            JCExpression rhs = rewriter.convertExpr(that.getRightOperand());
            rhs = rewriter.addImplicitConversion(rhs,newtype,rhs);

            if (javaChecks) {
                if (op == JCTree.DIV || op == JCTree.MOD) {
                    JCExpression nonzero = rewriter.nonZeroCheck(that,rhs,newtype);
                    rewriter.addAssert(that,
                            rewriter.translatingJML ? Label.UNDEFINED_DIV0 : Label.POSSIBLY_DIV0,
                            rewriter.condition == null ? nonzero : rewriter.treeutils.makeImplies(that.pos, rewriter.condition, nonzero));
                }
            }

            JCExpression bin = rewriter.makeBin(that,op,that.getOperator(),lhs,rhs,newtype);
            return bin;
        }

    }

}
