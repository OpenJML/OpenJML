package com.sun.tools.javac.comp;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.util.*;
import com.sun.tools.javac.jvm.*;

import static com.sun.tools.javac.code.TypeTag.BOOLEAN;
import static com.sun.tools.javac.jvm.ByteCodes.bool_and;
import static com.sun.tools.javac.jvm.ByteCodes.bool_or;
import static com.sun.tools.javac.jvm.ByteCodes.dadd;
import static com.sun.tools.javac.jvm.ByteCodes.dcmpg;
import static com.sun.tools.javac.jvm.ByteCodes.dcmpl;
import static com.sun.tools.javac.jvm.ByteCodes.ddiv;
import static com.sun.tools.javac.jvm.ByteCodes.dmod;
import static com.sun.tools.javac.jvm.ByteCodes.dmul;
import static com.sun.tools.javac.jvm.ByteCodes.dsub;
import static com.sun.tools.javac.jvm.ByteCodes.fadd;
import static com.sun.tools.javac.jvm.ByteCodes.fcmpg;
import static com.sun.tools.javac.jvm.ByteCodes.fcmpl;
import static com.sun.tools.javac.jvm.ByteCodes.fdiv;
import static com.sun.tools.javac.jvm.ByteCodes.fmod;
import static com.sun.tools.javac.jvm.ByteCodes.fmul;
import static com.sun.tools.javac.jvm.ByteCodes.fsub;
import static com.sun.tools.javac.jvm.ByteCodes.iadd;
import static com.sun.tools.javac.jvm.ByteCodes.iand;
import static com.sun.tools.javac.jvm.ByteCodes.idiv;
import static com.sun.tools.javac.jvm.ByteCodes.if_acmpeq;
import static com.sun.tools.javac.jvm.ByteCodes.if_acmpne;
import static com.sun.tools.javac.jvm.ByteCodes.if_icmpeq;
import static com.sun.tools.javac.jvm.ByteCodes.if_icmpge;
import static com.sun.tools.javac.jvm.ByteCodes.if_icmpgt;
import static com.sun.tools.javac.jvm.ByteCodes.if_icmple;
import static com.sun.tools.javac.jvm.ByteCodes.if_icmplt;
import static com.sun.tools.javac.jvm.ByteCodes.if_icmpne;
import static com.sun.tools.javac.jvm.ByteCodes.imod;
import static com.sun.tools.javac.jvm.ByteCodes.imul;
import static com.sun.tools.javac.jvm.ByteCodes.ior;
import static com.sun.tools.javac.jvm.ByteCodes.ishl;
import static com.sun.tools.javac.jvm.ByteCodes.ishll;
import static com.sun.tools.javac.jvm.ByteCodes.ishr;
import static com.sun.tools.javac.jvm.ByteCodes.ishrl;
import static com.sun.tools.javac.jvm.ByteCodes.isub;
import static com.sun.tools.javac.jvm.ByteCodes.iushr;
import static com.sun.tools.javac.jvm.ByteCodes.iushrl;
import static com.sun.tools.javac.jvm.ByteCodes.ixor;
import static com.sun.tools.javac.jvm.ByteCodes.ladd;
import static com.sun.tools.javac.jvm.ByteCodes.land;
import static com.sun.tools.javac.jvm.ByteCodes.lcmp;
import static com.sun.tools.javac.jvm.ByteCodes.ldiv;
import static com.sun.tools.javac.jvm.ByteCodes.lmod;
import static com.sun.tools.javac.jvm.ByteCodes.lmul;
import static com.sun.tools.javac.jvm.ByteCodes.lor;
import static com.sun.tools.javac.jvm.ByteCodes.lshl;
import static com.sun.tools.javac.jvm.ByteCodes.lshll;
import static com.sun.tools.javac.jvm.ByteCodes.lshr;
import static com.sun.tools.javac.jvm.ByteCodes.lshrl;
import static com.sun.tools.javac.jvm.ByteCodes.lsub;
import static com.sun.tools.javac.jvm.ByteCodes.lushr;
import static com.sun.tools.javac.jvm.ByteCodes.lxor;
import static com.sun.tools.javac.jvm.ByteCodes.string_add;

import org.jmlspecs.openjml.Utils;

public class JmlConstFold extends ConstFold {
    protected Context context;
    
    public static void preRegister(final Context context) {
        context.put(ConstFold.constFoldKey, new Context.Factory<ConstFold>() {
            public ConstFold make(Context context) { 
                return new JmlConstFold(context);
            }
        });
    }
    
    protected JmlConstFold(Context context) {
        super(context);
        this.context = context;
    }
    
    Type fold1(int opcode, Type operand) {
        Object n = operand.constValue();
        if (opcode == ByteCodes.ineg) {
            long v = ((Number)n).longValue();
            if (v == Integer.MIN_VALUE) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range int negation: -(" + v + ")");
            }
        } else if (opcode == ByteCodes.lneg) {
            long v = ((Number)n).longValue();
            if (v == Long.MIN_VALUE) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range long negation: -(" + v + ")");
            }
        } else if (opcode == ByteCodes.dneg) {
            // FIXME -- is there any overflow
        } else if (opcode == ByteCodes.fneg) {
            // FIXME -- is there any overflow
        }
        return super.fold1(opcode, operand);
    }
    
    Type fold2(int opcode, Type left, Type right) {
        Object l = left.constValue();
        Object r = right.constValue();
        switch (opcode) {
        case iadd: {
            var vl = intValue(l);
            var vr = intValue(r);
            if ((vr > 0 && vl > Integer.MAX_VALUE - vr) || (vr < 0 && vl < Integer.MIN_VALUE - vr)) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range int sum: " + vl + " + " + vr);
            }
            break;
        }
        case isub: {
            var vl = intValue(l);
            var vr = intValue(r);
            if ((vr < 0 && vl > Integer.MAX_VALUE + vr) || (vr > 0 && vl < Integer.MIN_VALUE + vr)) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range int subtraction: " + vl + " - " + vr);
            }
            break;
        }
        case imul: {
            var vl = intValue(l);
            var vr = intValue(r);
            if ((vr > 1 && vl > Integer.MAX_VALUE/vr) || (vr < 0 && vl < Integer.MAX_VALUE/vr)
                    || (vr > 1 && vl < Integer.MIN_VALUE/vr) || (vr < -1 && vl > Integer.MIN_VALUE/vr)) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range int multiply: " + vl + " * " + vr);
            }
            break;
        }
        case idiv: {
            var vl = intValue(l);
            var vr = intValue(r);
            if (vr == -1 && vl == Integer.MIN_VALUE) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range int divide: " + vl + " / " + vr);
            }
            if (vr == 0) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: int divide by zero");
            }
            break;
        }
        case imod: {
            var vr = intValue(r);
            if (vr == 0) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: int divide or modulo by zero");
            }
            break;
        }
        case ishl: case ishll:
            // FIXME
            break;
        case ishr: case ishrl:
            // FIXME
            break;
        case iushr: case iushrl:
            // FIXME
            break;

        case ladd: {
            var vl = longValue(l);
            var vr = longValue(r);
            if ((vr > 0 && vl > Long.MAX_VALUE - vr) || (vr < 0 && vl < Long.MIN_VALUE - vr)) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range long sum: " + vl + " + " + vr);
            }
            break;
        }
        case lsub: {
            var vl = longValue(l);
            var vr = longValue(r);
            if ((vr < 0 && vl > Long.MAX_VALUE + vr) || (vr > 0 && vl < Long.MIN_VALUE + vr)) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range long subtraction: " + vl + " - " + vr);
            }
            break;
        }
        case lmul: {
            var vl = longValue(l);
            var vr = longValue(r);
            if ((vr > 1 && vl > Long.MAX_VALUE/vr) || (vr < 0 && vl < Long.MAX_VALUE/vr)
                    || (vr > 1 && vl < Long.MIN_VALUE/vr) || (vr < -1 && vl > Long.MIN_VALUE/vr)) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range long multiply: " + vl + " * " + vr);
            }
            break;
        }
        case ldiv: {
            var vl = longValue(l);
            var vr = longValue(r);
            if (vr == -1 && vl == Long.MIN_VALUE) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range long divide: " + vl + " / " + vr);
            }
            if (vr == 0) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: long divide by zero");
            }
            break;
        }
        case lmod: {
            var vr = longValue(r);
            if (vr == 0) {
                Utils.instance(context).warning(0, "jml.message", "Constant folding: long modulo by zero");
            }
            break;
        }
        case lshl: case lshll:
            // FIXME
            break;
        case lshr: case lshrl:
            // FIXME
            break;
        case lushr:
            // FIXME
            break;

            // FIXME - do these operations need checking
//        case fadd:
//            return syms.floatType.constType(
//                Float.valueOf(floatValue(l) + floatValue(r)));
//        case fsub:
//            return syms.floatType.constType(
//                Float.valueOf(floatValue(l) - floatValue(r)));
//        case fmul:
//            return syms.floatType.constType(
//                Float.valueOf(floatValue(l) * floatValue(r)));
//        case fdiv:
//            return syms.floatType.constType(
//                Float.valueOf(floatValue(l) / floatValue(r)));
//        case fmod:
//            return syms.floatType.constType(
//                Float.valueOf(floatValue(l) % floatValue(r)));
//        case dadd:
//            return syms.doubleType.constType(
//                Double.valueOf(doubleValue(l) + doubleValue(r)));
//        case dsub:
//            return syms.doubleType.constType(
//                Double.valueOf(doubleValue(l) - doubleValue(r)));
//        case dmul:
//            return syms.doubleType.constType(
//                Double.valueOf(doubleValue(l) * doubleValue(r)));
//        case ddiv:
//            return syms.doubleType.constType(
//                Double.valueOf(doubleValue(l) / doubleValue(r)));
//        case dmod:
//            return syms.doubleType.constType(
//                Double.valueOf(doubleValue(l) % doubleValue(r)));

        default:
            break;
        }
        return super.fold2(opcode, left, right);
    }
    
    Type coerce(Type etype, Type ttype) {
        if (etype.isNumeric()) {
            Object n = etype.constValue();
            switch (ttype.getTag()) {
            case BYTE:
                if (etype.isIntegral()) {
                    long v = ((Number)n).longValue();
                    if (v < Byte.MIN_VALUE || v > Byte.MAX_VALUE) {
                        Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range conversion: (byte)" + v);
                    }
                } else {
                    
                }
                break;
            case CHAR:
                if (etype.isIntegral()) {
                    long v = ((Number)n).longValue();
                    if (v < Character.MIN_VALUE || v > Character.MAX_VALUE) {
                        Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range conversion: (char)" + v);
                    }
                } else {
                    
                }
                break;
            case SHORT:
                if (etype.isIntegral()) {
                    long v = ((Number)n).longValue();
                    if (v < Short.MIN_VALUE || v > Short.MAX_VALUE) {
                        Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range conversion: (short)" + v);
                    }
                } else {
                    
                }
                break;
            case INT:
                if (etype.isIntegral()) {
                    long v = ((Number)n).longValue();
                    if (v < Integer.MIN_VALUE || v > Integer.MAX_VALUE) {
                        Utils.instance(context).warning(0, "jml.message", "Constant folding: out of range conversion: (int)" + v);
                    }
                } else {
                    
                }
                break;
            case LONG:
            case FLOAT:
            case DOUBLE:
            }
        }

        return super.coerce(etype, ttype);
    }

}
