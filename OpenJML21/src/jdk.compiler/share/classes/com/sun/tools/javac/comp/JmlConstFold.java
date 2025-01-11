package com.sun.tools.javac.comp;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.util.Context;

public class JmlConstFold extends ConstFold {
    
    // FIXME - need to do this check only if the local environment is 'safe'
    // FIXME - need a position for the error messages
    // FIXME - need to check the unary and binary operators also
    
    Context context;

    protected JmlConstFold(Context context) {
        super(context);
        this.context = context;
        System.out.println("MADE A JmlCOnstFold");
    }
    
    public static ConstFold instance(Context context) {
        ConstFold instance = context.get(constFoldKey);
        if (instance == null)
            instance = new JmlConstFold(context);
        return instance;
    }
    
    public static void preRegister(final Context context) {
        context.put(constFoldKey, new Context.Factory<ConstFold>() {
            public ConstFold make(Context context) {
                return new JmlConstFold(context); // Registers itself on construction
            }
        });
    }

    
    Type coerce(Type etype, Type ttype, com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition pos) {
        // WAS if (etype.baseType() == ttype.baseType())
        if (etype.tsym.type == ttype.tsym.type)
            return etype;
        if (pos != null && etype.isNumeric()) {
            Object n = etype.constValue();
            switch (etype.getTag()) {
            case DOUBLE:
            case FLOAT:
                var d = doubleValue(n);
                switch (ttype.getTag()) {
                case BYTE:
                    if (d < Byte.MIN_VALUE || d > Byte.MAX_VALUE) {
                        // FIXME Need a position
                        org.jmlspecs.openjml.Utils.instance(context).error(0, "jml.message", "Constant folding computation is out of range: (byte)" + d);
                    }
                    break;
                case CHAR:
                    if (d < Character.MIN_VALUE || d > Character.MAX_VALUE) {
                        // FIXME Need a position
                        org.jmlspecs.openjml.Utils.instance(context).error(0, "jml.message", "Constant folding computation is out of range: (char)" + d);
                    }
                    break;
                case SHORT:
                    if (d < Short.MIN_VALUE || d > Short.MAX_VALUE) {
                        // FIXME Need a position
                        org.jmlspecs.openjml.Utils.instance(context).error(0, "jml.message", "Constant folding computation is out of range: (short)" + d);
                    }
                    break;
                case INT:
                    if (d < Integer.MIN_VALUE || d > Integer.MAX_VALUE) {
                        // FIXME Need a position
                        org.jmlspecs.openjml.Utils.instance(context).error(0, "jml.message", "Constant folding computation is out of range: (int)" + d);
                    }
                    break;
                case LONG:
                    if (d < Long.MIN_VALUE || d > Long.MAX_VALUE) {
                        // FIXME Need a position
                        org.jmlspecs.openjml.Utils.instance(context).error(0, "jml.message", "Constant folding computation is out of range: (long)" + d);
                    }
                    break;
                case FLOAT:
                    // FIXME - check range here?
                    break;
                case DOUBLE:
                    break;
                }
                break;
            default:
                long k = longValue(n);
                switch (ttype.getTag()) {
                case BYTE:
                    if (k < Byte.MIN_VALUE || k > Byte.MAX_VALUE) {
                        // FIXME Need a position
                        org.jmlspecs.openjml.Utils.instance(context).error(0, "jml.message", "Constant folding computation is out of range: (byte)" + k);
                    }
                    break;
                case CHAR:
                    if (k < Character.MIN_VALUE || k > Character.MAX_VALUE) {
                        // FIXME Need a position
                        org.jmlspecs.openjml.Utils.instance(context).error(0, "jml.message", "Constant folding computation is out of range: (char)" + k);
                    }
                    break;
                case SHORT:
                    if (k < Short.MIN_VALUE || k > Short.MAX_VALUE) {
                        // FIXME Need a position
                        org.jmlspecs.openjml.Utils.instance(context).error(pos, "jml.message", "Constant folding computation is out of range: (short)" + k);
                    }
                    break;
                case INT:
                    if (k < Integer.MIN_VALUE || k > Integer.MAX_VALUE) {
                        // FIXME Need a position
                        org.jmlspecs.openjml.Utils.instance(context).error(0, "jml.message", "Constant folding computation is out of range: (int)" + k);
                    }
                    break;
                case LONG:
                case FLOAT:
                case DOUBLE:
                    // FIXME - any checking for float and double
                    break;
                }
                break;
            }
        }
        return super.coerce(etype, ttype, pos);
    }


}
