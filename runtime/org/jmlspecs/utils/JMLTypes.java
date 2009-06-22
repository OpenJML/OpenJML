package org.jmlspecs.utils;

import java.util.Map;

import org.jmlspecs.annotations.*;

/** Utility functions that implement functions for the IJmlType interface
 * and its subinterfaces.
 * 
 * @author David R. Cok
 *
 */
public class JMLTypes {

    static JMLTypesImpl types = new JMLTypesImpl();
    
    static IJMLReferenceType makeReferenceType(Class<?> clazz) {
        return types.makeReferenceType(clazz);
    }

    static IJMLReferenceType makeParameterizedType(IJMLReferenceType clazz, IJMLReferenceType[] args) {
        return types.makeParameterizedType(clazz,args);
    }
    
    static boolean isSubtypeOf(IJMLType tsub, IJMLType tsup) {
        return tsub.isSubtypeOf(tsup);
    }
    
    static IJMLType convert(Class<?> clazz) {
        return types.convert(clazz);
    }

    static public class JMLTypesImpl {

        public IJMLReferenceType makeReferenceType(Class<?> clazz) {
            return new JMLReferenceType(clazz);
        }

        public IJMLReferenceType makeParameterizedType(IJMLReferenceType clazz, IJMLReferenceType[] args) {
            return new JMLParameterizedType(clazz,args);
        }

        public IJMLType convert(Class<?> clazz) {
            if (!clazz.isPrimitive()) return makeReferenceType(clazz);
            if (clazz.equals(Integer.TYPE)) return JMLPrimitiveType.INT;
            if (clazz.equals(Boolean.TYPE)) return JMLPrimitiveType.BOOLEAN;
            if (clazz.equals(Short.TYPE)) return JMLPrimitiveType.SHORT;
            if (clazz.equals(Character.TYPE)) return JMLPrimitiveType.CHAR;
            if (clazz.equals(Byte.TYPE)) return JMLPrimitiveType.BYTE;
            if (clazz.equals(Long.TYPE)) return JMLPrimitiveType.LONG;
            if (clazz.equals(Float.TYPE)) return JMLPrimitiveType.FLOAT;
            if (clazz.equals(Double.TYPE)) return JMLPrimitiveType.DOUBLE;
            return null;
        }

        static public class JMLPrimitiveType implements IJMLPrimitiveType {
            private JMLPrimitiveType() {
            }
            public boolean equals(IJMLPrimitiveType t) {
                return this == t;
            }
            public boolean equals(IJMLType t) {
                return this == t;
            }
            public boolean equals(Object t) {
                return this == t;
            }
            public boolean isSubtypeOf(IJMLType t) {
                return false;
            }


            static private IJMLPrimitiveType INT = new JMLPrimitiveType();
            static private IJMLPrimitiveType BOOLEAN = new JMLPrimitiveType();
            static private IJMLPrimitiveType BIGINT = new JMLPrimitiveType();
            static private IJMLPrimitiveType REAL = new JMLPrimitiveType();
            static private IJMLPrimitiveType SHORT = new JMLPrimitiveType();
            static private IJMLPrimitiveType CHAR = new JMLPrimitiveType();
            static private IJMLPrimitiveType BYTE = new JMLPrimitiveType();
            static private IJMLPrimitiveType LONG = new JMLPrimitiveType();
            static private IJMLPrimitiveType DOUBLE = new JMLPrimitiveType();
            static private IJMLPrimitiveType FLOAT = new JMLPrimitiveType();

            public IJMLPrimitiveType INT() { return INT; }
            public IJMLPrimitiveType SHORT() { return SHORT; }
            public IJMLPrimitiveType LONG() { return LONG; }
            public IJMLPrimitiveType FLOAT() { return FLOAT; }
            public IJMLPrimitiveType DOUBLE() { return DOUBLE; }
            public IJMLPrimitiveType CHAR() { return CHAR; }
            public IJMLPrimitiveType BYTE() { return BYTE; }
            public IJMLPrimitiveType BOOLEAN() { return BOOLEAN; }
            public IJMLPrimitiveType REAL() { return REAL; }
            public IJMLPrimitiveType BIGINT() { return BIGINT; }
        }


        static public class JMLReferenceType implements IJMLReferenceType {
            final protected Class<?> clazz;
            public JMLReferenceType(Class<?> clazz) {
                this.clazz = clazz;
            }
            public IJMLReferenceType baseType() { return this;}
            public IJMLReferenceType[] args() { return  emptyArgs; }
            public int numArgs() { return 0; }
            public boolean equals(IJMLType t) {
                if (this == t) return true;
                if (!(t instanceof JMLReferenceType)) return false;
                return ((JMLReferenceType)t).clazz.equals(this.clazz);
            }
            public boolean equals(Object t) {
                if (t == null) return false;
                if (!(t instanceof IJMLType)) return false;
                return t.equals(this);
            }
            public boolean isSubtypeOf(IJMLType t) {
                if (!(t instanceof JMLReferenceType)) return false;
                JMLReferenceType r = (JMLReferenceType)t;
                return r.clazz.isAssignableFrom(this.clazz);
            }

            public boolean equals(IJMLReferenceType t, Map<IJMLTypeVar,IJMLTypeVar> map) {
                return ((JMLReferenceType)t).clazz.equals(this.clazz);
            }
        }

        @Pure
        static public class JMLParameterizedType implements IJMLReferenceType {
            final protected IJMLReferenceType baseType;
            final protected IJMLReferenceType[] typeargs;

            public JMLParameterizedType(IJMLReferenceType baseType, IJMLReferenceType[] args) {
                this.baseType = baseType;
                this.typeargs = args;
            }

            public IJMLReferenceType baseType() { return baseType;}
            public IJMLReferenceType[] args() { return  typeargs; }
            public int numArgs() { return typeargs.length; }
            public boolean equals(IJMLType t) {
                if (this == t) return true;
                if (!(t instanceof IJMLReferenceType)) return false;
                IJMLReferenceType r = (IJMLReferenceType)t;
                if (this.numArgs() != r.numArgs()) return false;
                if (!baseType.equals(r.baseType())) return false;
                IJMLReferenceType[] args = r.args();
                for (int i=0; i<typeargs.length; i++) {
                    if (!typeargs[i].equals(args[i])) return false;
                }
                return true;
            }
            public boolean equals(Object t) {
                if (t == null) return false;
                if (!(t instanceof IJMLType)) return false;
                return t.equals(this);
            }
            public boolean isSubtypeOf(IJMLType t) {
                if (!(t instanceof IJMLReferenceType)) return false;
                IJMLReferenceType r = (IJMLReferenceType)t;
                if (this.numArgs() != r.numArgs()) return false;
                if (!this.baseType().isSubtypeOf(r.baseType())) return false;
                IJMLReferenceType[] args = r.args();
                for (int i=0; i<typeargs.length; i++) {
                    if (!typeargs[i].equals(args[i])) return false;
                }
                return true;
            }
            public boolean equals(IJMLReferenceType r, Map<IJMLTypeVar,IJMLTypeVar> map) {
                if (this.numArgs() != r.numArgs()) return false;
                if (!this.baseType().isSubtypeOf(r.baseType())) return false;
                IJMLReferenceType[] args = r.args();
                for (int i=0; i<typeargs.length; i++) {
                    if (!typeargs[i].equals(args[i],map)) return false;
                }
                return true;
            }
        }
        
        @Pure
        static public class JMLTypeVar implements IJMLReferenceType {
            public IJMLReferenceType baseType() { return this; }
            
            public IJMLReferenceType[] args() { return emptyArgs; }
            
            public int numArgs() { return 0; }
            
            public boolean equals(IJMLType t) {
                return this == t;
            }
            
            public boolean equals(Object t) {
                return this == t;
            }

            public boolean equals(IJMLReferenceType r, Map<IJMLTypeVar,IJMLTypeVar> map) {
                if (!(r instanceof JMLTypeVar)) return false;
                IJMLTypeVar v = map.get(this);
                return v == r;
            }
            
            public boolean isSubtypeOf(IJMLType t) { return false; } // FIXME - depends on bounds
            
        }
        
        @Pure
        static public class JMLGenericType implements IJMLReferenceType {
            final protected IJMLReferenceType[] typevars;
            final protected IJMLReferenceType paramType;
            
            public JMLGenericType(IJMLReferenceType[] tvars, IJMLReferenceType base) {
                this.typevars = tvars;
                this.paramType = base;
            }
            
            public IJMLReferenceType baseType() { return paramType.baseType(); }
            
            public IJMLReferenceType[] args() { return paramType.args(); }
            
            public int numArgs() { return args().length; }
            
            public boolean equals(JMLGenericType t) {
                if (this == t) return true;
                if (!paramType.baseType().equals(t.paramType.baseType())) return false;
                if (paramType.numArgs() != t.paramType.numArgs()) return false;
                return true; // FIXME
            }
            
            public boolean equals(IJMLType t) {
                if (this == t) return true;
                if (!(t instanceof JMLGenericType)) return false;
                return t.equals(this);
            }
            
            public boolean equals(Object t) {
                if (t == null) return false;
                if (!(t instanceof IJMLType)) return false;
                return t.equals(this);
            }

            public boolean equals(IJMLReferenceType r, Map<IJMLTypeVar,IJMLTypeVar> map) {
                if (this == r) return true;
                if (!paramType.baseType().equals(r.baseType())) return false;
                if (paramType.numArgs() != r.numArgs()) return false;
                IJMLReferenceType[] args = r.args();
                // FIXME - this is a generic within a generic?
                return true;
//                for (int i=0; i<args.length; i++) {
//                    if (!())
//                }
            }
                
            public boolean isSubtypeOf(IJMLType t) {
                return false;  // FIXME - depends on bounds
            }
        }
    }
}
