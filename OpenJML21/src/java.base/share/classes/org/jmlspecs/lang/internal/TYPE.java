package org.jmlspecs.lang.internal;

import java.util.*;

public class TYPE implements org.jmlspecs.lang.IJmlPrimitiveType {
    
    public String bsName() { return "\\TYPE"; }

    final private Class<?> base;
    final private TYPE[] args;
    final static public TYPE[] noargs = new TYPE[] {};
    final private static Map<TYPE,TYPE> internSet = new HashMap<TYPE,TYPE>();
    
    public static TYPE of(Class<?> base) {
        TYPE t = new TYPE(base, noargs);
        return t.intern();
    }
    
    public static TYPE of(Class<?> base, TYPE ... args) {
        TYPE t = new TYPE(base,args);
        return t.intern();
    }
    
    public String toString() {
        if (base == null) return "?"; // FIXME - really this is just unknown, not a wildcard
        String s = base.toString();
        if (args != null && args.length > 0) {
            s = s + "<";
            boolean first = true;
            for (TYPE t: args) {
                if (first) first = false; else s = s + ",";
                s = s + t.toString();
            }
            s = s + ">";
        }
        return s;
    }
    
    private TYPE intern() {
        TYPE tt = internSet.get(this);
        if (tt == null) {
            tt = this;
            internSet.put(this,this);
        }
        return tt;
    }
    
    private TYPE(Class<?> base, TYPE... args) {
        this.base = base;
        this.args = args;
    }

    public TYPE[] typeargs() {
        return args;
    }
    
    public boolean eq(TYPE t) {
        if (!base.equals(t.base)) return false;
        if (args.length != t.args.length) {
            if (args.length == 0) {
                System.out.println("Warning: runtime type information has no type arguments: " + this);
                return true;
            } else if (t.args.length == 0) {
                System.out.println("Warning: runtime type information has no type arguments: " + t);
                return true;
            }
            return false;
        }
        int k = 0;
        for (var a: args) {
            if (!a.eq(t.args[k])) return false;
            ++k;
        }
        return true;
    }
    
    public boolean ne(TYPE t) {
        return !this.eq(t);
    }

    @Override
    public boolean equals(Object t) {
        return eq((TYPE)t);
    }
    
    @Override
    public int hashCode() {
        if (base == null) return 0;
        int i = base.hashCode();
        int k = 0;
        for (TYPE t: args) i = i + (t.hashCode()<< (++k));
        return i;
    }

    public Class<?> erasure() {
        return base;
    }

    public boolean isArray() {
        return base.isArray();
    }

    public boolean isSubtypeOf(TYPE t) {
        return t.erasure().isAssignableFrom(this.base);
    }
    
    // FIXME - does not work for arrays of JML types with type arguments.
    public TYPE getComponentType() {
        if (!base.isArray()) return null;
        return TYPE.of(base.getComponentType());
    }

//    @Override
//    public boolean equals(IJMLTYPE t) {
//        // TODO Auto-generated method stub
//        return false;
//    }
//
//    @Override
//    public boolean isSubtypeOf(IJMLTYPE t) {
//        return isSubtypeOf((TYPE)t);
//    }

}
