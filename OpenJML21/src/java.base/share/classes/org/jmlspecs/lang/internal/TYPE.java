package org.jmlspecs.lang.internal;

import java.util.*;

public class TYPE implements org.jmlspecs.lang.IJmlPrimitiveType {
    
    public String bsName() { return "\\TYPE"; } // FIXME - do we need this

    final private Class<?> base;
    final private TYPE[] args;
    final static public TYPE[] noargs = new TYPE[] {};
    final private static Map<TYPE,TYPE> internSet = new HashMap<TYPE,TYPE>();
    
    public static TYPE of(Class<?> base) { // FIXME - get problems without this declaration, even though it should not be needed
        TYPE t = new TYPE(base,noargs);
        return t.intern();
    }
    
    public static TYPE of(Class<?> base, TYPE ... args) {
        TYPE t = new TYPE(base,args.length == 0 ? noargs : args);
        return t.intern();
    }
    
    public static TYPE empty() {
        return of(boolean.class);
    }
    
    public String toString() {
        if (base == null) return "???"; // This is a defensive output, not any wildcard
        int count = 0;
        var b = base;
        while (b.isArray()) { ++count; b = b.getComponentType(); }
        String s = b.toString();
        if (args != null && args.length > 0) {
            s = s + "<";
            boolean first = true;
            for (TYPE t: args) {
                if (first) first = false; else s = s + ",";
                s = s + t.toString();
            }
            s = s + ">";
        }
        while (count > 0) { --count; s = s + "[]"; }
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
    
    public TYPE typearg0() {
        if (args.length == 0) throw new IllegalArgumentException("\\TYPE value in call of typearg0 has no type arguments");
        return args[0];
    }
    
    public TYPE typearg(int n) {
        if (n < 0 || n >= args.length) throw new IllegalArgumentException("\\TYPE value in call of typearg has an argument that is negative or not in range: 0 <= " + n + " < " + args.length);
        return args[n];
    }
    
    public boolean eq(TYPE t) {
        //System.out.println("EQ " + base + " " + t.base + " " + base.equals(t.base) + " " + args.length + " " + t.args.length);
        if (!base.equals(t.base)) return false;
        if (args.length != t.args.length) {
            if (args.length == 0) {
                System.out.println("Warning: runtime type information has no type arguments: " + this); // FIXME - use log.warning?
                return true;
            } else if (t.args.length == 0) {
                System.out.println("Warning: runtime type information has no type arguments: " + t); // FIXME - use log.warning?
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
        // Unsupported externally, but have to support it here to enable interning Maps
        return (t instanceof TYPE tt) && this.eq(tt);
        //throw new UnsupportedOperationException("\\TYPE.equals is not supported; use ==");
    }
    
    @Override
    public int hashCode() {
        if (base == null) return 0;
        int i = base.hashCode();
        int k = 0;
        for (TYPE t: args) i = i + (t.hashCode() << (++k));
        return i;
    }

    public Class<?> erasure() {
        return base;
    }

    public TYPE arraytype() {
        Class<?> c = java.lang.reflect.Array.newInstance(this.base,0).getClass();
        return TYPE.of(c, this.args);
    }

    public boolean isArray() {
        return base.isArray();
    }

    public boolean isSubtypeOf(TYPE t) {
        if (!t.erasure().isAssignableFrom(this.base)) return false;
        if (this.args.length != t.args.length) return false;
        for (int i=0; i< args.length; i++) {
            if (!this.args[i].eq(t.args[i])) return false;
        }
        return true;
    }
    
    public boolean isSubtypeOfProper(TYPE t) {
        return isSubtypeOf(t) && !eq(t);
    }
    
    public TYPE getComponentType() {
        if (!base.isArray()) throw new IllegalArgumentException("Calling \\elemtype on a value that is not an (or does not have) array type: " + this);
        return TYPE.of(base.getComponentType(), args);
    }

}
