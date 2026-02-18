package org.jmlspecs.lang.internal;

import java.util.*;

public class TYPE implements org.jmlspecs.lang.IJmlPrimitiveType {
    
    public String bsName() { return "\\TYPE"; } // FIXME - do we need this

    final private Class<?> base;
    final private TYPE[] args;
    final static public TYPE[] noargs = new TYPE[] {};
    final private static Map<TYPE,TYPE> internSet = new HashMap<TYPE,TYPE>();
    
    public static TYPE of(Class<?> base) { // FIXME - get problems without this declaration, even though it should not be needed
        if (base == null) throw new NullPointerException("base may not be null in \\TYPE.of");
        TYPE t = new TYPE(base,noargs);
        return t.intern();
    }
    
    public static TYPE of(Class<?> base, TYPE t1) {
        TYPE t = new TYPE(base,new TYPE[] {t1});
        return t.intern();
    }
    
    public static TYPE of(Class<?> base, TYPE t1, TYPE t2) {
        TYPE t = new TYPE(base,new TYPE[] {t1, t2});
        return t.intern();
    }
    
    public static TYPE of(Class<?> base, TYPE t1, TYPE t2, TYPE t3) {
        TYPE t = new TYPE(base,new TYPE[] {t1, t2, t3});
        return t.intern();
    }
    
    public static TYPE of(Class<?> base, TYPE ... args) {
        // CAUTION: holding a reference to a mutable array
        if (args == null) throw new NullPointerException("argument list may not be null in \\TYPE.of");
        TYPE t = new TYPE(base,args.length == 0 ? noargs : args);
        return t.intern();
    }
    
    /** Returns a value thta serves as a zero-equivalent value of \TYPE (since there are no null values) */
    public static TYPE empty() {
        return of(boolean.class);
    }
    
    /** Returns a conventional String representation of the type */
    public String toString() {
        if (base == null) return "???"; // This is a defensive output, not any wildcard
        int count = 0;
        var b = base;
        while (b.isArray()) { ++count; b = b.getComponentType(); }
        String s = b.toString();
        s = s.substring(s.indexOf(' ')+1); // remove any leading 'class' or 'interface' etc.
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
    
    // FIXME - do we need to, or is it helpful to, use interning
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
    
    public int numargs() {
        return args.length;
    }
    
    public TYPE typearg1() {
        if (args.length == 0) throw new IllegalArgumentException("\\TYPE value in call of typearg1 has no type arguments");
        return args[0];
    }
    
    public TYPE typearg2() {
        if (args.length < 2) throw new IllegalArgumentException("\\TYPE value in call of typearg2 has only " + args.length + " type arguments");
        return args[1];
    }
    
    public TYPE typearg3() {
        if (args.length == 0) throw new IllegalArgumentException("\\TYPE value in call of typearg3 has only " + args.length + " type arguments");
        return args[2];
    }
    
    public TYPE typearg(int n) {
        if (n <= 0 || n > args.length) throw new IllegalArgumentException("\\TYPE value in call of typearg has an out of range argument: 0 < " + n + " <= " + args.length);
        return args[n-1];
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
    
    public boolean equals(TYPE t) { return eq(t); }

    @Override
    public boolean equals(Object t) {
        // Unsupported externally, but have to support it here to enable interning Maps
        return (t instanceof TYPE tt) && this.eq(tt);
        //throw new UnsupportedOperationException("\\TYPE.equals is not supported; use ==");
    }
    
    @Override
    public int hashCode() {
        if (base == null) return 0;
        return base.hashCode() + 3 * java.util.Arrays.hashCode(args);
    }

    public Class<?> erasure() {
        return base;
    }

    /** Returns a TYPE that represents an array with the receiver as element type */
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
    
    public boolean isProperSubtypeOf(TYPE t) {
        return isSubtypeOf(t) && base != t.base;
    }
    
    public TYPE getComponentType() {
        if (!base.isArray()) throw new IllegalArgumentException("Calling \\elemtype on a value that is not an (or does not have) array type: " + this);
        return TYPE.of(base.getComponentType(), args);
    }

}
