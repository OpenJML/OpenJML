package org.jmlspecs.lang.internal;

import java.util.*;

public class TYPE implements org.jmlspecs.lang.IJmlPrimitiveType {
    
    public String bsName() { return "\\TYPE"; }

    final private Class<?> head;
    final private TYPE[] typeargs;
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
        if (head == null) return "?"; // FIXME - really this is just unknown, not a wildcard
        String s = head.toString();
        if (typeargs != null && typeargs.length > 0) {
            s = s + "<";
            boolean first = true;
            for (TYPE t: typeargs) {
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
    
    private TYPE(Class<?> head, TYPE... typeargs) {
        this.head = head;
        this.typeargs = typeargs;
    }

    public TYPE[] typeargs() {
        return typeargs;
    }
    
//    public TYPE typearg(int i) {
//        return typeargs[i];
//    }
    
    public boolean eq(TYPE t) {
        if (!head.equals(t.head)) return false;
        if (typeargs.length != t.typeargs.length) {
            if (typeargs.length == 0) {
                System.out.println("Warning: runtime type information has no type arguments: " + this);
                return true;
            } else if (t.typeargs.length == 0) {
                System.out.println("Warning: runtime type information has no type arguments: " + t);
                return true;
            }
            return false;
        }
        int k = 0;
        for (var a: typeargs) {
            if (!a.eq(t.typeargs[k])) return false;
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
        if (head == null) return 0;
        int i = head.hashCode();
        int k = 0;
        for (TYPE t: typeargs) i = i + (t.hashCode()<< (++k));
        return i;
    }

    public Class<?> erasure() {
        return head;
    }

    public int numargs() {
        return typeargs.length;
    }

    public boolean isArray() {
        return head.isArray();
    }

    public boolean isSubtypeOf(TYPE t) {
        return t.erasure().isAssignableFrom(this.head);
    }
    
    // FIXME - does not work for arrays of JML types with type arguments.
    public TYPE getComponentType() {
        if (!head.isArray()) return null;
        return TYPE.of(head.getComponentType());
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
