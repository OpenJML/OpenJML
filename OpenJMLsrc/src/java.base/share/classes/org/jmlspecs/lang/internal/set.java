package org.jmlspecs.lang.internal;
import java.util.*;
import org.jmlspecs.lang.IJmlPrimitiveType;
import org.jmlspecs.lang.IJmlArrayLike;

//@ immutable no_state 
public abstract class set<T> implements IJmlPrimitiveType, IJmlArrayLike {
    
    private set() {}
    
    private static <X> set<X> proto() { return new UsingHashSet<X>(); }
        
    @SuppressWarnings("unchecked")
    static public <T> set<T> empty() { return set.<T>proto().from(); }

//    @SafeVarargs
    @SuppressWarnings("unchecked")
    static public <X> set<X> of(X ... data) {
        return set.<X>proto().from(data);
    }

    // These alternate version of 'of' make for simpler reasoning about the method's effects,
    // particularly relating to the resulting size of the set.

    static public <X> set<X> of(X e) { return set.<X>empty().add(e); }
    
    static public <X> set<X> of(X e, X ee) { return set.<X>empty().add(e).add(ee); }

    static public <X> set<X> of(X e, X ee, X eee) { return set.<X>empty().add(e).add(ee).add(eee); }

    static protected <X> set<X> of(java.util.Collection<X> s) { return set.<X>proto().from(s); }

    abstract public bigint size();

    @SuppressWarnings("unchecked")
    abstract protected set<T> from(T ... data);
    
    abstract protected set<T> from(java.util.Collection<T> data);

    abstract public boolean contains(T x);

    abstract public boolean isEmpty();
    
    abstract public boolean eq(set<T> ss);
    
    public boolean ne(set<T> ss) {
        return !eq(ss);
    }
    
    public boolean equals(set<T> s) { return eq(s); }
    
    @SuppressWarnings("unchecked")
    @Override
    public boolean equals(Object s) {
        return s instanceof set<?> ss && eq((set<T>)ss);
    }
    
    @Override
    abstract public int hashCode();
    
    @Override
    abstract public String toString();

    /** true if this is an improper subset of s */
    abstract public boolean isSubsetOf(set<T> s);
    
    /** true if this is an improper subset of s */
    abstract public boolean isProperSubsetOf(set<T> s);
    
    abstract public set<T> add(T x);
    
    abstract public set<T> remove(T x);

    abstract public set<T> filter(java.util.function.Predicate<T> p);
    
    abstract public set<T> union(set<T> s);

    abstract public set<T> intersect(set<T> s);

    abstract public set<T> subtract(set<T> s);
    
    public static class UsingHashSet<T> extends set<T> {

        private final java.util.Set<T> value;
        
        private UsingHashSet() { value = new java.util.HashSet<T>(); }

        private UsingHashSet(java.util.Set<T> data) { value = data; }
        
        private UsingHashSet<T> copy() {
            return new UsingHashSet<T>(new java.util.HashSet<T>(value));
        }

        static public <T> set<T> empty() { return new UsingHashSet<T>(); }

        @Override
        public bigint size() { return bigint.of(value.size()); }

        @SuppressWarnings("unchecked")
        @Override
        public set<T> from(T ... data) {
            var s = new UsingHashSet<T>();
            for (var i: data) s.value.add(i);
            return s;
        }
        
        public set<T> from(java.util.Collection<T> data) {
            return new UsingHashSet<T>(new HashSet<T>(data));
        }
        
        @Override
        public boolean eq(set<T> ss) {
            return value.equals(((UsingHashSet)ss).value); // FIXME - what kind of equals to use
        }
        
        @Override
        public boolean ne(set<T> ss) {
            return !eq(ss);
        }
        
     
        @Override
        public boolean contains(T x) {
            return value.contains(x);
        }

        @Override
        public boolean isEmpty() {
            return size().eq(bigint.zero);
        }
        
        @Override
        public int hashCode() {
            return value.hashCode();
        }

        @Override
        public boolean isSubsetOf(set<T> s) {
            for (var k: this.value) if (!((UsingHashSet)s).value.contains(k)) return false;
            return true;
        }
        
        @Override
        public boolean isProperSubsetOf(set<T> s) {
            return size().lt(s.size()) && isSubsetOf(s);
        }
        
        @Override
        public set<T> add(T x) {
            var c = this.copy();
            c.value.add(x);
            return c;
        }
        
        @Override
        public set<T> remove(T x) {
            var c = this.copy();
            c.value.remove(x);
            return c;
        }

        @Override
        public set<T> filter(java.util.function.Predicate<T> p) {
            var c = new UsingHashSet<T>();
            for (var x: this.value) if (p.test(x)) c.value.add(x);
            return c;
        }
        
        @SuppressWarnings("unchecked")
        @Override
        public set<T> union(set<T> s) {
            var r = this.copy();
            r.value.addAll(((UsingHashSet)s).value);
            return r;
        }

        @SuppressWarnings("unchecked")
        @Override
        public set<T> intersect(set<T> s) {
            var r = this.copy();
            r.value.retainAll(((UsingHashSet)s).value);
            return r;
        }

        @SuppressWarnings("unchecked")
        @Override
        public set<T> subtract(set<T> s) {
            var r = this.copy();
            r.value.removeAll(((UsingHashSet)s).value);
            return r;
        }
        
        @Override
        public String toString() {
            return value.toString();
        }
    }

}