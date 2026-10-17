// gitbug671a: a conditional expression as a method argument (a poly expression, attributed
// speculatively) with a generic method call as a branch, as in commons-collections'
// CollectionUtils.selectRejected (#671). OpenJML recomputed the type of every conditional from its
// branches, and a branch could still be DEFERRED during speculative attribution: type checking
// crashed with 'AssertionError: isSubtype DEFERRED'.
import java.util.function.Predicate;

public class Cond {
    static <T> /*@ nullable */ Predicate<T> not(Predicate<? super T> p) { return null; }

    static <C> boolean filter(Iterable<C> c, /*@ nullable */ Predicate<? super C> p) { return true; }

    public static <C> boolean m(Iterable<C> c, /*@ nullable */ Predicate<? super C> p) {
        return filter(c, p == null ? null : not(p));
    }

    //@ ensures \result == (b ? 0 : x);
    public static long bigintBranch(boolean b, long x) {
        //@ ghost \bigint g = b ? 0 : (\bigint)x;  // a \bigint branch: the JML typing still applies
        return b ? 0 : x;
    }
}
