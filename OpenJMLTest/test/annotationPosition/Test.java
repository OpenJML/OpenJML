// Some simple checks of annotations and qualified type names
import org.jmlspecs.annotation.*;
public class Test {
    public void m1(final /*@ nullable */ Object o) { @NonNull Object oo = o; }
    public void m1a(@Nullable Object o) { @NonNull Object oo = o; }
    public void m2(/*@ nullable */ java.lang.Object o) { @NonNull Object oo = o; }
    public void m2a(java.lang.Object o) {}
    public void m2b(java.lang.@Nullable Object o) { @NonNull Object oo = o; }
}