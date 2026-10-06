// gitbug947: RAC of a non_null local variable that also has a type annotation retained at
// RUNTIME (here a user's own; formerly also JML's @NonNull). RAC checked the initializer before
// the declaration, so an unused variable had an empty live range, while the check's code (with
// the declaration's position) marked the variable's type annotation as placed; writing the class
// file then failed: NullPointerException 'p.lvarOffset is null'. The variable is now checked after
// its declaration.
import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE_USE)
@interface Tag {}

public class RuntimeAnno {
    public static void m(/*@ nullable */ Object p) {
        /*@ non_null */ @Tag Object kk = p; // not used afterwards
    }

    public static void main(String... args) {
        m("x");
        System.out.println("non-null initializer: OK");
        m(null); // reported by RAC
        System.out.println("END");
    }
}
