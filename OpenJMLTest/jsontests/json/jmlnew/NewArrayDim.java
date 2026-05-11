import org.jmlspecs.annotation.*;

// Exercises JCNewArrayAdapter with dimAnnotations:
// type-use annotations on array dimensions populate JCNewArray.dimAnnotations.
public class NewArrayDim {

    // Single-dimension annotated array: dimAnnotations has one entry.
    void single() {
        Object @NonNull [] a = new Object @NonNull [3];
    }

    // Multi-dimension: dimAnnotations has two entries.
    void multi() {
        Object @NonNull [] @Nullable [] b = new Object @NonNull [3] @Nullable [2];
    }

    // Mix of annotated and unannotated dimensions.
    void mixed() {
        int[] c = new int[5];
        Object @NonNull [] d = new Object @NonNull [5];
    }
}
