import org.jmlspecs.annotation.*;

//@ non_null_by_default
public class MM {

  public void m() {
    @NonNull Object[] a = new Object[5];
    @Nullable Object[] b = new @Nullable Object[5];
    @NonNull Object[] c = new @NonNull Object[5];
    @NonNull Object[][] o = new Object[5][3];
  }
}

//@ nullable_by_default
class NN {

  public void m() {
    @NonNull Object[] a = new Object[5];
    @Nullable Object[] b = new @Nullable Object[5];
    @NonNull Object[] c = new @NonNull Object[5];
    @NonNull Object[][] o = new Object[5][3];
  }
}
