import org.jmlspecs.annotation.*;
public class TC {

  public static void main(String ... args) {
    @Nullable Object o = args.length == 0 ? null : new Object();
    var oo = (@NonNull Object)o;
  }
}
