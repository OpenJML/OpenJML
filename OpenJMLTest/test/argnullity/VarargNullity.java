import org.jmlspecs.annotation.*;

//@ nullable_by_default
public class VarargNullity {

  public void m(/*@ nullable*/ Integer in) {
    Integer ii = 1;
    //@ ghost var s1 = \seq.<Integer>of(ii,in);
    //@ ghost var s2 = \seq.<@NonNull Integer>of(ii,in);
    //@ ghost var s3 = \seq.<@Nullable Integer>of(ii,in);
  }

  public void v(@NonNull Integer ... args) {
    //@ assert args.length > 0 ==> args[0] != null; // OK
  }

  public void v2(@Nullable Integer ... args) {
    //@ assert args.length > 0 ==> args[0] != null; // FAILS
  }

  public void v3(Integer ... args) {
    //@ assert args.length > 0 ==> args[0] != null; // FAILS
  }

}

//@ non_null_by_default
class VarargNullity2 {

  public void m(/*@ nullable*/ Integer in) {
    Integer ii = 1;
    //@ ghost var s1 = \seq.<Integer>of(ii,in);
    //@ ghost var s2 = \seq.<@NonNull Integer>of(ii,in);
    //@ ghost var s3 = \seq.<@Nullable Integer>of(ii,in);
  }

  public void vv1(@NonNull Integer ... args) {
    //@ assert args.length > 0 ==> args[0] != null; // OK
  }

  public void vv2(@Nullable Integer ... args) {
    //@ assert args.length > 0 ==> args[0] != null; // FAILS
  }

  public void vv3(Integer ... args) {
    //@ assert args.length > 0 ==> args[0] != null; // OK
  }

}
