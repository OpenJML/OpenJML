import org.jmlspecs.annotation.*;

//@ nullable_by_default
public class ArgNullity {

  //@ ghost public \seq<Integer> zz;
  //@ ghost public \seq<@Nullable Integer> zzn;
  //@ ghost public \seq<@NonNull Integer> zznn;

  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void m1(@Nullable /* @ nullable*/ Integer in) {
    //@ ghost var s1 = zznn.insert(0,in); // FAILS
  }
  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void m2(/*@ nullable*/ Integer in) {
    //@ ghost var s2 = zzn.insert(0,in);
  }
  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void m3(/*@ nullable*/ Integer in) {
    //@ ghost var s3 = zz.insert(0,in);
  }
  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void m4(/*@ non_null*/ Integer in) {
    //@ ghost var s4 = zz.insert(0,in);
  }
  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void m5(Integer in) {
    //@ ghost var s5 = zznn.insert(0,in); // FAILS
  }

}

//@ non_null_by_default
class ArgNullity2 {

  //@ ghost public \seq<Integer> zz;
  //@ ghost public \seq<@Nullable Integer> zzn;
  //@ ghost public \seq<@NonNull Integer> zznn;

  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void mm1(/*@ nullable*/ Integer in) {
    //@ ghost var s1 = zznn.insert(0,in); // FAILS
  }
  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void mm2(/*@ nullable*/ Integer in) {
    //@ ghost var s2 = zzn.insert(0,in);
  }
  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void mm3(/*@ nullable*/ Integer in) {
    //@ ghost var s3 = zz.insert(0,in); // FAILS
  }
  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void mm4(/*@ non_null */ Integer in) {
    //@ ghost var s4 = zz.insert(0,in);
  }
  //@ requires zz.length > 0 && zzn.length > 0 && zznn.length > 0;
  public void mm5(Integer in) {
    //@ ghost var s4 = zz.insert(0,in);
  }

}
