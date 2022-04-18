public class BackslashTypesErrs<T,U> {

  public void m() {
    //@ ghost \seq<T,U> a ;
    //@ ghost \seq<T> b ;
    //@ ghost \seq c ;
    //@ ghost \set<T,U> d ;
    //@ ghost \set<T> e ;
    //@ ghost \set f ;
    //@ ghost \map<T,T> g ;
    //@ ghost \map<T> h ;
    //@ ghost \map i ;
    //@ ghost \string<T,U> j ;
    //@ ghost \string k ;
  }

  //@ ghost public \seq values = \seq.empty();
  //@ ghost public \seq<T> w = \seq.empty();
  //@ ghost public \seq v = \seq.<T>empty();
  //@ ghost \bigint i = \seq.<T>empty().size();
  //@ ghost \bigint k = \seq.empty().size();

  /*@ model public \seq m(\seq t);
   */

}
