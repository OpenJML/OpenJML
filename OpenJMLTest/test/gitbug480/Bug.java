import java.util.BitSet;

class xATransport {
  int Na;

  xATransport(){

  }

  /*@
  ensures  Crypto.encrypt(this.Na).equals(\result);  pure // - won't be provable in this simplified example
  @*/
  BitSet send3(int Na){
    return new BitSet();
  }


}

class Crypto {
  //@ normal_behavior pure
  static BitSet encrypt(Object plainTextMessage){
    return new BitSet(); //return encrypted message
  }

}
