import java.io.*;
public class TestInputStream {

  public static void main(String ... args) {
    try {
        t1();
    } catch (Exception e) {
        System.out.println("Unexpected exception: " + e);
    }
  }

  public static void t1() throws IOException {
      var st = InputStream.nullInputStream();
      var k = st.read();
      //@ check k == -1;
  }
}