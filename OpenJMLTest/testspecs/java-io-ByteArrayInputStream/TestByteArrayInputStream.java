import java.io.ByteArrayInputStream;
import java.io.IOException;
public class TestByteArrayInputStream {
    
    public static void main(String... args) {
        try {
            try { t1(); } catch (NullPointerException e) { System.out.println(e); }
            t2();
            t2b();
            t3();
            t3a();
            t3b();
            t3c();
            t5();
            t6();
            t7();
            t8();
            t9();
            t10();
        } catch (Exception e) {
            System.out.println("Unexpected Exception: " + e);
        }
    }
    
    /*@ pure */ public static void t1() {
        // Null input
        var st = new ByteArrayInputStream(null);
        st.read();
    }
    
    /*@ pure */ public static void t2() {
        // Empty input
        var st = new ByteArrayInputStream(new byte[0]);
        var k = st.read();
        //@ check k == -1;
    }
    
    /*@ pure */ public static void t2b() throws IOException {
        // Read into empty array
        var st = new ByteArrayInputStream(new byte[] {(byte)'a', (byte)'b'});
        var j = st.read();
        var k = st.read(new byte[0]);
        //@ check k == 0;
        j = st.read();
        j = st.read();
        //@ check j == -1;
    }
    
    /*@ pure */ public static void t3() {
        // Conventional successive read
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba);
        var k = st.read();
        //@ check k == 'a'; 
        var n = st.read();
        //@ check n == 'b'; 
    }
    
    /*@ pure */ public static void t3a() throws IOException {
        // Read into overly long array
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba);
        var k = st.read();
        //@ check k == 'a'; 
        var r = new byte[5];
        k = st.read(r);
        //@ check k <= 3; 
        //@ check k > 0 ==> r[0] == 'b';
        //@ check k > 2 ==> r[2] == 'd';
    }
    
    /*@ pure */ public static void t3b() throws IOException {
        // Read into short array
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba);
        var k = st.read();
        //@ check k == 'a'; 
        var r = new byte[2];
        k = st.read(r);
        //@ check k <= 2; 
        //@ check k > 0 ==> r[0] == 'b';
        //@ check k > 1 ==> r[1] == 'c';
    }
    
    /*@ pure */ public static void t3c() throws IOException {
        // Read into empty array at EOF
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba);
        st.skip(4);
        int k = st.read(new byte[0]);
        //@ check k <= 0;
        //+RAC@ check k == -1;
    }
    
    /*@ pure */ public static void t5() {
        // Read with skip(n)
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba);
        var k = st.read();
        //@ check k == 'a'; 
        var j = st.skip(2);
        //@ check j == 2;
        k = st.read();
        //@ check k == 'd'; 
    }
    
    /*@ pure */ public static void t6() {
        // Read with skip(n) and large n
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba);
        var k = st.read();
        //@ check k == 'a'; 
        var j = st.skip(5);
        //@ check j == 3;
        k = st.read();
        //@ check k == -1; 
    }
    
    /*@ pure */ public static void t7() {
        // Constructor with offset
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba, 1, 1);
        var k = st.read();
        //@ check k == 'b'; 
        var j = st.read();
        //@ check j == -1;
    }
    
    /*@ pure */ public static void t8() {
        // Constructor with offset
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba);
        //@ check st.markSupported();
        var k = st.read();  // read 'a'
        //@ check k == 'a'; 
        st.mark(10);
        k = st.read();   // read 'b'
        //@ check k == 'b';
        st.mark(10);
        k = st.read();   // read 'c'
        //@ check k == 'c';
        st.reset();
        //@ reachable
        k = st.read();   // read 'c' again
        //@ check k == 'c';
    }
    
    /*@ pure */ public static void t9() {
        // Constructor with offset
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba);
        var k = st.readAllBytes();
        //@ check k.length == 4;
        //@ check k[0] == 'a';
        //@ check k[3] == 'd';
        st = new ByteArrayInputStream(ba, 1, 2);
        k = st.readAllBytes();
        //@ check k.length == 2;
        //@ check k[0] == 'b';
        //@ check k[1] == 'c';
    }
    
    /*@ pure */ public static void t10() throws IOException {
        // Constructor with offset
        var ba = new byte[] {(byte)'a', (byte)'b', (byte)'c', (byte)'d' };
        var st = new ByteArrayInputStream(ba, 1, 1);
        var k = st.readNBytes(10);
        //@ check k.length == 1;
        //@ check k[0] == 'b';
    }
    
    // FIXME
    // Needs test for close
    // Needs test for transferTo
}
