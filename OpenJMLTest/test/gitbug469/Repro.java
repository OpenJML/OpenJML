import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

public class Repro {

public static class Bar {
    public static final FileInputStream URANDOM;

    static {
        FileInputStream tmp = null;
        try {
            tmp = new FileInputStream("/dev/urandom");
        } catch (FileNotFoundException e) {
            tmp = null;
        }
        URANDOM = tmp;
    }
    
    //@ ensures URANDOM != null;
    //@ static_initializer

    //-RAC@ public static invariant URANDOM != null;

    //@ requires URANDOM.isOpen;
    //@ requires length > 0;
    //@ requires URANDOM.availableBytes > 0;
    public static synchronized void getSeed(int length) {
        int read = 0;
        byte[] result = new byte[length];
        try {
    URANDOM.read(result, read, length-read);
        } catch (final IOException ex) {
            throw new RuntimeException(ex);
        }
    }
    
    //@ requires URANDOM.isOpen;
    //@ requires length > 0;
    //@ requires URANDOM.availableBytes > 0;
    public static synchronized void getSeed2(int length) {
        int read = 0;
        byte[] result = new byte[length];
        try {
    URANDOM.read(result, read, length-read);
        } catch (final IOException ex) {
            throw new RuntimeException(ex);
        }
    }
}

}