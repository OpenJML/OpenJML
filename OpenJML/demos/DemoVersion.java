// DemoVersion.java
import org.jmlspecs.openjml.*;

public class DemoVersion {
    public static void main(String[] argv) {
        try {
            IAPI m = Factory.makeAPI();
            String s = m.version();
            System.out.println(s);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}

