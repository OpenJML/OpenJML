// DemoExecute.java
import org.jmlspecs.openjml.*;

public class DemoExecute {

    public static void main(String[] argv) {
        try {
            IAPI m = Factory.makeAPI();
            String[] args = new String[]{"-check","src/demo/Err.java"};
            int retcode = m.execute(null,args);
            System.out.println("Return Code: " + retcode);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}

