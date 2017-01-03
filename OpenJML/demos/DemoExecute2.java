// DemoExecute2.java
import org.jmlspecs.openjml.*;
import javax.tools.*;

class MyDiagListener implements DiagnosticListener<JavaFileObject> {
    public int count = 0;
    public void report(Diagnostic<? extends JavaFileObject> diag) {
        System.out.println("Line: " + diag.getLineNumber());
        count++;
    }

}

public class DemoExecute2 {

    public static void main(String[] argv) {
        try {
            IAPI m = Factory.makeAPI();
            MyDiagListener listener = new MyDiagListener();
            int retcode = m.execute(new java.io.PrintWriter(System.out), listener, null,
                    "-check","-noPurityCheck","src/demo/Err.java");
            System.out.println("Errors: " + listener.count);
            System.out.println("Return code: " + retcode);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}

