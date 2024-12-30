import org.openjml.*;
import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

class Listener implements DiagnosticListener<JavaFileObject> {

    @Override
    public void report(Diagnostic<? extends JavaFileObject> diagnostic) {
        System.out.println("DIAGNOSTIC REPORTED");
        System.out.println("    Kind:           " + diagnostic.getKind());
        System.out.println("    Source:         " + diagnostic.getSource());
        System.out.println("    Start position: " + diagnostic.getStartPosition());
        System.out.println("    Position:       " + diagnostic.getPosition());
        System.out.println("    End position:   " + diagnostic.getEndPosition());
        System.out.println("    Line number:    " + diagnostic.getLineNumber());
        System.out.println("    Column number:  " + diagnostic.getColumnNumber());
        System.out.println("    Message:        " + diagnostic.getMessage(java.util.Locale.getDefault()));
    }
}


public class Run {
    
    public static void main(String... args) {
      try {
        IAPI api = IAPI.make(null, null, new Listener());
        int x = api.execute("--esc","--progress","-jmltesting","A.java");
	System.out.println("RUN-Z " + x);
        System.exit(x==1 ? 0 : 1);
      } catch (Exception e) {
        System.out.println("XX " + e);
      }
    }
}
