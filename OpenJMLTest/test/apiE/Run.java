import org.openjml.*;
import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;
import java.io.*;

class Listener implements DiagnosticListener<JavaFileObject> {
    private PrintWriter pw;

    public Listener(PrintWriter pw) { this.pw = pw; }
    @Override
    public void report(Diagnostic<? extends JavaFileObject> diagnostic) {
        pw.println("DIAGNOSTIC REPORTED");
        pw.println("    Kind:           " + diagnostic.getKind());
        pw.println("    Source:         " + diagnostic.getSource());
        pw.println("    Start position: " + diagnostic.getStartPosition());
        pw.println("    Position:       " + diagnostic.getPosition());
        pw.println("    End position:   " + diagnostic.getEndPosition());
        pw.println("    Line number:    " + diagnostic.getLineNumber());
        pw.println("    Column number:  " + diagnostic.getColumnNumber());
        pw.println("    Message:        " + diagnostic.getMessage(java.util.Locale.getDefault()));
    }
}


public class Run {
    
    public static void main(String... args) {
      var sw = new StringWriter();
      try (var pw = new PrintWriter(sw)) {
        IAPI api = IAPI.make(pw, null, new Listener(pw));
        int x = api.execute("--esc","--progress","-jmltesting","A.java");
        System.out.println(sw.toString());
        System.out.println("RUN-Z " + x);
        System.exit(x==6 ? 0 : 1);
      } catch (Exception e) {
        System.out.println(sw.toString());
        System.out.println("XX " + e);
      }
    }
}
