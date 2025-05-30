import java.io.*;
import org.openjml.IAPI;

public class Run {

 public static void main(String... args) {
   PrintWriter pw = new PrintWriter(System.out);
   int ex = -1;
   try {
     IAPI api = IAPI.make();
     ex = api.execute("--esc", "A.java");
     System.out.println("EXIT: " + ex);
     api = IAPI.make(pw, null);
     ex = api.execute("--esc", "B.java");
     System.out.println("EXIT: " + ex);
     api = IAPI.make(null, null, null);
     ex = api.execute("--check", null, "C.java"); // Includes a test that null arguments are ignored
     System.out.println("EXIT: " + ex);
     ex = api.execute("--check", "", "C.java"); // Includes a test of an empty argument
     System.out.println("EXIT: " + ex);
     ex = IAPI.openjml("\"--check\"", "C.java"); // Includes a test of a quoted argument
     System.out.println("EXIT: " + ex + " " + (ex == org.jmlspecs.openjml.Main.Result.OK.exitCode));
   } finally {
     pw.flush();
   }
 }
}
