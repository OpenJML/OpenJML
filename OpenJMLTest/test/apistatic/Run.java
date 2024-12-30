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
     ex = api.execute("--esc", "B.java");
     System.out.println("EXIT: " + ex);
   } finally {
     pw.flush();
   }
 }
}
