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
     ex = api.execute(pw, "--esc", "B.java");
     System.out.println("EXIT: " + ex);
     ex = api.execute(System.out , "--esc", "B.java");
     System.out.println("EXIT: " + ex);
   } finally {
     pw.close();
   }
 }
}
