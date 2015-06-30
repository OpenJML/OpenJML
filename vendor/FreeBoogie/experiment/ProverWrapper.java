import java.io.*;
import java.util.*;

public class ProverWrapper {
  public static void main(String[] args) throws Exception {
    ProcessBuilder pb = new ProcessBuilder(Arrays.asList(args));
    Process p = pb.start();
    BufferedReader cin = new BufferedReader(
      new InputStreamReader(System.in));
    BufferedReader in = new BufferedReader(
      new InputStreamReader(p.getInputStream()));
    PrintStream out = new PrintStream(p.getOutputStream());

    while (true) {
      Thread.sleep(200);
      while (in.ready()) System.out.print((char)in.read());
      String line = cin.readLine();
      if ("quit".equals(line)) break;
      out.println(line);
      out.flush();
    }
    out.close();
    p.waitFor();
    while (in.ready()) System.out.print(in.read());
    System.out.println("exit code " + p.exitValue()); 
  }
}
