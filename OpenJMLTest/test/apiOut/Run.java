import org.openjml.*;

public class Run {
    
    public static void main(String... args) {
      try {
        IAPI api = IAPI.make(new java.io.PrintWriter(System.out), null);
        int x = api.execute("-sdf");
        System.out.println("EXIT " + x);
        api = IAPI.make(new org.jmlspecs.openjml.Main.NullPrintWriter(), null);
        boolean b = api.isOptionSet("--show-summary");
        System.out.println("Option set " + b);
        String s = api.getOption("--command");
        System.out.println("Option value " + s);
        x = api.execute("-asd");
        System.out.println("EXIT " + x);
        System.exit(x==2 ? 0 : 1);
      } catch (Throwable e) {
        System.out.println("XX " + e);
      }
    }
}
