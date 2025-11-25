import org.openjml.*;

public class Run {
    
    public static void main(String... args) {
      try {
        IAPI api = IAPI.make();
        int x = api.execute("--esc","--progress","-jmltesting","A.java");
        System.out.println("RUN-Z " + x);
        System.exit(x==6 ? 0 : 1);
      } catch (Exception e) {
        System.out.println("XX " + e);
        System.exit(1);
      }
    }
}
