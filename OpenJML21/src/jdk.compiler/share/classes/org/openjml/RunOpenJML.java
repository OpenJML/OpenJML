// This class is used to run openjml programmatically, in particular to run it when there are JVM options to set (such as profiling or coverage)

public class RunOpenJML {
    
  public static void main(String... args) {
    int x = org.openjml.IAPI.openjml(args);
    System.exit(x);
  }
}
