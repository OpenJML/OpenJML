// This class is used to run openjml programmatically, in particular to run it for coverage testing.
// This will not work if $EXPORTS contains paths to modules that have spaces in the paths

import java.util.Arrays;

public class RunOpenJML {
    
  public static void main(String... args) {
    String exp = System.getenv("EXPORTS");
    var combined = args;
    if (exp != null) {
       String[] exps = exp.split(" ");
       var list = Arrays.asList(exps);
       list.addAll(Arrays.asList(args));
       combined = (String[])list.toArray(new String[list.size()]);
       System.out.println(String.join(" ", combined));
    }
    int x = org.openjml.IAPI.openjml(combined);
    System.exit(x);
  }
}
