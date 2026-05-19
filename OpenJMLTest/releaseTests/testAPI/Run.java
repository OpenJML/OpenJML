import java.util.ArrayList;
import java.util.Arrays;
import org.openjml.*;

public class Run {

  public static void main(String... args) {
    String exp = System.getenv("OPENJML_EXPORTS");
    var combined = args;
    if (exp != null) {
       String[] exps = exp.split(" ");
       var list = new ArrayList<>(Arrays.asList(exps));  // mutable — Arrays.asList returns fixed-size
       list.addAll(Arrays.asList(args));
       combined = (String[])list.toArray(new String[list.size()]);
    }
    API api = (API)IAPI.make();
    int x = IAPI.make().execute(combined);
    System.exit(x);
  }
}
