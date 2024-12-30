import java.util.Arrays;

public class Run {
    
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
    int x = org.jmlspecs.openjml.Main.execute(combined);
    System.exit(x);
  }
}
