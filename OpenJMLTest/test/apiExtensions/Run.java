// All compilations in one JVM must use the same --extensions (#1026). The first fixes the set.
public class Run {

    static final String E1 = "org.jmlspecs.openjml.ext.MatchExt";
    static final String E2 = "org.jmlspecs.openjml.ext.StatementLocationsExtension";

    static void check(String... exts) {
        String[] args = exts.length == 0 ? new String[] { "--check", "A.java" }
            : new String[] { "--check", "--extensions=" + String.join(",", exts), "A.java" };
        System.out.println("--extensions=" + String.join(",", exts));
        System.out.flush();
        int x = org.openjml.IAPI.openjml(args);
        System.out.println("exit " + x);
        System.out.flush();
    }

    public static void main(String... args) {
        if (args[0].equals("none")) {
            check();
            check(E1);        // differs
            check("X");       // X does not exist: load failure only
            check();
        } else {
            check(E1, E2);
            check(E2, E1);    // same set, different order
            check();          // differs
            check(E1);        // differs
            check(E1, E2, "X"); // load failure only
        }
    }
}
