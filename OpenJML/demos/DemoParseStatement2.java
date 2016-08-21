// DemoParseStatement2.java
import org.jmlspecs.openjml.*;
import com.sun.tools.javac.tree.JCTree;

public class DemoParseStatement2 {

    public static void main(String[] argv) {
        try {
            IAPI m = Factory.makeAPI(new String[]{});
            JCTree.JCStatement stat = m.parseStatement("loop_invariant b;", true);
            String s = m.prettyPrint(stat);
            System.out.println(s);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
