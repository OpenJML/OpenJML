// DemoParseStatement.java
import org.jmlspecs.openjml.*;
import com.sun.tools.javac.tree.JCTree;

public class DemoParseStatement {

    public static void main(String[] argv) {
        try {
            IAPI m = Factory.makeAPI(new String[]{});
            JCTree.JCStatement stat = m.parseStatement("a=b*c;", false);
            String s = m.prettyPrint(stat);
            System.out.println(s);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
