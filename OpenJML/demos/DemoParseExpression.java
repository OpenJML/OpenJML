// DemoParseExpression.java
import org.jmlspecs.openjml.*;
import com.sun.tools.javac.tree.JCTree;

public class DemoParseExpression {

    public static void main(String[] argv) {
        try {
            IAPI m = Factory.makeAPI(new String[]{});
            JCTree.JCExpression expr = m.parseExpression("(a+b)*c", false);
            String s = m.prettyPrint(expr);
            System.out.println(s);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
