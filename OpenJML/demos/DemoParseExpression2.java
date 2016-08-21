// DemoParseExpression2.java
import org.jmlspecs.openjml.*;
import com.sun.tools.javac.tree.JCTree;

public class DemoParseExpression2 {

    public static void main(String[] argv) {
        try {
            IAPI m = Factory.makeAPI(new String[]{});
            JCTree.JCExpression expr = m.parseExpression("a <==> \\result", true);
            String s = m.prettyPrint(expr);
            System.out.println(s);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
