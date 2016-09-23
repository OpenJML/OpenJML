// DemoParseMultiple1.java
import org.jmlspecs.openjml.*;
import java.util.List;

public class DemoParseMultiple1 {

    public static void main(String[] argv) {
        try {
            java.io.File f = new java.io.File("src/demo/B.java");
            IAPI m = Factory.makeAPI();
            List<JmlTree.JmlCompilationUnit> asts = m.parseFiles(f);
            m.typecheck(asts);
            System.out.println("Trees: " + asts.size());
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
