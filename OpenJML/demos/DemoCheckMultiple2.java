// DemoCheckMultiple2.java
import org.jmlspecs.openjml.*;
import java.util.List;

public class DemoCheckMultiple2 {

    public static void main(String[] argv) {
        try {
            java.io.File f1 = new java.io.File("src/demo/A.java");
            java.io.File f2 = new java.io.File("src/demo/B.java");
            IAPI m = Factory.makeAPI("-noPurityCheck");
            List<JmlTree.JmlCompilationUnit> asts = m.parseFiles(f1,f2);
            int ret = m.typecheck(asts);
            System.out.println("Trees: " + asts.size() + "  Errors: " + ret);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
