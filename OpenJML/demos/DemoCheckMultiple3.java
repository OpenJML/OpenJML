// DemoCheckMultiple3.java
import org.jmlspecs.openjml.*;
import java.util.List;

public class DemoCheckMultiple3 {

    public static void main(String[] argv) {
        try {
            java.io.File f2 = new java.io.File("src/demo/B.java");
            IAPI m = Factory.makeAPI("-noPurityCheck","-sourcepath","src");
            List<JmlTree.JmlCompilationUnit> asts = m.parseFiles(f2);
            int ret = m.typecheck(asts);
            System.out.println("Trees: " + asts.size() + "  Errors: " + ret);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
