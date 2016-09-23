// DemoCheckFiles.java
import org.jmlspecs.openjml.*;
import java.util.List;

public class DemoCheckFiles {

    public static void main(String[] argv) {
        try {
            java.io.File f = new java.io.File("src/demo/A.java");
            IAPI m = Factory.makeAPI("-noPurityCheck");
            List<JmlTree.JmlCompilationUnit> asts = m.parseFiles(f);
            int ret = m.typecheck(asts);
            System.out.println("Trees: " + asts.size() + "  Errors: " + ret);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
