// DemoParseSingle.java
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.*;

public class DemoParseSingle {

    public static void main(String[] argv) {
        try {
            IAPI m = Factory.makeAPI();
            String f1 = "src/demo/A.java";
            JavaFileObject f2 = m.makeJFOfromFilename("specs/demo/A.jml");
            JmlTree.JmlCompilationUnit ast1 = m.parseSingleFile(f1);
            JmlTree.JmlCompilationUnit ast2 = m.parseSingleFile(f2);
            m.attachSpecs(ast1,ast2);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
