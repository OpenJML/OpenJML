// DemoParseAndPrint2.java
import org.jmlspecs.openjml.*;

public class DemoParseAndPrint2 {

    public static void main(String[] argv) {
        try {
            java.io.File f = new java.io.File("src/demo/A.java");
            IAPI m = Factory.makeAPI(new String[]{"-specspath","specs"});
            String s = m.prettyPrint(m.parseFiles(f).get(0));
            System.out.println(s);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
