// DemoProgress.java
import org.jmlspecs.openjml.*;

import java.util.List;

public class DemoProgress {

    public static class ProgressReporter extends IAPI.AbstractProgressReporter {
        @Override
        public boolean report(int ticks, int level, String message) {
            //if (level <= 1 || (context != null && JmlOption.isOption(context,JmlOption.JMLVERBOSE))) 
                System.out.println(ticks + " " + level + ") " + message);
            return false;
        }
    }
    
    public static void main(String[] argv) {
        try {
            java.io.File f2 = new java.io.File("src/demo/B.java");
            IAPI m = Factory.makeAPI("-noPurityCheck","-sourcepath","src");
            m.setProgressReporter(new ProgressReporter());
            System.out.println("PARSING");
            List<JmlTree.JmlCompilationUnit> asts = m.parseFiles(f2);
            System.out.println("TYPE-CHECKING");
            int ret = m.typecheck(asts);
            System.out.println("Errors: " + ret);
        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
