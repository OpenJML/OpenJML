import org.jmlspecs.openjml.*;

public class MainApp
{
    public static void main( String[] args ) throws Exception
    {
        IAPI api = Factory.makeAPI("-progress -verbose");
//        api.execute(null, "-cp", "src/main/java/", "src/main/java/MaxBad.java");
        System.out.println("END");
    }
}
