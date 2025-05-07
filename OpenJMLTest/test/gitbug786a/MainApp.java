import org.openjml.*;

public class MainApp
{
    public static void main( String[] args ) throws Exception
    {
        IAPI api = IAPI.make();
        System.out.println("START");
        int k = api.execute("--esc", "-cp", ".", "./MaxBad.java","--progress");
        System.out.println("END " + k);
        System.exit(k);
    }
}
