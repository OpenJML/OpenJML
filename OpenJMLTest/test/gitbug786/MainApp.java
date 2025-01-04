import org.openjml.*;

public class MainApp
{
    public static void main( String[] args ) throws Exception
    {
        System.out.println("START");
        int k = IAPI.openjml("--esc", "-cp", ".", "./MaxBad.java","--progress");
        System.out.println("END " + k);
        System.exit(k);
    }
}
