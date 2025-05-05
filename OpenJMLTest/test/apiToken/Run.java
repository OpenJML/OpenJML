import org.openjml.*;

public class Run {
    
    public static void main(String... args) {
      try {
        IAPI api = IAPI.make();
        IAPI.ITokenIterator iter = api.makeTokenIterator("for a < 8 ;//@ c ==> \"asd\" \n");
        while (iter.hasNext()) {
            var t = iter.next();
            System.out.println(t + " : " + t.pos() + " " + t.endPos() + " " + t.kind() + " " + t.jmlKind() + " " +t.getTokenClass());
            System.out.println("          " + t.toStringDetail());
        }
        System.out.println("DONE");
      } catch (Exception e) {
        System.out.println("EXCEPTION: " + e);
      }
    }
}
