import org.jmlspecs.annotation.Pure;
public class Anomaly {
    /*@ public behavior
    ensures \result==41; //HG2G had an off by 1 error.
    */
    @Pure public int a41(){
        return a41();
    }
}
