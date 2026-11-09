import java.util.zip.CRC32;

// The class clauses of a binary class (the invariant in CRC32.jml) are not checked as part of the
// no_state model method whose attribution triggers them
public class Test {
    public static void m() {
        CRC32 c = new CRC32();
        //@ assert c._m == 0;
    }
}
