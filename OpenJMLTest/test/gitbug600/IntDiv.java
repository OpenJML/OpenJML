import org.jmlspecs.runtime.*;
public class IntDiv {

//@ requires y != 0;
// @ requires x != Integer.MIN_VALUE && y != Integer.MIN_VALUE;
//@ ensures Math.abs(\result * y) <= Math.abs(x);
//@ ensures Math.abs(x) - Math.abs(\result * y) < Math.abs(y);
//@ ensures \result != 0 ==> ((\result >= 0) <==> (x>= 0 <==> y>=0));
public static int IntDiv(int x, int y) {
	int z = 0;
	int signe = 1;
    test(x);
	if (x < 0) {
		signe = -1;
		x = -x;
	}
	if (y < 0) {
		signe = -signe;
		y = -y;
	}
	if (y == 0) {
		y=y; // Instruction factice pour voir si elle
			// a été couverte
	}
	// @ ghost int xpos = x;
	// @ loop_invariant z >= 0 && z == \count && z <= xpos && 0 <= x && x == xpos - z * y;
	// while (x > y) { // Version erronée
		while (x >= y) {
		x = x - y;
		z = z + 1;
	}
	z = signe * z;
	return z;
}

//@ requires i != 1;
public static void test(int i) {}

public static void main(String ... args) {
    try {
        IntDiv(0,0);
    } catch (JmlAssertionError.PreconditionEntry e) {
        System.out.println("Expected invalid entry precondition");
    } catch (Exception e) {
        System.out.println("FAILED"); e.printStackTrace(System.out);
    }
    try {
        IntDiv(1,1);
    } catch (JmlAssertionError.PreconditionEntry e) {
        System.out.println("UNEXPECTED invalid entry precondition");
    } catch (JmlAssertionError.Precondition e) {
        System.out.println("Expected invalid non-entry precondition"); e.printStackTrace(System.out);
    } catch (Exception e) {
        System.out.println("FAILED"); e.printStackTrace(System.out);
    }
    System.out.println("END");
}

}