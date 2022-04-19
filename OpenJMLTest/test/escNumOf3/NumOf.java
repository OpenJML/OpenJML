public class NumOf {
	//@ ensures \result == (\num_of int i; 0 < i < 5 || 7 < i < 9 ; i != 3);
	public static int numof() {
		return 4;
	}
}
