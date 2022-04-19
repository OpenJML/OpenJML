public class Sum {
    	//@ ensures \result == (\sum int i; 0 < (i + 1) < 4; i);
	public static int expr() {
		return  1 + 2;
	}
}
