public class Sum {
    	//@ ensures \result == (\sum int i; 0 < i && i < 3; (\sum int j; 0 < j && j < i; i+j));
	public static int sum() {
		return  3;
	}
}
