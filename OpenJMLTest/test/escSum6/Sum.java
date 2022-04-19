public class Sum {
    	//@ ensures \result == (\sum int i; 0 < i && i < 3; ((double)i) * 0.1);
	public static double nonints() {
		return 0.1 + 0.2;
	}
}
