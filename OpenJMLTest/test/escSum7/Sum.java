public class Sum {
    	//@ requires 0 < n < 10;
	//@ ensures \result == (\sum int i; 0 <= i && i < n; i * 0.1);
	public static double nonints(int n) {
		double total = 0;

		//@ maintaining 0 <= j <= n;
		//@ maintaining total == (\sum int i; 0 <= i && i < j; i * 0.1);
		//@ decreasing n - j;
		for (int j = 0; j < n; j++) {
			total += j * 0.1;
		}

		return total;
	}
}
