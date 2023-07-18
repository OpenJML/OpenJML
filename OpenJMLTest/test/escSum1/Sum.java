public class Sum {

	//@ requires 0 < n < 10;
	//@ ensures \result == (\sum int i; 0 <= i && i < n; i);
	public static int sum(int n) {
		int total = 0;

		//@ maintaining 0 <= j <= n;
		//@ maintaining total == (\sum int i; 0 <= i && i < j; i);
		//@ decreasing n - j;
		for (int j = 0; j < n; j++) {
			//@ assume Integer.MIN_VALUE <= total + j <= Integer.MAX_VALUE;
			total += j;
		}

		return total;
	}
}
