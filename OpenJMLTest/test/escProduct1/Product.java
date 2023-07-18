public class Product {
	//@ requires 1 < n < 5;
	//@ ensures \result == (\product int i; 1 <= i && i < n; i);
	public static int product(int n) {
		int total = 1;

		//@ maintaining 1 <= j <= n;
		//@ maintaining total == (\product int i; 1 <= i && i < j; i);
		//@ decreasing n - j;
		for (int j = 1; j < n; j++) {
			total *= j;
		}

		return total;
	}
}
