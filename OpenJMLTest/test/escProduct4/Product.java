public class Product {
    //@ requires 0 < n < 5;
    //@ ensures \result == (\product int i; 1 <= i < n; i);
    public static float factorial(int n) {
		int total = 1;

		//@ maintaining 1 <= j <= n;
			//@ maintaining total == (\product int i; 1 <= i < j; i);
			//@ decreasing n - j;
		for (int j = 0; j < n; j++) {
			total *= j;
		}

		return total;
    }
}
