public class Sum {
	//@ requires 0 < arr.length < 10;
	//@ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
	public static int sum(int[] arr) {
		int total = 0;

		//@ maintaining 0 <= j <= arr.length;
		//@ maintaining total == (\sum int i; 0 <= i && i < j; arr[i]);
		//@ decreasing arr.length - j;
		for (int j = 0; j < arr.length; j++) {
			//@ assume Integer.MIN_VALUE <= total + arr[j] <= Integer.MAX_VALUE;
			total += arr[j];
		}

		return total;
	}
}
