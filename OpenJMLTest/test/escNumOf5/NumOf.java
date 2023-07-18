public class NumOf {
	//@ requires 1 < arr.length < 5;
	//@ ensures \result == (\num_of int i; 0 <= i < arr.length; arr[i] == 3);
	public static int numof(int[] arr) {
		int count = 0;

		//@ maintaining 0 <= j <= arr.length;
		//@ maintaining count == (\num_of int i; 0 <= i < j; arr[i] == 3);
		//@ decreasing arr.length - j;
		for (int j = 0; j < arr.length; j++) {
			if (arr[j] >= 3) count++;
		}

		return count;
	}
}
