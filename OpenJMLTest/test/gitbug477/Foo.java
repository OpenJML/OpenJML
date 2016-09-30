import java.util.Arrays;

public class Foo {

	public static void foo(){
		int[] a = {0, 1, 2};
		//  @ assert \elemtype(\typeof(a)) == \type(int);
		int[] b = a.clone();
		//@assert b != a;
		//@assert Arrays.equals(a,b);
	}

}
