//@ nullable_by_default
public class Test {
	
	int fd;

	//@ code_safe_math
	public static void m(int i) {
	    int k; k = i + i;
	    int j; j = i + i;
	}
	
	public static void mm(Test o) {
		int k = o.fd;
		int j = o.fd;
	}
}
