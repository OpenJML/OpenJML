@org.jmlspecs.annotation.NullableByDefault
public class TestInteger {

	@org.jmlspecs.annotation.SkipEsc
	public static void main(String... args) {
		esc(10);
	}
	
	public static void esc(int i) {
		Integer a = new Integer(i);
		Integer c = new Integer(i+1);
		Integer b = i;
		//@ assert a != null;
		//@ assert b != null;
		// @ assert a != b; // Does not necessarily hold
		//@ assert a.intValue() == b.intValue();
		//@ assert a.equals(b);
		//@ assert a.intValue() != c.intValue();
		//@ assert !a.equals(c);
		//@ assert ((int)a) == i;
		int k = b;
		//@ assert k == i;
		//@ assert a.equals(b);
		//@ assert !a.equals(c);
		//@ assert !a.equals(null);
		//@ assert Integer.MIN_VALUE == -2147483648;
		//@ assert Integer.MAX_VALUE == 2147483647;
		
		//@ assert \typeof(a) == \type(Integer);
		//@ assert \typeof(a) != \type(Object);
		
		// FIXME SIZE
		
		// FIXME - string operations
		
//		String s = a.toString();
//		int k = Integer.parseInt(s);
//		//@ assert k == i;
//		s = Integer.toString(a);
//		k = Integer.parseInt(s);
//		//@ assert k == i;
		
		//@ assert a.hashCode() == i;
	}
}
