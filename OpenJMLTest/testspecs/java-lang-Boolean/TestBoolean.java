@org.jmlspecs.annotation.NullableByDefault
public class TestBoolean {

	@org.jmlspecs.annotation.SkipEsc
	public static void main(String... args) {
		esc(true,true);
	}
	
	public static void esc(boolean p, boolean q) {
		Boolean t = Boolean.TRUE;
		Boolean f = Boolean.FALSE;
		//@ assert p ==> t == Boolean.TRUE;
		//@ assert q ==> f == Boolean.FALSE;
		//@ assert t != null;
		//@ assert f != null;
		
		//@ assert t.booleanValue();
		//@ assert !f.booleanValue();
		
        //-RAC@ show t.theBoolean, f.theBoolean, Boolean.TRUE.theBoolean, Boolean.FALSE.theBoolean;
        //-RAC@ show Boolean.TRUE_HC, Boolean.FALSE_HC;
		//-RAC@ show t.hashCode(), f.hashCode(), Boolean.TRUE.hashCode(), Boolean.FALSE.hashCode();
		//@ assert t.hashCode() != f.hashCode();
		//@ assert t.hashCode() == Boolean.TRUE.hashCode();
		//@ assert f.hashCode() == Boolean.FALSE.hashCode();
		
		//@ assert t.equals(t);
		//@ assert f.equals(f);
		//@ assert !t.equals(f);
		//@ assert !t.equals(null);
		//@ assert !f.equals(null);
		
		// FIXME - behavior of toString()
		// FIXME - behavior of Boolean(String)
		
		/*+RAC@
		 @ assert t.toString().equals("true");
		 @ assert f.toString().equals("false");
		 @ ghost Boolean b;
		 @ set b = new Boolean("true"); assert b;
		 @ set b = new Boolean("True"); assert b;
		 @ set b = new Boolean("TRUE"); assert b;
		 @ set b = new Boolean("truE"); assert b;
		 @ set b = !new Boolean("false"); assert b;
		 @ set b = !new Boolean(null); assert b;
		 @ set b = !new Boolean(""); assert b;
		 @ set b = !new Boolean("abc"); assert b;
		 */
		
		// static operations
		
		Boolean tt = Boolean.valueOf(true);
		Boolean ttt = Boolean.valueOf(true);
		Boolean ff = Boolean.valueOf(false);
		Boolean fff = Boolean.valueOf(false);
		
		//@ assert tt.booleanValue();
		//@ assert !ff.booleanValue();
		
		//@ assert tt == ttt;
		//@ assert ff == fff;
		
		// FIXME behavior of valueOf(String)
		// FIXME behavior of getBoolean(String) -- applies to system properties
		// FIXME behavior of toString(boolean)
		
		/*+RAC@
		 @ assert Boolean.valueOf("true");
		 @ assert Boolean.valueOf("True");
		 @ assert !Boolean.valueOf("false");
		 @ assert !Boolean.valueOf(null);
		 @ assert Boolean.toString(true).equals("true");
		 @ assert Boolean.toString(false).equals("false");
		 */
		
		// Types
		
		//@ assert \typeof(tt) == \type(Boolean);
		//@ assert \typeof(ff) != \type(Integer);
		//@ assert \typeof(t) != \type(Object);
		//@ assert Boolean.TYPE == boolean.class;
		
		// Comparison
		
		//@ assert Boolean.compare(true,true) == 0;
		//@ assert Boolean.compare(false,false) == 0;
		//@ assert Boolean.compare(true,false) > 0;
		//@ assert Boolean.compare(false,true) < 0;
		
		//@ assert t.compareTo(t) == 0;
		//@ assert f.compareTo(f) == 0;
		//@ assert t.compareTo(f) > 0;
		//@ assert f.compareTo(t) < 0;
		
	}
}
