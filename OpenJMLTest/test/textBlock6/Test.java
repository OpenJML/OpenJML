public class Test {
	
	public void m() {
/*@		ghost String s = 
			"""
			abc
			  def
			ghi
			@*/ // ERROR - not closed
		//@ show s.length();
		//@ assert s.length() == 14;
	}
}