public class Test {
	
	public void m() {
		String s = 
			"""
			abc
			  def
			ghi
			""";
		//@ show s.length();
		//@ assert s.length() == 14;
	}
}