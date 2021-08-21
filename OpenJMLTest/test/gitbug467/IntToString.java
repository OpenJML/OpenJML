public class IntToString {
	  public static String intToStringA(int x) {
		    return x + "";
	  }
	  public static String intToStringB(int x) {
		    return Integer.toString(x);
	  }
	  public static String intToStringC(int x) {
		    return Integer.toString(x,10);
	  }
	  public static String intToStringD(int x) {
		    return String.valueOf(x) + "";
	  }
}