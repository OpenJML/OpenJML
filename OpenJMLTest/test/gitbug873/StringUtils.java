public class StringUtils {
    public static void bad () {
        StringBuilder v = new StringBuilder();
	v.append("ABC");
	v.append("DEF");
	//@ show v.toString();
    }
    public static void main(String... args) {
	bad();
    }
}
