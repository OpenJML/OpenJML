import java.security.*;
import javax.crypto.Mac;
import javax.crypto.spec.*;

public class Test {

public void f0() {
	try {
		Mac sha256Hmac = Mac.getInstance("HmacSHA256");
	} catch (NoSuchAlgorithmException  e) {
		e.printStackTrace();
	}
}


public void f1() throws NoSuchAlgorithmException {


	Mac sha256Hmac = Mac.getInstance("HmacSHA256");

}

public static void f2(byte[] inputTextVal, byte[] key) throws NoSuchAlgorithmException, InvalidKeyException {

		Mac sha256Hmac = Mac.getInstance("HmacSHA256");

		SecretKeySpec keySpec = new SecretKeySpec(key, "HmacSHA256");

		sha256Hmac.init(keySpec);



}
}


