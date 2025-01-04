
import java.util.Arrays;

public class error{
	


		// _______________________________________________________________________________________________
		//@ public normal_behavior
		//@ requires byteArray!=null;
		//@ requires 0<=byteArray.length<=  (Integer.MAX_VALUE - lengthDiff); 
		//@ requires lengthDiff>=0;
		//@ ensures \result.length == \old(byteArray.length+lengthDiff);
		//@ ensures \forall int k; 0 <= k < \old(lengthDiff); \result[k] == (byte)0;
		//@ ensures \forall int k; \old(lengthDiff) <= k < \old(byteArray.length+lengthDiff); \result[k] == byteArray[k-lengthDiff];
		//@ ensures \forall int k; 0 <= k < \old(byteArray.length); \result[k+lengthDiff] == byteArray[k];
		//@ spec_pure
		public static byte[] lengthBalancerAddingZeroes(byte[] byteArray, int lengthDiff) {
			byte[] res = new byte[byteArray.length + lengthDiff];
			System.arraycopy(byteArray, 0, res, lengthDiff, byteArray.length);
			return res;
		}
		
        //@ public normal_behavior
        //@ requires byteArray!=null;
        //@ requires 0<=byteArray.length<=  (Integer.MAX_VALUE - lengthDiff); 
        //@ requires lengthDiff>=0;
        //@ ensures \result == ( result.length == \old(byteArray.length+lengthDiff)
        //@                    && (\forall int k; 0 <= k < \old(lengthDiff); result[k] == (byte)0)
        //@                    && (\forall int k; \old(lengthDiff) <= k < \old(byteArray.length+lengthDiff); result[k] == byteArray[k-lengthDiff])
        //@                    && (\forall int k; 0 <= k < \old(byteArray.length); result[k+lengthDiff] == byteArray[k]));
        //@ pure model 
		//@ public boolean lengthBalancerContent(byte[] byteArray, int lengthDiff, byte[] result);
		

		// _______________________________________________________________________________________________

		//@ public normal_behavior
		//@ requires byteArray1!=null & byteArray2!=null;
		//@ requires (byteArray1.length == byteArray2.length);
		//@ ensures  (\result.length ==byteArray1.length);
		//@ ensures  (\forall int k; 0 <= k < byteArray1.length; \result[k] == (\old(byteArray1[k]^ byteArray2[k])));
		//@ spec_pure
		public static byte[] xorFunctionSameLength(byte[] byteArray1, byte[] byteArray2) {

			int lengthBalance = byteArray1.length;
			byte[] res = new byte[lengthBalance];

			//@ loop_invariant 0 <= i <= lengthBalance;
			//@ loop_invariant \forall int k; 0 <= k < i; res[k] == (byte)(byteArray1[k]^ byteArray2[k]);
			//@ loop_decreases lengthBalance-i;
			for (int i = 0; i < lengthBalance; i++) {
				res[i] = (byte)(byteArray1[i] ^ byteArray2[i]);
			}
			return res;
		}
// _______________________________________________________________________________________________

		//@ public normal_behavior
		//@ requires byteArray1!=null & byteArray2!=null;
		
		//@ ensures (byteArray1.length > byteArray2.length)==> (\result.length ==byteArray1.length);
		//@ ensures (byteArray1.length < byteArray2.length)==> (\result.length ==byteArray2.length);
		//@ ensures (byteArray1.length == byteArray2.length)==> (\result.length ==byteArray2.length);
		
		//@ ensures (byteArray1.length == byteArray2.length)==> (\forall int k; 0 <= k < byteArray1.length; \result[k] == (\old(byteArray1[k]^ byteArray2[k])));
		
		//@ ensures (byteArray1.length > byteArray2.length)==> Arrays.equals(\result , xorFunctionSameLength(byteArray1, lengthBalancerAddingZeroes(byteArray2, ( byteArray1.length - byteArray2.length) )));
		//@ ensures (byteArray1.length > byteArray2.length)==> (\forall int k; 0 <= k < (byteArray1.length-byteArray2.length); \result[k] == (\old(byteArray1[k])^ (byte)0));
		//@ ensures (byteArray1.length > byteArray2.length)==> (\forall int k; (byteArray1.length-byteArray2.length) <= k < (byteArray1.length); \result[k] == (\old(byteArray1[k])^ byteArray2[k-(byteArray1.length-byteArray2.length)]));
		
		
	    //@ ensures (byteArray2.length > byteArray1.length)==> Arrays.equals(\result , xorFunctionSameLength( lengthBalancerAddingZeroes(byteArray1, ( byteArray2.length - byteArray1.length) ) ,  byteArray2));
		//@ ensures (byteArray2.length > byteArray1.length)==> (\forall int k; 0 <= k < (byteArray2.length-byteArray1.length); \result[k] == (\old(byteArray2[k])^ (byte)0));
		//@ ensures (byteArray2.length > byteArray1.length)==> (\forall int k; (byteArray2.length-byteArray1.length) <= k < (byteArray2.length); \result[k] == (\old(byteArray2[k])^ byteArray1[k-(byteArray2.length-byteArray1.length)]));
		
		//@ pure
		public static byte[] xorFunction(byte[] byteArray1, byte[] byteArray2) {

			byte[] res;
			//lengthDiff > 0
			if (byteArray1.length > byteArray2.length) {// byteArray1_len > byteArray2_len
			    res = xorFunctionSameLength(byteArray1, lengthBalancerAddingZeroes(byteArray2, ( byteArray1.length -byteArray2.length) ));
				//@ assert Arrays.equals(res,xorFunctionSameLength(byteArray1, lengthBalancerAddingZeroes(byteArray2, ( byteArray1.length -byteArray2.length) )));
				return res;
			} 

			else if (byteArray1.length < byteArray2.length) {// byteArray1_len < byteArray2_len
				res = xorFunctionSameLength(lengthBalancerAddingZeroes(byteArray1,  ( byteArray2.length-byteArray1.length)), byteArray2 );
				//@ assert Arrays.equals(res,xorFunctionSameLength(lengthBalancerAddingZeroes(byteArray1, ( byteArray2.length -byteArray1.length) ),byteArray2));

				return res;
			} 
			// boolArray1_len == boolArray2_len
				res = xorFunctionSameLength(byteArray1,byteArray2 );
				//@ assert Arrays.equals(res,xorFunctionSameLength(byteArray1,byteArray2 ) );
				
                return res;
			
		}

	
	 }
