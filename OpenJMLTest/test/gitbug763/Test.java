public class Test {
	 
//@ requires binary_str!=null;
//@ requires 0<=binary_str.length()<=  (Integer.MAX_VALUE - lengthDiff); 
//@ requires lengthDiff>0;
//------step1
//@ ensures  \result.length() == \old(binary_str.length()+lengthDiff);
//------step2
//@ ensures \result.chars.tail(\old(lengthDiff)) == \old(binary_str.chars);
//------step3 
// (This will be added to the specification after the the error will be solved:) ensures \forall int j; 0 <= j < \old(lengthDiff); \result.charAt(j) == '0';
//@ writes \nothing;

static String lengthBalancerAddingZeroes(String binary_str, int lengthDiff)  
{  
	
	//@ loop_invariant 0 <= i <= \old(lengthDiff);
	//@ loop_invariant binary_str != null;
	//------step1
	//@ loop_invariant binary_str.length() == \old(binary_str, \Pre ).length()+ i;
	//------step2
	//@ loop_invariant binary_str.chars.tail(i) == \old(binary_str.chars);
	//------step3
	//@ loop_invariant (i>0) ==> (binary_str.charAt(i-1) == '0');
	//@ loop_invariant (i>0) ==> (binary_str.charAt(0) == '0');
	//@ loop_invariant (\forall int k; 0 <= k < i; binary_str.charAt(k) == '0');
	//@ loop_decreases lengthDiff - i;
    for (int i = 0; i < lengthDiff; i++)  
    {  
        //@ ghost int len = binary_str.length();
        binary_str = "0" + binary_str;  //@ check binary_str.chars.length > 0;
        //@ assert binary_str.charAt(0) == '0' && binary_str.charAt(i) == '0';
        //@ assert \forall int k; 1 <= k <= i; binary_str.charAt(k) == \old(binary_str, \LoopBody).charAt(k-1);
    }  
    return binary_str; 
}

//@ requires binary_str!=null;
//@ old int len = binary_str.length();
//@ requires 0<= len <=  (Integer.MAX_VALUE - lengthDiff); 
//@ requires lengthDiff>0;
//------step1
//@ ensures  \result.length() == len+lengthDiff;
//------step2
//@ ensures \result.chars.tail(lengthDiff) == binary_str.chars;
//------step3 
//(This will be added to the specification after the the error will be solved:) ensures \forall int j; 0 <= j < lengthDiff; \result.charAt(j) == '0';
//@ writes \nothing;

static String lengthBalancerAddingZeroesB(String binary_str, int lengthDiff)  
{  
    int initialLength = binary_str.length();
    String initialStr = binary_str;
  
  //@ loop_invariant 0 <= i <= \old(lengthDiff);
  //@ loop_invariant binary_str != null;
  //------step1
  //@ loop_invariant binary_str.length() == initialLength + i;
  //------step2
  //@ loop_invariant binary_str.chars.tail(i) == initialStr.chars;
  //------step3
  //@ loop_invariant (i>0) ==> (binary_str.charAt(i-1) == '0');
  //@ loop_invariant (i>0) ==> (binary_str.charAt(0) == '0');
  //@ loop_invariant (\forall int k; 0 <= k < i; binary_str.charAt(k) == '0');
  //@ loop_decreases lengthDiff - i;
  for (int i = 0; i < lengthDiff; i++)  
  {  
      binary_str = "0" + binary_str;  
      //@ assert binary_str.charAt(0) == '0' && binary_str.charAt(i) == '0';
      //@ assert \forall int k; 1 <= k <= i; binary_str.charAt(k) == \old(binary_str, \LoopBody).charAt(k-1);
  }  
  return binary_str; 
}

}
