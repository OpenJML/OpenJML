// The complaint was that this did not prove. The problem is partly the specs and partly the code
// and partly handling of Strings.
public class buggyPalindrome
{
   private /*@ spec_public@*/String reverse = "";
   //@ public normal_behavior
   //@ assignable reverse, System.out.outputText;
   //@ ensures \result <==> reverse.equals(original);
   public boolean palindromeCheck(String original)
   {
      reverse = "";
      // @ assume \invariant_for(original);
      int length = original.length();
    
      //@ ghost int i_counter;
      //@ set i_counter = 0;
      //@ maintaining -1 <= i < original.length(); 
      //@ maintaining i_counter + i + 1 == length;
      //@ maintaining reverse != null && reverse instanceof String && i_counter == reverse.length();
      //@ maintaining \forall int k; 0<=k<i_counter; reverse.charAt(k) == original.charAt(length-1-k);
      //@ loop_writes reverse, i_counter;
      //@ decreases i;
      // @ maintaining \invariant_for(reverse);
      for (int i = length - 1; i >= 0; i--){
          //@ assert \forall int k; 0<=k<i_counter; reverse.charAt(k) == original.charAt(length-1-k);
          //@ assert reverse.length() == i_counter;
         String reversex = reverse + original.charAt(i);
         //@ assume reversex != original;
         //@ assume \forall int k; 0<=k<i_counter; reversex.charAt(k) == reverse.charAt(k);
         //@ assert \forall int k; 0<=k<i_counter; reversex.charAt(k) == original.charAt(length-1-k);
         reverse = reversex;
         //@ assert reverse.length() == i_counter+1;
         //@ ghost int k2 = 0; havoc k2; assume 0<=k2<i_counter;
         //@ assert reversex.charAt(k2) == original.charAt(length-1-k2); // \forall int k; 0<=k<i_counter; reversex.charAt(k) == original.charAt(length-1-k);
         //@ ghost int k1 = 0; havoc k1; assume 0<=k1<i_counter;
         //@ show k1, k2, length, i_counter, original, reverse, reversex, reversex.charAt(k2), original.charAt(length-1-k2);
         //@ assert reverse.charAt(k1) == original.charAt(length-1-k1); // assert \forall int k1; 0<=k1<i_counter; reverse.charAt(k1) == original.charAt(length-1-k1);
         //@ assert reverse.charAt(i_counter) == original.charAt(length-1-i_counter);
         //@ assert \forall int k; 0<=k<=i_counter; reverse.charAt(k) == original.charAt(length-1-k);
         // @ assert reverse.charAt(i_counter) == (original.charAt(reverse.length() - 1));
         //@ set i_counter = i_counter + 1;
       }
      //@ assert i_counter == length; 

         
      if (reverse.equals(original)){
         System.out.println("The string is a palindrome.");
     return true;
    }
      else{
         System.out.println("The string isn't a palindrome.");
     return false;
    }     
   }
   //@ assignable reverse, System.out.outputText;
   //@ ensures \result <==> reverse.equals(original);
   public boolean palindromeCheckExc(String original)
   {
      
       reverse = "";
       // @ assume \invariant_for(original);
      int length = original.length();
    
      //@ ghost int i_counter;
      //@ set i_counter = 0;
      //@ maintaining i >= -1 && i < original.length(); 
      //@ decreases i;
      //@ maintaining i_counter + i + 1 == length;
      for (int i = length - 1; i >= 0; i--){
         reverse = reverse + original.charAt(i-50); // Won't fail
         // assert original.charAt(i) == (reverse.charAt(reverse.length() - 1));
         //@ set i_counter = i_counter + 1;
       }
      //@ assert i_counter == length; 

         
      if (reverse.equals(original)){
         System.out.println("The string is a palindrome.");
     return true;
    }
      else{
         System.out.println("The string isn't a palindrome.");
     return false;
    }     
   }
   //@ public normal_behavior
   //@ assignable reverse, System.out.outputText;
   //@ ensures \result <==> reverse.equals(original);
   public boolean palindromeCheckCatch(String original)
   {
      
      int length = original.length();
    
      //@ ghost int i_counter;
      //@ set i_counter = 0;
      //@ maintaining i >= -1 && i < original.length(); 
      //@ decreases i;
      //@ maintaining i_counter + i + 1 == length;
      for (int i = length - 1; i >= 0; i--){
         reverse = reverse + original.charAt(i-50); // Fails
         //@ assume reverse instanceof String;
     // assert original.charAt(i) == (reverse.charAt(reverse.length() - 1));
     //@ set i_counter = i_counter + 1;
       }
      //@ assert i_counter == length; 

         
      if (reverse.equals(original)){
         System.out.println("The string is a palindrome.");
     return true;
    }
      else{
         System.out.println("The string isn't a palindrome.");
     return false;
    }     
   }
} 
