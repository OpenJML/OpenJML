//Printing first n prime numbers
     
    public class PrimeNumbers
    {
	private /*@ spec_public nullable@*/ int primeArray[];
	//@ requires n >= 1;
	//@ assignable primeArray;
	//@ ensures primeArray.length == n;
	//@ ensures (\forall int i, j; i >= 0 && i < primeArray.length && j >= 2 && j <= primeArray[i]/2; primeArray[i]%j != 0); 
	public void Prime(int n)
       {
          int status = 1, num = 3, count, j =2;
	  primeArray = new int[n];
          //@ assert num ==3;
          if (n >= 1)
          {
             System.out.println("First "+n+" prime numbers are:");
             System.out.println(2);
	     primeArray[0] = 2;
          }

	 //@ ghost int maxnumber = Integer.MAX_VALUE;

         // maintaining (\forall int i, k; i >= 0 && i < count-1 && k >= 2 && k <= primeArray[i]/2; primeArray[i]%k != 0); 
	 //@ maintaining num >= 3;
         //@ maintaining count >= 2 && count <= n + 1; 
         //@ decreases maxnumber - num; 
          for (count = 2; count <=n;)
          {    
	     //@ maintaining j> 1 && j <= num/2 + 1; 
	     //@ decreases num - j;
             for (j = 2; j <= num/2; j++)
             {
                if (num%j == 0)
                {
		   //@ assert num%j == 0;
                   status = 0;
                   break;
                }
		//@ assert num%j != 0;
             }

             if (status != 0)
             {	
		//@ assert status != 0;
		primeArray[count -1] = num;
		//@ assert (\forall int i; i >= 2 && i <= num/2; num%i != 0);
		System.out.println("prime is : "+num);	
                count++;
             }
             status = 1;
             num++;
          }   
       }
    }
