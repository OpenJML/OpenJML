package javax.safetycritical.test.cyclic;

import java.util.Enumeration;

import javax.scj.util.Const;

import org.jmlspecs.utils.JmlAssertionError;

import unitTest_Remove.TestCase;
import unitTest_Remove.TestFailure;
import unitTest_Remove.TestResult;
import unitTest_Remove.TestSuite;

public class AllTests
{
	static final TestResult result = new TestResult(); 
	  
	  static final String name = "CyclicSchedule";
	  
	  public static void main (String[] args)
	  {
		Const.setDefaultErrorReporter();
		  
	    TestSuite suite = new TestSuite(); 
	    
	    //suite.addTest(test_CyclicSchedule);    
	    suite.addTest(test_CyclicExecutive);   
	        
	    suite.run(result);

	    printResult();
	  }

	  private static void printResult() {
	  	System.out.println("\nTest of " + name + ":");
	  	System.out.println("    Test cases:  " + result.runCount());
	  	System.out.println("    Test errors: " + result.errorCount());
	  	System.out.println("    JML errors:  " + result.JMLerrorCount());

	  	if (result.errorCount() > 0) {
	  		System.out.println("\nTest errors are in:");

	  		for (Enumeration<TestFailure> e = result.errors(); e.hasMoreElements();) {
	  			System.out.println("" + e.nextElement());
	  		}
	  	}
	  	if (result.JMLerrorCount() > 0) {
	  		System.out.println("\nJML errors are in:");

	  		for (Enumeration<TestFailure> e = result.JMLerrors(); e.hasMoreElements();) {
	  			System.out.println("" + e.nextElement());
	  		}
	  	}
	  
  }

    
    public static TestCase test_CyclicExecutive = new TestCyclicExecutive ("CyclicExecutive")
    {
      public void runTest ()
      {
        int i = 1;
        try
        {        
          for ( ; i <= TestCyclicExecutive.testCount; i++)
            test(i);  
        }
        catch (JmlAssertionError e) { 
          AllTests.result.addJMLError(this, e); 
          this.setCaseNumber(i);}
        catch (Throwable e) { 
          AllTests.result.addError(this, e); 
          this.setCaseNumber(i);}
      }
    };
  
}


