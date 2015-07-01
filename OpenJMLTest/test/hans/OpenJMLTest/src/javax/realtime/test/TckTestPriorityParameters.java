package javax.realtime.test;

import javax.realtime.PriorityParameters;
import javax.safetycritical.PriorityScheduler;
import javax.scj.util.Const;

import org.jmlspecs.utils.JmlAssertionError;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestPriorityParameters extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestPriorityParameters.testCount;
		TestCase test = new TestPriorityParameters(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);

		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/realtime/PriorityParameters.java";
	}
}

class TestPriorityParameters extends TestCase
{
  static final int testCount = 11;  
  
  public TestPriorityParameters(TestResult result, int testCount) {
		super(result, testCount);
  }

  public void test (int i) 
  {
    int min = PriorityScheduler.instance().getMinPriority();
    int max = PriorityScheduler.instance().getMaxPriority();
    switch (i) {
               // public PriorityParameters(int priority)
      case  1: try { new PriorityParameters(min-1); assert false; }
               catch (JmlAssertionError e){} 
               break;
      case  2: new PriorityParameters(min);
               break;
      case  3: new PriorityParameters((min+max)/2); break;
      case  4: new PriorityParameters(max); break;      
      case  5: try { new PriorityParameters(max+1); assert false; }
               catch (JmlAssertionError e){}
               break;
               
               // public int getPriority()
      case  6: new PriorityParameters((min+max)/2).getPriority(); break;
      
               // public void setPriority (int value)
      case  7: try {
    	         new PriorityParameters(min).setPriority(min-1); 
    	         assert false;
    	       }
               catch (JmlAssertionError e){} 
               break;               
      case  8: new PriorityParameters(min+1).setPriority(min); break;
      case  9: new PriorityParameters(min).setPriority((min+max)/2); break;
      case 10: new PriorityParameters(min).setPriority(max); break;      
      case 11: try {
    	         new PriorityParameters(min).setPriority(max+1); 
    	         assert false;
    	       }
               catch (JmlAssertionError e){} 
               break;
      default: break;
    }
  }
}
