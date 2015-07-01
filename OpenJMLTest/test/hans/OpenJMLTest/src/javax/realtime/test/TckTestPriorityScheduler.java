package javax.realtime.test;

import javax.safetycritical.PriorityScheduler;
import javax.scj.util.Const;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestPriorityScheduler extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestPriorityScheduler.testCount;
		TestCase test = new TestPriorityScheduler(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);

		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/realtime/PriorityScheduler.java";
	}
}

class TestPriorityScheduler extends TestCase
{
  static final int testCount = 3; 
  
  public TestPriorityScheduler(TestResult result, int testCount) {
		super(result, testCount);
  }
  
  public void test (int i) 
  {
    switch (i) {
               // public int getMaxPriority()
      case  1: PriorityScheduler.instance().getMaxPriority();
               break;
               // public int getMinPriority()
      case  2: PriorityScheduler.instance().getMinPriority();
               break;
               // public int getNormPriority()
      case  3: PriorityScheduler.instance().getNormPriority();
               break;
               
      default: break;
    }
  }
}