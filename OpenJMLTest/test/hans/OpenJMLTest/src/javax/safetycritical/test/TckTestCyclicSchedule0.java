package javax.safetycritical.test;


import javax.safetycritical.CyclicSchedule;
import javax.safetycritical.Frame;
import javax.scj.util.Const;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestCyclicSchedule0 extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestCyclicSchedule0.testCount;
		TestCase test = new TestCyclicSchedule0(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);
		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/safetycritical/Frame.java ICECAPSDK/src/javax/safetycritical/CyclicSchedule.java";
	}
}

class TestCyclicSchedule0 extends TestCase {

	// --- Stub classes ----------------------------------


	//--- TestCyclicSchedule0 ---------------------------------

	static final int testCount = 2;

	public TestCyclicSchedule0(TestResult result, int testCount) {
		super(result, testCount);
	}

	public void test(int i) {
		
		switch (i) {
		
		// public CyclicSchedule(Frame[] frames)
		case  1: // frame array is null
	        try { new CyclicSchedule (null); assert false; }
	        catch (IllegalArgumentException e){}; 
	        break;
        case  2: // empty frame array
            new CyclicSchedule (new Frame[] {});
        break;

		default:
			break;
		}
	}
}
