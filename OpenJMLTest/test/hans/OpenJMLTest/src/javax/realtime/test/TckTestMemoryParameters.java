package javax.realtime.test;

import javax.realtime.MemoryParameters;
import javax.scj.util.Const;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestMemoryParameters extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestMemoryParameters.testCount;
		TestCase test = new TestMemoryParameters(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);

		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/realtime/MemoryParameters.java";
	}

}

class TestMemoryParameters extends TestCase {
	
	static final int testCount = 9;

	TestMemoryParameters(TestResult result, int testCount) {
		super(result, testCount);
	}

	public void test(int i) {
		switch (i) {
		// public MemoryParameters(long maxMemoryArea, long maxImmortal) 

		case 1:
			new MemoryParameters(0, 0);
		case 2:
			new MemoryParameters(1, 0);
		case 3:
			new MemoryParameters(0, 1);
		case 5:
			new MemoryParameters(MemoryParameters.NO_MAX, 1);
			break;
		case 6:
			new MemoryParameters(1, MemoryParameters.NO_MAX);
			break;
		case 7:
			new MemoryParameters(MemoryParameters.NO_MAX, MemoryParameters.NO_MAX);
			break;
		case 8:
			try {
				new MemoryParameters(-2L, 0);
				assert false;
			} catch (IllegalArgumentException e) {
			}
			;
			break;
		case 9:
			try {
				new MemoryParameters(0, -2L);
				assert false;
			} catch (IllegalArgumentException e) {
			}
			;
			break;

		default:
			break;
		}
	}

}
