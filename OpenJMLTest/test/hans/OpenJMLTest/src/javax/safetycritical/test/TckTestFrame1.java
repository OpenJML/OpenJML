package javax.safetycritical.test;

import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.Frame;
import javax.safetycritical.Mission;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;
import javax.safetycritical.TestPortal;
import javax.scj.util.Const;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestFrame1 extends BasicJMLTest {
	
	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestFrame1.testCount;
		TestCase test = new TestFrame1(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);
		result.print(test.getClass().getName(), numberOfCases);
		
		if (result.JMLerrorCount() + result.errorCount() == 0)
		{
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/safetycritical/Frame.java";
	}
}

class TestFrame1 extends TestCase {
	// --- Stub classes ----------------------------------

	static StorageParameters storageParameters_Handlers = new StorageParameters(Const.PRIVATE_BACKING_STORE,
			new long[] { Const.HANDLER_STACK_SIZE }, Const.PRIVATE_MEM, 0, 0);

	class PeriodicEvhStub extends PeriodicEventHandler {
		int count = 0;

		protected PeriodicEvhStub(PriorityParameters priority, PeriodicParameters periodic, StorageParameters storage) {
			super(priority, periodic, storage);
		}

		public void handleAsyncEvent() {
			devices.Console.println("pevh");
			count++;
			if (count > 1)
				Mission.getMission().requestTermination();
		}
	}

	//--- TestFrame1 ---------------------------------

	static final int testCount = 7;

	TestFrame1(TestResult result, int testCount)
	  {
		  super (result, testCount);
	}

	public void test(int i) {
		TestPortal.ManagedMemory_allocateBackingStore(Const.PRIVATE_BACKING_STORE);

		PeriodicEventHandler pevh = new PeriodicEvhStub(new PriorityParameters(1), new PeriodicParameters(
				new RelativeTime(), new RelativeTime(2000, 0)), storageParameters_Handlers);

		switch (i) {
		//public Frame(RelativeTime duration, PeriodicEventHandler[] handlers)

		case 1: // Frame (null, null):    	 
			try {
				new Frame(null, null);
				assert false;
			} catch (IllegalArgumentException e) {
			}
			;
			break;

		case 2: // Frame (not null, null):
			try {
				new Frame(new RelativeTime(1, 1), null);
				assert false;
			} catch (IllegalArgumentException e) {
			}
			;
			break;

		case 3: // Frame (not null, handlers not null but empty):
			new Frame(new RelativeTime(1, 1), new PeriodicEventHandler[0]);
			break;

		case 4: // Frame (null, handlers not null):
			try {
				new Frame(null, new PeriodicEventHandler[] { pevh });
				assert false;
			} catch (IllegalArgumentException e) {
			}
			;
			break;

		case 5: // Frame (not null, handlers not null); millisecs < 0        
			try {
				new Frame(new RelativeTime(-1, 1), new PeriodicEventHandler[] { pevh });
				assert false;
			} catch (IllegalArgumentException e) {
			}
			;
			break;

		case 6: // Frame (not null, handlers not null); millisecs < 0 && nanosecs < 0       
			try {
				new Frame(new RelativeTime(-1, -1), new PeriodicEventHandler[] { pevh });
				assert false;
			} catch (IllegalArgumentException e) {
			}
			;
			break;

		case 7: // Frame (not null, handlers not null but empty); time > 0      
			new Frame(new RelativeTime(-1, 2 * 1000000), new PeriodicEventHandler[0]);
			break;

		default:
			break;
		}
	}

}
