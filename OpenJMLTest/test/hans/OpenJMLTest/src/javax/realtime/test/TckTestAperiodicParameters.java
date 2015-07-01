package javax.realtime.test;

import javax.realtime.AperiodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.AperiodicEventHandler;
import javax.safetycritical.StorageParameters;
import javax.safetycritical.TestPortal;
import javax.scj.util.Const;

import org.jmlspecs.utils.JmlAssertionError;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestAperiodicParameters extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestAperiodicParameters.testCount;
		TestCase test = new TestAperiodicParameters(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);

		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/realtime/AperiodicParameters.java";
	}
}
	
class TestAperiodicParameters extends TestCase
{
  // --- Stub class ------------------------------------------
	
  class AperiodicEventHandlerStub extends AperiodicEventHandler
  {
    public AperiodicEventHandlerStub(PriorityParameters priority,
        AperiodicParameters release,
        StorageParameters storage)
    {
      super (priority, release, storage);
    }

    public void handleAsyncEvent ()
    {
    }
  }
  
  //--- TestAperiodicParameters ---------------------------------
  
  static final int testCount = 7;  
  
  public TestAperiodicParameters(TestResult result, int testCount) {
	super(result, testCount);
  }
  
  public void test (int i) 
  {
    RelativeTime time_1 = new RelativeTime (1, 0); 

    TestPortal.ManagedMemory_allocateBackingStore(1000);
    AperiodicEventHandler miss = new AperiodicEventHandlerStub(
        new PriorityParameters(1), new AperiodicParameters(), 
        new StorageParameters (1000L, new long[]{ 100L }, 100L, 200L, 200L) );
    
    switch (i) {  
      // AperiodicParameters():
      case  1: 
        new AperiodicParameters();
        break;
               
      // public AperiodicParameters(RelativeTime deadline, AperiodicEventHandler missHandler):
      case  2: 
        new AperiodicParameters(null, null);
        break;
      case  3:
        new AperiodicParameters(null, miss);
        break;  
      case  4: 
        new AperiodicParameters(time_1, null);
        break; 
      case  5:
        new AperiodicParameters(time_1, miss);
        break;
               
      // inherited from ReleaseParameters
      case  6:
        try { new AperiodicParameters(new RelativeTime (-1, 0), miss);
              assert false;}
        catch (JmlAssertionError e){} 
        break;
      case  7:
        try { new AperiodicParameters(new RelativeTime (0, -1), miss);
              assert false;}
        catch (JmlAssertionError e){} 
        break;       
      default: break;
    }
  }
}
