package javax.realtime.test;

import javax.realtime.AperiodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.realtime.ReleaseParameters;
import javax.safetycritical.AperiodicEventHandler;
import javax.safetycritical.StorageParameters;
import javax.safetycritical.TestPortal;
import javax.scj.util.Const;

import org.jmlspecs.utils.JmlAssertionError;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestReleaseParameters extends BasicJMLTest {
	
	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestReleaseParameters.testCount;
		TestCase test = new TestReleaseParameters(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);

		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/realtime/ReleaseParameters.java";
	}
}

class TestReleaseParameters extends TestCase
{ 
  // --- Stub classes ----------------------------------
	
  class ReleaseParametersStub extends ReleaseParameters
  {
    protected ReleaseParametersStub ()
    {
      super();
    }

    protected ReleaseParametersStub (RelativeTime deadline,
        AperiodicEventHandler missHandler)
    {
      super(deadline, missHandler);
    }
  }
  
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
  
  //--- TestReleaseParameters ---------------------------------
  
  static final int testCount = 6; 
  
  public TestReleaseParameters(TestResult result, int testCount) {
		super(result, testCount);
  }
  
  public void test (int i) 
  {
    AperiodicEventHandler miss = null;
      
    switch (i) { 
      case  1: new ReleaseParametersStub(); break;
      case  2: new ReleaseParametersStub(null, null); break;
      case  3: new ReleaseParametersStub(new RelativeTime (0, 0), null);
               break;
      case  4: 
        TestPortal.ManagedMemory_allocateBackingStore(1000);
        miss = new AperiodicEventHandlerStub(
            new PriorityParameters(1), new AperiodicParameters(), 
            new StorageParameters (1000L, new long[]{ 100L }, 100L, 200L, 200L) );
        
        new ReleaseParametersStub (new RelativeTime (1, 0), miss);
        break;
               
      case  5: 
        TestPortal.ManagedMemory_allocateBackingStore(1000);
        miss = new AperiodicEventHandlerStub(
            new PriorityParameters(1), new AperiodicParameters(), 
            new StorageParameters (1000L, new long[]{ 100L }, 100L, 200L, 200L) );
        
        try { new ReleaseParametersStub (new RelativeTime (-1, 0), miss); 
              assert false; } 
        catch (JmlAssertionError e){} 
        break;
        
      case  6: 
        TestPortal.ManagedMemory_allocateBackingStore(1000);
        miss = new AperiodicEventHandlerStub(
            new PriorityParameters(1), new AperiodicParameters(), 
            new StorageParameters (1000L, new long[]{ 100L }, 100L, 200L, 200L) );
        
        try { new ReleaseParametersStub (new RelativeTime (0, -1), miss); 
              assert false; }
        catch (JmlAssertionError e){} 
        break;
        
      default: break;
    }
  }  
}