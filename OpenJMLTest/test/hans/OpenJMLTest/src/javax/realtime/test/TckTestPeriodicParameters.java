package javax.realtime.test;

import javax.realtime.AperiodicParameters;
import javax.realtime.PeriodicParameters;
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

public class TckTestPeriodicParameters extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestPeriodicParameters.testCount;
		TestCase test = new TestPeriodicParameters(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);

		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/realtime/PeriodicParameters.java";
	}
}

class TestPeriodicParameters extends TestCase
{
  // --- Stub class ----------------------------------
	
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
  
  //--- TestPeriodicParameters ---------------------------------
  
  static final int testCount = 18;  
  
  public TestPeriodicParameters(TestResult result, int testCount) {
	super(result, testCount);
  }
  
  public void test (int i) 
  {
    RelativeTime time_0 = new RelativeTime (0, 0);    
    RelativeTime time_1 = new RelativeTime (1, 0);
    RelativeTime time_2 = new RelativeTime (2, 0);
    
    TestPortal.ManagedMemory_allocateBackingStore(1000);
    AperiodicEventHandler miss = 
      new AperiodicEventHandlerStub(
            new PriorityParameters(1), new AperiodicParameters(), 
            new StorageParameters (1000L, new long[]{ 100L }, 100L, 200L, 200L) );
    
    switch (i) {  
      // PeriodicParameters(RelativeTime start, RelativeTime period):
      case  1: 
        try { new PeriodicParameters(null, null);
              assert false;}
        catch (IllegalArgumentException e){};
        break;
               
      // start == null
      case  2: 
        try { new PeriodicParameters(null, time_0);
              assert false;}
        catch (JmlAssertionError e){};
        break; 
        
      // period < 0 
      case  3: 
        try { new PeriodicParameters(null, new RelativeTime (-1, 0));
              assert false;}
        catch (JmlAssertionError e){} // invariant in superclass
        break;  
      case  4: 
        try { new PeriodicParameters(null, new RelativeTime (0, -1));
              assert false;}
        catch (JmlAssertionError e){} // invariant in superclass
        break; 
               
      // start != null
      case  5: 
        try { new PeriodicParameters(time_0, null);
              assert false;}
        catch (IllegalArgumentException e){};
        break;
      case  6: 
        new PeriodicParameters(time_0, time_1);
        break; 
      // start < 0
      case  7: 
        try { new PeriodicParameters(new RelativeTime (-1, 0), time_1);
              assert false;}
        catch (JmlAssertionError e){};
        break;
      case  8: 
        try { new PeriodicParameters(new RelativeTime (0, -1), time_1);
              assert false;}
        catch (JmlAssertionError e){};
        break;
               
     // PeriodicParameters(RelativeTime start, RelativeTime period,
     //                    RelativeTime deadline, AperiodicEventHandler missHandler):
     case  9: 
       try { new PeriodicParameters(null, null, null, null);}
       catch (IllegalArgumentException e){};
       break;
     case 10: 
       new PeriodicParameters(time_0, time_1, null, null);
       break;        
     case 11: 
       new PeriodicParameters(time_0, time_2, time_1, null);
       break;
     case 12: 
       new PeriodicParameters(time_0, time_2, time_1, miss);
       break;
     // start < 0
     case 13:
       try { new PeriodicParameters (new RelativeTime (-1, 0), 
               time_2, time_1, miss); 
             assert false;}
       catch (JmlAssertionError e){} 
       break;
     case 14: 
       try { new PeriodicParameters (new RelativeTime (0, -1),   
               time_2, time_1, miss); 
             assert false; }
       catch (JmlAssertionError e){} 
       break;  
       
     // period < 0        
     case 15:
       try { new PeriodicParameters (null, new RelativeTime (-1, 0), 
               time_1, miss); 
             assert false;}
       catch (JmlAssertionError e){} 
       break;
     case 16: 
       try { new PeriodicParameters (null, new RelativeTime (0, -1),   
               time_1, miss); 
             assert false; }
       catch (JmlAssertionError e){} 
       break;
       
     // deadline < 0  
     case 17:
       try { new PeriodicParameters (null, time_1, 
             new RelativeTime (-1, 0), miss); 
           assert false;}
       catch (JmlAssertionError e){} // invariant in superclass
       break;
     case 18: 
       try { new PeriodicParameters (null, time_1,   
               new RelativeTime (0, -1), miss); 
             assert false; }
       catch (JmlAssertionError e){} // invariant in superclass
       break;
       
      default: break;
    }
  }
}