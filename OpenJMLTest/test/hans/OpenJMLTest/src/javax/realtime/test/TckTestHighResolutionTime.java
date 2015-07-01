package javax.realtime.test;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.RelativeTime;
import javax.realtime.TestPortal.HighResolutionTimeStub;
import javax.scj.util.Const;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestHighResolutionTime extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestHighResolutionTime.testCount;
		TestCase test = new TestHighResolutionTime(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);

		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/realtime/HighResolutionTime.java ICECAPSDK/src/javax/realtime/AbsoluteTime.java ICECAPSDK/src/javax/realtime/RelativeTime.java";
	}
}

class TestHighResolutionTime extends TestCase 
{ 
	// --- Stub classes ----------------------------------
	
	class ClockStub extends Clock 
	{	    
	    public ClockStub() {
	      super(false);
	    }

	    public RelativeTime getEpochOffset() {
	      return null;
	    } 
	    public RelativeTime getResolution() {
	      return null;
	    }
	    public RelativeTime getResolution(RelativeTime dest) {
	      return null;    
	    }
	    public AbsoluteTime getTime() {
	      return null;
	    }
	    public AbsoluteTime getTime(AbsoluteTime dest) {	      
	      return null;
	    }        
	  }

  //--- TestHighResolutionTime ---------------------------------
	
  static final int testCount = 26;
  
  public TestHighResolutionTime(TestResult result, int testCount) {
		super(result, testCount);
  }
  
  public void test(int i) {    

    HighResolutionTimeStub hrs, hrs1; 
    AbsoluteTime abs;
    
    switch (i) {
      // HighResolutionTime(long millis, int nanos, Clock clock) 
      case  1:
        new HighResolutionTimeStub(0,0,null); break;
      case  2: 
        new HighResolutionTimeStub(0,1000001,null); break;
      case  3: 
        new HighResolutionTimeStub(0,-1000001,null); break;
      case  4: 
        new HighResolutionTimeStub(-1,1,null); break;
      case  5: 
        new HighResolutionTimeStub(1,-1,null); break;
        
//      case  6: 
//        hrs = new HighResolutionTimeStub(Long.MAX_VALUE,1000001,null);
//        assert hrs.getNanoseconds() == -999999; 
//        break;
//      case  7: 
//        hrs = new HighResolutionTimeStub(Long.MIN_VALUE,-1000001,null); 
//        assert hrs.getNanoseconds() == 999999; 
//        break; 
        
      // set  
      case  8: 
        hrs = new HighResolutionTimeStub(1,1,Clock.getRealtimeClock());            
        try { hrs.set(null); assert false; }
        catch (IllegalArgumentException e){}; 
        break;
      case  9: 
        abs = new AbsoluteTime(); hrs = new HighResolutionTimeStub(1,1,null);  
        try { hrs.set(abs); assert false; }
        catch (ClassCastException e){}; 
        break;
      case 10: 
        hrs = new HighResolutionTimeStub(1,1,null); 
        hrs.set(hrs); break;
      case 11:
        hrs = new HighResolutionTimeStub(1,1,null); 
        hrs1 = new HighResolutionTimeStub(2,2,null); 
        hrs1.set(hrs); 
        break;
      case 12: 
        hrs = new HighResolutionTimeStub(1,1,null); 
        hrs.set(1); break;
        
//      case 13: 
//        hrs = new HighResolutionTimeStub(1,1,null); 
//        hrs.set(Long.MAX_VALUE,1000001); break;
//      case 14: 
//        hrs = new HighResolutionTimeStub(1,1,null); 
//        hrs.set(Long.MIN_VALUE,-1000001); break;
        
      // equals
      case 15:
        hrs = new HighResolutionTimeStub(1,1,null); 
        hrs.equals(null); break;
      case 16:
        hrs = new HighResolutionTimeStub(1,1,null); 
        hrs.equals(this); break;
      case 17: 
        hrs = new HighResolutionTimeStub(1,1,null); 
        hrs1 = new HighResolutionTimeStub(2,2,null); 
        hrs1.equals(hrs1); break;
      case 18:
        hrs = new HighResolutionTimeStub(1,1,null); 
        hrs1 = new HighResolutionTimeStub(2,2,null); 
        hrs1.equals(hrs); break;
        
      // public int compareTo (HighResolutionTime time)      
      case 19: 
        hrs = new HighResolutionTimeStub(1,1,null); 
        try { hrs.compareTo(null); assert false; }
        catch (IllegalArgumentException e){}; break;
      case 20: 
        hrs = new HighResolutionTimeStub(1,1,null); 
        abs = new AbsoluteTime();
        try { hrs.compareTo(abs); assert false; }
        catch (ClassCastException e){}; break;
      case 21:
        hrs = new HighResolutionTimeStub(2,2,Clock.getRealtimeClock());
        hrs1 = new HighResolutionTimeStub(2,2,new ClockStub());
        try { hrs.compareTo(hrs1); assert false; }
        catch (IllegalArgumentException e){}; 
        break;        
      case 22: 
        new HighResolutionTimeStub(1,2,null).
          compareTo(new HighResolutionTimeStub(2,2,null)); break;
      case 23: 
        new HighResolutionTimeStub(2,1,null).
          compareTo(new HighResolutionTimeStub(2,2,null)); break;
      case 24:
        new HighResolutionTimeStub(2,2,null).
          compareTo(new HighResolutionTimeStub(2,2,null)); break;
      case 25: 
        new HighResolutionTimeStub(2,2,null).
          compareTo(new HighResolutionTimeStub(1,2,null)); break;
      case 26: 
        new HighResolutionTimeStub(2,2,null).
          compareTo(new HighResolutionTimeStub(2,1,null)); break;
          
      default:
        break;
    }
  } 
  
}