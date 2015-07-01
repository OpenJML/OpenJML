package javax.realtime.test;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.RelativeTime;
import javax.scj.util.Const;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestRelativeTime extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestRelativeTime.testCount;
		TestCase test = new TestRelativeTime(result, numberOfCases);

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

class TestRelativeTime extends TestCase 
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
  //--- TestAbsoluteTime ---------------------------------	
	
  static final int testCount = 76;
	
  public TestRelativeTime (TestResult result, int testCount) {
	super(result, testCount);
  }
  
  public void test(int i) 
  {
    RelativeTime rel, rel1, rel2;
    AbsoluteTime abs;
    
    switch (i) {
      // Inherited from HighResolutionTime
      // void set(HighResolutionTime time)
      case  1: rel = new RelativeTime(1,1,Clock.getRealtimeClock());            
               try{rel.set(null); assert false;}
               catch (IllegalArgumentException e){}; 
               break;
      case  2: rel = new RelativeTime();
               abs = new AbsoluteTime();
               try{rel.set(abs); assert false;}
               catch (ClassCastException e){}; 
               break;
      case  3: rel = new RelativeTime(1,2); 
               rel.set(rel); break;
      case  4: rel = new RelativeTime(1,2); rel1 = new RelativeTime(2,2,null); 
               rel1.set(rel); break;
      case  5: rel = new RelativeTime(1,2); rel2 = new RelativeTime(2,2); 
               rel2.set(rel); break;
               
      // void set (long millis)
      case  6: rel1 = new RelativeTime(2,2); 
               rel1.set(1); break;
      
      // void set (long millis, int nanos) 
      case  7: rel = new RelativeTime(1,2); 
               rel.set(0,1000001); break;
      case  8: rel = new RelativeTime(1,2);
               rel.set(0,-1000001); break;
               
//      case  9: rel1 = new RelativeTime(1,2); // does not woork
//               rel1.set(Long.MAX_VALUE,1000001); break;
//      case 10: rel1 = new RelativeTime(1,2); 
//               rel1.set(Long.MIN_VALUE,-1000001); break;
               
      // boolean equals (HighResolutionTime time)     
      case 11: rel = new RelativeTime(1,2); 
               rel.equals(null); break;
      case 12: rel = new RelativeTime(1,2); 
               rel.equals(this); break;
      case 13: rel = new RelativeTime(1,2); 
               rel.equals(rel); break;
      case 14: rel = new RelativeTime(1,2); rel1 = new RelativeTime(1,3); 
               rel1.equals(rel); break;
               
      // int compareTo (HighResolutionTime time)      
      case 15: try { rel = new RelativeTime(1,2); 
                     rel.compareTo(null); assert false;}
               catch (IllegalArgumentException e){}; break;
      case 16: try { rel = new RelativeTime(1,2); abs = new AbsoluteTime(1,2); 
                     rel.compareTo(abs); assert false;}
               catch (ClassCastException e){}; break;
      case 17: try {
    	         rel1 = new RelativeTime(2, 2); 
    	         rel2 = new RelativeTime(2, 2, new ClockStub());
                 rel1.compareTo(rel2);assert false;
               }
               catch (IllegalArgumentException e){ }; 
               break; 
      case 18: new RelativeTime(1,2,null).compareTo(new RelativeTime(2,2,null)); break;
      case 19: new RelativeTime(2,1,null).compareTo(new RelativeTime(2,2,null)); break;
      case 20: new RelativeTime(2,2,null).compareTo(new RelativeTime(2,2,null)); break;
      case 21: new RelativeTime(2,2,null).compareTo(new RelativeTime(1,2,null)); break;
      case 22: new RelativeTime(2,2,null).compareTo(new RelativeTime(2,1,null)); break;
      
      // RelativeTime()
      case 23: new RelativeTime(); break;
      
      // RelativeTime(long millis, int nanos)      
      case 24: new RelativeTime(0,0); break;
      case 25: new RelativeTime(0,1000001); break;
      case 26: new RelativeTime(0,-1000001); break;
      case 27: new RelativeTime(-1,1); break;
      case 28: new RelativeTime(1,-1); break;
      
//      case 29: rel = new RelativeTime(Long.MAX_VALUE,1000001); 
//               assert rel.getNanoseconds() == -999999; break;
//      case 30: rel = new RelativeTime(Long.MIN_VALUE,-1000001); 
//               assert rel.getNanoseconds() == 1; break;
               
      // RelativeTime(RelativeTime time)
      case 31: rel = new RelativeTime(); new RelativeTime(rel); break;
      case 32: rel = null; 
               try{ new RelativeTime(rel); assert false;}
               catch (IllegalArgumentException e){}; break;
               
      // RelativeTime (long millis, int nanos, Clock clock)
      case 33: new RelativeTime(0,0,null); break;
      case 34: new RelativeTime(0,1000001,null); break;
      case 35: new RelativeTime(0,-1000001,null); break;
      case 36: new RelativeTime(-1,1,null); break;
      case 37: new RelativeTime(1,-1,null); break;
      
//      case 38: rel = new RelativeTime(Long.MAX_VALUE,1000001,null); 
//               assert rel.getNanoseconds() == -999999; break;
//      case 39: rel = new RelativeTime(Long.MIN_VALUE,-1000001,null); 
//               assert rel.getNanoseconds() == 1; break;
               
      case 40: new RelativeTime(1,1,Clock.getRealtimeClock()); break; 
      
      // RelativeTime (Clock clock)
      case 41: Clock c= null; new RelativeTime(c); break;
      case 42: new RelativeTime(Clock.getRealtimeClock()); break;
      
      // RelativeTime add (long millis, int nanos)     
      case 43: rel = new RelativeTime(); rel.add(0,0); break;
      case 44: rel = new RelativeTime(); rel.add(0,1000001); break;
      case 45: rel = new RelativeTime(); rel.add(0,-1000001); break;
      case 46: rel = new RelativeTime(); rel.add(-1,1); break;
      case 47: rel = new RelativeTime(); rel.add(1,-1); break;
      
//      case 48: rel = new RelativeTime(); rel.add(Long.MAX_VALUE,1000001); 
//               assert rel.getNanoseconds() == -999999; break;
//      case 49: rel = new RelativeTime(); rel.add(Long.MIN_VALUE,-1000001); 
//               assert rel.getNanoseconds() == 1; break;  
               
      // RelativeTime add (long millis, int nanos, RelativeTime dest)
      case 50: rel = new RelativeTime(); rel.add(0,0,null); break;
      case 51: rel = new RelativeTime(); rel.add(0,1000001,null); break;
      case 52: rel = new RelativeTime(); rel.add(0,-1000001,null); break;
      case 53: rel = new RelativeTime(); rel.add(-1,1,null); break;
      case 54: rel = new RelativeTime(); rel.add(1,-1,null); break;
      
//      case 55: rel = new RelativeTime(); rel.add(Long.MAX_VALUE,1000001,null); 
//               assert rel.getNanoseconds() == -999999; break;
//               
//      case 56: rel = new RelativeTime(); rel.add(Long.MIN_VALUE,-1000001,null); 
//               assert rel.getNanoseconds() == 1; break; 
               
      case 57: rel1 = new RelativeTime(1,-1); rel = new RelativeTime(); 
               rel.add(0,0,rel1); break;        
      case 58: rel = new RelativeTime(1,-1); rel.add(0,1000001,rel); break;
      case 59: rel = new RelativeTime(1,-1); rel.add(0,-1000001,rel); break;
      
      // RelativeTime add (RelativeTime time)      
      case 60: rel = new RelativeTime(); 
               rel.add(new RelativeTime(1,-1)); break;
               
      case 61: rel1 = new RelativeTime(); 
               rel2 = new RelativeTime(1,1,null); 
               rel1.add(rel2); 
               break;
      case 62: rel1 = new RelativeTime(1,1,Clock.getRealtimeClock()); 
               rel2 = new RelativeTime(1,1,null); 
               rel1.add(rel2); 
               break;        
               
               
      case 63: rel = new RelativeTime();            
               try{rel.add(null); assert false;}
               catch (IllegalArgumentException e){}; break;      
      case 64: rel1 = new RelativeTime(1,1,Clock.getRealtimeClock());
               rel2 = new RelativeTime(1,1,new ClockStub());
               try{rel1.add(rel2); assert false;}
               catch (IllegalArgumentException e){}; break;
               
      // RelativeTime add (RelativeTime time, RelativeTime dest)
      case 65: rel = new RelativeTime(); 
               rel.add(new RelativeTime(1,-1),null); break;
      case 66: rel = new RelativeTime();            
               try{rel.add(null,null); assert false;}
               catch (IllegalArgumentException e){}; break;     
      case 67: rel1 = new RelativeTime(1,1,Clock.getRealtimeClock());
               rel2 = new RelativeTime(1,1,new ClockStub());
               try { rel1.add(rel2,null); assert false;}
               catch (IllegalArgumentException e){}; break;                
      case 68: rel1 = new RelativeTime(); rel = new RelativeTime(); 
               rel.add(new RelativeTime(1,-1),rel1); break;
      case 69: rel = new RelativeTime(); rel.add(new RelativeTime(1,-1),rel); break;
      
      // RelativeTime subtract (RelativeTime time)
      case 70: rel = new RelativeTime(); rel.subtract(new RelativeTime(1,-1)); break;
      case 71: rel = new RelativeTime();            
               try{rel1 = null; rel.subtract(rel1); assert false;}
               catch (IllegalArgumentException e){}; 
               break;      
      case 72: rel1 = new RelativeTime(1,1,Clock.getRealtimeClock());
               rel2 = new RelativeTime(1,1,new ClockStub());
               try { rel1.subtract(rel2); assert false; }
               catch (IllegalArgumentException e){}; 
               break;
               
      // RelativeTime subtract (RelativeTime time, RelativeTime dest)
      case 73: rel = new RelativeTime(); 
               rel.subtract(new RelativeTime(1,-1),null); break;
      case 74: rel = new RelativeTime(); 
               rel.subtract(new RelativeTime(1,-1),rel); break;
      case 75: rel = new RelativeTime();            
               try{rel1 = null; rel.subtract(null,rel1); assert false;}
               catch (IllegalArgumentException e){}; break;     
      case 76: rel = new RelativeTime(1,1,Clock.getRealtimeClock());
               rel2 = new RelativeTime(1,1,new ClockStub());
               try{rel1 = null; rel.subtract(rel2, rel1); assert false;}
               catch (IllegalArgumentException e){}; 
               break;
  
      default: break;
    }
  }
  
}