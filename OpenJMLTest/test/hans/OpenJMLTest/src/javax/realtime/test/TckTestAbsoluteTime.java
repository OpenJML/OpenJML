package javax.realtime.test;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.RelativeTime;
import javax.scj.util.Const;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestAbsoluteTime extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestAbsoluteTime.testCount;
		TestCase test = new TestAbsoluteTime(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);

		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/realtime/HighResolutionTime.java ICECAPSDK/src/javax/realtime/AbsoluteTime.java";
	}
}

class TestAbsoluteTime extends TestCase 
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
	
  static final int testCount = 83;
  
  public TestAbsoluteTime(TestResult result, int testCount) {
		super(result, testCount);
  }
  
  public void test(int i) 
  {	  
    AbsoluteTime abs, abs1, abs2;
    RelativeTime rel;
    
    switch (i) {    
      // AbsoluteTime()
      case  1:
    	new AbsoluteTime(); break;
    	
      // AbsoluteTime(long millis, int nanos) 
      case  2:
      	new AbsoluteTime(0,0); break;
      case  3:
      	new AbsoluteTime(0,1000001); break;  
      case  4: 
    	new AbsoluteTime(0,-1000001); break;
      case  5: 
    	  new AbsoluteTime(-1,1); break;
      case  6: 
    	  new AbsoluteTime(1,-1); break;
    	  
//    case  7: 
//        abs = new AbsoluteTime(Long.MAX_VALUE,1000001); // does not work
//        assert abs.getNanoseconds() == -999999; 
//        break;
//    case  8: 
//    	abs = new AbsoluteTime(Long.MIN_VALUE,-1000001); // does not work
//        assert abs.getNanoseconds() == 999999; 
//        break; 
    	  

      //  AbsoluteTime(AbsoluteTime time)
      case  9: 
    	  abs = new AbsoluteTime(); new AbsoluteTime(abs); break;
      case 10: 
    	  abs = null; 
          try { new AbsoluteTime(abs); assert false; }
          catch (IllegalArgumentException e){}; 
          break;
  
      //  AbsoluteTime (long millis, int nanos, Clock clock)	
      case 11:
    	new AbsoluteTime(0,0,null); break;         
      case 12: 
        new AbsoluteTime(0,1000001,null); break;
      case 13: 
        new AbsoluteTime(0,-1000001,null); break;
      case 14: 
        new AbsoluteTime(-1,1,null); break;
      case 15: 
        new AbsoluteTime(1,-1,null); break;
    	
      case 16:
        new AbsoluteTime(1, 1, Clock.getRealtimeClock()); break; 

      //  AbsoluteTime (Clock clock)
      case 17: 
    	  Clock c= null; new AbsoluteTime(c); break;
      case 18: 
    	  new AbsoluteTime(Clock.getRealtimeClock()); break;  
        
      // Inherited from HighResolutionTime
      // void set(HighResolutionTime time)
      case 19: abs = new AbsoluteTime(1,1,Clock.getRealtimeClock());            
               try{abs.set(null); assert false;}
               catch (IllegalArgumentException e){}; break;
      case 20: abs = new AbsoluteTime();
               try{abs.set(new RelativeTime()); assert false;}
               catch (ClassCastException e){}; 
               break;
      case 21: abs = new AbsoluteTime(1,2); 
               abs.set(abs); break;
      case 22: abs = new AbsoluteTime(1,2); abs1 = new AbsoluteTime(2,2,null); 
               abs1.set(abs); break;
      case 23: abs = new AbsoluteTime(1,2); abs2 = new AbsoluteTime(2,2); 
               abs2.set(abs); break;
               
      // void set (long millis)
      case 24: abs1 = new AbsoluteTime(2,2); 
               abs1.set(1); break;
               
      // void set (long millis, int nanos)   
      case 25: abs1 = new AbsoluteTime(1,2); 
               abs1.set(0,1000001); break;
      case 26: abs1 = new AbsoluteTime(1,2); 
               abs1.set(0,-1000001); break;
      
//      case 27: abs1 = new AbsoluteTime(1,2); // does not work
//               abs1.set(Long.MAX_VALUE,1000001); break;
//      case 28: abs1 = new AbsoluteTime(1,2);  // does not work
//               abs1.set(Long.MIN_VALUE,-1000001); break;
               
      // boolean equals (HighResolutionTime time)     
      case 29: abs = new AbsoluteTime(1,2); 
               abs.equals(null); break;
      case 30: abs = new AbsoluteTime(1,2); 
               abs.equals(this); break;
      case 31: abs = new AbsoluteTime(1,2); 
               abs.equals(abs); break;
      case 32: abs = new AbsoluteTime(1,2); abs1 = new AbsoluteTime(1,2); 
               abs1.equals(abs); break;
               
      // int compareTo (HighResolutionTime time)      
      case 33: try{abs = new AbsoluteTime(1,2); 
                   abs.compareTo(null); assert false;}
               catch (IllegalArgumentException e){}; 
               break;
      case 34: try{abs = new AbsoluteTime(1,2); rel = new RelativeTime(1,2);
                   abs.compareTo(rel); assert false;}
               catch (ClassCastException e){}; 
               break;
      case 35: try{abs = new AbsoluteTime(); 
                   new AbsoluteTime(2,2,null).compareTo(abs);assert false;}
               catch (IllegalArgumentException e){}; break; 
      case 36: new AbsoluteTime(1,2,null).compareTo(new AbsoluteTime(2,2,null)); 
               break;
      case 37: new AbsoluteTime(2,1,null).compareTo(new AbsoluteTime(2,2,null)); 
               break;
      case 38: new AbsoluteTime(2,2,null).compareTo(new AbsoluteTime(2,2,null)); 
               break;
      case 39: new AbsoluteTime(2,2,null).compareTo(new AbsoluteTime(1,2,null));  
               break;
      case 40: new AbsoluteTime(2,2,null).compareTo(new AbsoluteTime(2,1,null)); 
               break; 
      
      // AbsoluteTime add (long millis, int nanos)     
      case 41: abs = new AbsoluteTime(); abs.add(0,0); break;
      case 42: abs = new AbsoluteTime(); abs.add(0,1000001); break;
      case 43: abs = new AbsoluteTime(); abs.add(0,-1000001); break;
      case 44: abs = new AbsoluteTime(); abs.add(-1,1); break;
      case 45: abs = new AbsoluteTime(); abs.add(1,-1); break;
      
//      case 46: abs = new AbsoluteTime(); abs.add(Long.MAX_VALUE,1000001); // does not work
//               assert abs.getNanoseconds() == -999999; break;
//      case 47: abs = new AbsoluteTime(); abs.add(Long.MIN_VALUE,-1000001); // does not work
//               assert abs.getNanoseconds() == 1; break; 
               
      // AbsoluteTime add (long millis, int nanos, AbsoluteTime dest)
      case 48: abs = new AbsoluteTime(); abs.add(0,0,null); break;
      case 49: abs = new AbsoluteTime(); abs.add(0,1000001,null); break;
      case 50: abs = new AbsoluteTime(); abs.add(0,-1000001,null); break;
      case 51: abs = new AbsoluteTime(); abs.add(-1,1,null); break;
      case 52: abs = new AbsoluteTime(); abs.add(1,-1,null); break;
      
//      case 53: abs = new AbsoluteTime(); abs.add(Long.MAX_VALUE,1000001,null);  // does not work
//               assert abs.getNanoseconds() == -999999; break;
//      case 54: abs = new AbsoluteTime(); abs.add(Long.MIN_VALUE,-1000001,null); // does not work
//               assert abs.getNanoseconds() == 1; break; 
               
      case 55: abs = new AbsoluteTime(); abs1 = new AbsoluteTime(1,-1); 
               abs.add(0,0,abs1); break; 
               
      case 56: abs = new AbsoluteTime(1,-1); abs1 = new AbsoluteTime();
               abs.add(0,1000001,abs1); break;
      case 57: abs = new AbsoluteTime(1,-1); 
               abs.add(0,1000001,abs); break;      
      case 58: abs = new AbsoluteTime(1,-1); 
               abs.add(0,-1000001,abs); break;
      
      // AbsoluteTime add (RelativeTime time)      
      case 59: abs = new AbsoluteTime(); 
               abs.add(new RelativeTime(1,-1)); break;
      case 60: abs = new AbsoluteTime(); 
               rel = new RelativeTime(1,1,null); 
               abs.add(rel); 
               break;
      case 61: abs = new AbsoluteTime(1,1,Clock.getRealtimeClock()); 
               rel = new RelativeTime(1,1,null); 
               abs.add(rel); 
               break;
      case 62: abs = new AbsoluteTime();            
               try{abs.add(null); assert false;}
               catch (IllegalArgumentException e){}; 
               break;      
      case 63: abs = new AbsoluteTime(1,1,Clock.getRealtimeClock()); 
               rel = new RelativeTime(1,1,new ClockStub());                    
               try { abs.add(rel); assert false; }
               catch (IllegalArgumentException e){}; 
               break;
               
      // AbsoluteTime add (RelativeTime time, AbsoluteTime dest)
      case 64: abs = new AbsoluteTime(); 
               abs.add(new RelativeTime(1,-1),null); 
               break;
      case 65: abs = new AbsoluteTime();            
               try{abs.add(null,null); assert false;}
               catch (IllegalArgumentException e){}; 
               break;     
      case 66: abs = new AbsoluteTime(1,1,Clock.getRealtimeClock());
               rel = new RelativeTime(1,1,new ClockStub());
               try{abs.add(rel,null); assert false;}
               catch (IllegalArgumentException e){}; 
               break;                
      case 67: abs1 = new AbsoluteTime(); abs = new AbsoluteTime(); 
               abs.add(new RelativeTime(1,-1),abs1); break;
      case 68: abs = new AbsoluteTime(); 
               abs.add(new RelativeTime(1,-1),abs); break;
      
      // RelativeTime subtract (AbsoluteTime time)
      case 69: abs = new AbsoluteTime(); abs.subtract(new RelativeTime(1,-1)); break;
      case 70: abs = new AbsoluteTime();            
               try{rel = null; abs.subtract(rel); assert false;}
               catch (IllegalArgumentException e){}; break;      
      case 71: abs = new AbsoluteTime(1,1,Clock.getRealtimeClock()); 
               rel = new RelativeTime(1,1,new ClockStub());
               try{abs.subtract(rel); assert false;}
               catch (IllegalArgumentException e){}; 
               break;
               
      // RelativeTime subtract (AbsoluteTime time, RelativeTime dest)
      case 72: abs = new AbsoluteTime(); 
               abs.subtract(new AbsoluteTime(1,-1),null); break;
      case 73: abs = new AbsoluteTime(); rel = new RelativeTime(); 
               abs.subtract(new AbsoluteTime(1,-1),rel); break;
      case 74: abs = new AbsoluteTime();            
               try{rel = null; abs.subtract(null,rel); assert false;}
               catch (IllegalArgumentException e){}; break;     
      case 75: abs = new AbsoluteTime(1,1,Clock.getRealtimeClock());            
               try{rel = null; abs.subtract(new AbsoluteTime(1,1,null),rel); assert false;}
               catch (IllegalArgumentException e){}; break;
               
      // AbsoluteTime subtract (RelativeTime time)
      case 76: abs = new AbsoluteTime(); 
               abs.subtract(new RelativeTime(1,-1)); break;
      case 77: abs = new AbsoluteTime();            
               try{rel = null; abs.subtract(rel); assert false;}
               catch (IllegalArgumentException e){}; break;      
      case 78: abs = new AbsoluteTime(1,1,Clock.getRealtimeClock()); 
               rel = new RelativeTime(1,1,new ClockStub());
               try{ abs.subtract(rel); assert false;}
               catch (IllegalArgumentException e) {}; 
               break;
               
      // AbsoluteTime subtract (RelativeTime time, AbsoluteTime dest)
      case 79: abs = new AbsoluteTime(); 
               abs.subtract(new RelativeTime(1,-1),null); break;
      case 80: abs = new AbsoluteTime(); abs1 = new AbsoluteTime(); 
               abs.subtract(new RelativeTime(1,-1),abs1); break;
      case 81: abs = new AbsoluteTime(); 
               abs.subtract(new RelativeTime(1,-1),abs); break;
      case 82: abs = new AbsoluteTime();            
               try{ abs.subtract(null,abs); assert false;}
               catch (IllegalArgumentException e){}; break;     
      case 83: abs = new AbsoluteTime(1,1,Clock.getRealtimeClock());
               rel = new RelativeTime(1,1,new ClockStub());
               try{ abs.subtract(rel, abs); assert false;}
               catch (IllegalArgumentException e) {}; 
               break; 
      default: break;
    }
  }
}