package javax.realtime.test.clock;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.RelativeTime;
import javax.safetycritical.TestPortal;
import javax.scj.util.Const;

import unitTest_Remove.TestCase;

public class TestClock extends TestCase
{  
  class ClockStub extends Clock 
  {
    private RelativeTime epochOffset;
    private RelativeTime resolution;
    private AbsoluteTime time;
    
    public ClockStub(int offset, int grain) {
      super(false);
      System.out.println("ClockStub 1");
      epochOffset = new RelativeTime(offset,0,this);
      resolution = new RelativeTime(grain,0,this);
      time = new AbsoluteTime(this);
      System.out.println("ClockStub 4");
    }
    
    public ClockStub() {
      this(0,1);
    }

    public RelativeTime getEpochOffset() {
      return epochOffset;
    }    

    public RelativeTime getResolution() {
      return new RelativeTime(resolution);
    }

    public RelativeTime getResolution(RelativeTime dest) {
      if (dest == null)
        return getResolution();
      else {
        dest.set(resolution.getMilliseconds(), resolution.getNanoseconds());
        return dest;
      }      
    }
    
    public AbsoluteTime getTime() {
      time.add(resolution,time);
      return time;
    }

    public AbsoluteTime getTime(AbsoluteTime dest) {
      if (dest == null) 
        return getTime();
      else
      {
        time.add(resolution, time);
        dest.set(time.getMilliseconds(), time.getNanoseconds());
      }
      return dest;
    }        
  }
  
  public static final int testCount = 1;  
  
  public TestClock(String name)
  {
    super(name);
  }
  
  public void test (int i) 
  {
	  System.out.println("test");
	  //TestPortal.ManagedMemory_allocateBackingStore(Const.PRIVATE_BACKING_STORE);
//    Clock clk = new ClockStub(1,1);
//    RelativeTime res;
//    AbsoluteTime dest;
      
    switch (i) { 
      case  1:
    	  System.out.println("case 1");
    	  new ClockStub(0,0);
    	  System.out.println("case 1 end");
    	  break;
//      case  2: new ClockStub(1,1); break;
//      case  3: new ClockStub(-1,0); break;
//      case  4: new ClockStub(0, -1); break;
//      
//               // Clock()
//      case  5: new ClockStub(); break;
//      
//               // RelativeTime getEpochOffset
//      case  6: clk.getEpochOffset(); break;
//      
//               // Clock getRealtimeClock()
//      case  7: ClockStub.getRealtimeClock(); break;
//      
//               // RelativeTime getResolution ()
//      case  8: clk.getResolution(); break;
//      
//               // RelativeTime getResolution(RelativeTime dest)
//      case  9: res = new RelativeTime();      
//               clk.getResolution(res);
//               break;
//      case 10: res = null;
//               clk.getResolution(res); break;
//               
//               // AbsoluteTime getTime ()
//      case 11: clk.getTime(); break;
//      
//               // AbsoluteTime getTime (AbsoluteTime dest)
//      case 12: dest = new AbsoluteTime();
//               clk.getTime(dest); break;
//      case 13: dest = null;
//               clk.getTime(dest); break;
//               
//               // Clock test from Anders P. Ravn and Hans Søndergaard:
//               // A Test Suite for Safety-Critical Java using JML.
//               // Proceedings of the 11th International Workshop on Java Technologies 
//               // for Real-time and Embedded Systems, JTRES 2013.
//               // Association for Computing Machinery, 2013. pp 80-88.                
//      case 14: clockTest(clk); break;

      default: break;
    }
  }
  
  

   
//  final int SIZE = 5;
//  AbsoluteTime[] sample; 
//  boolean failure;
//  RelativeTime resolution;
//  
//  /*@ 
//    behaviour
//      requires true; 
//      
//      ensures !failure;
//      ensures               
//        (\forall int i; 0 < i && i < SIZE;
//           sample[i-1].compareTo(sample[i]) < 0);
//      ensures 
//        (\forall int i; 0 < i && i < SIZE;
//            (sample[i]).subtract(sample[i-1]).
//               compareTo(resolution) >= 0 );
//    @*/
//  void clockTest(Clock c) {
//    resolution = c.getResolution();
//    final int MAXLOOPS = 10;
//    sample= new AbsoluteTime[SIZE];
//    failure = false;
//    
//    for (int i = 0; i < SIZE; i++)
//      sample[i] = new AbsoluteTime(c);
//    
//    c.getTime(sample[0]);
//    
//    for (int i = 1; i < SIZE; i++) {
//      int j = 0;
//      do {
//        c.getTime(sample[i]); 
//        j++;
//      } 
//      while (sample[i].subtract(sample[i-1]). compareTo (resolution) < 0 && j < MAXLOOPS );
//      
//      if (j == MAXLOOPS) {
//        failure = true; break;
//      }      
//    }
//  }  
}