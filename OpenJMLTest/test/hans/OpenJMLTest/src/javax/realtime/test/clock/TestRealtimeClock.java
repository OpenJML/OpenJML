package javax.realtime.test.clock;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.RelativeTime;

import unitTest_Remove.TestCase;

public class TestRealtimeClock extends TestCase
{  
  public TestRealtimeClock(String name)
  {
    super(name);
  }
  
  public void test (int i) 
  {
	System.out.println("TestRealtimeClock.test begin");
	
    Clock clk = Clock.getRealtimeClock();
    
    System.out.println("TestRealtimeClock.test ...");
    
    RelativeTime res, res2;
    AbsoluteTime dest;
      
    switch (i) { 
      // RelativeTime getEpochOffset()
      case  1: clk.getEpochOffset(); 
               break;
      
      // RelativeTime getResolution ()
      case  2: clk.getResolution(); break;
      
      // RelativeTime getResolution(RelativeTime dest)
      case  3: res = new RelativeTime();
               res2 = clk.getResolution(res); break;
      case  4: res = null;
               res2 = clk.getResolution(res); break; 
               
      // AbsoluteTime getTime ()
      case  5: clk.getTime(); break;
      
      // AbsoluteTime getTime (AbsoluteTime dest)
      case  6: dest = new AbsoluteTime();
               clk.getTime(dest); break;
      case  7: dest = null;
               clk.getTime(dest); break; 
               
               // Clock test from Anders P. Ravn and Hans Søndergaard:
               // A Test Suite for Safety-Critical Java using JML
               // Proceedings of the 11th International Workshop on Java Technologies 
               // for Real-time and Embedded Systems, JTRES 2013.
               // Association for Computing Machinery, 2013. pp 80-88.                
      //case  8: clockTest(clk); break;

      default: break;
    }
  }
  
  public static final int testCount = 8;  
  
  
//  final int SIZE = 20;
//  AbsoluteTime[] sample;
//  boolean failure;
//  RelativeTime resolution;
//  
//  
//  /*@ 
//    behaviour
//      requires true; 
//    
//      ensures !failure;
//      ensures 
//        (\forall int i; 0 < i && i < SIZE;
//           sample[i-1].compareTo(sample[i]) < 0);
// 
//      ensures 
//        (\forall int i; 0 < i && i < SIZE;
//           (sample[i]).subtract(sample[i-1]).
//             compareTo(resolution) >= 0 );      
//    @*/
//  void clockTest(Clock c) {
//    resolution = c.getResolution();
//    final int MAXLOOPS = 10000;
//    sample= new AbsoluteTime[SIZE];
//    failure = false; 
//    
//    for (int i = 0; i < SIZE; i++)
//      sample[i] = new AbsoluteTime(c);
//   
//    c.getTime(sample[0]);
//    for (int i = 1; i < SIZE; i++){
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