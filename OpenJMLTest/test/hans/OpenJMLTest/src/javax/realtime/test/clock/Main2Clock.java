package javax.realtime.test.clock;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.RelativeTime;

public class Main2Clock
{

  public static void main (String[] args)
  {
    
    class ClockStub extends Clock 
    {
      private RelativeTime epochOffset;
      private RelativeTime resolution;
      private AbsoluteTime time;
      
      public ClockStub(int offset, int grain) {
        super(true);
        epochOffset = new RelativeTime(offset,0,this);
        resolution = new RelativeTime(grain,0,this);
        time = new AbsoluteTime(this);
      }
      
//      public ClockStub() {
//        this(0,1);
//      }

      public RelativeTime getEpochOffset() {
        return epochOffset;
      }

      public RelativeTime getResolution() {
        return resolution;
      }

      public RelativeTime getResolution(RelativeTime dest) {
        if (dest == null) 
          dest = new RelativeTime(resolution);
        else
          dest = resolution;
        return dest;
      }

      public AbsoluteTime getTime() {
        time.add(resolution);
        //devices.Console.println("time: " + time);
        return time;
      }

      public AbsoluteTime getTime(AbsoluteTime dest) {
        time.add(resolution, time);
        if (dest == null) 
          dest = new AbsoluteTime(time);
        else
          dest = time;
        //devices.Console.println("dest: " + dest);
        return dest;
      }
    }
    
    final int SIZE = 5;
    AbsoluteTime[] sample;
    
    Clock c = new ClockStub (1, 1);
    clockTest (c);
    
    
    sample= new AbsoluteTime[SIZE];
    
    sample[0] = c.getTime(sample[0]);
    devices.Console.println("sample[0]: " + sample[0]);
    
    for (int i = 1; i < SIZE; i++){       
      sample[i] = c.getTime(sample[i]);  // sample[i] = time + resolution
      devices.Console.println("\nsample[" + (i-1) + "]: " + sample[i-1]);
      devices.Console.println("sample[" + i + "]: " + sample[i]);
      devices.Console.println("compare (i-1) and i : " + sample[i-1].compareTo(sample[i]) + "\n");
      
      boolean result = (sample[i].subtract(sample[i-1])). compareTo(c.getResolution()) >= 0;
      
      devices.Console.println("(sample[i]).subtract(sample[i-1])).compareTo(c.getResolution()) >= 0: " + result);
          
    }
    devices.Console.println("Main2Clock end");
  }

  
   
  //void clockTest(Clock c) { 
  //  sample= new AbsoluteTime[SIZE];
  //  
  //  sample[0] = c.getTime(sample[0]);
  //  for (int i = 1; i < SIZE; i++) {
  //    sample[i] = c.getTime(sample[i]);  // sample[i] = time + resolution   
  //  }
  //}
  
  static void clockTest(Clock c) {
    
    final int MAXLOOPS = 10;
    final int SIZE = 3;
    AbsoluteTime[] sample;
    boolean failure;
    
    sample= new AbsoluteTime[SIZE];
    RelativeTime resolution = c.getResolution();
    failure = false;
    
//    sample[0] = c.getTime(sample[0]);
//    for (int i = 1; i < SIZE; i++){
//      int j = 0;
//      do {
//        sample[i] = c.getTime(sample[i]); j++;
//      } while (sample[i].equals(sample[i-1]) && j < MAXLOOPS );
//      if (j == MAXLOOPS) {
//        failure = true; break;
//      }
//    }
    
    sample[0] = c.getTime(sample[0]);
    for (int i = 1; i < SIZE; i++){
      int j = 0;
      do {
        sample[i] = c.getTime(sample[i]); j++;
      } while (sample[i].subtract(sample[i-1]). compareTo (resolution) < 0 && j < MAXLOOPS );
      if (j == MAXLOOPS) {
        failure = true; break;
      }
    }
    
    devices.Console.println("failure: " + failure);
    
  }
  
}