package javax.realtime.test.clock;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.RelativeTime;

public class Main2RealtimeClock
{

  public static void main (String[] args)
  {
    final int SIZE = 5;
    AbsoluteTime[] sample;
    
    Clock c = Clock.getRealtimeClock();
    devices.Console.println("\nClock resolution: " + c.getResolution());
    
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
 
  static void clockTest(Clock c) 
  {
    final int MAXLOOPS = 10000;
    final int SIZE = 20;
    AbsoluteTime[] sample;
    boolean failure;
    RelativeTime resolution;
    int j = 0;
    
    sample= new AbsoluteTime[SIZE];
    failure = false;
    resolution = new RelativeTime(c);
    c.getResolution(resolution);
    
    
    sample[0] = c.getTime(sample[0]);
    for (int i = 1; i < SIZE; i++){
      
      do {
        sample[i] = c.getTime(sample[i]); j++;
      } while (sample[i].equals(sample[i-1])&& j < MAXLOOPS );
      if (j == MAXLOOPS) {
        failure = true; break;
      }
    }
    
    devices.Console.println("failure: " + failure + "\n");
    devices.Console.println("loop count: " + j + "\n");
  }

}
