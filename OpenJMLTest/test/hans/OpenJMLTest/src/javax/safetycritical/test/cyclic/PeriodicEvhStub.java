package javax.safetycritical.test.cyclic;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.safetycritical.Mission;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;

public class PeriodicEvhStub extends PeriodicEventHandler
{
    int number;    
    int count = 0; 
    
    protected PeriodicEvhStub (PriorityParameters priority,
                               PeriodicParameters periodic,
                               StorageParameters storage,
                               int number) 
    {
      super(priority, periodic, storage);
      this.number = number;
    }

    public void handleAsyncEvent() 
    {  
      count++;
      TestCyclicExecutive.timeRecord[TestCyclicExecutive.idx++] = getCurrentTimeInNano();
      
      System.out.println("Periodic pevh" + number);
      
      // testing one cycle only:
      if (number == 6 && count == 2)
        Mission.getMission().requestTermination();
    }
    
    private long getCurrentTimeInNano() 
    {
      AbsoluteTime time = Clock.getRealtimeClock().getTime();
      long nanos = time.getMilliseconds() * 1000000 + time.getNanoseconds();
      if (nanos < 0)
        nanos = Long.MAX_VALUE;
      System.out.println("getCurrentTimeInNano: " + nanos);
      return nanos;
    }
  } 
