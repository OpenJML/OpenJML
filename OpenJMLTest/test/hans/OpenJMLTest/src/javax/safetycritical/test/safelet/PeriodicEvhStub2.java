package javax.safetycritical.test.safelet;

import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.safetycritical.Mission;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;

public class PeriodicEvhStub2 extends PeriodicEventHandler
  {
    int number;
    int count = 0;    
    
    protected PeriodicEvhStub2 (PriorityParameters priority,
                               PeriodicParameters periodic,
                               StorageParameters storage,
                               int number) 
    {
      super(priority, periodic, storage);
      this.number = number;
    }

    public void handleAsyncEvent() 
    {
      devices.Console.println("pevh" + number);
      count++;
      if (count == 2)
        Mission.getMission().requestTermination();
    }
  }
