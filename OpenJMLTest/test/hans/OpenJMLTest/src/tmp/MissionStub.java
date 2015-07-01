package tmp;

import javax.realtime.MemoryArea;
import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.Mission;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;
import javax.scj.util.Const;
import javax.scj.util.Priorities;

import javax.safetycritical.MissionMemory;

public class MissionStub extends Mission {

	StorageParameters storageParameters_Handlers = 
		      new StorageParameters(
		          Const.PRIVATE_BACKING_STORE, 
		          new long[] { Const.HANDLER_STACK_SIZE },
		          Const.PRIVATE_MEM + 33, 
		          0, 
		          0);
	
	protected void initialize()
    {  
      PeriodicEventHandler pevh = createInMissionMem ();
      pevh.register();
      
      System.out.println("=> area of " + pevh + " is \n" + MemoryArea.getMemoryArea(pevh));
    }
    
    public long missionMemorySize ()
    {
      return Const.MISSION_MEM + 22;
    } 
    
//    /*@ 
//      public behaviour
//        requires true;     
//        ensures MemoryArea.getMemoryArea(\result) instanceof MissionMemory;      
//      @*/
    public PeriodicEventHandler createInMissionMem ()
    {
      return new PeriodicEvhStub(
          new PriorityParameters(Priorities.PR98),
          new PeriodicParameters(new RelativeTime (),     // start  
                                 new RelativeTime (50, 0)), // period 
                                 storageParameters_Handlers); 
    }

}
