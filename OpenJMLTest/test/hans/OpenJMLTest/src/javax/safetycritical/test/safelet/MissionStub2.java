package javax.safetycritical.test.safelet;

import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.Mission;
import javax.safetycritical.PriorityScheduler;
import javax.scj.util.Const;

public class MissionStub2 extends Mission
{
    public int missionNo;
    
    public MissionStub2 (int missionNo)
    {
      this.missionNo = missionNo;
    }
        
    public void initialize()
    {
      int MAX_PRIORITY = PriorityScheduler.instance().getMaxPriority();
      int MIN_PRIORITY = PriorityScheduler.instance().getMinPriority();
      
      int NOR_PRIORITY = (MAX_PRIORITY + MIN_PRIORITY)/2;

      PriorityParameters priority = new PriorityParameters(NOR_PRIORITY);
      
      new PeriodicEvhStub2(
          priority,
          new PeriodicParameters(new RelativeTime (0L, 0),     // start  
                                 new RelativeTime (500, 0)), // period 
          TestSafelet2.storageParameters_Handlers,
          missionNo).register(); 
    }
    
    public long missionMemorySize ()
    {
      return Const.MISSION_MEM;
    }     
    
    public boolean cleanUp()
    {
      System.out.println("\nMissionStub2.cleanUp: ... \n");
      return super.cleanUp();
    }
  
  }