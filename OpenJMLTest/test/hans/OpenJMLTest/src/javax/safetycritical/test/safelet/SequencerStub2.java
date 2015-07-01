package javax.safetycritical.test.safelet;

import javax.realtime.PriorityParameters;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.PriorityScheduler;

public class SequencerStub2 extends MissionSequencer<MissionStub2> {
	public static MissionStub2[] missions;  
    private int active = 2;    
    private MissionStub2 miss;
    private int activation = 0;
    
    SequencerStub2()
    {
      super (new PriorityParameters (
               PriorityScheduler.instance().getMinPriority()+1), 
               TestSafelet2.storageParameters_Sequencer); 
      missions = new MissionStub2[3];
      missions[0] = new MissionStub2 (0);
      missions[1] = new MissionStub2 (1);
      missions[2] = new MissionStub2 (2);
      
      miss = missions[0];
    }
    
    public MissionStub2 getNextMission() 
    {      
      if (missions[active].terminationPending() && activation > TestSafelet2.SIZE)
      {
        return null;
      }
      else
      {
        active = (active + 1) % missions.length;
        miss = missions[active]; 
        TestSafelet2.activationOrder[activation] = miss;
        
        System.out.println("SeqStub2.getNextMission: " + active + "; activation: " + activation);
        
        activation++;
        return miss;
      }
    }
    
    /*@ 
      public behaviour 
        requires true; 
      
        ensures               
          (\forall int i; 0 <= i && i < TestSafelet2.SIZE;
             TestSafelet2.activationOrder[i].missionNo == i % SequencerStub2.missions.length);
      @*/
    public void cleanUp() {    	
      System.out.println("\nSequencerStub2.cleanUp: ... ");
      
	  for (int i = 0; i < TestSafelet2.SIZE; i++)  {
         System.out.println("Mission " + TestSafelet2.activationOrder[i].missionNo);
 	   }
	   System.out.println();
	   
	   
    }
  }