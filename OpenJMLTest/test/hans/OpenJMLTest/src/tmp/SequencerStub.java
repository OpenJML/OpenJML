package tmp;

import javax.realtime.PriorityParameters;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.StorageParameters;
import javax.scj.util.Const;
import javax.scj.util.Priorities;

public class SequencerStub extends MissionSequencer<MissionStub> 
{
	static StorageParameters storageParameters_Sequencer = 
		      new StorageParameters(
		          Const.OUTERMOST_SEQ_BACKING_STORE,
		          new long[] { Const.HANDLER_STACK_SIZE },
		          Const.PRIVATE_MEM, 
		          Const.IMMORTAL_MEM, 
		          Const.MISSION_MEM + 22);
	
    private MissionStub mission;
    
    SequencerStub()
    {
      super (new PriorityParameters (Priorities.PR95), storageParameters_Sequencer);      
      mission = new MissionStub(); 
    }
    
    public MissionStub getNextMission() 
    {
      if (mission.terminationPending())  
        return null; 
      else
        return mission; 
    } 
}
