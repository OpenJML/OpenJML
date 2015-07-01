package javax.safetycritical.test.cyclic;

import javax.realtime.PriorityParameters;
import javax.safetycritical.MissionSequencer;
import javax.scj.util.Priorities;

public class SequencerStub extends MissionSequencer<CyclicExecutiveStub> 
  {
    private CyclicExecutiveStub mission;
    
    SequencerStub()
    {
      super (new PriorityParameters (Priorities.MIN_PRIORITY + 1), 
    		  TestCyclicExecutive.storageParameters_Sequencer); 
      mission = new CyclicExecutiveStub(); 
    }
    
    public CyclicExecutiveStub getNextMission() 
    {
      if (mission.terminationPending())  
        return null; 
      else
        return mission;
    } 
  }
