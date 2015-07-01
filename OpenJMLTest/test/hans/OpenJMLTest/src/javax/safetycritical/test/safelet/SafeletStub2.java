package javax.safetycritical.test.safelet;

import javax.safetycritical.MissionSequencer;
import javax.safetycritical.Safelet;
import javax.scj.util.Const;

public class SafeletStub2 implements Safelet<MissionStub2>
  { 
    public MissionSequencer<MissionStub2> getSequencer()
    { 
      MissionSequencer<MissionStub2> seq = new SequencerStub2();      
      return seq;
    }
    
    public long immortalMemorySize()
    {
      return Const.IMMORTAL_MEM;
    }
    
    public void initializeApplication()
    {      
    }
  }  
