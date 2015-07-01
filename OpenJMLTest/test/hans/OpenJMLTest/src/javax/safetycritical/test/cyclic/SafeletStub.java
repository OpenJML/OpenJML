package javax.safetycritical.test.cyclic;

import javax.safetycritical.MissionSequencer;
import javax.safetycritical.Safelet;
import javax.scj.util.Const;

public class SafeletStub implements Safelet<CyclicExecutiveStub>
  { 
    public MissionSequencer<CyclicExecutiveStub> getSequencer()
    {       
      return new SequencerStub();
    }
    
    public long immortalMemorySize()
    {
      return Const.IMMORTAL_MEM;
    }
    
    public void initializeApplication()
    {      
    }
  }  
