package tmp;

import javax.realtime.MemoryArea;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.Safelet;
import javax.scj.util.Const;

import javax.safetycritical.ManagedMemory;

// java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp /home/hso/git/hvm-scj/icecapSDK/bin/:/home/hso/java/SCJ_Workspace/OpenJMLTest/bin -d /home/hso/java/SCJ_Workspace/OpenJMLTest/bin -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs /home/hso/java/SCJ_Workspace/OpenJMLTest/src/javax/realtime/test/memoryArea/*.java 

public class SafeletStub implements Safelet<MissionStub>
{ 
//    /*@ 
//      public behavior  // specification from Safelet
//        requires true;
//   
//        ensures \result != null;
//        ensures (MemoryArea.getMemoryArea(\result) instanceof ManagedMemory.ImmortalMemory);
//      
//      also  // indicates there are inherited specifications
//    
//        requires true;     
//        ensures MemoryArea.getMemoryArea(\result) instanceof ManagedMemory.ImmortalMemory;      
//      @*/
    public MissionSequencer<MissionStub> getSequencer()
    {    
      MissionSequencer<MissionStub> seq = new SequencerStub();
      
      System.out.println("=> area of " + seq + " is " + MemoryArea.getMemoryArea(seq));
      
      return seq;
    }
    
    public long immortalMemorySize()
    {
      return Const.IMMORTAL_MEM;
    }
    
    public void initializeApplication()  {
    }
}  