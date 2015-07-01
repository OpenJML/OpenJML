package tmp;

import javax.realtime.MemoryArea;
import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.Launcher;
import javax.safetycritical.Mission;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.Safelet;
import javax.safetycritical.StorageParameters;
import javax.safetycritical.ManagedMemory;
import javax.safetycritical.MissionMemory;
import javax.safetycritical.PrivateMemory;
import javax.safetycritical.TestPortal;
import javax.scj.util.Priorities;
import javax.scj.util.Const;

import org.jmlspecs.utils.JmlAssertionError;

import unitTest_Remove.TestCase;

@SuppressWarnings("unused")
public class TestMemoryArea extends TestCase
{
  static StorageParameters storageParameters_Sequencer = 
      new StorageParameters(
          Const.OUTERMOST_SEQ_BACKING_STORE,
          new long[] { Const.HANDLER_STACK_SIZE },
          Const.PRIVATE_MEM, 
          Const.IMMORTAL_MEM, 
          Const.MISSION_MEM + 22);
  
  static StorageParameters storageParameters_Handlers = 
      new StorageParameters(
          Const.PRIVATE_BACKING_STORE, 
          new long[] { Const.HANDLER_STACK_SIZE },
          Const.PRIVATE_MEM + 33, 
          0, 
          0);
    
  
  class SafeletStub implements Safelet<MissionStub>
  { 
    /*@ 
      public behavior  // specification from Safelet
        requires true;
   
        ensures \result != null;
        ensures (MemoryArea.getMemoryArea(\result) instanceof ManagedMemory.ImmortalMemory);
      
      also  // indicates there are inherited specifications
    
        requires true;     
        ensures MemoryArea.getMemoryArea(\result) instanceof ManagedMemory.ImmortalMemory;      
      @*/
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
  
  class SequencerStub extends MissionSequencer<MissionStub> 
  {
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
  
  class MissionStub extends Mission 
  {
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
    
    /*@ 
      public behaviour
        requires true;     
        ensures MemoryArea.getMemoryArea(\result) instanceof MissionMemory;      
      @*/
    public PeriodicEventHandler createInMissionMem ()
    {
      return new PeriodicEvhStub(
          new PriorityParameters(Priorities.PR98),
          new PeriodicParameters(new RelativeTime (),     // start  
                                 new RelativeTime (50, 0)), // period 
                                 storageParameters_Handlers); 
    }
  }
  
  class PeriodicEvhStub extends PeriodicEventHandler
  {
    protected PeriodicEvhStub (PriorityParameters priority,
                               PeriodicParameters periodic,
                               StorageParameters storage) 
    {
      super(priority, periodic, storage);
    }
    
    
    public void handleAsyncEvent() 
    {
      devices.Console.println("--> PEvh");
      Integer obj = createInPrivateMem();
      
      System.out.println("=> area of " + obj + " is " + MemoryArea.getMemoryArea(obj));
      
      Mission.getMission().requestTermination();
    }
    
    /*@ 
      public behaviour
        requires true;   
        ensures MemoryArea.getMemoryArea(\result) instanceof PrivateMemory;      
      @*/
    public Integer createInPrivateMem ()
    {
      return new Integer (1234);
    }
  } 
 
  
  public TestMemoryArea (String name)
  {
    super(name);
  } 
  
  public void test (int i) 
  {
    ManagedMemory mem = null;
    
    switch (i) { 
      // public static MemoryArea getMemoryArea(Object object)
      case  1:
    	System.out.println("\nTestMemoryArea begin case 1");
        //vm.Memory.startMemoryAreaTracking();
//        try {
          new Launcher(new SafeletStub(), 1);
//        }
//        catch (JmlAssertionError e){
//        };
        //vm.Memory.reportMemoryUsage();
        System.out.println("TestMemoryArea end case 1 \n");	
        break;
        
        // Next three cases: move the test to a subclass, i.e. ManagedMemory
                      
//      // public long memoryConsumed()
//      case  2:
//        TestPortal.ManagedMemory_allocateBackingStore(2*1000);
//        mem = TestPortal.ManagedMemory_allocateImmortalMemory(1000);
//        mem.memoryConsumed();
//        break;
//        
//      // public long memoryRemaining()
//      case  3:
//        TestPortal.ManagedMemory_allocateBackingStore(2*1000);
//        mem = TestPortal.ManagedMemory_allocateImmortalMemory(1000);
//        mem.memoryRemaining();
//        break;
//        
//      // public long size()
//      case  4:
//        TestPortal.ManagedMemory_allocateBackingStore(2*1000);
//        mem = TestPortal.ManagedMemory_allocateImmortalMemory(1000);
//        mem.size();
//        break;
        
      default: break;
    }
  }
  
  public static final int testCount = 1; 
  
}

