/**************************************************************************
 * File name  : TestPriorityCeilingEmulation.java
 * 
 * This file is part a TCK implementation, 
 * based on SCJ Draft, Version 0.94, 25 June 2013.
 *
 * Copyright 2014 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *************************************************************************/
package javax.safetycritical.test.priorityScheduling;

import javax.realtime.AbsoluteTime;
import javax.realtime.AperiodicParameters;
import javax.realtime.Clock;
import javax.realtime.HighResolutionTime;
import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.Launcher;
import javax.safetycritical.Mission;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.OneShotEventHandler;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.PriorityScheduler;
import javax.safetycritical.Safelet;
import javax.safetycritical.Services;
import javax.safetycritical.StorageParameters;
import javax.scj.util.Const;

import unitTest_Remove.TestCase;

/**
 * Test of preemptive scheduling at Level 1.
 * This test is inspired by the example in Section 11.8 of 
 * Burns and Wellings: Real-Time Systems and Programming Languages, 4th edition.
 * Table 11.11 in the book gives an overview of the tasks and 
 * their execution sequences.
 * Figure 11.9 shows the actual execution when ICPP is used.
 * 
 * @author APR and HSO
 */
public class TestPriorityCeilingEmulation extends TestCase
{
  static StorageParameters storageParameters_Sequencer = 
      new StorageParameters(
          Const.OUTERMOST_SEQ_BACKING_STORE,
          new long[] { Const.HANDLER_STACK_SIZE },
          Const.PRIVATE_MEM, 
          Const.IMMORTAL_MEM, 
          Const.MISSION_MEM);
  
  static StorageParameters storageParameters_Handlers = 
      new StorageParameters(
          Const.PRIVATE_BACKING_STORE, 
          new long[] { Const.HANDLER_STACK_SIZE },
          Const.PRIVATE_MEM, 
          0, 
          0);   
  
  /*
   * The time of aStart, dStart, dEnd, cStart, cEnd, bStart, bEnd, aEnd in order
   */
  static final int SIZE = 8;
  static private long[] timeRecord = new long[SIZE];
    
  class SafeletStub implements Safelet<MissionStub>
  { 
    public MissionSequencer<MissionStub> getSequencer()
    {      
      MissionSequencer<MissionStub> seq = new SequencerStub();
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
  
  class SequencerStub extends MissionSequencer<MissionStub> 
  {
    private MissionStub mission;
    
    SequencerStub()
    {
      super (new PriorityParameters (PriorityScheduler.instance().getMinPriority() + 1),
             storageParameters_Sequencer);      
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
        
    public void initialize()
    { 
      Q q = new Q();
      V v = new V();
      
      int MAX_PRIORITY = PriorityScheduler.instance().getMaxPriority();
      int MIN_PRIORITY = PriorityScheduler.instance().getMinPriority();
      
      int NOR_PRIORITY = (MAX_PRIORITY + MIN_PRIORITY)/2;

      PriorityParameters a_Priority = new PriorityParameters(NOR_PRIORITY + 1);
      PriorityParameters b_Priority = new PriorityParameters(NOR_PRIORITY + 2);
      PriorityParameters c_Priority = new PriorityParameters(NOR_PRIORITY + 3);
      PriorityParameters d_Priority = new PriorityParameters(NOR_PRIORITY + 4);
      
      devices.Console.println("Priorities: a: " + a_Priority.getPriority() + 
          "; b: " + b_Priority.getPriority() +  
          "; c: " + c_Priority.getPriority() + 
          "; d: " + d_Priority.getPriority() +"\n");
      
      new a_PEvhStub(
          a_Priority,
          new PeriodicParameters(new RelativeTime ( 0*tickTime, 0),  // start  
                                 new RelativeTime (25*tickTime, 0)), // period 
          storageParameters_Handlers,
          q, "a").register(); 
      
      new b_PEvhStub(
          b_Priority,
          new PeriodicParameters(new RelativeTime ( 2*tickTime, 0),  // start  
                                 new RelativeTime (25*tickTime, 0)), // period 
          storageParameters_Handlers,
          "b").register();
      
      new c_PEvhStub(
          c_Priority,
          new PeriodicParameters(new RelativeTime ( 2*tickTime, 0),  // start  
                                 new RelativeTime (25*tickTime, 0)), // period 
          storageParameters_Handlers,
          v, "c").register(); 
      
      new d_PEvhStub(
          d_Priority,
          new PeriodicParameters(new RelativeTime ( 4*tickTime, 0),  // start  
                                 new RelativeTime (25*tickTime, 0)), // period 
          storageParameters_Handlers,
          q, v, "d").register(); 

      new OneShotEvhStub (new PriorityParameters (MAX_PRIORITY),
          new RelativeTime (20*tickTime, 0), 
          new AperiodicParameters(new RelativeTime (500, 0), null),
          storageParameters_Handlers) .register(); 
      
      Services.setCeiling(q, d_Priority.getPriority()); 
      Services.setCeiling(v, d_Priority.getPriority()); 
    }
    
    public long missionMemorySize ()
    {
      return Const.MISSION_MEM;
    } 
    
    /*@ 
      protected behaviour
        requires true; 
      
        ensures               
          (\forall int i; 0 <= i && i < SIZE-1;
             timeRecord[i] < timeRecord[i + 1]);
    @*/
    protected boolean cleanUp()
    {
      devices.Console.println("\nMissionStub.cleanUp: ... \n");
//      for (int i = 0; i < SIZE-1; i++)
//        if (timeRecord[i] > timeRecord[i + 1])
//          AllTests.result.addError(AllTests.test_PriorityCeilingEmulation, 
//              AllTests.assertionError); 
      return true;
    }
  }
  
  static final long tickTime = 3*100L;
  static final int N = 3*1;
  
  static void tick()
  {
    int n = N*1000000;
    for (int i = 0; i < n; i++)
    {  i = i + 1; i = i - 1; }
  }
  
  static void e_Method()
  {
    tick();
  }
   
  static long getCurrentTimeInNano() 
  {
    AbsoluteTime time = Clock.getRealtimeClock().getTime();
    long nanos = time.getMilliseconds() * 1000000 + time.getNanoseconds();
    if (nanos < 0)
      nanos = Long.MAX_VALUE;

    return nanos;
  }
  
  class Q
  {
    public synchronized void a_Method()
    {
      tick();
      tick();
      tick();
      tick();
    }
    
    public synchronized void d_Method()
    {
      tick();
    }
  }
  
  class V
  {
    public synchronized void c_Method()
    {
      tick();
      tick();
    }
    
    public synchronized void d_Method()
    {
      tick();
    }
  }
  
  class a_PEvhStub extends PeriodicEventHandler
  {
    Q q;
    String name;
    
    protected a_PEvhStub (PriorityParameters priority,
                          PeriodicParameters periodic,
                          StorageParameters storage,
                          Q q,
                          String name) 
    {
      super(priority, periodic, storage);
      this.q = q;
      this.name = name;
    }

    public void handleAsyncEvent() 
    {          
      timeRecord[0] = getCurrentTimeInNano();
      devices.Console.println("0 " + name + ": begin");  
      
      e_Method();
      q.a_Method();
      e_Method();      
            
      devices.Console.println("7 " + name + ": end; \n");
      timeRecord[7] = getCurrentTimeInNano(); 
    }
  }
  
  class b_PEvhStub extends PeriodicEventHandler
  {
    String name;
    
    protected b_PEvhStub (PriorityParameters priority,
                          PeriodicParameters periodic,
                          StorageParameters storage,
                          String name) 
    {
      super(priority, periodic, storage);
      this.name = name;
    }

    public void handleAsyncEvent() 
    {
      timeRecord[5] = getCurrentTimeInNano();  
      devices.Console.println("5 " + name + ": begin");        
      
      e_Method();
      e_Method(); 
        
      devices.Console.println("6 " + name + ": end;");
      timeRecord[6] = getCurrentTimeInNano();    
    }
  }
  
  class c_PEvhStub extends PeriodicEventHandler
  {
    V v;
    String name;
    
    protected c_PEvhStub (PriorityParameters priority,
                          PeriodicParameters periodic,
                          StorageParameters storage,
                          V v,
                          String name) 
    {
      super(priority, periodic, storage);
      this.v = v;
      this.name = name;
    }

    public void handleAsyncEvent() 
    {
      timeRecord[3] = getCurrentTimeInNano();
      devices.Console.println("3 " + name + ": begin");       
          
      e_Method();
      v.c_Method();
      e_Method();      
      
      devices.Console.println("4 " + name + ": end;");
      timeRecord[4] = getCurrentTimeInNano(); 
    }
  }
  
  class d_PEvhStub extends PeriodicEventHandler
  {
    Q q;
    V v;
    String name;
    
    protected d_PEvhStub (PriorityParameters priority,
                          PeriodicParameters periodic,
                          StorageParameters storage,
                          Q q, V v,
                          String name) 
    {
      super(priority, periodic, storage);
      this.q = q; this.v = v;
      this.name = name;
    }

    public void handleAsyncEvent() 
    {
      timeRecord[1] = getCurrentTimeInNano(); 
      devices.Console.println("1 " + name + ": begin");      
          
      e_Method();
      e_Method();
      q.d_Method();
      v.d_Method();
      e_Method();      
       
      devices.Console.println("2 " + name + ": end;");
      timeRecord[2] = getCurrentTimeInNano();
    }
  }
  
  class OneShotEvhStub extends OneShotEventHandler
  {
    public OneShotEvhStub (PriorityParameters priority,
                           HighResolutionTime releaseTime,
                           AperiodicParameters release,
                           StorageParameters storage)
    {
      super (priority, releaseTime, release, storage);      
    }
    
    public void handleAsyncEvent()
    {
      devices.Console.println("PriorityCeiling: OneShotEvhStub.handleAsyncEvent: requestTermination \n");
      Mission.getMission().requestTermination();
    }    
  }
  
  public TestPriorityCeilingEmulation (String name)
  {
    super(name);
  } 
  
  public void test (int i) 
  {
        
    switch (i) { 
      
      case  1: 
        devices.Console.println("\nTestPriorityCeilingEmulation begin");
        new Launcher(new TestPriorityCeilingEmulation.SafeletStub(), 1);
        devices.Console.println("TestPriorityCeilingEmulation end \n");
        break;  
        
      default: break;
    }
  }
  
  public static final int testCount = 1; 
}
