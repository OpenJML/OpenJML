/**************************************************************************
 * File name  : TestPreemptiveScheduling.java
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
import javax.safetycritical.Safelet;
import javax.safetycritical.StorageParameters;
import javax.safetycritical.PriorityScheduler;
import javax.safetycritical.test.safelet.TestSafelet2;

import javax.scj.util.Const;

import unitTest_Remove.TestCase;

/**
 * Test of preemptive scheduling at Level 1.
 * This test is inspired by the Purdue TCK, TestSchedule 405.
 * 
 * Compile this test case with jml4c.
 * Compile the packages javax.realtime and javax.safetycritical with the usual compiler.
 * 
 * @author APR and HSO
 */
public class TestPreemptiveScheduling extends TestCase
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
   * The time of lowStart, highStart, highEnd, medianStart, medianEnd, lowEnd in order
   */
  static final int SIZE = 6;
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
      super (new PriorityParameters (PriorityScheduler.instance().getMinPriority() + 10),
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
    
    /*@ 
    public behaviour 
      requires true; 
    
      ensures               
          (\forall int i; 0 <= i && i < SIZE-1;
             timeRecord[i] < timeRecord[i + 1]);
    @*/
    public void cleanUp() {
      System.out.println("\nSequencerStub.cleanUp: ... ");
    
      for (int i = 0; i < SIZE; i++)  {
        System.out.println("Time " + timeRecord[i]);
      }
      System.out.println();
   
      super.cleanUp();
    }
}
  
  
  class MissionStub extends Mission 
  {   
    public void initialize()
    {  
      int MAX_PRIORITY = PriorityScheduler.instance().getMaxPriority();
      int MIN_PRIORITY = PriorityScheduler.instance().getMinPriority();
      
      int NOR_PRIORITY = (MAX_PRIORITY + MIN_PRIORITY)/2;

      PriorityParameters high = 
        new PriorityParameters((MAX_PRIORITY - NOR_PRIORITY) / 2 + NOR_PRIORITY);
      PriorityParameters median = new PriorityParameters(NOR_PRIORITY);
      PriorityParameters low = 
        new PriorityParameters(NOR_PRIORITY - (NOR_PRIORITY - MIN_PRIORITY) / 2);
      
      new PeriodicEvhStub(
          low,
          new PeriodicParameters(new RelativeTime (0L, 0),     // start  
                                 new RelativeTime (5*1000, 0)), // period 
          storageParameters_Handlers,
          0, 5, "Low").register();  
      
      new PeriodicEvhStub(
          high,
          new PeriodicParameters(new RelativeTime (20L, 0),     // start  
                                 new RelativeTime (5*1000, 0)), // period 
          storageParameters_Handlers,
          1, 2, "High" ).register();
      
      new PeriodicEvhStub(
          median,
          new PeriodicParameters(new RelativeTime (40L, 0),     // start  
                                 new RelativeTime (5*1000, 0)), // period 
          storageParameters_Handlers,
          3, 4, "Median" ).register();
      
      new OneShotEvhStub (new PriorityParameters (MAX_PRIORITY),
          new RelativeTime (3*1000L, 0), 
          new AperiodicParameters(new RelativeTime (100, 0), null),
          storageParameters_Handlers) .register();      
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
      super.cleanUp();
//      devices.Console.println("\nMissionStub.cleanUp: ... \n");
//      for (int i = 0; i < SIZE-1; i++)
//        if (timeRecord[i] > timeRecord[i + 1])
//          AllTests.result.addError(AllTests.test_PreemptiveScheduling, 
//              new AssertionError());
      return true;
    }
  }
  
  class PeriodicEvhStub extends PeriodicEventHandler
  {
    final int N = 3*1;
    
    int index1, index2;
    String name;    
    
    protected PeriodicEvhStub (PriorityParameters priority,
                               PeriodicParameters periodic,
                               StorageParameters storage,
                               int index1, int index2,
                               String name) 
    {
      super(priority, periodic, storage);
      this.index1 = index1; this.index2 = index2;
      this.name = name;
    }

    public void handleAsyncEvent() 
    {
      //devices.Console.println(name + ": begin; " + Clock.getRealtimeClock().getTime());      
      timeRecord[index1] = getCurrentTimeInNano();   
      
      doWork();
      
      timeRecord[index2] = getCurrentTimeInNano();     
      //devices.Console.println(name + ": end; " + Clock.getRealtimeClock().getTime());
    }
    
    private void doWork() 
    {
      int n = N*1000000;
      for (int i = 0; i < n; i++)
      {  i = i + 1; i = i - 1; }
    }
    
    private long getCurrentTimeInNano() 
    {
      AbsoluteTime time = Clock.getRealtimeClock().getTime();
      long nanos = time.getMilliseconds() * 1000000 + time.getNanoseconds();
      if (nanos < 0)
        nanos = Long.MAX_VALUE;

      return nanos;
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
      devices.Console.println("PreemptiveSch: OneShotEvhStub.handleAsyncEvent: requestTermination");
      Mission.getMission().requestTermination();
    }    
  }
  
  public TestPreemptiveScheduling (String name)
  {
    super(name);
  } 
  
  public void test (int i) 
  {
    switch (i) { 
      
      case  1: 
        devices.Console.println("\nTestPreemptiveScheduling begin");
        new Launcher(new TestPreemptiveScheduling.SafeletStub(), 1);
        devices.Console.println("TestPreemptiveScheduling end \n");
        break;
        
      default: break;
    }
  }
  
  public static final int testCount = 1; 
}
