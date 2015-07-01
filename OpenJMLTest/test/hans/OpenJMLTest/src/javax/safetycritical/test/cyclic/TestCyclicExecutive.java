/**************************************************************************
 * File name  : TestCyclicExecutive.java
 * 
 * This file is part a TCK implementation, 
 * based on SCJ Draft, Version 0.94, 25 June 2013.
 *
 * Copyright 2014 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *************************************************************************/
package javax.safetycritical.test.cyclic;


import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.CyclicExecutive;
import javax.safetycritical.CyclicSchedule;
import javax.safetycritical.Frame;
import javax.safetycritical.Launcher;
import javax.safetycritical.Mission;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.Safelet;
import javax.safetycritical.StorageParameters;

import javax.scj.util.Const;
import javax.scj.util.Priorities;

import unitTest_Remove.TestCase;

/*
 * Commands of
 *   CyclicExecutive.java:
 * 
 * java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp /home/hso/git/hvm-scj/icecapSDK/bin/ -d /home/hso/git/hvm-scj/icecapSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs /home/hso/git/hvm-scj/icecapSDK/src/javax/safetycritical/CyclicExecutive.java
 *
 *   CyclicExecutiveStub.java:
 *
 * java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp /home/hso/git/hvm-scj/icecapSDK/bin/:./bin/ -d /home/hso/git/hvm-scj/icecapSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs /home/hso/java/SCJ_Workspace/OpenJMLTest/src/javax/safetycritical/test/cyclic/CyclicExecutiveStub.java

 */
/**
 * Test of cyclic executive scheduling at Level 0.
 * 
 * Six frames. Three periodic event handlers with the periods:
 * pevh2: 2*minorCycle, pevh3: 3*minorCycle, pevh6: 6*minorCycle.
 * 
 * frames[0] has pevh6 and pevh2
 * frames[1] has pevh3
 * frames[2] has pevh2
 * frames[3] is empty
 * frames[4] has pevh2 and pevh3
 * frames[5] is empty.
 * 
 * @author APR and HSO
 */
public class TestCyclicExecutive extends TestCase
{
  public static StorageParameters storageParameters_Sequencer = 
      new StorageParameters(
          Const.OUTERMOST_SEQ_BACKING_STORE,
          new long[] { Const.HANDLER_STACK_SIZE },
          Const.PRIVATE_MEM, 
          Const.IMMORTAL_MEM, 
          Const.MISSION_MEM);
  
  public static StorageParameters storageParameters_Handlers = 
      new StorageParameters(
          Const.PRIVATE_BACKING_STORE, 
          new long[] { Const.HANDLER_STACK_SIZE },
          Const.PRIVATE_MEM, 
          0, 
          0);
  
  public static long minorCycle = 1000L;  // in msecs
  public static long minorCycleInNanos = 1000L * 1000000; 
  
  public static final int SIZE = 6;
  public static long[] timeRecord = new long[SIZE+2];
  static int idx = 0;
  
//  class SafeletStub implements Safelet<CyclicExecutiveStub>
//  { 
//    public MissionSequencer<CyclicExecutiveStub> getSequencer()
//    {       
//      return new SequencerStub();
//    }
//    
//    public long immortalMemorySize()
//    {
//      return Const.IMMORTAL_MEM;
//    }
//    
//    public void initializeApplication()
//    {      
//    }
//  }  
  
//  class SequencerStub extends MissionSequencer<CyclicExecutiveStub> 
//  {
//    private CyclicExecutiveStub mission;
//    
//    SequencerStub()
//    {
//      super (new PriorityParameters (Priorities.MIN_PRIORITY + 1), 
//          storageParameters_Sequencer); 
//      mission = new CyclicExecutiveStub(); 
//    }
//    
//    public CyclicExecutiveStub getNextMission() 
//    {
//      if (mission.terminationPending())  
//        return null; 
//      else
//        return mission;
//    } 
//  }
  
//  class CyclicExecutiveStub extends CyclicExecutive
//  {
//    public void initialize()
//    { 
//      PeriodicEventHandler pevh2 = new PeriodicEvhStub(
//          new PriorityParameters(Priorities.MIN_PRIORITY),
//          new PeriodicParameters(new RelativeTime (),         // start  
//                                 new RelativeTime (2*minorCycle, 0)), // period 
//          storageParameters_Handlers, 
//          2);
//      pevh2.register();
//      
//      PeriodicEventHandler pevh3 = new PeriodicEvhStub(
//          new PriorityParameters(Priorities.MIN_PRIORITY),
//          new PeriodicParameters(new RelativeTime (),         // start  
//                                 new RelativeTime (3*minorCycle, 0)), // period 
//          storageParameters_Handlers, 
//          3);
//      pevh3.register();
//      
//      PeriodicEventHandler pevh6 = new PeriodicEvhStub(
//          new PriorityParameters(Priorities.MIN_PRIORITY),
//          new PeriodicParameters(new RelativeTime (),         // start  
//                                 new RelativeTime (6*minorCycle, 0)), // period 
//          storageParameters_Handlers, 
//          6);
//      pevh6.register();
//    }
//    
//    public long missionMemorySize ()
//    {
//      return Const.MISSION_MEM;
//    }
//    
//    public CyclicSchedule getSchedule (PeriodicEventHandler[] handlers)
//    {
//      RelativeTime duration = new RelativeTime (minorCycle, 0);
//      return generateCyclicSchedule (handlers, duration);
//    }
//    
//    private CyclicSchedule generateCyclicSchedule (
//      PeriodicEventHandler[] handlers, RelativeTime duration)
//    {
//      Frame[] frames = new Frame[6];
//      PeriodicEventHandler[] frame0 = new PeriodicEventHandler[2];
//      PeriodicEventHandler[] frame1 = new PeriodicEventHandler[1];
//      PeriodicEventHandler[] frame2 = new PeriodicEventHandler[1];
//      PeriodicEventHandler[] frame3 = new PeriodicEventHandler[0];
//      PeriodicEventHandler[] frame4 = new PeriodicEventHandler[2];
//      PeriodicEventHandler[] frame5 = new PeriodicEventHandler[0];
//      
//      frame0[0] = handlers[2];
//      frame0[1] = handlers[0];
//      
//      frame1[0] = handlers[1];
//      
//      frame2[0] = handlers[0];
//      
//      frame4[0] = handlers[0];
//      frame4[1] = handlers[1];
//      
//      frames[0] = new Frame (duration, frame0);
//      frames[1] = new Frame (duration, frame1);
//      frames[2] = new Frame (duration, frame2);
//      frames[3] = new Frame (duration, frame3);
//      frames[4] = new Frame (duration, frame4);
//      frames[5] = new Frame (duration, frame5);
//      
//      return new CyclicSchedule (frames);
//    }
//    
//    /*@ 
//      protected behaviour
//        requires true; 
//      
//        // evh6.time < evh2.time < evh3.time < evh2.time < evh2.time < evh3.time
//        ensures timeRecord[0] < timeRecord[1];
//                        
////          (\forall int i; 0 < i && i < SIZE-2; timeRecord[i] < timeRecord[i + 1]);
////        // frame 0    
////        ensures (timeRecord[1] - timeRecord[0] <= 1* minorCycleInNanos);
////        // frame 1
////        ensures (timeRecord[3] - timeRecord[0] <= 2* minorCycleInNanos);
////        // frame 2
////        ensures (timeRecord[4] - timeRecord[0] <= 3* minorCycleInNanos);
////        // frame 4
////        ensures (timeRecord[5] - timeRecord[0] <= 5* minorCycleInNanos);
////        ensures (timeRecord[6] - timeRecord[0] <= 5* minorCycleInNanos);
//    @*/
//    protected boolean cleanUp()
//    {
//      super.cleanUp();
//      System.out.println("\nMissionStub.cleanUp: ... \n");
//      for (int i = 0; i < 6; i++)
//        System.out.println ( "  " + timeRecord[i]);
//      
////      // starttime < evh6.time < evh2.time < evh3.time < evh2.time < evh2.time < evh3.time
////      for (int i = 0; i < 6; i++) {          
////        if (timeRecord[i] > timeRecord[i + 1])
////          AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
////      }
////      // frame 0
////      if (timeRecord[1] - timeRecord[0] > 1* minorCycleInNanos)
////        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
////      if (timeRecord[2] - timeRecord[0] > 1* minorCycleInNanos)
////        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
////      
////      // frame 1
////      if (timeRecord[3] - timeRecord[0] > 2* minorCycleInNanos)
////        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
////      
////      // frame 2
////      if (timeRecord[4] - timeRecord[0] > 3* minorCycleInNanos)
////        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
////      
////      // frame 4
////      if (timeRecord[5] - timeRecord[0] > 5* minorCycleInNanos)
////        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
////      if (timeRecord[6] - timeRecord[0] > 5* minorCycleInNanos)
////        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
//      return true;
//    }
//  }
  
//  class PeriodicEvhStub extends PeriodicEventHandler
//  {
//    int number;    
//    int count = 0; 
//    
//    protected PeriodicEvhStub (PriorityParameters priority,
//                               PeriodicParameters periodic,
//                               StorageParameters storage,
//                               int number) 
//    {
//      super(priority, periodic, storage);
//      this.number = number;
//    }
//
//    public void handleAsyncEvent() 
//    {  
//      count++;
//      timeRecord[idx++] = getCurrentTimeInNano();
//      
//      System.out.println("Periodic pevh" + number);
//      
//      // testing one cycle only:
//      if (number == 6 && count == 2)
//        Mission.getMission().requestTermination();
//    }
//    
//    private long getCurrentTimeInNano() 
//    {
//      AbsoluteTime time = Clock.getRealtimeClock().getTime();
//      long nanos = time.getMilliseconds() * 1000000 + time.getNanoseconds();
//      if (nanos < 0)
//        nanos = Long.MAX_VALUE;
//      System.out.println("getCurrentTimeInNano: " + nanos);
//      return nanos;
//    }
//  } 
  
  public TestCyclicExecutive (String name)
  {
    super(name);
  } 
  
  public void test (int i) 
  {
        
    switch (i) { 
      
      case  1: 
    	System.out.println("\nTestCyclicExecutive begin");
        //new Launcher(new TestCyclicExecutive.SafeletStub(), 0);
        new Launcher(new SafeletStub(), 0);
        System.out.println("TestCyclicExecutive end \n");     
        break; 
        
      default: break;
    }
  }
  
  public static final int testCount = 1; 
}
