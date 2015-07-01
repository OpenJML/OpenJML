package javax.safetycritical.test.cyclic;

import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.CyclicExecutive;
import javax.safetycritical.CyclicSchedule;
import javax.safetycritical.Frame;
import javax.safetycritical.PeriodicEventHandler;
import javax.scj.util.Const;
import javax.scj.util.Priorities;

public class CyclicExecutiveStub extends CyclicExecutive
  {
    public void initialize()
    { 
      PeriodicEventHandler pevh2 = new PeriodicEvhStub(
          new PriorityParameters(Priorities.MIN_PRIORITY),
          new PeriodicParameters(new RelativeTime (),         // start  
                                 new RelativeTime (2*TestCyclicExecutive.minorCycle, 0)), // period 
          TestCyclicExecutive.storageParameters_Handlers, 
          2);
      pevh2.register();
      
      PeriodicEventHandler pevh3 = new PeriodicEvhStub(
          new PriorityParameters(Priorities.MIN_PRIORITY),
          new PeriodicParameters(new RelativeTime (),         // start  
                                 new RelativeTime (3*TestCyclicExecutive.minorCycle, 0)), // period 
          TestCyclicExecutive.storageParameters_Handlers, 
          3);
      pevh3.register();
      
      PeriodicEventHandler pevh6 = new PeriodicEvhStub(
          new PriorityParameters(Priorities.MIN_PRIORITY),
          new PeriodicParameters(new RelativeTime (),         // start  
                                 new RelativeTime (6*TestCyclicExecutive.minorCycle, 0)), // period 
          TestCyclicExecutive.storageParameters_Handlers, 
          6);
      pevh6.register();
    }
    
    public long missionMemorySize ()
    {
      return Const.MISSION_MEM;
    }
    
    public CyclicSchedule getSchedule (PeriodicEventHandler[] handlers)
    {
      RelativeTime duration = new RelativeTime (TestCyclicExecutive.minorCycle, 0);
      return generateCyclicSchedule (handlers, duration);
    }
    
    private CyclicSchedule generateCyclicSchedule (
      PeriodicEventHandler[] handlers, RelativeTime duration)
    {
      Frame[] frames = new Frame[6];
      PeriodicEventHandler[] frame0 = new PeriodicEventHandler[2];
      PeriodicEventHandler[] frame1 = new PeriodicEventHandler[1];
      PeriodicEventHandler[] frame2 = new PeriodicEventHandler[1];
      PeriodicEventHandler[] frame3 = new PeriodicEventHandler[0];
      PeriodicEventHandler[] frame4 = new PeriodicEventHandler[2];
      PeriodicEventHandler[] frame5 = new PeriodicEventHandler[0];
      
      frame0[0] = handlers[2];
      frame0[1] = handlers[0];
      
      frame1[0] = handlers[1];
      
      frame2[0] = handlers[0];
      
      frame4[0] = handlers[0];
      frame4[1] = handlers[1];
      
      frames[0] = new Frame (duration, frame0);
      frames[1] = new Frame (duration, frame1);
      frames[2] = new Frame (duration, frame2);
      frames[3] = new Frame (duration, frame3);
      frames[4] = new Frame (duration, frame4);
      frames[5] = new Frame (duration, frame5);
      
      return new CyclicSchedule (frames);
    }
    
    /*@ 
      public behaviour
        requires true; 
      
        // evh6.time < evh2.time < evh3.time < evh2.time < evh2.time < evh3.time
        ensures TestCyclicExecutive.timeRecord[0] < TestCyclicExecutive.timeRecord[1];
                        
//          (\forall int i; 0 < i && i < SIZE-2; timeRecord[i] < timeRecord[i + 1]);
//        // frame 0    
//        ensures (timeRecord[1] - timeRecord[0] <= 1* minorCycleInNanos);
//        // frame 1
//        ensures (timeRecord[3] - timeRecord[0] <= 2* minorCycleInNanos);
//        // frame 2
//        ensures (timeRecord[4] - timeRecord[0] <= 3* minorCycleInNanos);
//        // frame 4
//        ensures (timeRecord[5] - timeRecord[0] <= 5* minorCycleInNanos);
//        ensures (timeRecord[6] - timeRecord[0] <= 5* minorCycleInNanos);
    @*/
    public boolean cleanUp()
    {
      super.cleanUp();
      System.out.println("\nMissionStub.cleanUp: ... \n");
      for (int i = 0; i < 6; i++)
        System.out.println ( "  " + TestCyclicExecutive.timeRecord[i]);
      
//      // starttime < evh6.time < evh2.time < evh3.time < evh2.time < evh2.time < evh3.time
//      for (int i = 0; i < 6; i++) {          
//        if (timeRecord[i] > timeRecord[i + 1])
//          AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
//      }
//      // frame 0
//      if (timeRecord[1] - timeRecord[0] > 1* minorCycleInNanos)
//        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
//      if (timeRecord[2] - timeRecord[0] > 1* minorCycleInNanos)
//        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
//      
//      // frame 1
//      if (timeRecord[3] - timeRecord[0] > 2* minorCycleInNanos)
//        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
//      
//      // frame 2
//      if (timeRecord[4] - timeRecord[0] > 3* minorCycleInNanos)
//        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
//      
//      // frame 4
//      if (timeRecord[5] - timeRecord[0] > 5* minorCycleInNanos)
//        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
//      if (timeRecord[6] - timeRecord[0] > 5* minorCycleInNanos)
//        AllTests.result.addError(AllTests.test_CyclicExecutive, new AssertionError());
      return true;
    }
  }
