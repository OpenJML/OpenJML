package javax.safetycritical.test.cyclic;

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
import javax.safetycritical.PriorityScheduler;
import javax.safetycritical.Safelet;
import javax.safetycritical.StorageParameters;
import javax.scj.util.Const;

import test.BasicJMLTest;
import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestCyclicSchedule3 extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestCyclicSchedule3.testCount;
		TestCase test = new TestCyclicSchedule3(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);
		result.print(test.getClass().getName(), numberOfCases);

		if (result.JMLerrorCount() + result.errorCount() == 0) {
			args = null;
		}
	}

	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/safetycritical/Frame.java ICECAPSDK/src/javax/safetycritical/CyclicSchedule.java";
	}
}

class TestCyclicSchedule3 extends TestCase {

	// --- Stub classes ----------------------------------

	static StorageParameters storageParameters_Sequencer = new StorageParameters(
			Const.OUTERMOST_SEQ_BACKING_STORE,
			new long[] { Const.HANDLER_STACK_SIZE }, Const.PRIVATE_MEM,
			Const.IMMORTAL_MEM, Const.MISSION_MEM);

	static StorageParameters storageParameters_Handlers = new StorageParameters(
			Const.PRIVATE_BACKING_STORE,
			new long[] { Const.HANDLER_STACK_SIZE }, Const.PRIVATE_MEM, 0, 0);

	class SafeletStub implements Safelet<CyclicExecutive> {
		
		public MissionSequencer<CyclicExecutive> getSequencer() {
			return new SequencerStub();
		}

		public long immortalMemorySize() {
			return Const.IMMORTAL_MEM;
		}

		public void initializeApplication() {
		}
	}

	class SequencerStub extends MissionSequencer<CyclicExecutive> {

		CyclicExecutive mission;

		SequencerStub() {
			super(new PriorityParameters(PriorityScheduler.instance().getMinPriority() + 1),
					storageParameters_Sequencer);
			mission = new CyclicExecutiveStub();
		}

		public CyclicExecutive getNextMission() {
			if (mission.terminationPending())
				return null;
			else
				return mission;
		}
	}

	class CyclicExecutiveStub extends CyclicExecutive {

		public void initialize() {
			int NOR_PRIORITY = PriorityScheduler.instance().getNormPriority();
			
			new PeriodicEventHandlerStub1(new PriorityParameters(NOR_PRIORITY),
					new PeriodicParameters(new RelativeTime(),
							new RelativeTime(2000, 0)),
					storageParameters_Handlers).register();
			
			new PeriodicEventHandlerStub2(new PriorityParameters(NOR_PRIORITY),
					new PeriodicParameters(new RelativeTime(),
							new RelativeTime(4000, 0)),
					storageParameters_Handlers).register();
		}

		public long missionMemorySize() {
			return Const.MISSION_MEM;
		}

		public CyclicSchedule getSchedule(PeriodicEventHandler[] handlers) {
			
			RelativeTime minorCycle = 
				new RelativeTime(2, 0, Clock.getRealtimeClock());

			Frame[] frames = new Frame[3];
			PeriodicEventHandler[] frame0 = new PeriodicEventHandler[2];
			PeriodicEventHandler[] frame1 = null;
            PeriodicEventHandler[] frame2 = new PeriodicEventHandler[1];
			
            frame0[0] = handlers[0];
            frame0[1] = handlers[1];

            frame2[0] = handlers[0];

			frames[0] = new Frame(minorCycle, frame0);
			frames[1] = null;
			frames[2] = new Frame(minorCycle, frame2);
			System.out.println("CyclicExecutiveStub.getSchedule");
			return new CyclicSchedule(frames);
		}
	}

	class PeriodicEventHandlerStub1 extends PeriodicEventHandler {
		
		public PeriodicEventHandlerStub1(PriorityParameters priotity,
				PeriodicParameters period, StorageParameters storage) {
			super(priotity, period, storage);
		}

		public void handleAsyncEvent() {
			System.out.println("Running1");
		}
	}
	
	class PeriodicEventHandlerStub2 extends PeriodicEventHandler {
		int count = 0;
		
		public PeriodicEventHandlerStub2(PriorityParameters priotity,
				PeriodicParameters period, StorageParameters storage) {
			super(priotity, period, storage);
		}

		public void handleAsyncEvent() {
			System.out.println("Running2");
			count++;
			if (count > 2) 
				Mission.getMission().requestTermination();
		}
	}

	//--- TestCyclicSchedule3 ---------------------------------

	static final int testCount = 1;

	public TestCyclicSchedule3(TestResult result, int testCount) {
		super(result, testCount);
	}

	public void test(int i) {
		
		switch (i) {
		
		  // public CyclicSchedule(Frame[] frames)
		  case 1: // frame array with a null element
                  // new CyclicSchedule (new Frame[] {frame0, null, frame2});
			try {
			  new Launcher(new TestCyclicSchedule3.SafeletStub(), 0);
			  assert false; }
	        catch (IllegalArgumentException e){}; 
			break;
		  default:
			break;
		}
	}
}
