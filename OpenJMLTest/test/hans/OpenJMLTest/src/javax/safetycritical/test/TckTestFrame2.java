package javax.safetycritical.test;

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

public class TckTestFrame2 extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();

		int numberOfCases = TestFrame2.testCount;
		TestCase test = new TestFrame2(result, numberOfCases);

		suite.addTest(test);
		suite.run(result);
		result.print(test.getClass().getName(), numberOfCases);
		
		if (result.JMLerrorCount() + result.errorCount() == 0)
		{
			args = null;
		}
	}
	
	@Override
	public String getJMLAnnotationCommand() {
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/safetycritical/Frame.java";
	}
}

class TestFrame2 extends TestCase {
	// --- Stub classes ----------------------------------

	static StorageParameters storageParameters_Sequencer = 
			new StorageParameters(Const.OUTERMOST_SEQ_BACKING_STORE,
			new long[] { Const.HANDLER_STACK_SIZE }, Const.PRIVATE_MEM, 
			Const.IMMORTAL_MEM, Const.MISSION_MEM);

	static StorageParameters storageParameters_Handlers = 
			new StorageParameters(Const.PRIVATE_BACKING_STORE,
			new long[] { Const.HANDLER_STACK_SIZE }, Const.PRIVATE_MEM, 0, 0);

	class SafeletStub implements Safelet<MissionStub> {
		public MissionSequencer<MissionStub> getSequencer() {
			MissionSequencer<MissionStub> seq = new SequencerStub();
			return seq;
		}

		public long immortalMemorySize() {
			return Const.IMMORTAL_MEM;
		}

		public void initializeApplication() {
		}
	}

	class SequencerStub extends MissionSequencer<MissionStub> {
		private MissionStub mission;

		SequencerStub() {
			super(new PriorityParameters(PriorityScheduler.instance().getMinPriority() + 1),
					storageParameters_Sequencer);
			mission = new MissionStub();
		}

		public MissionStub getNextMission() {
			if (mission.terminationPending())
				return null;
			else
				return mission;
		}
	}

	class MissionStub extends CyclicExecutive {
		public void initialize() {
			int NOR_PRIORITY = PriorityScheduler.instance().getNormPriority();

			new PeriodicEvhStub(new PriorityParameters(NOR_PRIORITY), 
					new PeriodicParameters(new RelativeTime(0L, 0), // start  
					    new RelativeTime(2 * 1000, 0)), // period 
					storageParameters_Handlers).register();
		}

		public long missionMemorySize() {
			return Const.MISSION_MEM;
		}

		public CyclicSchedule getSchedule(PeriodicEventHandler[] handlers) {
			System.out.println("  *** MissionStub: getSchedule");
			RelativeTime minorCycle = new RelativeTime(2000, 0, Clock.getRealtimeClock());

			Frame[] frames = new Frame[1];
			PeriodicEventHandler[] frame0 = new PeriodicEventHandler[1];

			frame0[0] = handlers[0];

			frames[0] = new Frame(minorCycle, frame0);
			return new CyclicSchedule(frames);
		}
	}

	class PeriodicEvhStub extends PeriodicEventHandler {
		int count = 0;

		protected PeriodicEvhStub(PriorityParameters priority, PeriodicParameters periodic, StorageParameters storage) {
			super(priority, periodic, storage);
		}

		public void handleAsyncEvent() {
			devices.Console.println("pevh");
			count++;
			if (count > 1)
				Mission.getMission().requestTermination();
		}
	}

	// --- TestFrame2 ---------------------------------

	static final int testCount = 1;

	TestFrame2(TestResult result, int testCount) {
		  super (result, testCount);
	}

	public void test(int i) {
		switch (i) {
		//public Frame(RelativeTime duration, PeriodicEventHandler[] handlers)     
		//  one handler, and it is registered and in mission scope
		case 1:
			System.out.println("\nTestFrame2 case 1 begin");
			new Launcher(new TestFrame2.SafeletStub(), 0);
			System.out.println("TestFrame2 case 1 end \n");

		default:
			break;
		}
	}
}
