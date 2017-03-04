package javax.safetycritical.test.safelet;

import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
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


/*
 * OpenJML call:
 * 
 * cd /home/hso/java/SCJ_Workspace/OpenJMLTest
 *
 *  Safelet:
 *  
 * java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp /home/hso/git/hvm-scj/icecapSDK/bin/ -d /home/hso/git/hvm-scj/icecapSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs /home/hso/git/hvm-scj/icecapSDK/src/javax/safetycritical/Safelet.java
 *
 *  TckTestSafelet2:
 *  
 *  java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp ./bin/:/home/hso/git/hvm-scj/icecapSDK/bin/ -d /home/hso/java/SCJ_Workspace/OpenJMLTest/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ./src/javax/safetycritical/test/safelet/TckTestSafelet2.java
 *
 *
 *  SafeletStub2 and SequencerStub2:
 *   
 *  java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp ./bin/:/home/hso/git/hvm-scj/icecapSDK/bin/ -d /home/hso/java/SCJ_Workspace/OpenJMLTest/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ./src/javax/safetycritical/test/safelet/SafeletStub2.java 
 * 
 *  java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp ./bin/:/home/hso/git/hvm-scj/icecapSDK/bin/ -d /home/hso/java/SCJ_Workspace/OpenJMLTest/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ./src/javax/safetycritical/test/safelet/SequencerStub2.java 
 *
 */

public class TckTestSafelet2 extends BasicJMLTest {
	
	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();
		
		int numberOfCases = TestSafelet2.testCount;
		TestCase test = new TestSafelet2(result, numberOfCases);

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
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/safetycritical/Safelet.java WORKSPACE/OpenJMLTest/src/javax/safetycritical/test/TckTestSafelet2.java";
	}
}

////--- Stub classes ----------------------------------
//
//	class SafeletStub2 implements Safelet<MissionStub2>
//	{ 
//		/*@ 
//	      also
//	        requires true;
//	        ensures true; 
//	      @*/
//	    public MissionSequencer<MissionStub2> getSequencer()
//	    { 
//	      MissionSequencer<MissionStub2> seq = new SequencerStub2();      
//	      return seq;
//	    }
//	    
//	    public long immortalMemorySize()
//	    {
//	      return Const.IMMORTAL_MEM;
//	    }
//	    
//	    public void initializeApplication()
//	    {      
//	    }
//	}
//	
//	class SequencerStub2 extends MissionSequencer<MissionStub2> {
//		public static MissionStub2[] missions;  
//	    private int active = 2;    
//	    private MissionStub2 miss;
//	    private int activation = 0;
//	    
//	    SequencerStub2()
//	    {
//	      super (new PriorityParameters (
//	               PriorityScheduler.instance().getMinPriority()+1), 
//	               TestSafelet2.storageParameters_Sequencer); 
//	      missions = new MissionStub2[3];
//	      missions[0] = new MissionStub2 (0);
//	      missions[1] = new MissionStub2 (1);
//	      missions[2] = new MissionStub2 (2);
//	      
//	      miss = missions[0];
//	    }
//	    
//	    public MissionStub2 getNextMission() 
//	    {      
//	      if (missions[active].terminationPending() && activation > TestSafelet2.SIZE)
//	      {
//	        return null;
//	      }
//	      else
//	      {
//	        active = (active + 1) % missions.length;
//	        miss = missions[active]; 
//	        TestSafelet2.activationOrder[activation] = miss;
//	        
//	        System.out.println("SeqStub2.getNextMission: " + active + "; activation: " + activation);
//	        
//	        activation++;
//	        return miss;
//	      }
//	    }
//	    
//	    /*@ 
//	      public behaviour 
//	        requires true; 
//	      
//	        ensures               
//	          (\forall int i; 0 <= i && i < TestSafelet2.SIZE;
//	             TestSafelet2.activationOrder[i].missionNo == i % SequencerStub2.missions.length);
//	      @*/
//	    public void cleanUp() {    	
//	      System.out.println("\nSequencerStub2.cleanUp: ... ");
//	      
//		  for (int i = 0; i < TestSafelet2.SIZE; i++)  {
//	         System.out.println("Mission " + TestSafelet2.activationOrder[i].missionNo);
//	 	   }
//		   System.out.println();
//		   
//		   
//	    }
//	  }
//	
//	class MissionStub2 extends Mission
//	{
//	    public int missionNo;
//	    
//	    public MissionStub2 (int missionNo)
//	    {
//	      this.missionNo = missionNo;
//	    }
//	        
//	    public void initialize()
//	    {
//	      int MAX_PRIORITY = PriorityScheduler.instance().getMaxPriority();
//	      int MIN_PRIORITY = PriorityScheduler.instance().getMinPriority();
//	      
//	      int NOR_PRIORITY = (MAX_PRIORITY + MIN_PRIORITY)/2;
//
//	      PriorityParameters priority = new PriorityParameters(NOR_PRIORITY);
//	      
//	      new PeriodicEvhStub2(
//	          priority,
//	          new PeriodicParameters(new RelativeTime (0L, 0),     // start  
//	                                 new RelativeTime (500, 0)), // period 
//	          TestSafelet2.storageParameters_Handlers,
//	          missionNo).register(); 
//	    }
//	    
//	    public long missionMemorySize ()
//	    {
//	      return Const.MISSION_MEM;
//	    }     
//	    
//	    public boolean cleanUp()
//	    {
//	      System.out.println("\nMissionStub2.cleanUp: ... \n");
//	      return super.cleanUp();
//	    }
//	  
//	  }
//	
//	class PeriodicEvhStub2 extends PeriodicEventHandler
//	  {
//	    int number;
//	    int count = 0;    
//	    
//	    protected PeriodicEvhStub2 (PriorityParameters priority,
//	                               PeriodicParameters periodic,
//	                               StorageParameters storage,
//	                               int number) 
//	    {
//	      super(priority, periodic, storage);
//	      this.number = number;
//	    }
//
//	    public void handleAsyncEvent() 
//	    {
//	      devices.Console.println("pevh" + number);
//	      count++;
//	      if (count == 2)
//	        Mission.getMission().requestTermination();
//	    }
//	  }
//	

class TestSafelet2 extends TestCase
{ 
	//--- Stub classes ----------------------------------

		class SafeletStub2 implements Safelet<MissionStub2>
		{ 
			/*@ 
		      also
		        requires true;
		        ensures true; 
		      @*/
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
		
		class SequencerStub2 extends MissionSequencer<MissionStub2> {
			public /*static*/ MissionStub2[] missions;  
		    private int active = 2;    
		    private MissionStub2 miss;
		    private int activation = 0;
		    
		    SequencerStub2()
		    {
		      super (new PriorityParameters (
		               PriorityScheduler.instance().getMinPriority()+1), 
		               TestSafelet2.storageParameters_Sequencer); 
		      missions = new MissionStub2[3];
		      missions[0] = new MissionStub2 (0);
		      missions[1] = new MissionStub2 (1);
		      missions[2] = new MissionStub2 (2);
		      
		      miss = missions[0];
		    }
		    
		    public MissionStub2 getNextMission() 
		    {      
		      if (missions[active].terminationPending() && activation > TestSafelet2.SIZE)
		      {
		        return null;
		      }
		      else
		      {
		        active = (active + 1) % missions.length;
		        miss = missions[active]; 
		        TestSafelet2.activationOrder[activation] = miss;
		        
		        System.out.println("SeqStub2.getNextMission: " + active + "; activation: " + activation);
		        
		        activation++;
		        return miss;
		      }
		    }
		    
		    /*@ 
		      also
		        requires true; 
		      
//		        ensures               
//		          (\forall int i; 0 <= i && i < TestSafelet2.SIZE;
//		             TestSafelet2.activationOrder[i].missionNo == i % missions.length);
		      @*/
		    public void cleanUp() {    	
		      System.out.println("\nSequencerStub2.cleanUp: ... ");
		      
			  for (int i = 0; i < TestSafelet2.SIZE; i++)  {
		         System.out.println("Mission " + TestSafelet2.activationOrder[i].missionNo);
		 	   }
			   System.out.println();			   
		    }
		  }
		
		class MissionStub2 extends Mission
		{
		    public int missionNo;
		    
		    public MissionStub2 (int missionNo)
		    {
		      this.missionNo = missionNo;
		    }
		        
		    public void initialize()
		    {
		      int MAX_PRIORITY = PriorityScheduler.instance().getMaxPriority();
		      int MIN_PRIORITY = PriorityScheduler.instance().getMinPriority();
		      
		      int NOR_PRIORITY = (MAX_PRIORITY + MIN_PRIORITY)/2;

		      PriorityParameters priority = new PriorityParameters(NOR_PRIORITY);
		      
		      new PeriodicEvhStub2(
		          priority,
		          new PeriodicParameters(new RelativeTime (0L, 0),     // start  
		                                 new RelativeTime (500, 0)), // period 
		          TestSafelet2.storageParameters_Handlers,
		          missionNo).register(); 
		    }
		    
		    public long missionMemorySize ()
		    {
		      return Const.MISSION_MEM;
		    }     
		    
		    public boolean cleanUp()
		    {
		      System.out.println("\nMissionStub2.cleanUp: ... \n");
		      return super.cleanUp();
		    }
		  
		  }
		
		class PeriodicEvhStub2 extends PeriodicEventHandler
		  {
		    int number;
		    int count = 0;    
		    
		    protected PeriodicEvhStub2 (PriorityParameters priority,
		                               PeriodicParameters periodic,
		                               StorageParameters storage,
		                               int number) 
		    {
		      super(priority, periodic, storage);
		      this.number = number;
		    }

		    public void handleAsyncEvent() 
		    {
		      devices.Console.println("pevh" + number);
		      count++;
		      if (count == 2)
		        Mission.getMission().requestTermination();
		    }
		  }
		

	// --- TestSafelet2 ---------------------------------
	
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
	  
	  // Activation of missions should be: 0,1,2,0,1,2
	  public static final int SIZE = 6;
	  public static MissionStub2[] activationOrder = new MissionStub2[SIZE+1];
		  
	  static final int testCount = 1; 
	  
	  public TestSafelet2 (TestResult result,int testCount)
	  {
          //super (result, testCount);
          super ();
	  } 
		  
	  public void test (int i) 
	  {
	    switch (i) { 
	      
	      case  1: 
	        devices.Console.println("\nTestSafelet2: serialization of missions begin");
	        new Launcher(new SafeletStub2(), 1);
	        devices.Console.println("TestSafelet2: serialization of missions end \n");
	        break;         
	        
	      default: break;
	    }
	  }
}