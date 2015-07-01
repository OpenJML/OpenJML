package javax.safetycritical.test;

import javax.realtime.MemoryArea;
import javax.realtime.PriorityParameters;
import javax.safetycritical.ManagedMemory;
import javax.safetycritical.Mission;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.Safelet;
import javax.safetycritical.StorageParameters;
import javax.safetycritical.TestPortal;
import javax.scj.util.Const;
import javax.scj.util.Priorities;

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
 *  java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp /home/hso/git/hvm-scj/icecapSDK/bin/ -d /home/hso/git/hvm-scj/icecapSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs /home/hso/git/hvm-scj/icecapSDK/src/javax/safetycritical/Safelet.java
 *
 *  TckTestSafelet1:
 *  
 *  java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp /home/hso/git/hvm-scj/icecapSDK/bin/:./bin/ -d /home/hso/java/SCJ_Workspace/OpenJMLTest/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ./src/javax/safetycritical/test/safelet/TckTestSafelet1.java 
 *
 */


public class TckTestSafelet1 extends BasicJMLTest {
	
	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();
		
		int numberOfCases = TestSafelet1.testCount;
		TestCase test = new TestSafelet1(result, numberOfCases);

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
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/:WORKSPACE/OpenJMLTest/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath WORKSPACE/OpenJMLTest/specs/ WORKSPACE/OpenJMLTest/src/javax/safetycritical/test/TckTestSafelet1.java ";
	}
}


class TestSafelet1 extends TestCase
{ 
	//--- Stub classes ----------------------------------

	class SafeletStub1 implements Safelet<MissionStub1>
	{ 
	  /*@ 
	    also
	      ensures true;
	    @*/
	  public MissionSequencer<MissionStub1> getSequencer()
	  { 
	    // seq in immortal memory
	    MissionSequencer<MissionStub1> seq = new SequencerStub1();
	    
	    devices.Console.println("==> area of " + seq + " is " + MemoryArea.getMemoryArea(seq));
	    
	    return seq;
	  }
	  
	  public long immortalMemorySize()
	  {
	    return Const.IMMORTAL_MEM;
	  }
	  
//    /*@ 
//	    also
//	      ensures true; 
//	    @*/
	  public void initializeApplication()
	  {   
	    Integer a = new Integer(1234);
	  	System.out.println("=> area of " + a + " is " + MemoryArea.getMemoryArea(a));
	  }
	}  

	class SequencerStub1 extends MissionSequencer<MissionStub1> 
	{
	  SequencerStub1()
	  {
	    super (new PriorityParameters (Priorities.PR95), 
	        new StorageParameters(
	          Const.OUTERMOST_SEQ_BACKING_STORE,
	          new long[] { Const.HANDLER_STACK_SIZE },
	          Const.PRIVATE_MEM, 
	          Const.IMMORTAL_MEM, 
	          Const.MISSION_MEM)); 
	  }
	  
	  public MissionStub1 getNextMission() 
	  {
	    return null;
	  } 
	}

	class MissionStub1 extends Mission 
	{
	  public void initialize()
	  { 
	  }
	  
	  public long missionMemorySize ()
	  {
	    return Const.MISSION_MEM;
	  }    
	}

  // --- TestSafelet1 ---------------------------------
	
  static final int testCount = 3; 
  
  public TestSafelet1 (TestResult result,int testCount)
  {
	  super (result, testCount);
  } 
  
  public void test (int i) 
  {
    TestPortal.ManagedMemory_allocateBackingStore(Const.OUTERMOST_SEQ_BACKING_STORE);
    ManagedMemory mem = TestPortal.ManagedMemory_allocateImmortalMemory(Const.IMMORTAL_MEM);
    
    switch (i) { 
      case  1:         
        javax.safetycritical.TestPortal.executeInAreaOf(mem, new Runnable()
          { 
            public void run()
            {
              new SafeletStub1().getSequencer();
            }
          } );        
      case  2: 
        javax.safetycritical.TestPortal.executeInAreaOf(mem, new Runnable()
          { 
            public void run()
            {
              new SafeletStub1().immortalMemorySize();
            }
          } );
        break; 
      case  3:        
        javax.safetycritical.TestPortal.executeInAreaOf(mem, new Runnable()
        { 
          public void run()
          {
            new SafeletStub1().initializeApplication();
          }
        } );
        break;
        
      default: break;
    }
  }
  
}
