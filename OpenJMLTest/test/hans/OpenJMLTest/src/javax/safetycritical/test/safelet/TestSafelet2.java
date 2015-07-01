/**************************************************************************
 * File name  : TestSafelet2.java
 * 
 * This file is part a TCK implementation, 
 * based on SCJ Draft, Version 0.94, 25 June 2013.
 *
 * Copyright 2014 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *************************************************************************/
package javax.safetycritical.test.safelet;

import javax.safetycritical.Launcher;
import javax.safetycritical.StorageParameters;
import javax.scj.util.Const;

import unitTest_Remove.TestCase;

/**
 * Test of serialization of missions at Level 1.
 * 
 * @author APR and HSO
 */
/*
 * OpenJML call:
 * 
 * cd /home/hso/java/SCJ_Workspace/OpenJMLTest
 *
 *  Safelet:
 *  
 * java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp /home/hso/git/hvm-scj/icecapSDK/bin/ -d /home/hso/git/hvm-scj/icecapSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs /home/hso/git/hvm-scj/icecapSDK/src/javax/safetycritical/Safelet.java
 *
 *  SafeletStub1:
 *  
 *  java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp /home/hso/git/hvm-scj/icecapSDK/bin/:./bin/ -d /home/hso/java/SCJ_Workspace/OpenJMLTest/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented /home/hso/java/SCJ_Workspace/OpenJMLTest/src/javax/safetycritical/test/safelet/SequencerStub2.java 
 * 
 */

public class TestSafelet2 extends TestCase
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
  
  // Activation of missions should be: 0,1,2,0,1,2
  public static final int SIZE = 6;
  public static MissionStub2[] activationOrder = new MissionStub2[SIZE+1];
  
  public TestSafelet2 (String name)
  {
    super(name);
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
  
  public static final int testCount = 1; 
}
