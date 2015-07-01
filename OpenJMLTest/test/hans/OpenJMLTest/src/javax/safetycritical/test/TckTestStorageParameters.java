package javax.safetycritical.test;

import javax.safetycritical.StorageParameters;
import javax.scj.util.Const;

import org.jmlspecs.utils.JmlAssertionError;

import test.BasicJMLTest;

import unitTest.TestCase;
import unitTest.TestResult;
import unitTest.TestSuite;

public class TckTestStorageParameters extends BasicJMLTest {

	public static void main(String[] args) {
		Const.setDefaultErrorReporter();
		
		TestSuite suite = new TestSuite();
		TestResult result = new TestResult();
		
		int numberOfCases = TestStorageParameters.testCount;
		TestCase test = new TestStorageParameters(result, numberOfCases);

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
		return "java -jar WORKSPACE/OpenJMLTest/lib/openjml.jar -cp ICECAPSDK/bin/ -d ICECAPSDK/bin/ -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ICECAPSDK/src/javax/safetycritical/StorageParameters.java";
	}

}

class TestStorageParameters extends TestCase
{
	static final int testCount = 23;  

  TestStorageParameters(TestResult result,int testCount)
  {
	  super (result, testCount);
  }
  
  public void test (int i) 
  {    
    switch (i) {
        // public StorageParameters(long totalBackingStore, long [] sizes, 
        //   int messageLength, int stackTraceLength,
	    //   long maxMemoryArea, long maxImmortal, long maxMissionMemory) 
	    case  1: 
	        new StorageParameters (1L, new long[] {}, 0, 0, 0, 0, 0);
	        break;        
	    case  2: 
	        new StorageParameters (1L, new long[] {1L}, 0, 0, 0, 0, 0);
	        break;
	    case  3: 
	        new StorageParameters (1L, null,  0, 0, 0, 0, 0);
	        break;
	    case  4: 
	      try { new StorageParameters (0, new long[] {1L}, 0, 0, 0, 0, 0); 
	            assert false; }
	      catch (JmlAssertionError e){}; break;
		case  5: 
	      new StorageParameters (1L, new long[]{ 0, 2L }, 0, 0, 0, 0, 0);
	      break;
		case  6: 
	      try { new StorageParameters (0, new long[] {1L}, 0, 0, 0, 0, 0); 
	            assert false; }
	      catch (JmlAssertionError e){}; break;
	    case  7: 
	      try { new StorageParameters (1L, new long[]{ -2L }, 0, 0, 0, 0, 0); 
	            assert false;}
	      catch (JmlAssertionError e){}; break;
 
	    case  8:
	      try { new StorageParameters (1L, new long[]{ 1L }, -1, 0, 0, 0, 0); 
	            assert false;}
	      catch (JmlAssertionError e){}; break;
	    case  9:
	      try { new StorageParameters (1L, new long[]{ 1L }, 0, -1, 0, 0, 0); 
	            assert false;}
	      catch (JmlAssertionError e){}; break;
	    case  10:
	      new StorageParameters (1L, new long[]{ 1L }, 1, 1, 1L, 1L, 1L);
	      break;
	    case  11: 
	      new StorageParameters (1L, new long[]{ 1L }, 1, 1, StorageParameters.NO_MAX, StorageParameters.NO_MAX, 0);
	      break;
	    case  12: 
	      try { new StorageParameters (1L, new long[]{ 1L }, 1, 1, 0, 0, -1L); 
	            assert false;}
	      catch (JmlAssertionError e){}; break;       
	    case 13: 
	      try { new StorageParameters (1L, new long[]{ 1L }, 1, 1, -2L, 0, 0);
	            assert false;}
	      catch (IllegalArgumentException e){ }; 
	      break;
	    case 14: 
	      try { new StorageParameters (1L, new long[]{ 1L }, 1, 1, 0, -2L, 0); 
	            assert false;}
	      catch (IllegalArgumentException e){}; break;
	    
	      
	    // public StorageParameters(long totalBackingStore, long [] sizes,
	    //   long maxMemoryArea, long maxImmortal, long maxMissionMemory)
	    case  15: 
	      new StorageParameters (1L, null, 0, 0, 0);
	      break;
	    case  16: 
	      try{new StorageParameters (0, null, 0, 0, 0); assert false;}
	      catch (JmlAssertionError e){}; break;
	    case  17: 
	      try{new StorageParameters (1L, new long[]{ -2L }, 0, 0, 0); assert false;}
	      catch (JmlAssertionError e){}; break;
	    case  18: 
	      new StorageParameters (1L, new long[]{ 0, 1L }, 0, 0, 0);
	      break; 
	    case  19:
	      new StorageParameters (1L, new long[]{ 1L }, 1L, 1L, 1L);
	      break;
	    case  20: 
	      new StorageParameters (1L, new long[]{ 1L }, StorageParameters.NO_MAX, StorageParameters.NO_MAX, 0);
	      break;
	    case  21: 
	      try{new StorageParameters (1L, new long[]{ 1L }, 0, 0, -1L); assert false;}
	      catch (JmlAssertionError e){}; break;       
	    case  22: 
	      try{new StorageParameters (1L, new long[]{ 1L }, -2L, 0, 0); assert false;}
	      catch (IllegalArgumentException e){}; break;
	    case  23: 
	      try{new StorageParameters (1L, new long[]{ 1L }, 0, -2L, 0); assert false;}
	      catch (IllegalArgumentException e){}; break;        
	      
	    default: break;
    } 
  }

}
