package javax.realtime.test.timeClasses;

import javax.realtime.TestPortal.HighResolutionTimeStub;

public class Main2AbsoluteTime
{

  public static void main (String[] args)
  {
    devices.Console.println("Main2AbsoluteTime begin");
    HighResolutionTimeStub hrs = new HighResolutionTimeStub(Long.MAX_VALUE,0,null);
    assert hrs.getNanoseconds() == 0; 
    
    devices.Console.println("after assert 1");
    
    hrs = new HighResolutionTimeStub(Long.MAX_VALUE,1000001,null);
    
    //long ms = hrs.getMilliseconds();
    int ns = hrs.getNanoseconds();
    
    assert hrs.getNanoseconds() == -999999;  
   
    //devices.Console.println("after assert 2: ms = " + ms);
    devices.Console.println("after assert 2: ns = " + ns);
    
    hrs = new HighResolutionTimeStub(Long.MIN_VALUE,-1000001,null); 
    
    //ms = hrs.getMilliseconds();
    ns = hrs.getNanoseconds();
    
    //assert hrs.getNanoseconds() == 1;     
    
    //devices.Console.println("after assert 3: ms = " + ms);
    devices.Console.println("after assert 3: ns = " + ns);
    
//    AbsoluteTime abs = new AbsoluteTime(1,-1); 
//    
//    devices.Console.println("abs: " + abs);
    
//    int this_nanos = abs.getNanoseconds();
//    int param_nanos = 1000001;
       
    //AbsoluteTime result = abs.add(0,1000001,abs);
//    abs = abs.add(0,1000001,abs);
//    
//    devices.Console.println("abs: " + abs);
    //devices.Console.println("result: " + abs);
    
    //ensures  (\result.getNanoseconds() - this.getNanoseconds() - nanos) % 1000000  == 0;
    
//    int r = (result.getNanoseconds() - this_nanos - param_nanos) % 1000000;
//    
//    devices.Console.println("r: " + r);
    
//    RelativeTime rel = new RelativeTime (-1, -1);
//    devices.Console.println("rel time: " + rel);
    
    
    devices.Console.println("Main end");

  }

}
