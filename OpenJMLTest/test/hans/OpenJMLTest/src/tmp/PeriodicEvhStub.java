package tmp;

import javax.realtime.MemoryArea;
import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.safetycritical.Mission;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;

import javax.safetycritical.PrivateMemory;
import javax.safetycritical.MissionMemory;


public class PeriodicEvhStub extends PeriodicEventHandler {

	protected PeriodicEvhStub (PriorityParameters priority,
            PeriodicParameters periodic,
            StorageParameters storage) 
	{
		super(priority, periodic, storage);
	}
	
	
	public void handleAsyncEvent() 
	{
		System.out.println("--> PEvh");
		Integer obj = createInPrivateMem();
		
		//System.out.println("=> area of " + obj + " is " + MemoryArea.getMemoryArea(obj));
		
		Mission.getMission().requestTermination();
	}
	
//	/*@ 
//	public behaviour
//	requires true;   
//	ensures MemoryArea.getMemoryArea(\result) instanceof PrivateMemory;      
//	@*/
	public Integer createInPrivateMem ()
	{
		//System.out.println("--> PEvh.createInPrivateMem");
		return new Integer (1234);
	}
}
