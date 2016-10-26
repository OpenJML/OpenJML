package org.jmlspecs.openjml.strongarm;

public class Timing {

    private long ts1;
    private long ts2;
    
    public Timing(){
        ts1 = System.currentTimeMillis();
    }
    
    public static Timing start(){
        return new Timing();
    }
    
    public long stop(){
        ts2 = System.currentTimeMillis();
        
        return ts2 - ts1;
    }
    
    public String tell(){
        if(ts2==0){
            stop();
        }
        
        String timing = String.format(" (%d ms)", (ts2 - ts1));

        return timing;
    }
}
