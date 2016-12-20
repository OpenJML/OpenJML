package org.jmlspecs.openjml.strongarm;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

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
    public void tellFile(String caseName, String file){
        
        String t = tell();
        
        try {
            PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(file, true)));
            out.println(String.format("%s,%d",caseName, ts2 - ts1));
            out.close();
        } catch (IOException e) {
        }
        
    }
    public String tell(){
        if(ts2==0){
            stop();
        }
        
        String timing = String.format(" (%d ms)", (ts2 - ts1));

        return timing;
    }
}
