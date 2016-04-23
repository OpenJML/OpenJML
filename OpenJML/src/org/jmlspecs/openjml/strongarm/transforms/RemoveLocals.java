package org.jmlspecs.openjml.strongarm.transforms;

import com.sun.tools.javac.util.Context;

public class RemoveLocals {
    
    public static RemoveLocals instance;
    
    public RemoveLocals(Context context){}
    
    public void cache(Context context){
        if(instance==null){
            instance = new RemoveLocals(context);
        }
    }
    

}
