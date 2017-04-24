package org.jmlspecs.openjml.strongarm.gui;

import org.jmlspecs.openjml.strongarm.Strongarm;

public class BasicBlockExecutionDebuggerConfigurationUtil {
    
    public static boolean debugBasicBlockExecution(){
        return System.getProperty("STRONGARM:DEBUG_BBE", null)!=null || Strongarm._DEV_MODE;
    }
    

}
