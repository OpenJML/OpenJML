package org.jmlspecs.openjml.strongarm.gui;

public class BasicBlockExecutionDebuggerConfigurationUtil {
    
    public static boolean debugBasicBlockExecution(){
        return System.getProperty("STRONGARM:DEBUG_BBE", null)!=null;
    }
    

}
