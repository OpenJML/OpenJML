package org.jmlspecs.openjml.utils.ui;

public class ASTViewerConfigurationUtil {
    
    public static boolean viewASTEnabled(){
        return System.getProperty("JML:DEBUG_AST", null)!=null;
    }
    
}
