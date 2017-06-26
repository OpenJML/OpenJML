package org.jmlspecs.openjml.strongarm;

import org.jmlspecs.openjml.JmlOption;

import com.sun.tools.javac.util.Context;

public class AnalysisTypes {

    public enum AnalysisType {
        REDUNDANT, 
        UNSAT, 
        TAUTOLOGIES, 
        FRAMES, 
        PURTY, 
        VISIBILITY,
        ALL;
    }
    
    public static boolean enabled(Context context, AnalysisType type){
        
        if(JmlOption.isOption(context, JmlOption.INFER_ANALYSIS_TYPES)==false){
            return true;
        }
        
        String types  = JmlOption.value(context, JmlOption.INFER_ANALYSIS_TYPES);
        
        if(types.equalsIgnoreCase(AnalysisType.ALL.toString())){
            return true;
        }
        
        //otherwise, see if it's in the list.
        if(types.indexOf(',')==-1){
            return types.equalsIgnoreCase(type.toString());
        }
        
        String[] parts = types.split(",");
        
        for(String part : parts){
            if(part.equalsIgnoreCase(type.toString())){
                return true;
            }
        }

        return false;
    }
}
