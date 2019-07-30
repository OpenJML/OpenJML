package org.jmlspecs.openjml.strongarm;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.ext.OptionsInfer;
import org.jmlspecs.openjml.strongarm.AnalysisTypes.AnalysisType;

import com.sun.tools.javac.util.Context;

public class AnalysisTypes {

    public enum AnalysisType {
        REDUNDANT, 
        UNSAT, 
        TAUTOLOGIES, 
        FRAMES, 
        PURITY, 
        VISIBILITY,
        FAR,
        ALL;
    }
    public static Context context;
    
    public static boolean enabled(Context context, AnalysisType type){
    
        AnalysisTypes.context = context;
        
        if(JmlOption.isOption(context, OptionsInfer.INFER_ANALYSIS_TYPES)==false){
            return true;
        }
        
        String types  = JmlOption.value(context, OptionsInfer.INFER_ANALYSIS_TYPES);
        
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

    public static boolean enabled(AnalysisType type) {
        return AnalysisTypes.enabled(context, type);
    }
}
