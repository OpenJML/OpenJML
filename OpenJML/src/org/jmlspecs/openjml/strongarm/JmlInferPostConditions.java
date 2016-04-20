package org.jmlspecs.openjml.strongarm;

import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.MethodProverBoogie;
import org.jmlspecs.openjml.esc.MethodProverSMT;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverResult;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Context.Key;

public class JmlInferPostConditions extends JmlInfer<JmlInferPostConditions> {

    protected static final Context.Key<JmlInferPostConditions> key = new Context.Key<JmlInferPostConditions>();
    private static final String INFER_KIND = InferenceType.POSTCONDITIONS.toString();
    
    public JmlInferPostConditions(Context context) {
        super(context);
    }

    public static JmlInferPostConditions instance(Context context){
        
        JmlInferPostConditions instance = context.get(key);
        
        if (instance == null) {
            instance = new JmlInferPostConditions(context);
            context.put(key,instance);
        }
        
        return instance;
    }

    @Override
    public Key getKey() {
        return key;
    }

    @Override
    public void inferContract(JmlMethodDecl methodDecl) {        
        
        try{
            new Strongarm(this).infer(methodDecl); 

            utils.progress(1,1,"Completed inference of " + utils.qualifiedMethodSig(methodDecl.sym)); 
        } catch (Exception e) {
            log.error("jml.internal","Inference aborted with exception: " + e.getMessage());
            
            utils.progress(1,1,"Inference ABORTED of " + utils.qualifiedMethodSig(methodDecl.sym)
                    + " - exception"
                    );
        }
                
    }

    @Override
    public String inferenceType() {
        return INFER_KIND;
    }

}
