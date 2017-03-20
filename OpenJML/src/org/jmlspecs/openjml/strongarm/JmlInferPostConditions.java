package org.jmlspecs.openjml.strongarm;

import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

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
import com.sun.tools.javac.util.Log.WriterKind;

public class JmlInferPostConditions extends JmlInfer<JmlInferPostConditions> {

    protected static final Context.Key<JmlInferPostConditions> key = new Context.Key<JmlInferPostConditions>();
    private static final String INFER_KIND = InferenceType.POSTCONDITIONS.toString();
    private int timeout;
    public JmlInferPostConditions(Context context) {
        super(context);
        
        if(JmlOption.isOption(context, JmlOption.INFER_TIMEOUT)){  
            timeout = Integer.parseInt(JmlOption.value(context,  JmlOption.INFER_TIMEOUT));
        }else{
            timeout = -1;
        }
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
        
        JmlInferPostConditions inferenceRoot = this;
        
        
        ExecutorService service = Executors.newSingleThreadExecutor();
        Future<Long> future = service.submit(new Callable<Long>() {
            @Override
            public Long call() throws Exception {
                try{
                    Timing t = Timing.start();
                    new Strongarm(inferenceRoot).infer(methodDecl); 
                    long elapsed = t.stop();
                    
                    utils.progress(1,1,"Completed inference of " + utils.qualifiedMethodSig(methodDecl.sym) + t.tell());
                    
                    
                  
                    return elapsed;
                    
                } catch (Exception e) {

                    e.printStackTrace();
                    log.error("jml.internal","Inference aborted with exception: " + e.getMessage());
                    
                    utils.progress(1,1,"Inference ABORTED of " + utils.qualifiedMethodSig(methodDecl.sym)
                            + " - exception"
                            );
                    return -1L;
                }
            }
        });

        try {
            if(timeout==-1){
                future.get();
            }else{
                future.get(timeout, TimeUnit.SECONDS);
            }
        }
        catch(TimeoutException | InterruptedException | ExecutionException e) {
            // timeout
            log.getWriter(WriterKind.NOTICE).println(String.format("ABORTED INFERENCE OF %s. MAXIMUM INFERENCE TIME OF %d SECONDS EXCEEDED.",  utils.qualifiedMethodSig(methodDecl.sym), timeout)); //$NON-NLS-1$

        } 
        
        
                
    }

    @Override
    public String inferenceType() {
        return INFER_KIND;
    }

}
