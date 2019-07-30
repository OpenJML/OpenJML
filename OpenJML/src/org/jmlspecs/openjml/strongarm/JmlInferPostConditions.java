package org.jmlspecs.openjml.strongarm;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
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
import org.jmlspecs.openjml.ext.OptionsInfer;
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
        
        timeout = Integer.parseInt(JmlOption.value(context,  OptionsInfer.INFER_TIMEOUT));
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

    synchronized static public void emitStrongarmFatalError(String method, Exception e){
        File file = new File("strongarm-error.log");
        try {
            PrintStream ps = new PrintStream(new FileOutputStream(file, true));
            ps.println(String.format("====STRONGARM FATAL ERROR====\nMethod: %s\nDate %s", method, LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss.SSS"))));
            e.printStackTrace(ps);
            ps.flush();
            ps.close();
        } catch (FileNotFoundException e1) {            
            e1.printStackTrace();
        }
    }
    
    @Override
    public void inferContract(JmlMethodDecl methodDecl) {  
        
        JmlInferPostConditions inferenceRoot = this;
        
                
        Runnable runnable = new Runnable(){

            @Override
            public void run() {
                try{
                    Timing t = Timing.start();
                    new Strongarm(inferenceRoot).infer(methodDecl); 
                    long elapsed = t.stop();
                    
                    utils.progress(1,1,"Completed inference of " + utils.qualifiedMethodSig(methodDecl.sym) + t.tell());
                    
                }
                catch (StackOverflowError so) {
                    
                    methodDecl.cases = null;
                    methodDecl.methodSpecsCombined = null;

                    Exception e = new Exception("Stackoverflow error during inference.");
                    
                    emitStrongarmFatalError(utils.qualifiedMethodSig(methodDecl.sym), e);
                    e.printStackTrace();
                    
                    utils.progress(1,1,"Inference ABORTED of " + utils.qualifiedMethodSig(methodDecl.sym)
                            + " - exception"
                            );
                } 
                catch(InferenceAbortedException e){
                    // time to exit.
                    utils.progress(1,1,"Terminating thread for " + utils.qualifiedMethodSig(methodDecl.sym));
                }
                catch (Exception e) {
                    
                    methodDecl.cases = null;
                    methodDecl.methodSpecsCombined = null;

                    emitStrongarmFatalError(utils.qualifiedMethodSig(methodDecl.sym), e);
                    e.printStackTrace();
                    
                    utils.progress(1,1,"Inference ABORTED of " + utils.qualifiedMethodSig(methodDecl.sym)
                            + " - exception"
                            );
                }
                
            }
            
        };
        
        
        long startTime = System.currentTimeMillis();
        long timeoutMs = timeout * 1000L;
        
        
        Thread t = new Thread(runnable);
        t.start();

        try {
            if(timeout!=-1){
                while (t.isAlive()) {
                    t.join(1000);
                    if (((System.currentTimeMillis() - startTime) > timeoutMs)
                          && t.isAlive()) {
                        t.interrupt();
                        t.join();
                        
                        log.getWriter(WriterKind.NOTICE).println(String.format("ABORTED INFERENCE OF %s. MAXIMUM INFERENCE TIME OF %d SECONDS EXCEEDED.",  utils.qualifiedMethodSig(methodDecl.sym), timeout)); //$NON-NLS-1$
                        // wipe out the contract. 
                        methodDecl.cases = null;
                        methodDecl.methodSpecsCombined = null;
                    }
                }
            
            }else{
                t.join();
            }
        }catch(InterruptedException e){
            log.getWriter(WriterKind.NOTICE).println(String.format("ABORTED INFERENCE OF %s. MAXIMUM INFERENCE TIME OF %d SECONDS EXCEEDED.",  utils.qualifiedMethodSig(methodDecl.sym), timeout)); //$NON-NLS-1$
            // wipe out the contract. 
            methodDecl.cases = null;
            methodDecl.methodSpecsCombined = null;            
        }
        
    }

    @Override
    public String inferenceType() {
        return INFER_KIND;
    }

}
