package org.jmlspecs.openjml.strongarm;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.strongarm.InferenceManager.History;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class Fix {

    public static final String strongarmDebug = "-strongarm:debug";
    
    public final String[] strongarmArgs = new String[]{"-strongarm:debug"}; // these get stripped out. 
    public final String[] debugArgs = new String[]{"-minQuant", "-noexit", "-infer", "-infer-persist", "-progress", "-verbose"};
    public final String[] args;
    
    private static final String persistLine = "[INFER] Persisting specs to:";
    
    final protected SimpleLog              log;
    public final boolean                   debug; 
    private int                            iteration;
    public int maxSpecs;
    public Fix(boolean debug, String[] additionalArgs){
        
        // remove internal args not recognized by openjml
        for(String strip : strongarmArgs){
            additionalArgs = stripArg(strip, additionalArgs);
        }
        
        // enable debugging
        args = Arrays.copyOf(debugArgs, debugArgs.length + additionalArgs.length);
        System.arraycopy(additionalArgs, 0, args, debugArgs.length, additionalArgs.length);

        this.debug      = debug;
        
        this.log        = new SimpleLog(SimpleLog.Level.INFO);
        
    }
    
       
    public static String[] stripArg(String arg, String args[]){
        
        if(!containsArg(arg, args)){
            return args;
        }
        
        String[] newArgs = new String[args.length - countArg(arg, args)];
        
        int idx=0;
        
        for(String s : args){
            
            if(s.equals(arg)==false){
                newArgs[idx] = s;
                idx++;
            }
        }
        
        return newArgs;
    }
    
    public static int countArg(String arg, String args[]){
        int count = 0;
        
        for(String s : args){
            if(s.equals(arg)){
                count++;
            }
        }
        
        return count;        
    }
    
    public static boolean containsArg(String arg, String args[]){
        return countArg(arg, args) > 0;
    }
    
    public void fix() throws Exception {
        
       InferenceManager.getInstance().newRound();

       log.info("Fixing iteration: %d ", InferenceManager.getInstance().round);

        
       String classpath = System.getProperty("java.class.path");
       String javaHome = System.getProperty("java.home");
       String javaBin = javaHome +
               File.separator + "bin" +
               File.separator + "java";
       
       String[] baseArgs = new String[]{javaBin, "-Xmx5G", "-Dopenjml.eclipseSpecsProjectLocation=../../Specs","-cp", classpath, "org.jmlspecs.openjml.Main"};

       String[] processArgs = new String[baseArgs.length + args.length];
       
       System.arraycopy(baseArgs, 0, processArgs, 0, baseArgs.length);
       System.arraycopy(args, 0, processArgs, baseArgs.length, args.length);

       ProcessBuilder builder = new ProcessBuilder(processArgs);

       Process process = builder.start();
       
       BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
       
       String line;
       
       List<String> jml = new ArrayList<String>();
       
       StringBuilder output = new StringBuilder();
       int max = 100;
       
       
       BufferedWriter bw = null;
       FileWriter fw      = null;
       try {
           fw = new FileWriter("/Users/jls/Desktop/runs/run1.out");
           bw = new BufferedWriter(fw);
           
           while ( ( line = reader.readLine()) != null) {
               if(debug){
                   System.out.println(line);
                   bw.write(line);
                   bw.write("\n");
               }
               output.append(line);
           
               max--;
               
               if(max <= 0){
                   output.setLength(0);
                   max = 100;
               }
               
               if(line.contains(persistLine)){
                   String[] splits = line.split(":");
                   jml.add(splits[1].trim());
               }
            }
       }catch(Exception e){}
       finally {
           if(bw!=null){
               bw.close();
           }
           if(fw!=null){
               fw.close();
           }
       }
       
       int exit = process.waitFor();

       if(exit!=0){
           log.error("Failed, Please check logs.");
           //log.error(output.toString());
       }
       
       
       for(String j : jml){
           InferenceManager.getInstance().logInference(j);           
           log.info("[IDX SPEC] %s", j);
       }
       
       printSummary();
    }
    
    private void printSummary(){
        log.info("Summary");
        log.info("=======================");
        
        List<History> thisRound = InferenceManager.getInstance().filesChanged();
        
        if(thisRound.size() > maxSpecs){
            maxSpecs = thisRound.size();
        }
        
        if(InferenceManager.getInstance().round == 1){
            log.info("Δ + %d Specifications", thisRound.size());
        }else{
        
            List<History> lastRound = InferenceManager.getInstance().filesChanged(InferenceManager.getInstance().round-1);

            if(lastRound.size() > thisRound.size()){
                log.info("Δ  -%d Specifications From Last Round. This Round %d Specs Changed.", lastRound.size() - thisRound.size(), thisRound.size());    
                
            }else if(lastRound.size() < thisRound.size()){
                log.info("Δ  +%d Specifications From Last Round. This Round %d Specs Changed.", thisRound.size() - lastRound.size(), thisRound.size());    
                
            }else{
                log.info("Δ  +/-0 Specifications From Last Round (no change). This Round %d Specs Changed.", thisRound.size());    
            }

            
           
            
        }

        List<History> changed = InferenceManager.getInstance().filesChanged();

        for(History h : changed){
            log.info("[CHANGED SPEC] %s (%s)", h.file, h.checksum);
        }
        
        log.info("=======================");

        
        

    }
    
    public boolean hasChanges(){
        List<History> changed = InferenceManager.getInstance().filesChanged();
        return changed.size() > 0;
    }
    
    public static void main(String args[]) throws Exception {
        
        long ts1 = System.currentTimeMillis();
        
        Fix f = new Fix(containsArg(strongarmDebug, args), args);
        
        f.fix();
        
        while(f.hasChanges()){
            f.fix();
        }
        
        long ts2 = System.currentTimeMillis();
        
        f.log.info("DONE");
        f.log.info("Completed %d Rounds in %.2f Seconds. %d Specifications Infererred.", 
                InferenceManager.getInstance().round,
                (double)(ts2 - ts1) / (double)1000L,
                f.maxSpecs
                );
    }
}
