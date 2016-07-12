package org.jmlspecs.openjml.strongarm;

import java.io.BufferedReader;
import java.io.File;
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
    public final String[] debugArgs = new String[]{"-noexit", "-infer", "-infer-persist", "-progress", "-verbose"};
    public final String[] args;
    
    
    
    final protected Log                    log;
    final protected Context                context;
    public final boolean                   debug; 
    private int                            iteration;
    
    public Fix(boolean debug, String[] additionalArgs){
        
        // remove internal args not recognized by openjml
        for(String strip : strongarmArgs){
            additionalArgs = stripArg(strip, additionalArgs);
        }
        
        // enable debugging
        args = Arrays.copyOf(debugArgs, debugArgs.length + additionalArgs.length);
        System.arraycopy(additionalArgs, 0, args, debugArgs.length, additionalArgs.length);

        this.debug = true;
        
        this.context    = new Context();
        this.log        = Log.instance(context);
        
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

       System.out.println("[STRONGARM] Fixing iteration: " + InferenceManager.getInstance().round);

        
       String classpath = System.getProperty("java.class.path");
       String javaHome = System.getProperty("java.home");
       String javaBin = javaHome +
               File.separator + "bin" +
               File.separator + "java";
       
       String[] baseArgs = new String[]{javaBin, "-Dopenjml.eclipseSpecsProjectLocation=../../Specs","-cp", classpath, "org.jmlspecs.openjml.Main"};

       String[] processArgs = new String[baseArgs.length + args.length];
       
       System.arraycopy(baseArgs, 0, processArgs, 0, baseArgs.length);
       System.arraycopy(args, 0, processArgs, baseArgs.length, args.length);

       ProcessBuilder builder = new ProcessBuilder(processArgs);

       Process process = builder.start();
       
       BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
       
       String line;
       
       List<String> jml = new ArrayList<String>();
       
       while ( ( line = reader.readLine()) != null) {
           if(debug)
               System.out.println(line);
           
           if(line.contains("[STRONGARM] Persisting specs to:")){
               String[] splits = line.split(":");
               jml.add(splits[1].trim());
           }
        }
       
       process.waitFor();

       for(String j : jml){
           InferenceManager.getInstance().logInference(j);           
           System.out.println("[STRONGARM] Indexing Specification " + j);
       }
       
       System.out.println("[STRONGARM] DONE.");

    }
    
    public boolean hasChanges(){
        List<History> changed = InferenceManager.getInstance().filesChanged();
        
        for(History h : changed){
            System.out.println("[STRONGARM] Iteration " + InferenceManager.getInstance().round +" Changed File: " + h.file + " Checksum: " + h.checksum);
        }
                
        return changed.size() > 0;
    }
    
    public static void main(String args[]) throws Exception {
        
        
        Fix f = new Fix(containsArg(strongarmDebug, args), args);
        
        f.fix();
        
        while(f.hasChanges()){
            f.fix();
        }
    }
}
