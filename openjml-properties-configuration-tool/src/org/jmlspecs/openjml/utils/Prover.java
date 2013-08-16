package org.jmlspecs.openjml.utils;

public abstract class Prover {
    
    private String executable;
    
    public abstract boolean isValid(String output);
    public abstract String versionArgument();
    public abstract String getPropertiesName();
    
    public Prover(String executable){
        this.executable = executable;
    }
    
    public String getExecutable(){
        return executable;
    }
    
    public static Prover getProver(String prover, String executable){
        if(prover.equalsIgnoreCase("Z3") || prover.startsWith("z3")){
            return new Z3Prover(executable);
        }else if(prover.equalsIgnoreCase("CVC4")){
            return new CVC4Prover(executable);
        }else if(prover.equalsIgnoreCase("Yices")){
            return new YicesProver(executable);
        }
        
        throw new IllegalArgumentException("Unknown prover requested: " + prover);
    }
    
    
}
