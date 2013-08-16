package org.jmlspecs.openjml.utils;

public class CVC4Prover extends Prover {
    
    public CVC4Prover(String executable) {
        super(executable);
    }

    @Override
    public boolean isValid(String output) {
        return output.startsWith("This is CVC4 version 1.1") || output.startsWith("This is CVC4 version 1.2");
    }

    @Override
    public String versionArgument() {
        return "--version";
    }
    
    @Override
    public String getPropertiesName() {
        return "cvc4";
    }



}
