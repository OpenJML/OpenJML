package org.jmlspecs.openjml.utils;

public class Z3Prover extends Prover {

    public Z3Prover(String executable) {
        super(executable);
    }

    @Override
    public boolean isValid(String output) {
        return output.startsWith("Z3 version 4.3");
    }

    @Override
    public String versionArgument() {
        return "-version";
    }

    @Override
    public String getPropertiesName() {
        return "z3_4_3";
    }

}
