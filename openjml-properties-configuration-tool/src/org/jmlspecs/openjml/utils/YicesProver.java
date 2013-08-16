package org.jmlspecs.openjml.utils;

public class YicesProver extends Prover {

    public YicesProver(String executable) {
        super(executable);
    }

    @Override
    public boolean isValid(String output) {
        return output.startsWith("1.0");
    }

    @Override
    public String versionArgument() {
        return "-V";
    }

    @Override
    public String getPropertiesName() {
        return "yices";
    }

}
