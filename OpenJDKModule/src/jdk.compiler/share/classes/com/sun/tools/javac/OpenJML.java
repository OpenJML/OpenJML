package com.sun.tools.javac;

public class OpenJML {
	
	private OpenJML() {}
	
	public static void main(String... args) {
        System.exit(execute(args));
	}

    public static int execute(String... args) {
        return org.jmlspecs.openjml.Main.execute(args);
    }

}
