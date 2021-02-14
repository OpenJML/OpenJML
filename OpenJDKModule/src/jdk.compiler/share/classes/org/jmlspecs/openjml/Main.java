package org.jmlspecs.openjml;

import com.sun.tools.javac.main.Main.Result;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.ScannerFactory;
import com.sun.tools.javac.util.Context;

public class Main extends com.sun.tools.javac.main.Main {
	
    public Main() { super("openjml"); }
    public Main(String name) { super(name); }

    public static boolean useJML = false;
	
	public static void main(String[] args) {
    	System.out.println("Starting OpenJML Main: ");
    	useJML = true;
        //System.exit(com.sun.tools.javac.Main.compile(args));
    	System.out.println("Starting openjml compile: ");
        com.sun.tools.javac.main.Main compiler = new Main("openjml");
        System.exit(compiler.compile(args).exitCode);
	}
	
	@Override
    public Result compile(String[] argv, Context context) {
		System.out.println("Preregistsering tools");
		JmlScanner.JmlFactory.preRegister(context);
		return super.compile(argv, context);
	}

}
