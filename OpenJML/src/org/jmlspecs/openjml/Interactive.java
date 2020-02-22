/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.parser.JmlDebugTreePrinter;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

/**
 * This class executes the OpenJML tool interactively; call the main routine to
 * begin the interactive command loop. See the list of implemented commands in
 * the 'command' method.
 * 
 * @author David Cok
 */
// FIXME - review whether to support this; review this class
public class Interactive extends Main {

    /** This is the main entry point for the application
     * @param args the non-null array of command line argument
     */
    //@ requires args != null && \nonnullelements(args);
    //@ diverges true;
    public static void main(String[] args) {
        try {
            System.exit(new Interactive().run(args));
        } catch (Exception e) {
            System.err.println("Failed with exception " + e);
        }
    }
    
    /** The constructor for an object of this class, initiating the base class
     * with System.out as the output location. */
    public Interactive() throws Exception {
        super("jml-interactive", new PrintWriter(System.out, true), null, null);
    }
    
    /** The top-level routine that implements the interactive command processing.
     * 
     * @param args the arguments as supplied on the command line
     * @return 0
     */ 
    //@ requires args != null && \nonnullelements(args);
    public int run(String[] args) {
        setup(args);
        commandLoop();
        System.out.println("... exiting");
        return 0;
    }
    
    // FIXME - finish documentation
    
    public JavacFileManager fileManager;
    
    public void setup(String[] args) {
        context = new Context();
        JavacFileManager.preRegister(context); // can't create it until Log has been set up
        compile(args, context);
        fileManager = (JavacFileManager)context.get(JavaFileManager.class);
        //filemanager = (JavacFileManager)
//        if (fileManager instanceof JavacFileManager) {
//            // A fresh context was created above, so jfm must be a JavacFileManager
//            ((JavacFileManager)fileManager).close();
//        }
    }
    
    /** This method executes a command loop; each iteration does the following:
     * <UL>
     * <LI> prints a prompt to System.out
     * <LI> reads a string from System.in (terminated by a newline)
     * <LI> executes that string as a command (calling method command)
     * </UL>
     * The loop terminates when (a) the command method returns -1, (b) an 
     * exception occurs when reading input or executing the command.
     */ 
    public void commandLoop() {
        try {
            BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
            String str = "";
            while (str != null) {
                System.out.print("> ");
                str = in.readLine();
                try {
                    int c = command(str);
                    if (c == -1) break;
                } catch (Exception e) {
                    System.out.println("... Exception during command: " + e);
                    e.printStackTrace(System.out);
                }
            }
        } catch (IOException e) {
            System.out.println(" .... failed to perform IO: " + e);
        }
    }
    
    /** This executes an interactive command; it returns -1 if the command loop
     * should exit.  If the input command is null, -1 is returned.
     * @param command the possibly null input command
     * @return -1 if the command loop is to be exited, non-negative otherwise
     * @throws Exception
     */
    //@ ensures command == null ==> \result == -1;
    public int command(String command) throws Exception {
        int e = 0;
        if (command == null) return -1;
        if (command.length() == 0) return 0;
        if (command.startsWith("quit")) return -1;
        if (command.startsWith("help")) return help(command);
        if (command.startsWith("parse")) return parse(command);
        if (command.startsWith("check")) return check(command);
        if (command.startsWith("reset")) return reset(command);
        if (command.startsWith("cclass")) return cclass(command);
        if (command.startsWith("specs")) return specs(command);
        System.out.println("UNKNOWN COMMAND: " + command);
        return e;
    }
    
    /** Executes the help command
     * 
     * @param command - ignored, but should be "help"
     * @return 0
     */
    public int help(String command) {
        System.out.println("  Implemented commands:");
        System.out.println("     help - lists the commands");
        System.out.println("     quit - terminates the program");
        System.out.println("     CTRL-Z - terminates the program");
        System.out.println("     parse <file> - parses the given file");
        System.out.println("     check <file> - parses and typechecks the given file");
        System.out.println("     reset - restarts with a new compilation context");
        System.out.println("     cclass - parses and typechecks a class by fully-qualified name");
        System.out.println("     specs - shows specs for a class by fully-qualified name");
        return 0;
    }

    public int parse(String command) {
        int n = command.indexOf(' ');
        String[] files = command.substring(n+1).split(" ");
        for (String f: files) {
            JavaFileObject j = fileManager.getRegularFile(new File(f));
            JmlCompilationUnit cu = (JmlCompilationUnit)JmlCompiler.instance(context).parse(j);
            cu.accept(new JmlDebugTreePrinter(System.out,null)); // FIXME - this prints debug information - is that what we want?
        }
        return 0;
    }

    public int check(String command) throws Exception {
        int n = command.indexOf(' ');
        String[] files = command.substring(n+1).split(" ");
        for (String f: files) {  // FIXME - do in one swoop
            JmlCompiler jmlCompiler = (JmlCompiler)JmlCompiler.instance(context);
            JavaFileObject j = fileManager.getRegularFile(new File(f));
            jmlCompiler.compile(List.of(j),List.<String>nil(),null);
            // FIXME - do we really need to expose compilerKey? if not, put it back to protected
            context.put(JavaCompiler.compilerKey,(JavaCompiler)null);
            JmlCompiler.preRegister(context);
            Log.instance(context).nerrors = 0;
            Log.instance(context).nwarnings = 0;
        }
        return 0;
    }
    
    public int reset(String command) throws Exception {
        String[] args = command.substring(command.indexOf(" ")).split(" ");
        setup(args);
        return 0;
    }
    
    public int cclass(String command) throws Exception {
        String[] args = command.substring(command.indexOf(" ")).split(" ");
        JmlSpecs.instance(context).initializeSpecsPath(); // FIXME - should not this happen in setup
        for (String s: args) {
            if (s.length() == 0) continue;
            Name name = Names.instance(context).fromString(s);
            ClassSymbol csym = ClassReader.instance(context).enterClass(name);
            csym.complete();
            JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).get(csym);
            if (tsp == null) {
                ((JmlCompiler)JmlCompiler.instance(context)).loadSpecsForBinary(null,csym);
            }
            JmlAttr.instance(context).attribClass(csym);
        }
        return 0;
    }
    
    public int specs(String command) throws Exception {
        String[] args = command.substring(command.indexOf(" ")).split(" ");
        JmlSpecs.instance(context).initializeSpecsPath(); // FIXME - should not this happen in setup
        for (String s: args) {
            if (s.length() == 0) continue;
            Name name = Names.instance(context).fromString(s);
            ClassSymbol csym = ClassReader.instance(context).enterClass(name);
            csym.complete();
            JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).get(csym);
            if (tsp == null) {
                ((JmlCompiler)JmlCompiler.instance(context)).loadSpecsForBinary(null,csym);
            }
            JmlAttr.instance(context).attribClass(csym);
            tsp = JmlSpecs.instance(context).get(csym);
            if (tsp == null) {
                System.out.println("... Could not find specs for " + name);
            } else {
                System.out.println("  Specifications for " + name);
                if (tsp.file == null) System.out.println("      No source file given");
                if (tsp.file != null) System.out.println("      Source: " + tsp.file);
                if (tsp.modifiers == null) System.out.println("      No modifiers object present");
                else {
                    System.out.println("      Java modifiers: " + Flags.toString(tsp.modifiers.flags));
                    System.out.print("      Annotations:");
                    for (JCAnnotation a: tsp.modifiers.annotations) {
                        System.out.print(" " + a);
                    }
                    System.out.println();
                }
                if (tsp.clauses == null) System.out.println("      No clause list");
                else {
                    System.out.println("      " + tsp.clauses.size() + " clauses");
                    for (JmlTypeClause t : tsp.clauses) {
                        System.out.println("        " + t);
                    }
                }
                if (tsp.methods == null) System.out.println("      No method list");
                else {
                    System.out.println("      " + tsp.methods.size() + " methods");
                    for (MethodSymbol m : tsp.methods.keySet()) {
                        JmlSpecs.MethodSpecs sp = tsp.methods.get(m);
                        System.out.println("        " + m);
                        System.out.println(sp.mods);
                        System.out.println(sp.cases);
                    }
                }
                if (tsp.fields == null) System.out.println("      No fields list");
                else {
                    System.out.println("      " + tsp.fields.size() + " fields");
                    for (VarSymbol f : tsp.fields.keySet()) {
                        JmlSpecs.FieldSpecs sp = tsp.fields.get(f);
                        System.out.println("        " + f);
                    }
                }
                
            }
        }
        return 0;
    }

}
