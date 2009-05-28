/**
 * Copyright (c) 2005 David R. Cok.
 *
 * @author David R. Cok
 * Jun 17, 2005 
 */
package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.io.PrintWriter;
import java.net.URL;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.*;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.internal.compiler.problem.ProblemSeverities;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.Main.JmlCanceledException;
import org.jmlspecs.openjml.esc.BasicBlocker;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.osgi.framework.Bundle;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.util.Context;

//FIXME - sort out whether this class is a collection of static routines
//or whether it actually needs to be an object.

/**
 * This class is the interface between the Eclipse UI that serves as view and
 * controller and the openjml packages that executes operations on JML annotations.
 */
public class OpenJMLInterface {

    static API lastRun = null;

    final protected Utils utils = Activator.getDefault().utils;

    public static enum Cmd { CHECK, ESC, RAC, JMLDOC};

    /** Executes the JLM Check (syntax and typechecking) or the RAC compiler
     * operations on the given set of resources.
     * @param command either CHECK or RAC
     * @param files the set of files (or containers) to check
     * @param monitor the progress monitor the UI is using
     */
    public void executeExternalCommand(Cmd command, List<IResource> files, IProgressMonitor monitor) {
        try {
            if (files.isEmpty()) {
                Log.log("Nothing applicable to process");
                Activator.getDefault().utils.showMessageInUI(null,"JML","Nothing applicable to process");
                return;
            }
            //String[] cmd = { "-classpath", "C:/home/runtime-EclipseApplication/Test/src;C:/home/projects/OpenJML/trunk/OpenJMLUI/jmlruntime.jar" };
            IJavaProject jp = JavaCore.create(files.get(0).getProject());
            List<String> args = getOptions(jp,command);
            args.add(JmlOptionName.DIRS.optionName());

            for (IResource r: files) {
                args.add(r.getLocation().toString());
            }
            Log.log(Timer.getTimeString() + " Executing openjml ");
            if (monitor != null) monitor.subTask("Executing openjml");
            try {
                PrintWriter w = new PrintWriter(((ConsoleLogger)Log.log.listener).getConsoleStream());
                API api = lastRun = new API(w,new EclipseDiagnosticListener(preq));
                if (monitor != null) monitor.setTaskName("JML Checking");
                lastRun.setProgressReporter(new UIProgressReporter(lastRun.context,monitor,null));
                int ret = api.compile(args.toArray(new String[args.size()]));
                if (ret == 0) Log.log(Timer.getTimeString() + " Completed");
                else if (ret == 1) Log.log(Timer.getTimeString() + " Completed with errors");
                else if (ret >= 2) {
                    StringBuilder ss = new StringBuilder();
                    for (String r: args) {
                        ss.append(r);
                        ss.append(" ");
                    }
                    Log.errorlog("INTERNAL ERROR: return code = " + ret + "   Command: " + ss,null);  // FIXME _ dialogs are not working
                    Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Internal failure in openjml - return code is " + ret + " " + ss); // FIXME - fix line ending
                }
            } catch (JmlCanceledException e) {
                throw e;
            } catch (Throwable e) {
                StringBuilder ss = new StringBuilder();
                for (String c: args) {
                    ss.append(c);
                    ss.append(" ");
                }
                Log.errorlog("Failure to execute openjml: "+ss,e); 
                Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Failure to execute openjml: " + e + " " + ss);
            }
            if (monitor != null) monitor.subTask("Completed openjml");
        } catch (JmlCanceledException e) {
            if (monitor != null) monitor.subTask("OpenJML Canceled: " + e.getMessage());
        }
    }
    
    public void generateJmldoc(IJavaProject p) {
        List<String> args = getOptions(p,Cmd.JMLDOC);
        args.add("-d");
        args.add(p.getProject().getLocation().toString() + "/docx");
        //args.add(JmlOptionName.DIRS.optionName());
        try {
            for (IPackageFragmentRoot pfr : p.getPackageFragmentRoots()) {
                // PackageFragmentRoots can be source folders or jar files
                // We want just the source folders
                IResource f = (IResource)pfr.getAdapter(IResource.class);  // FIXME - there must be a better way to do this
                if (!(f instanceof IFolder)) continue;
                IJavaElement[] packages = pfr.getChildren();
                for (IJavaElement je : packages) {
                    IPackageFragment pf = (IPackageFragment)je;
                    if (pf.containsJavaResources()) args.add(pf.getElementName()); // getElementName gives the fully qualified package name
                }
            }
        } catch (JavaModelException e) {
            // FIXME
        }
        int ret = API.jmldoc(args.toArray(new String[args.size()]));
    }

    /** Executes the JML ESC (static checking) operation
     * on the given set of resources.
     * @param command should be ESC
     * @param things the set of files (or containers) or Java elements to check
     * @param monitor the progress monitor the UI is using
     */
    public void executeESCCommand(Cmd command, List<Object> things, IProgressMonitor monitor) {
        try {
            if (things.isEmpty()) {
                Log.log("Nothing applicable to process");
                Activator.getDefault().utils.showMessageInUI(null,"JML","Nothing applicable to process");
                return;
            }
            if (lastRun == null) {
                List<IResource> rlist = new LinkedList<IResource>();
                for (Object o: things) {
                    if (o instanceof IResource) rlist.add((IResource)o);
                    else if (o instanceof IAdaptable) {
                        o = ((IAdaptable)o).getAdapter(IResource.class);
                        if (o instanceof IResource) rlist.add((IResource)o);
                    }
                }
                executeExternalCommand(Cmd.CHECK,rlist,monitor);
            }
            //String[] cmd = { "-classpath", "C:/home/runtime-EclipseApplication/Test/src;C:/home/projects/OpenJML/trunk/OpenJMLUI/jmlruntime.jar" }; 
            Object o = things.get(0);
            IJavaProject jp = (o instanceof IJavaElement) ? ((IJavaElement)o).getJavaProject() : 
                            (o instanceof IResource) ? JavaCore.create(((IResource)o).getProject()) : null;
           
            List<String> args = getOptions(jp,Cmd.ESC);
            List<IJavaElement> elements = new LinkedList<IJavaElement>();
            //for (String c: cmd) args.add(c);
            args.add(JmlOptionName.DIRS.optionName());
            int n = args.size();
            
            IResource rr;
            for (Object r: things) {
                if (r instanceof IResource) args.add(((IResource)r).getLocation().toString());
                else if (r instanceof IType || r instanceof IMethod) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else if (r instanceof IAdaptable && (rr=(IResource)((IAdaptable)r).getAdapter(IResource.class)) != null) {
                    args.add(rr.getLocation().toString());
                    PrintWriter w = new PrintWriter(((ConsoleLogger)Log.log.listener).getConsoleStream());
                    lastRun = new API(w,new EclipseDiagnosticListener(preq));
                    lastRun.setProgressReporter(new UIProgressReporter(lastRun.context,monitor,null));
                } else if (r instanceof IJavaElement) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else Log.log("Ignoring " + r.getClass() + " " + r.toString());
            }
            if (args.size() == n && elements.size() == 0) {
                Log.log("No files or elements to process");
                Activator.getDefault().utils.showMessageInUI(null,"JML","No files or elements to process");
                return;
            }
            if (args.size() > n) {
                Log.log(Timer.getTimeString() + " Executing openjml ");
                if (monitor != null) monitor.subTask("Executing openjml");
                try {
                    if (monitor != null) monitor.setTaskName("ESC");
                    int ret = lastRun.compile(args.toArray(new String[args.size()]));
                    if (ret == 0) Log.log(Timer.getTimeString() + " Completed");
                    else if (ret == 1) Log.log(Timer.getTimeString() + " Completed with errors");
                    else if (ret >= 2) {
                        StringBuilder ss = new StringBuilder();
                        for (String c: args) {
                            ss.append(c);
                            ss.append(" ");
                        }
                        Log.errorlog("INTERNAL ERROR: return code = " + ret + "   Command: " + ss,null);  // FIXME _ dialogs are not working
                        Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Internal failure in openjml - return code is " + ret + " " + ss); // FIXME - fix line ending
                    }
                } catch (Main.JmlCanceledException e) {
                    throw e;
                } catch (Throwable e) {
                    StringBuilder ss = new StringBuilder();
                    for (String c: args) {
                        ss.append(c);
                        ss.append(" ");
                    }
                    Log.errorlog("Failure to execute openjml: "+ss,e); 
                    Activator.getDefault().utils.showMessageInUI(null,"JML Execution Failure","Failure to execute openjml: " + e + " " + ss);
                }
            }
            for (IJavaElement je: elements) {
                if (je instanceof IMethod) {
                    MethodSymbol msym = convertMethod((IMethod)je);
                    lastRun.doEsc(msym);
                } else if (je instanceof IType) {
                    ClassSymbol csym = convertType((IType)je);
                    lastRun.doEsc(csym);
                }
            }
            if (monitor != null) monitor.subTask("Completed ESC operation");
            Log.log("Completed ESC operation");
        } catch (JmlCanceledException e) {
            Log.log("Canceled ESC operation");
            throw e;
        }
    }

    public @NonNull ClassSymbol convertType(IType type) {
        String className = type.getFullyQualifiedName();
        ClassSymbol csym = lastRun.getClassSymbol(className);
        if (csym == null) {
            String error = "No such class in OpenJML: " + className;
            Log.errorlog(error,null);
            throw new Utils.OpenJMLException(error);
        }
        return csym;
    }
    
    public MethodSymbol convertMethod(IMethod method) {
        ClassSymbol csym = convertType(method.getDeclaringType());
        try {
            com.sun.tools.javac.util.Name name = com.sun.tools.javac.util.Names.instance(lastRun.context).fromString(
                    method.isConstructor() ? "<init>" : method.getElementName());
            Scope.Entry e = csym.members().lookup(name); // FIXME - Need to match types & number
            MethodSymbol firstsym = null;
            outer: while (e != null && e.sym != null) {
                Symbol sym = e.sym;
                e = e.sibling;
                if (!(sym instanceof MethodSymbol)) continue;
                MethodSymbol msym = (MethodSymbol)sym;
                List<VarSymbol> params = msym.getParameters();
                String[] paramtypes = method.getParameterTypes();
                if (params.size() != paramtypes.length) continue;
                firstsym = msym;
                int i = 0;
                for (VarSymbol v: params) {
                    // Does v.type match paramtypes[i]
                    if (!typeMatches(v.type,paramtypes[i++])) continue outer;
                }
                return msym;
            }
            if (firstsym != null) return firstsym;  // FIXME: hack because of poor type matching
            String error = "No matching method in OpenJML: " + method.getDeclaringType().getFullyQualifiedName() + "." + method;
            Log.errorlog(error,null);
            throw new Utils.OpenJMLException(error);
        } catch (JavaModelException e) {
            throw new Utils.OpenJMLException("Unable to convert method " + method.getElementName() + " of " + method.getDeclaringType().getFullyQualifiedName(),e); 
        }
    }
    
    public boolean typeMatches(Type t, String tstring) {
        String vt = t.toString();
        if (tstring.charAt(0) == '[') {
            int k = 1;
            while (tstring.charAt(k) == '[') k++;
            int n = vt.length()-2*k;
            if (n < 0 || vt.charAt(n) != '[') return false;
            vt = vt.substring(0,vt.length()-2*k);
            tstring = tstring.substring(k);
        }
        char c = tstring.charAt(0);
        if (tstring.equals("I")) tstring = "int";
        else if (tstring.equals("F")) tstring = "float";
        else if (tstring.equals("D")) tstring = "double";
        else if (tstring.equals("C")) tstring = "char";
        else if (tstring.equals("J")) tstring = "long";
        else if (tstring.equals("S")) tstring = "short";
        else if (tstring.equals("B")) tstring = "byte";
        else if (tstring.equals("Z")) tstring = "boolean";
        else if (c == 'Q') tstring = tstring.substring(1,tstring.length()-1);
        else return false;
        if (c == 'Q') {
            int p = tstring.indexOf('<');
            if (p >= 0) {
                String prefix = tstring.substring(0,p);
                String rest = tstring.substring(p+1);
                if (!((ClassSymbol)t.tsym).getQualifiedName().toString().endsWith(prefix)) return false;
                return true; // FIXME
                //            List<Type> targs = t.getTypeArguments();
                //            for (Type ta : targs) {
                //                p = rest.index
                //            }
            }
        }
        if (vt.equals(tstring)) {
//            Log.log(tstring + " matches " + vt);
        } else if (vt.endsWith(tstring)) {  // FIXME - trouble with matching type parameters
//            Log.log(tstring + " ends " + vt);
        } else {
//            Log.log(tstring + " does not match " + vt);
            return false;
        }
        return true;
    }
    
    
    public String getSpecs(IType type) {
        ClassSymbol csym = convertType(type);
        try{
            TypeSpecs tspecs = lastRun.getSpecs(csym);
            String smods = lastRun.prettyPrint(tspecs.modifiers,false);
            return smods + "\n" + tspecs.toString();
        } catch (Exception e) { return "<Exception>: " + e; }
    }

    public String getAllSpecs(IType type) {
        if (lastRun == null) return null;
        ClassSymbol csym = convertType(type);
        List<TypeSpecs> typeSpecs = lastRun.getAllSpecs(csym);
        try {
            StringBuilder sb = new StringBuilder();
            for (TypeSpecs ts: typeSpecs) {
                sb.append("From " + ts.file.getName() + "\n");
                sb.append(lastRun.prettyPrint(ts.modifiers,false));
                sb.append("\n");
                sb.append(ts.toString());
                sb.append("\n");
            }
            return sb.toString();
        } catch (Exception e) { return "<Exception>: " + e; }
    }
    
    public String getAllSpecs(IMethod method) {
        if (lastRun == null) return null;
        MethodSymbol msym = convertMethod(method);
        List<JmlMethodSpecs> methodSpecs = lastRun.getAllSpecs(msym);
        try {
            StringBuilder sb = new StringBuilder();
            for (JmlMethodSpecs ts: methodSpecs) {
                sb.append("From " + ts.decl.sourcefile.getName() + "\n");
                sb.append(lastRun.prettyPrint(ts.decl.mods,false)); // FIXME - want the collected mods in the JmlMethodSpecs
                sb.append("\n");
                sb.append(lastRun.prettyPrint(ts,false));
                sb.append("\n");
            }
            return sb.toString();
        } catch (Exception e) { return "<Exception>: " + e; }
        
    }

//    // FIXME - does not include annotations or jml modifiers; inherited specs
//    public String getSpecs(IMethod method) {
//        String s = method.getDeclaringType().getFullyQualifiedName();
//        ClassSymbol csym = lastRun.getClassSymbol(s);
//        try {
//            com.sun.tools.javac.util.Name name = com.sun.tools.javac.util.Names.instance(lastRun.context).fromString(
//                    method.isConstructor() ? "<init>" : method.getElementName());
//            Symbol sym = csym.members().lookup(name).sym;
//            MethodSymbol msym = (MethodSymbol)sym;
//            JmlMethodSpecs mspecs = lastRun.getSpecs(msym);
//            try { 
//                String smods = lastRun.prettyPrint(mspecs.decl.mods,false);
//                return smods + "\n" + lastRun.prettyPrint(mspecs,false); // FIXME - use proper eol
//            } catch (Exception e) { return "<Exception>: " + e; }
//        } catch (JavaModelException e) { return "<Exception>: " + e; }
//    }

    // FIXME - this does not include annotations - classic or Java
    public String getSpecs(IField field) {
        if (lastRun == null) return null;
        String s = field.getDeclaringType().getFullyQualifiedName();
        ClassSymbol csym = lastRun.getClassSymbol(s);
        com.sun.tools.javac.util.Name name = com.sun.tools.javac.util.Names.instance(lastRun.context).fromString(field.getElementName());
        Symbol sym = csym.members().lookup(name).sym;
        VarSymbol fsym = (VarSymbol)sym;
        FieldSpecs fspecs = lastRun.getSpecs(fsym);
        try { 
            String smods = lastRun.prettyPrint(fspecs.mods,false);
            return smods + "\n" + fspecs.toString(); // FIXME - use proper eol
        } catch (Exception e) { return "<Exception>: " + e; }
    }

    public void showProofInfo(IMethod method, Shell shell) {
        if (lastRun == null) {
            utils.showMessageInUINM(shell,"JML Proof Results","There is no current proof result for " + method.getDeclaringType().getFullyQualifiedName() + "." + method.getElementName());
            return;
        }
        MethodSymbol msym = null;
        try { msym = convertMethod(method);
        } catch (Exception e) {}
        if (msym == null) {
            utils.showMessageInUINM(shell,"JML Proof Results","The method " + method.getElementName() + " has not yet been checked (or a proof attempted)");
            return;
        }
        Log.log("SPI msym = " + msym);
        IProverResult r = lastRun.getProofResult(msym);
        
        Log.log("prover result " + (r != null));
        String s = lastRun.getBasicBlockProgram(msym);
        Log.log("Launching for " + msym + " " + msym.owner + " " + (s != null));
        utils.launchEditor(s,msym.owner.name + "." + msym.name);

        if (r == null) {
            utils.showMessageInUINM(shell,"JML Proof Results","There is no current proof result for " + msym.owner + "." + msym);
            return;
        }

        Object o = r.otherInfo();
        if (o != null) utils.launchEditor(o.toString(),msym.owner.name + "." + msym.name);


        if (r.result() == IProverResult.UNSAT) {
            utils.showMessageInUINM(shell,"JML Proof Results",
                    "The verification proof succeeded for " + msym.owner + "." + msym + "\n"
                    + "Prover: " + r.prover());
            return;
        }
        if (r.result() == IProverResult.INCONSISTENT) {
            utils.showMessageInUINM(shell,"JML Proof Results","The assumptions are INCONSISTENT for " + msym.owner + "." + msym + "\n"
            + "Prover: " + r.prover());
            return;
        }
        if (r.result() == IProverResult.UNKNOWN) {
            utils.showMessageInUINM(shell,"JML Proof Results","The verification was not provable for " + msym.owner + "." + msym + "\n"
            + "Prover: " + r.prover());
            return;
        }
        
        
        if (r.counterexample() == null) {
            utils.showMessageInUINM(shell,"JML Counterexample", "There is no counterexample information for method " + msym); // FIXME - more name info
        } else {
            Set<Map.Entry<String,String>> set = r.counterexample().sortedEntries();
            StringBuffer sb = new StringBuffer();
            sb.append("COUNTEREXAMPLE STATE FOR " + msym.owner + "." + msym + "  Prover: " + r.prover());
            for  (Map.Entry<String,String> entry : set) {
                sb.append(entry.getKey());
                sb.append(" = ");
                sb.append(entry.getValue());
                sb.append("\n");
            }
            utils.launchEditor(sb.toString(),msym.owner.name + "." + msym.name);
        }
        return;
    }


    /** Instances of this class can be registered as DiagnosticListeners (that is,
     * listeners for errors from tools in the javac framework); they then convert
     * any diagnostic into an Eclipse problem (a JmlEclipseProblem) of the 
     * appropriate severity, which is
     * then fed to the given IProblemRequestor.
     * 
     * @author David Cok
     *
     */
    static public class EclipseDiagnosticListener implements DiagnosticListener<JavaFileObject> {

        protected IProblemRequestor preq;

        /** Creates a listener which will translate any diagnostics it hears and
         * send them off to the given IProblemRequestor.
         * @param p the problem requestor that wants to receive any diagnostics
         */
        public EclipseDiagnosticListener(@NonNull IProblemRequestor p) {
            preq = p;
        }

        /** This is the method that is called whenever a diagnostic is issued;
         * it will convert and pass it on to the problem requestor.  If the 
         * diagnostic cannot be converted to an Eclipse IProblem, then it is
         * printed to Log.log or Log.errorlog.
         * 
         * @param diagnostic the diagnostic to be translated and forwarded
         */
        //JAVA16 @Override
        @SuppressWarnings("restriction")
        public void report(@NonNull Diagnostic<? extends JavaFileObject> diagnostic) {
            JavaFileObject j = diagnostic.getSource();
            String message = diagnostic.getMessage(null); // uses default locale
            int id = 0; // FIXME
            Diagnostic.Kind kind = diagnostic.getKind();
            int severity = 
                kind == Diagnostic.Kind.ERROR ? ProblemSeverities.Error :
                    kind == Diagnostic.Kind.WARNING ? ProblemSeverities.Warning :
                        kind == Diagnostic.Kind.MANDATORY_WARNING ? ProblemSeverities.Error : // FIXME - should we be able to screen these out?
                            kind == Diagnostic.Kind.NOTE ? ProblemSeverities.Warning : // FIXME - would like this to be a different kind
                                kind == Diagnostic.Kind.OTHER ? ProblemSeverities.Warning : // FIXME - would like this to be a different kind
                                    ProblemSeverities.Error; // There should not be anything else, but we'll call it an error just in case.

            long pos = diagnostic.getPosition();
            long col = diagnostic.getColumnNumber();// 1-based, from beginning of line
            long line = diagnostic.getLineNumber(); // 1-based
            long startPos = diagnostic.getStartPosition();  //0-based, from beginning of file
            long endPos = diagnostic.getEndPosition();

            int ENOPOS = -1; // Eclipse value for not having position information

            long startPosition = pos == Diagnostic.NOPOS ? ENOPOS : (startPos-pos) + col; // FIXME - a hack - what if crosses lines
            long endPosition = pos == Diagnostic.NOPOS ? ENOPOS : (endPos-pos) + col; // FIXME - a hack - what if crosses lines

            long lineStart = pos == Diagnostic.NOPOS ? ENOPOS : (pos - col); // FIXME - a hack
            long lineEnd = pos == Diagnostic.NOPOS ? ENOPOS : lineStart + 100; // FIXME - a real hack

            IWorkspace workspace = ResourcesPlugin.getWorkspace();
            IWorkspaceRoot root = workspace.getRoot();
            IResource resource = null;
            if (j != null) { // if null, there is no source file
                String filename = j.toString(); // This should be the full, absolute path 
                IPath path = new Path(filename);
                resource = root.getFileForLocation(path); // For this to be non-null, 
                // the file must be in the workspace.  This means that all
                // source AND SPECS must be in open projects in the workspace.
            }

            if (resource == null) {
                // FIXME - associate with project?
                if (severity == ProblemSeverities.Error) Log.errorlog(diagnostic.toString(),null);
                else Log.log(diagnostic.toString());
            } else {
                JmlEclipseProblem problem = new JmlEclipseProblem((IFile)resource, message, id,  severity,
                        (int)startPosition, (int)endPosition, (int)line, null, // No source text avaialble? FIXME
                        (int)lineStart, (int)lineEnd);

                preq.acceptProblem(problem);
                // Log it as well - FIXME - control this with verbosity
                if (severity == ProblemSeverities.Error) Log.errorlog(diagnostic.toString(),null);
                else Log.log(diagnostic.toString());
            }
        }

    }

    public static class UIProgressReporter implements org.jmlspecs.openjml.Main.IProgressReporter {
        IProgressMonitor monitor;
        Context context;
        Shell shell = null;
        
        public UIProgressReporter(Context context, IProgressMonitor monitor, Shell shell) {
            this.monitor = monitor;
            this.context = context;
            this.shell = shell;
        }
        
        //JAVA16 @Override
        public boolean report(final int ticks, final int level, final String message) {
            Display d = shell == null ? Display.getDefault() : shell.getDisplay();
            d.asyncExec(new Runnable() {
                public void run() {
                    // FIXME - it seems that for a level==1, when both a Log message
                    // and a monitor subTask message are desired, only the Log message
                    // appears.
                    if (monitor != null) monitor.subTask(message);
                    if (level <= 1) Log.log(message);
                }
            });
            return monitor != null && monitor.isCanceled();
        }
        
        //JAVA16 @Override
        public void setContext(Context context) { this.context = context; }
    }

    //    /**
    //     * This is a factory class that produces a new Jml parser of one of
    //     * the implemented parsers.  As of this writing, there are two: an ANTLR-generated
    //     * parser and a hand-crafted parser.
    //     */
    //    public static class Factory {
    //
    //        /** An enum giving keys for the kinds of parsers */
    //        public enum Mode { 
    //            /** The hand-crafted parser */
    //            CUSTOM, 
    //            /** The ANTLR-generated parser */
    //            ANTLR};
    //
    //            /** A field indicating which kind of parser to generate */
    //            static public Mode mode = Mode.CUSTOM;
    //
    //            /** Returns a new parser of the kind indicated by the mode field.
    //             * @param level the version of Java to be parsed (typically Env.Level.JLS1_5)
    //             * @param preq the problem reporter to use to report lexing and parsing errors
    //             * @return a new jml parser
    //             */
    ////            static public IJmlParser newJMLParser(Env.Level level, IProblemRequestor preq) {
    ////                return newJMLParser(mode,level,preq);
    ////            }
    //            /** Returns a new parser of the kind indicated by the mode field.
    //             * @param m the kind of parser to produce
    //             * @param level the version of Java to be parsed (typically Env.Level.JLS1_5)
    //             * @param preq the problem reporter to use to report lexing and parsing errors
    //             * @return a new jml parser
    //             */
    ////            static public IJmlParser newJMLParser(Mode m, Env.Level level, IProblemRequestor preq) {
    ////                //      if (m == Mode.CUSTOM) {
    ////                //        return new org.jmlspecs.eclipse.customparser.JmlParser(level,preq);
    ////                //      } else {
    ////                //        return new org.jmlspecs.eclipse.antlrparser.JmlParser(level,preq);
    ////                //      }  // OLDFIXME
    ////                return null;
    ////            }
    //    }

    /** The project information */
    final private ProjectInfo pi;

    //    /** The Eclipse parser to use to parse Java */
    //    private ASTParser parser;
    //
    //    /** The JML parser to use to parse JML comments */
    ////    private IJmlParser jmlparser;

    /** The problem requestor that translates problem location information
     * from a modified file back to the original source locations.
     */
    //@ non_null
    static private JmlProblemRequestor preq = JMLBuilder.preq;

    //    /** The problem requestor that prints information about JML problems
    //     * that are reported.
    //     */
    //    //@ non_null
    //    //static protected JmlProblemRequestor userpreq = null;
    //    // OLDFIXME - sort out the staticness of this field and of parseJmlSpecifications and the filterComment methods


    /** The constructor, which initializes all of the fields of the object.
     *
     * @param pi The information about the context of the files to be checked
     */
    public OpenJMLInterface(/*@ non_null */ ProjectInfo pi) {
        //    userpreq = (JmlProblemRequestor)pi.problemRequestor;
        //    preq = new TranslatingProblemRequestor(userpreq);
        this.pi = pi;
        preq = pi==null? null : (JmlProblemRequestor)pi.problemRequestor;
        //    parser = ASTParser.newParser(Env.astLevel);
        //    jmlparser = Factory.newJMLParser(Env.jlsLevel, preq);
    }



    //    /** This saves the CUInfo argument in a map, keyed against the instance of the
    //     * working copy, to be3 retrieved via getInfo or getNNInfo
    //     * @param cuinfo the argument to be stored
    //     */
    //    private void putMap(CUInfo cuinfo) {
    ////        if (cuinfo.workingCopy != null) pi.cumap.put(cuinfo.workingCopy,cuinfo);
    ////        if (cuinfo.file != null) pi.resmap.put(cuinfo.file,cuinfo);
    //    }

    /** Retrieves from the cache the instance of a CUInfo object with the given
     * compilation unit as key (or its working copy version); if there is none a new
     * CUInfo object is created and initialized for this compilation unit. 
     * @param icu the compilation unit to use as key
     * @return the corresponding CUInfo object
     */
    //    private CUInfo getNNInfo(ICompilationUnit icu) {
    //        ICompilationUnit ncu = icu;
    //        ICompilationUnit wcu = ncu.findWorkingCopy(pi.owner);
    //        if (wcu != null) ncu = wcu;
    //        CUInfo cuinfo = pi.cumap.get(ncu);
    //        if (cuinfo == null) {
    //            cuinfo = new CUInfo();
    //            cuinfo.file = (IFile)icu.getResource();
    //            cuinfo.original = icu;
    //            cuinfo.workingCopy = wcu;
    //            putMap(cuinfo);
    //        }
    //        return cuinfo;
    //    }

    //    /** Retrieves from the cache the instance of a CUInfo object with the given
    //     * compilation unit as the working copy key; if there is none,
    //     * null is returned.  In this call, the argument MUST be the working copy.
    //     * @param workingCopy the compilation unit to use as key
    //     * @return the corresponding CUInfo object
    //     */
    //    private CUInfo getInfo(ICompilationUnit workingCopy) {
    //        CUInfo cuinfo = pi.cumap.get(workingCopy);
    //        return cuinfo;
    //    }

    /** Processes the given set of compilation units, parsing them and
     * producing any error messages caused by bad syntax or semantics.
     * FIXME - no JML checking or rac or jmldoc stuff is done as yet.
     * 
     * @param icus the set of compilation units to parse, created from source files
     * @param monitor the IProgressMonitor on which to report progress and cancellations
     * @throws Exception  ??? FIXME
     */
    public void doProcessing(ICompilationUnit[] icus, IProgressMonitor monitor) throws Exception {
        Options options = pi.options;
        if (options.verbosity > 2) Log.log(Timer.getTimeString() + " parsing...");

        // Make working copies.  Creating a working copy also "opens"
        // the compilation unit, if it has not already been opened.
        // Opening a CU includes parsing the file sufficient to obtain
        // the basic Java structure of the CU - types, field and method
        // signatures, so that inter-CU name resolution can be performed.

        if (options.verbosity > 2) Log.log(Timer.getTimeString() + " Read compilation units");
        if (monitor != null) monitor.subTask("Reading compilation units");

        List<ICompilationUnit> workingCopyList = new ArrayList<ICompilationUnit>(icus.length);
        List<CUInfo> infoList = new ArrayList<CUInfo>(icus.length*2);
        for (ICompilationUnit icu: icus) {
            if (monitor != null) monitor.subTask("Reading compilation units - " + icu.getElementName());
            try {
                ICompilationUnit wcu = icu.getWorkingCopy(pi.owner,preq,null);  // FIXME - what are we supposed to do with problem requestors?
                workingCopyList.add(wcu);
                //                CUInfo cuinfo = new CUInfo();
                //                cuinfo.file = (IFile)icu.getResource();
                //                cuinfo.original = icu;
                //                cuinfo.workingCopy = wcu;
                //                putMap(cuinfo);
                //                infoList.add(cuinfo);
            } catch (Exception e) {
                // FIXME - report properly
                Log.log("Skipping " + icu.getElementName() + " because it does not appear to exist in the file system");
                continue;
            }
            if (monitor != null) {
                monitor.worked(1);
                if (monitor.isCanceled()) {
                    // Discard all of these working copies
                    //          for (ICompilationUnit c: workingCopyList) {
                    //            c.discardWorkingCopy();
                    //          }
                    return;
                }
            }
        }
        org.eclipse.jdt.core.IJavaElement e;
        ICompilationUnit[] workingCopies = workingCopyList.toArray(new ICompilationUnit[workingCopyList.size()]);

        try {
            List<IResource> ics = new java.util.LinkedList<IResource>();
            for (ICompilationUnit icu : workingCopies) {
                ics.add(icu.getResource());
            }
            //                executeExternalCommand(Cmd.CHECK, ics,monitor);
            //              List<CompilationUnit> parsedCUs = parseCUs(workingCopies,monitor);
            //              if (monitor != null && monitor.isCanceled()) return; // see finally block below
            //              getSpecs(infoList,TypeInfo.State.TYPECHECKED,monitor);
            //              if (monitor!=null && monitor.isCanceled()) return; // see finally block below
            //              typeCheck(infoList,parsedCUs,monitor);
        } finally {
            // Any cleanup - but we are not discarding the working copies
            // we want to keep them so that work is not repeated on subsequent
            // calls, and so that type and spec information is available for
            // querying.  However, some sort of cleanup needs to be done 
            // eventually, perhaps manually.  FIXME
        }
    }
    
    public @NonNull List<String> getOptions(IJavaProject jproject, Cmd cmd) {
        List<String> opts = new LinkedList<String>();
        if (cmd == Cmd.ESC) opts.add(JmlOptionName.ESC.optionName());
        if (cmd == Cmd.RAC) opts.add(JmlOptionName.RAC.optionName());
        Options opt = Activator.options;
        if (opt.debug) opts.add(JmlOptionName.JMLDEBUG.optionName());
        // FIXME if (opt.verbosity != 0)  { opts.add(JmlOptionName.JMLVERBOSE.optionName()); opts.add(Integer.toString(opt.verbosity)); }
        if (opt.source != null && opt.source.length()!=0) { opts.add("-source"); opts.add(opt.source); }
        if (cmd != Cmd.JMLDOC && opt.destination != null && opt.destination.length()!=0)  { opts.add("-d"); opts.add(opt.destination); }
        if (!opt.checkPurity) opts.add(JmlOptionName.NOPURITYCHECK.optionName());
        // FIXME if (opt.parsePlus) opts.add(JmlOptionName.PARSEPLUS.optionName());
        if (opt.showNotImplemented) opts.add(JmlOptionName.SHOW_NOT_IMPLEMENTED.optionName());
        // FIXME if (opt.showNotExecutable) opts.add(JmlOptionName.SHOWNOTIMPLEMENTED.optionName());
        if (opt.noInternalSpecs) opts.add(JmlOptionName.NOINTERNALSPECS.optionName());
        if (opt.noInternalRuntime) opts.add(JmlOptionName.NOINTERNALRUNTIME.optionName());
        if (!opt.checkSpecsPath) opts.add(JmlOptionName.NOCHECKSPECSPATH.optionName());
        if (opt.nonnullByDefault) opts.add(JmlOptionName.NONNULLBYDEFAULT.optionName());
        else                      opts.add(JmlOptionName.NULLABLEBYDEFAULT.optionName());
        
        if (cmd == Cmd.JMLDOC) {
            // jmldoc specific options
            opts.add("-private");
        }
        List<String> cpes = utils.getClasspath(jproject);
        boolean first = true;
        StringBuilder ss = new StringBuilder();
        for (String s: cpes) {
            //Log.log("CPE " + s );
            if (first) first = false; else ss.append(java.io.File.pathSeparator);
            ss.append(s);
        }
        opts.add("-classpath");
        opts.add(ss.toString());

        List<File> files = utils.specsPaths.get(jproject);
        first = true;
        ss = new StringBuilder();
        if (files != null) { 
            for (File s: files) {
                //Log.log("CPE " + s );
                if (first) first = false; else ss.append(java.io.File.pathSeparator);
                ss.append(s.toString());
            }
        }
        
        if (lastRun != null) {
            String versionString = System.getProperty("java.version");
            int version = 6; // the current default
            if (versionString.startsWith("1.6")) version = 6;
            else if (versionString.startsWith("1.5")) version = 5;
            else if (versionString.startsWith("1.4")) version = 4;
            else if (versionString.startsWith("1.7")) version = 7;
            else {
                Log.log("Unrecognized version: " + versionString);
                version = 6; // default, if the version string is in an unexpected format
            }

            Bundle specsBundle = Platform.getBundle(Activator.SPECS_PLUGIN_ID);
            if (specsBundle == null) {
                Log.log("No specification plugin " + Activator.SPECS_PLUGIN_ID);
            } else {
                String loc = null;
                try {
                    URL url = FileLocator.toFileURL(specsBundle.getResource(""));
                    File root = new File(url.toURI());
                    loc = root.toString();
                    Log.log("JMLSpecs plugin found " + root + " " + root.exists());
                    String[] defspecs = new String[5]; // null entries OK
                    if (root.isFile()) {
                        // Presume it is a jar or zip file
                        JarFile j = new JarFile(root);
                        JarEntry f = j.getJarEntry("java8");
                        if (version >= 8 && f != null) defspecs[0] = loc + "!java8";
                        f = j.getJarEntry("java7");
                        if (version >= 7 && f != null) defspecs[1] = loc + "!java7";
                        f = j.getJarEntry("java6");
                        if (version >= 6 && f != null) defspecs[2] = loc + "!java6";
                        f = j.getJarEntry("java5");
                        if (version >= 5 && f != null) defspecs[3] = loc + "!java5";
                        f = j.getJarEntry("java4");
                        if (version >= 4 && f != null) defspecs[4] = loc + "!java4";
                    } else if (root.isDirectory()) {
                        // Normal file system directory
                        File f = new File(root,"java8");
                        if (version >= 8 && f.exists()) defspecs[0] = root + "/java8";
                        f = new File(root,"java7");
                        if (version >= 7 && f.exists()) defspecs[1] = root + "/java7";
                        f = new File(root,"java6");
                        if (version >= 6 && f.exists()) defspecs[2] = root + "/java6";
                        f = new File(root,"java5");
                        if (version >= 5 && f.exists()) defspecs[3] = root + "/java5";
                        f = new File(root,"java4");
                        if (version >= 4 && f.exists()) defspecs[4] = root + "/java4";
                    } else {
                        Log.log("Stuff not found in specs bundle at " + root);
                    }
                    for (String z: defspecs) if (z != null) lastRun.setLibrarySpecsPath(defspecs);
                    if (JmlSpecs.externalDefaultSpecs != null) Log.log("Set library specspath defaults from JMLspecs plugin");
                } catch (Exception e) {
                    Log.log("Stuff not found in specs bundle: "+ loc + " " + e);
                }
            }
            Bundle selfBundle = Platform.getBundle(Activator.PLUGIN_ID);
            if (selfBundle == null) {
                Log.log("No self plugin");
            } else {
                String dir = "specs1" + version;
                URL url = selfBundle.getResource("openjml.jar");
                //Log.log("openjml.jar resource? " + url);
                url = selfBundle.getResource(dir);
                //Log.log(dir +" resource? " + url);
                
                if (JmlSpecs.externalDefaultSpecs == null && url != null) {
                    try {
                        url = FileLocator.toFileURL(selfBundle.getResource(""));
                        File root = new File(url.toURI());
                        String loc = root.toString();
                        Log.log(dir + " owner: " + loc);
                        url = FileLocator.toFileURL(selfBundle.getResource(""));
                        root = new File(url.toURI());
                        loc = root.toString();
                        Log.log(dir + ": " + loc);
                        
                    
                    } catch (Exception e) {
                        Log.log("Self plugin with specs directories failed");
                    }
                    
                }
            }
        }

        if (ss.toString().length()!=0) {
            opts.add(JmlOptionName.SPECS.optionName());
            opts.add(ss.toString());
        }
        // specsProjectName
        // roots, nojml, nojavacompiler
        // trace subexpressions counterexample
        // specs , classpath , sourcepath, stopiferrors
        // Java options, Jmldoc options
        return opts;
    }
    
//    public java.util.List<String> getSpecsPath() {
//        return lastRun.getSpecsPath();
//    }
    
    public void setOption(String name, String value) {
        lastRun.setOption(name,value);
    }
    
    public String getBasicBlockProgram(MethodSymbol msym) {
        return lastRun.getBasicBlockProgram(msym);
    }
    
    //    public List<CompilationUnit> parseCUs(ICompilationUnit[] workingCopies, IProgressMonitor monitor) {
    //        // Now create the Java ASTs from the working copies
    //        // Problems are notified through the ProblemRequestor (preq)
    //        // used to create the working copies.
    //        // ASTs are returned through the ASTRequestor below.
    //
    //        final Options options = pi.options;
    //
    //        if (options.verbosity > 2) Log.log(Timer.getTimeString() + " Create and resolve Java ASTs");
    //        if (monitor != null) monitor.subTask("Creating and resolving ASTs");
    //
    //        final List<CompilationUnit> parsedCUs = new LinkedList<CompilationUnit>();
    //        ASTRequestor req = new ASTRequestor() {
    //            public void acceptAST(ICompilationUnit icu, CompilationUnit a) {
    //                //if (options.debug) Log.log("REC'D  " + icu.getResource().getName()); //getLocation().toOSString());
    //                parsedCUs.add(a);
    ////                CUInfo cuinfo = pi.cumap.get(icu);
    ////                if (cuinfo == null) Log.errorlog("Failed to find a CUInfo for " + icu.getElementName(),null);
    ////                else {
    ////                    cuinfo.parsedCU = a;
    ////                }
    //
    //                //        if (options.debugast) {
    //                //          ASTPrinter.print("Java AST",a);
    //                //        } // OLDFIXME
    //
    //                // Problems are reported through the JmlProblemRequestor supplied in
    //                // the creation of the working copy.  That way if the working copy
    //                // is modified and then reconciled, we also get any new errors in the modifications.
    //                // The following code also works for the problems generated in creating 
    //                // the AST (but not the later reconciliation of the AST), if you want
    //                // to look at the problems directly instead of using a callback.
    //                // Log.log("PROBLEMS");
    //                // for (IProblem p: a.getProblems()) preq.acceptProblem(p);
    //            }
    //        };
    //
    //        if (options.verbosity > 2) Log.log(Timer.getTimeString() + " parsing Java code");
    //        if (monitor != null) monitor.subTask("Creating ASTs");
    //        parser.setProject(pi.jproject());
    //        parser.setResolveBindings(true);
    //        IProgressMonitor submon = monitor == null ? null : new SubProgressMonitor(monitor,workingCopies.length);
    //        parser.createASTs(workingCopies,new String[]{},req,submon);
    //        return parsedCUs;
    //    }

    //    public void typeCheck(List<CUInfo> infoList, List<CompilationUnit> parsedCUs, IProgressMonitor monitor) throws Exception {
    //        final Options options = pi.options;
    //
    //        // Although it might make for a more confused order of error messages,
    //        // we do all the Java parsing and then the JML parsing, because 
    //        // Eclipse is set up to be more efficient when all the Java typechecking
    //        // is done at once.
    //
    //        try {
    //
    //            // Now parse the JML specifications and insert them into the Eclipse AST
    //
    //            if (options.verbosity > 2) Log.log(Timer.getTimeString() + " parsing JML specifications");
    //            if (monitor != null) monitor.subTask("Parsing JML specs");
    //
    //            IJmlParser jmlparser = Factory.newJMLParser(Env.jlsLevel, preq);
    //            for (CUInfo cuinfo: infoList) {
    //                if (!cuinfo.specsInserted) {
    //                    if (monitor != null) monitor.subTask("Parsing JML specs - " + cuinfo.parsedCU.getJavaElement().getElementName());
    //                    // OLDFIXME - we really want to only do the implementation specs
    //                    parseJmlSpecifications(null, jmlparser, cuinfo.parsedCU);
    //                    cuinfo.specsInserted = true;
    //                }
    //                if (monitor != null) {
    //                    monitor.worked(1);
    //                    if (monitor.isCanceled()) return; // see finally block below
    //                }
    //                ICompilationUnit workingCopy = cuinfo.workingCopy;
    //                for (IType it: workingCopy.getTypes()) {
    //                    TypeInfo t = pi.types.findTypeInfo(it);
    //                    if (t == null) pi.types.putTypeInfo(t = new TypeInfo(it));  // OLDFIXME - this line and constructor are dubious
    //                    t.cuinfo = cuinfo;
    //                    t.state = TypeInfo.State.TYPE_ONLY;
    //                }
    //            }
    //
    //            // Now resolve all names and types, first for all signatures and
    //            // (the bodies need all the signatures successfully resolved before any
    //            //  body typechecking can be started)
    //            if (options.verbosity > 2) Log.log(Timer.getTimeString() + " resolving JML signatures");
    //            for (CompilationUnit cu : parsedCUs) {
    //                if (monitor != null) monitor.subTask("Resolving JML signatures - " + cu.getJavaElement().getElementName());
    //                JmlNameTypeResolverE.resolve(cu,pi,true);
    //                if (monitor != null) {
    //                    monitor.worked(1);
    //                    if (monitor.isCanceled()) return; // see finally block below
    //                }
    //            }
    //
    //
    //            if (options.verbosity > 2) Log.log(Timer.getTimeString() + " resolving JML bodies");
    //            for (CompilationUnit cu : parsedCUs) {
    //                if (monitor != null) monitor.subTask("Resolving JML bodies - " + cu.getJavaElement().getElementName());
    //                JmlNameTypeResolverE.resolve(cu,pi,false);
    //                if (monitor != null) {
    //                    monitor.worked(1);
    //                    if (monitor.isCanceled()) return; // see finally block below
    //                }
    //                ICompilationUnit icu = (ICompilationUnit)cu.getJavaElement();
    //                for (IType tt: icu.getTypes()) {
    //                    TypeInfo ti = pi.types.findNNTypeInfo(tt);
    //                    ti.state = TypeInfo.State.TYPECHECKED;
    //                }
    //            }
    //
    //        } finally {
    //            // OLDFIXME - when using this in the UI, do we really want to discard
    //            // the working copies?  Won't we want to reuse them?
    //
    //            // Discard working copies
    //            //      for (ICompilationUnit wcu : workingCopies) {
    //            //        wcu.discardWorkingCopy();
    //            //      }
    //
    //            if (options.verbosity > 2) {
    //                boolean c = monitor != null && monitor.isCanceled();
    //                Log.log(Timer.getTimeString() + (!c ? " parsing completed": " parsing cancelled"));
    //            }
    //        }
    //        return;
    //
    //
    //        //  if (options.verbosity > 2) Log.log("constructing JML ASTs");
    //
    //        //  // Construct the Jml version of the ASTs
    //        //  final Map<String,org.jmlspecs.eclipse.jmldom.CompilationUnit> fileToJmlASTMap = new HashMap<String,org.jmlspecs.eclipse.jmldom.CompilationUnit>();
    //        //  oldToJmlASTNodeMap = new HashMap<org.eclipse.jdt.core.dom.ASTNode, org.jmlspecs.eclipse.jmldom.ASTNode>();
    //        //  JmlParser jmlparser = new JmlParser(jlsLevel, preq);
    //        //  org.jmlspecs.eclipse.jmldom.AST ast = org.jmlspecs.eclipse.jmldom.AST.newAST(astLevel);
    //        //  List<org.jmlspecs.eclipse.jmldom.CompilationUnit> jmlcus = new LinkedList<org.jmlspecs.eclipse.jmldom.CompilationUnit>();
    //        //  for (CompilationUnit cu : parsedCUs) {
    //        //  ICompilationUnit icu = null;
    //        //  try {
    //        //  org.jmlspecs.eclipse.jmldom.CompilationUnit jmlcu = (org.jmlspecs.eclipse.jmldom.CompilationUnit)JmlASTCopier.eclipseToJmlAST(ast,cu);
    //        //  icu = (ICompilationUnit)(cu.getJavaElement());
    //        //  jmlcu.setOriginalSource(icu.getSource()); // also sets the lineEnd information
    //
    //        //  //JmlASTPrinter.print("JML AST-BEFORE",jmlcu);
    //        //  //Log.log("RES " + icu.getResource().getLocation().toOSString());
    //        //  jmlparser.setSource(jmlcu); // sets the scanner source
    //        //  List<Comment> comments = (List<Comment>)cu.getCommentList();
    //        //  JmlSpecInserterOLD.insert(ast,jmlcu,jmlparser,filterComments(comments,icu.getSource()),userpreq);
    //
    //        //  if (options.debugast) {
    //        //  JmlASTPrinter.print("JML AST",jmlcu);
    //        //  }
    //        //  jmlcus.add(jmlcu);
    //        //  //if (options.debug) Log.log("ADDED MAPPING FOR " + cu.getJavaElement().getResource().getFullPath());
    //        //  fileToJmlASTMap.put(cu.getJavaElement().getResource().getFullPath().toString() ,jmlcu);
    //
    //        //  // Check and parse the specs (especially the method specs):
    //
    //        ////org.jmlspecs.eclipse.jmlast.JmlSpecCollect.collect(jmlcu,preq);
    //        //  } catch (Exception e) {
    //        //  // OLDFIXME - use a problem report; should we continue with other files?
    //        //  Log.log("EXCEPTION while processing " + icu.getResource().getLocation().toOSString());
    //        //  throw e;
    //        //  }
    //
    //        //  }
    //        //  parsedCUs.clear();
    //
    //        //  {
    //        //  if (options.verbosity > 2) Log.log("Resolving type signatures...");
    //        //  int i=0;
    //        //  for (org.jmlspecs.eclipse.jmldom.CompilationUnit jmlcu : jmlcus) {
    //        //  JmlNameTypeResolver.resolve(jmlcu,true,pi);
    //        //  if (options.verbosity > 2) {
    //        //  Log.log_noln("."); i++;
    //        //  if ((i%80)==0) Log.log("");
    //        //  }
    //        //  }
    //        //  if (options.verbosity > 2 && ((i%80)!=0)) Log.log("");
    //        //  }
    //        //  {
    //        //  if (options.verbosity > 2) Log.log("Typechecking...");
    //        //  int i=0;
    //        //  for (org.jmlspecs.eclipse.jmldom.CompilationUnit jmlcu : jmlcus) {
    //        ////ICompilationUnit u = (ICompilationUnit)((CompilationUnit)jmlcu.oldNode).getJavaElement();
    //        ////if (u != null) {
    //        ////Log.log(u.findPrimaryType().getElementName());
    //        ////}
    //        //  JmlNameTypeResolver.resolve(jmlcu,false,pi);
    //        //  if (options.verbosity > 2) {
    //        //  Log.log_noln("."); i++;
    //        //  if ((i%80)==0) Log.log("");
    //        //  }
    //        //  }
    //        //  if (options.verbosity > 2 && ((i%80)!=0)) Log.log("");
    //        //  }
    //
    //        //  if (options.verbosity > 2) Log.log("checking completed");
    //        //  if (true) {
    //        //  return;
    //        //  }
    //
    //        //  // Construct an Eclipse version from which we can extract binding
    //        //  // information on the JML constructs.  The modify() call also
    //        //  // produces the revised source code and sets it into the 
    //        //  // corresponding workingCopy
    //
    //        //  for (org.jmlspecs.eclipse.jmldom.CompilationUnit jmlcu : jmlcus) {
    //        //  String newsource = modify(jmlcu, oldToJmlASTNodeMap);
    //        //  if (options.debug) Log.log(newsource);
    //        //  if (options.debugast) {
    //        //  ASTPrinter.print("MODIFIED AST",jmlcu.oldNode);
    //        //  }
    //        //  }
    //
    //        //  // Note that we need to have all compilation units modified before
    //        //  // reconciliation because files may refer to ghost/model variables
    //        //  // or methods or types in other compilation units (so those need to
    //        //  // be modified).  We actually need all files with specs to have 
    //        //  // generated revised type declarations.
    //        //  // OLDFIXME - need to generate revised CUs for all specs
    //
    //        //  if (options.verbosity > 2) Log.log("typechecking JML");
    //
    //        //  // We have made all the modifications, so now reconcile.
    //        //  // The problems generated from this step are with respect to
    //        //  // the new source, which the user does not see, so
    //        //  // although the problem report will print out sensibly, the line
    //        //  // number and the text of the source are not directly useful.
    //        //  // The problems need to be translated back to the original source.
    //        //  // We do that by figuring out what node in the new tree is
    //        //  // associated with the error, mapping back to the same node in the
    //        //  // original tree (as modified), figuring out the new source positions
    //        //  // with respect to the original source.  However, we cannot do the
    //        //  // node mapping until the reconciled ASTs are produced, so we hold
    //        //  // all problem reports until we have the data to do the translation.
    //
    //        //  // Recap on the different ASTs:
    //        //  // 1) We generated an Eclipse AST (A) based on the Java source and
    //        //  // resolved all bindings.
    //        //  // 2) We copied that to produce a JML AST (B) to which we added 
    //        //  // nodes for the JML constructs.  Each node of B contains references
    //        //  // back to corresponding nodes of A (the oldNode field).
    //        //  // 3) We altered AST A based on the JML constructs in B.
    //        //  // 4) We used the modified A to generate new source code, that
    //        //  // we then set into the working copy of the buffer.
    //        //  // 5) We are about to reconcile the working copy, generating 
    //        //  // a new AST (C) with new type bindings.
    //
    //        //  // To map from jml nodes in B to nodes in A use the oldNode field
    //        //  // To map from nodes in A to nodes in B, use the oldToJmlASTNodeMap map
    //        //  // In the compare step below, we fill in the newNode field that maps from B to C
    //        //  // We also generate the newToJmlASTNodeMap that maps from C nodes to B nodes. 
    //        //  // To get the working copy from a jml CompiliationUnit:
    //        //  //       workingcopy = jmlCU.oldNode.getJavaElement()
    //
    //        //  // Some issues:
    //        //  // - ASTs A and C ought to have the same structure, but C has all the
    //        //  // new bindings and A has references from the JML AST B.
    //        //  // - If there are naming conflicts between JML and Java then the
    //        //  // interpretations of some names in the Java code might change.  We
    //        //  // need to handle this (OLDFIXME) but don't yet.  We can check that this
    //        //  // does not happen, however.
    //
    //        //  preq.ignore();
    //
    //        //  // We can only reconcile working copies one at a time.  So it can
    //        //  // happen that working copy A does not see a change in working copy B since
    //        //  // B has not yet been reconciled.  So we need to run through the
    //        //  // reconciliation list twice, but only need to get ASTs and problem
    //        //  // reports the second time.  I though that utilizing a working copy
    //        //  // owner was supposed to avoid this problem. (OLDFIXME)
    //        //  // What we actually do is call makeConsistent the first time.  (The docs
    //        //  // have a warning about this, but it works ok, though a reconcile operation
    //        //  // works also; it seems the makeCOnsistent ought to be faster but this has
    //        //  // not been measured - OLDTODO).  makeCOnsistent does essentially re-open
    //        //  // the ocmpilation unit, but does not appear to do so recursively.  It also
    //        //  // does produce problem reports.  Since there are extraneous problem reports,
    //        //  // because not all CUs are consistent, we ignore the reports from this pass.
    //        //  // The we reconcile all CUs and report the problems at the end.
    //        //  // (OLDTODO - if we knew dependencies, would it be worth optimizing this?)
    //
    //        //  List<CompilationUnit> newasts = new LinkedList<CompilationUnit>();
    //        //  for (ICompilationUnit wcu : workingCopies) {
    //        //  if (options.debug) Log.log("ReconcilingA " + wcu.getResource().getFullPath());
    //        //  wcu.makeConsistent(null);
    //        //  //wcu.reconcile(astLevel, false, owner, null);
    //        //  }
    //        //  //preq.hold();
    //        //  for (ICompilationUnit wcu : workingCopies) {
    //        //  if (options.debug) Log.log("ReconcilingB " + wcu.getResource().getFullPath());
    //        //  CompilationUnit ncu = wcu.reconcile(astLevel, true, pi.owner, null);
    //        //  newasts.add(ncu);
    //        //  if (options.debugast) {
    //        //  ASTPrinter.print("RECONCILED AST",ncu);
    //        //  }
    //        //  }
    //
    //        //  // Comparing A and C for good measure and to generate
    //        //  // the node mapping needed to translate problem reports
    //        //  if (options.verbosity > 2) Log.log("comparing ASTs");
    //
    //        //  Map<org.eclipse.jdt.core.dom.ASTNode, org.jmlspecs.eclipse.jmldom.ASTNode> newToJmlASTNodeMap =
    //        //  new HashMap<org.eclipse.jdt.core.dom.ASTNode, org.jmlspecs.eclipse.jmldom.ASTNode>();
    //
    //        //  Iterator<org.jmlspecs.eclipse.jmldom.CompilationUnit> jmli = jmlcus.iterator();
    //        //  Iterator<CompilationUnit> newi = newasts.iterator();
    //        //  while (jmli.hasNext()) {
    //        //  org.jmlspecs.eclipse.jmldom.CompilationUnit jmlast = jmli.next();
    //        //  org.eclipse.jdt.core.dom.CompilationUnit newcu = newi.next();
    //        //  boolean b = compare(jmlast.oldNode,newcu,newToJmlASTNodeMap);
    //        //  if (!b) Log.log("INTERNAL ERROR - tree comparison failure"); // OLDFIXME
    //        //  // OLDFIXME
    //        //  if (!(((org.eclipse.jdt.core.dom.CompilationUnit)jmlast.oldNode).getJavaElement() == newcu.getJavaElement()))
    //        //  Log.log("WCU match: " +
    //        //  (((org.eclipse.jdt.core.dom.CompilationUnit)jmlast.oldNode).getJavaElement() == newcu.getJavaElement()));
    //
    //
    //        //  }
    //        //  preq.translate(newToJmlASTNodeMap,fileToJmlASTMap);
    //        ////preq.printProblems();
    //        //  preq.release();
    //        //  if (options.debug) Log.log("Fetch problems");
    //        //  for (CompilationUnit newast : newasts) {
    //        //  for (IProblem p : newast.getProblems()) {
    //        //  preq.acceptProblem(p);
    //        //  }
    //        //  }
    //        //  preq.translate(null,null);
    //
    //
    //        //  // Now resolve types for the JML tree
    //        //  if (options.verbosity > 2) Log.log("resolving types");
    //
    //        //  for (org.jmlspecs.eclipse.jmldom.CompilationUnit jmlcu : jmlcus) {
    //        //  JmlNameTypeResolver.resolve(jmlcu,false,pi);
    //        //  //JmlTypeResolver.resolveTypes(jmlcu,preq);
    //        //  }
    //
    //        ////if (options.rac) {
    //        ////if (options.verbosity > 2) Log.log("building");
    //
    //        //////    Commit changes to disk (in the racsources location)
    //
    //        ////for (ICompilationUnit wcu : workingCopies) {
    //        ////wcu.commitWorkingCopy(true,null);
    //        ////}
    //
    //        ////// Do the build
    //
    //        ////IProgressMonitor myProgressMonitor = null;
    //        ////project.build(IncrementalProjectBuilder.FULL_BUILD, myProgressMonitor);
    //
    //        ////}
    //
    //        //  // Discard working copies
    //        //  for (ICompilationUnit wcu : workingCopies) {
    //        //  wcu.discardWorkingCopy();
    //        //  }
    //
    //        //  if (options.verbosity > 2) Log.log("checking completed");

    //   }


    /** OLDFIXME
     * @param code
     * @param jmlparser
     * @param cu
     * @throws Exception
     */
    //    public void parseJmlSpecifications(String code, IJmlParser jmlparser, CompilationUnit cu) throws Exception {
    //        // OLDFIXME    org.jmlspecs.eclipse.jmldom.AST ast = jmlparser.AST();
    //        ICompilationUnit icu = null;
    //        try {
    //            // In normal use, cu is associated with an ICompilationUnit, from which
    //            // we can get the source code, and this method is then called with code=null.  
    //            // However, for testing, where the code comes from a String and not a file,
    //            // we supply the code string explicitly.
    //            if (code == null) {
    //                icu = (ICompilationUnit)cu.getJavaElement();
    //                jmlparser.setSource(icu); // sets the scanner source
    //                jmlparser.setLineEnds(null); // This determines the line end
    //                // information from the source set in the previous line
    //                code = icu.getSource();
    //            }
    //            List<Comment> comments = cu.getCommentList();
    //            // OLDFIXME      JmlSpecInserterE.insert(ast,cu,jmlparser,filterComments(comments,code),preq);
    //        } catch (Exception e) {
    //            JmlEclipseProblem.report(preq,cu,
    //                    cu.getStartPosition(),cu.getStartPosition()+cu.getLength()-1,Problems.UNEXPECTED_EXCEPTION,e.getMessage());
    //            if (icu != null) Log.errorlog("Unexpected exception while parsing JML comments in " + icu.getResource().getLocation().toOSString(),e);
    //            else Log.errorlog("Unexpected exception while parsing JML comments",e);
    //        }
    //        //JmlASTPrinterE.print("AST WITH SPECS",cu,specs);
    //    }


    //public String modify(org.jmlspecs.eclipse.jmldom.CompilationUnit jmlast, Map<org.eclipse.jdt.core.dom.ASTNode, org.jmlspecs.eclipse.jmldom.ASTNode> oldToJmlASTNodeMap ) throws Exception {
    //org.eclipse.jdt.core.dom.CompilationUnit originalAST = (org.eclipse.jdt.core.dom.CompilationUnit)(jmlast.oldNode);
    //ICompilationUnit wcu = (ICompilationUnit)originalAST.getJavaElement();

    //// OLDFIXME - Eclipse recommends using the rewrite API

    //// modify the AST
    //JmlASTCopier.jmlToEclipseAST(jmlast,oldToJmlASTNodeMap);

    ////Log.log("MODIFIED \n" + org.jmlspecs.eclipse.jmlast.oldNode.toString());

    //String newSource = org.jmlspecs.eclipse.eclipseast.ASTCodeWriter.generateCode(jmlast.oldNode);

    //// update of the compilation unit
    //wcu.getBuffer().setContents(newSource);

    //return newSource;
    //}


    //public boolean compare(org.eclipse.jdt.core.dom.ASTNode oldnode,
    //org.eclipse.jdt.core.dom.ASTNode newnode,
    //Map<org.eclipse.jdt.core.dom.ASTNode, org.jmlspecs.eclipse.jmldom.ASTNode> map) {
    //if (oldnode.getNodeType() != newnode.getNodeType()) {
    //Log.log("MISMATCHED NODES "+ oldnode.getClass() + " vs. " + newnode.getClass());
    //Log.log("   Positions " + oldnode.getStartPosition() + " " + newnode.getStartPosition());
    //return false;
    //}
    //org.jmlspecs.eclipse.jmldom.ASTNode jmlNode = oldToJmlASTNodeMap.get(oldnode);
    //map.put(newnode, jmlNode);
    //if (jmlNode != null) jmlNode.newNode = newnode;
    //boolean result = true;
    //Iterator<ASTNode> oldchildren = org.jmlspecs.eclipse.eclipseast.ASTChildrenVisitor.getChildren(oldnode).iterator();
    //Iterator<ASTNode> newchildren = org.jmlspecs.eclipse.eclipseast.ASTChildrenVisitor.getChildren(newnode).iterator();
    //while (oldchildren.hasNext() && newchildren.hasNext()) {
    //org.eclipse.jdt.core.dom.ASTNode oldchild = oldchildren.next();
    //org.eclipse.jdt.core.dom.ASTNode newchild = newchildren.next();
    //result = compare(oldchild,newchild,map) && result;
    //}
    //return result;
    //}

    // OLDFIXME - this can be simplified; it may still be
    // needed to report problems in rac compiles - though
    // there should not be any rac compile errors if the Java
    // and JML both typecheck correctly.
    // (what is really needed is to insert the old line numbers
    // into the new rac class files, so that exception traces are
    // understandable).
    static class TranslatingProblemRequestor extends JmlProblemRequestor {
        public TranslatingProblemRequestor(JmlProblemRequestor pr) {
            userpreq = pr;
        }
        private JmlProblemRequestor userpreq;
        private boolean hold = false;
        private boolean ignore = false;
        private List<IProblem> list = new LinkedList<IProblem>();
        // OLDFIXME   private Map<String,org.jmlspecs.eclipse.jmldom.CompilationUnit> toJmlASTMap;
        //    private Map<org.eclipse.jdt.core.dom.ASTNode,org.jmlspecs.eclipse.jmldom.ASTNode> nodeMap;
        public void acceptProblem(IProblem p) {
            if (ignore) {
                //if (options.debug) Log.log("IGNORING PROBLEM " + (p.getID() & IProblem.IgnoreCategoriesMask) + " " + String.valueOf(p.getOriginatingFileName()));
                // skip
            } else if (!hold) {
                int st = p.getSourceStart();
                int en = p.getSourceEnd();
                int ln = p.getSourceLineNumber();
                try {
                    translateProblem(p);
                    userpreq.acceptProblem(p);
                } catch (Exception e) {
                    e.printStackTrace();
                    String s = "Failed during translation and printing of a problem." +
                    " Was st = " + st + ", en = " + en + ", line = " + ln + "; " +
                    " Now st = " + p.getSourceStart() + ", en = " + p.getSourceEnd() + ", line = " + p.getSourceLineNumber();
                    Log.log(s);
                    Log.log(p.getMessage());
                }
            } else {
                //if (options.debug) Log.log("CACHING PROBLEM " + String.valueOf(p.getOriginatingFileName()));
                list.add(p);
            }
        }
        //    public void translate(Map<org.eclipse.jdt.core.dom.ASTNode,org.jmlspecs.eclipse.jmldom.ASTNode> map,
        //            Map<String,org.jmlspecs.eclipse.jmldom.CompilationUnit> toJmlASTMap) {
        //      this.toJmlASTMap = toJmlASTMap;
        //      this.nodeMap = map;
        //    }
        public void clear() { list.clear(); }
        public void ignore() { ignore = true; }
        public void hold() { hold = true; ignore = false; }
        public void release() {
            if (!list.isEmpty()) {
                Log.log(list.size() + " ITEMS STILL TO PRINT"); // FIXME
                for (IProblem p : list) {
                    userpreq.acceptProblem(p);
                }
                list.clear();
            }
            hold = false; 
            ignore = false;
        }
        public void printProblems() {
            Iterator<IProblem> i = list.iterator();
            while (i.hasNext()) {
                IProblem p = i.next();
                boolean done = false;
                try {
                    done = translateProblem(p);
                    userpreq.acceptProblem(p);
                } catch (Exception e) {
                    // continue.  This is just here for safety's sake, in case
                    // something goes wrong with the above computation.  At
                    // least any remaining problems will be reported
                    Log.log(Env.eol + "Error in printing " + e);
                    p.setSourceStart(-1);
                    p.setSourceEnd(-1);
                    p.setSourceLineNumber(-1);
                    userpreq.acceptProblem(p);
                    done = true;
                }
                if (done) i.remove();
            }
        }

        private boolean translateProblem(IProblem p) {
            //      if (nodeMap == null) return true;
            //      String s = String.valueOf(p.getOriginatingFileName());
            //      org.jmlspecs.eclipse.jmldom.CompilationUnit jmlcu = toJmlASTMap.get(s);
            //      ASTNode newAST = jmlcu.newNode;
            //      if (newAST != null) {
            //        try {
            //          int oldstart = p.getSourceStart();
            //          int oldend = p.getSourceEnd();
            //          if (oldstart >= 0) {
            //            int jmlstart = translate(oldstart,nodeMap,newAST);
            //            int jmlend = translate(oldend,nodeMap,newAST);
            //            p.setSourceStart(jmlstart);
            //            p.setSourceEnd(jmlend);
            //            p.setSourceLineNumber(jmlcu.lineNumber(jmlstart));
            //          }
            //        } catch (Exception e) {
            //          // continue.  This is just here for safety's sake, in case
            //          // something goes wrong with the above computation.  At
            //          // least any remaining problems will be reported
            //          Log.log(Env.eol + "Error in printing " + e);
            //          p.setSourceStart(-1);
            //          p.setSourceEnd(-1);
            //          p.setSourceLineNumber(-1);
            //        }
            //      } else {
            //        Log.log("NO AST MATCH");  // OLDFIXME
            //        return false;
            //      }
            return true;
        }

        //    private int translate(int position, Map<org.eclipse.jdt.core.dom.ASTNode,org.jmlspecs.eclipse.jmldom.ASTNode> map,
        //            org.eclipse.jdt.core.dom.ASTNode eclipseTop) {
        //      ASTLocator locator = ASTLocator.find(position,eclipseTop);
        //      int jmlPosition=-1;
        //      org.jmlspecs.eclipse.jmldom.ASTNode pNode;
        //      org.eclipse.jdt.core.dom.ASTNode parentnode = locator.getParentNode();
        //      org.eclipse.jdt.core.dom.ASTNode oldnode;
        //      int parentstart = parentnode.getStartPosition();
        //      int parentend = parentstart + parentnode.getLength() -1;
        //      if (position == parentstart) {
        //        pNode = map.get(parentnode);
        //        if (pNode == null) return -1;
        //        jmlPosition = pNode.getStartPosition();
        //      } else if (position == parentend) {
        //        pNode = map.get(parentnode);
        //        if (pNode == null) return -1;
        //        jmlPosition = pNode.getEndPosition();
        //      } else if ((oldnode=locator.getPreviousNode()) != null) {
        //        pNode = map.get(oldnode);
        //        if (pNode == null) return -1;
        //        jmlPosition = position-oldnode.getStartPosition()-oldnode.getLength()+1+pNode.getEndPosition();
        //      } else if ((oldnode=locator.getNextNode()) != null) {
        //        pNode = map.get(oldnode);
        //        if (pNode == null) return -1;
        //        jmlPosition = position-oldnode.getStartPosition()+pNode.getStartPosition();
        //      } else {
        //        // in the parent
        //        oldnode = locator.getParentNode();
        //        pNode = map.get(oldnode);
        //        if (pNode == null) return -1;
        //        int offset = position-oldnode.getStartPosition();
        //        if (offset < 0) offset = 0;
        //        if (offset >= pNode.getLength()) offset = pNode.getLength()-1;
        //        jmlPosition = offset+pNode.getStartPosition();
        //      }
        //      return jmlPosition;
        //    }
    }

    /**
     * A helper routine to issue a problem report with explicit start
     * and end positions for the ^^^, a given problem report and arguments;
     * use the more specialized routines for common cases, saving this routine
     * @param node the node that is the source of the problem
     * @param cu the root for that node
     * @param p the problem to report
     * @param arg any arguments to the problem
     */
    //  public void reportProblem(org.jmlspecs.eclipse.jmldom.ASTNode node, org.jmlspecs.eclipse.jmldom.CompilationUnit cu, Problems p, Object... arg) {
    //    JmlEclipseProblem.report(preq,cu,
    //            node.getStartPosition(),node.getEndPosition(),p,arg);
    //  }


    //    /** Filters the comment list according to the return value of
    //     * filterComment.  The comments in the input list are all from the
    //     * file with the given source.  The output is a new list with just the
    //     * retained comments.
    //     * @param list The list of comments from the given source (is not modified)
    //     * @param source The source text of the file from which the comments come
    //     * @return the filtered list of comments
    //     */
    //    static public List<Comment> filterComments(List<Comment> list, String source) {
    //        List<Comment> newlist = new LinkedList<Comment>();
    //        for (Comment c: list) {
    //            if (filterComment(c,source)) newlist.add(c);
    //        }
    //        return newlist;
    //    }

    //    /** Checks to see if the Java comment is one that should be kept -
    //     * it is kept if it is a JML comment, including both +@ and -@ forms.
    //     * @param comment the comment as returned by the Java AST parsing
    //     * @param source the source of the file the comment comes from
    //     * @return true if the comment is to be kept, false otherwise
    //     */
    //    static public boolean filterComment(Comment comment, String source) {
    //        int s = comment.getStartPosition()+2;
    //        if (comment.isDocComment())OLDFIXMErn false; // OLDFIXME - this needs to change for jmldoc
    //        // OLDFIXME - are s and s+1 valid for charAt? even in pathological situations?
    //        char c = source.charAt(s);
    //        boolean b = c == '@' || (source.charAt(s+1) == '@' && (c=='+' || c=='-'));
    //        // OLDFIXME - use options above
    //        return b;
    //    }

    /** This method finds the specs for the given type (and recursively for all
     * constructs within the type), using the refinement files.
     * @param t
     * @param state
     * @param monitor
     * @throws Exception
     */
    //    public void getSpecs(IType t, TypeInfo.State state, IProgressMonitor monitor) throws Exception {
    //        //    if (pi.options.verbosity > 2) Log.log("Requesting " + state + " for " + t);
    //        //    TypeInfo ti = pi.types.findNNTypeInfo(t);
    //        //    if (ti.state.compareTo(state) >= 0) {
    //        //      if (pi.options.verbosity > 2) Log.log("Already have " + ti.state + " for " + t);
    //        //      return;
    //        //    }
    //        //    if (t.isBinary()) {
    //        //      getSuperSpecs(t,TypeInfo.State.JML_SIGNATURE_ONLY,monitor);
    //        //      TypeInfo tti = pi.types.findNNTypeInfo(t);
    //        //      if (tti.state.compareTo(state) < 0) getJMLSpecs(t,monitor);
    //        //      if (state == TypeInfo.State.TYPECHECKED) {
    //        //        Log.errorlog("DID NOT EXPECT TO GET HERE",new Exception());
    //        //      }
    //        //    } else {
    //        //      ICompilationUnit icu = t.getCompilationUnit();
    //        //      CUInfo cuinfo = getNNInfo(icu);
    //        //      getSpecs(cuinfo,state,monitor);
    //        //    }
    //        //    if (pi.options.verbosity > 2) Log.log("Completed " + ti.state + " (requested " + state + ") for " + t);
    //    }
    //
    //    public void getSpecs(ICompilationUnit workingCopy, TypeInfo.State state, IProgressMonitor monitor) throws Exception {
    //        //    CUInfo info = getInfo(workingCopy);
    //        //    for (IType ti: info.workingCopy.getTypes()) {
    //        //      getSuperSpecs(ti,TypeInfo.State.JML_SIGNATURE_ONLY,monitor);
    //        //    }
    //        //    getMySpecs(info,state,monitor);
    //    }
    //
    //    public void getSpecs(List<CUInfo> infoList, TypeInfo.State state, IProgressMonitor monitor) throws Exception {
    //        for (CUInfo info: infoList) {
    //            for (IType ti: info.workingCopy.getTypes()) {
    //                getSuperSpecs(ti,TypeInfo.State.JML_SIGNATURE_ONLY,monitor);
    //            }
    //        }
    //        getMySpecs(infoList,state,monitor);
    //    }
    //
    //    public void getSpecs(CUInfo info, TypeInfo.State state, IProgressMonitor monitor) throws Exception {
    //        for (IType ti: info.workingCopy.getTypes()) {
    //            getSuperSpecs(ti,TypeInfo.State.JML_SIGNATURE_ONLY,monitor);
    //        }
    //        getMySpecs(info,state,monitor);
    //    }
    //
    //    public void getSuperSpecs(IType ti, TypeInfo.State state, IProgressMonitor monitor) throws Exception {
    //        //    if (ti == null || !ti.exists()) return;
    //        //    IType sst = Types.getSuperClass(ti,pi);
    //        //    if (sst != null) getSpecs(sst,state,monitor);
    //        //    
    //        //    for (String ss: ti.getSuperInterfaceNames()) {
    //        //      String[][] ssc = ti.resolveType(ss);
    //        //      if (ssc == null || ssc.length == 0) {
    //        //      // OLDFIXME - need to match to location in file
    //        //        Log.log("Could find no type definition for interface " + ss + " in " + ti);
    //        ////      JmlEclipseProblem.report(pi.preq,cu,
    //        ////              node.getStartPosition(),node.getEndPosition(),p,arg);
    //        //      } else if (ssc.length == 1) {
    //        //        IType st = pi.jproject().findType(ssc[0][0],ssc[0][1]);
    //        //        getSpecs(st,state,monitor);
    //        //      } else {
    //        //        // OLDFIXME - need to match to location in file
    //        //        String msg = "Found multiple type definitions for interface " + ss + " in " + ti + ":";
    //        //        for (int i=0; i<ssc.length; ++i) {
    //        //          msg += " " + ssc[i][0] + "." + ssc[i][1];
    //        //        }
    //        //        Log.log(msg);
    //        ////        JmlEclipseProblem.report(pi.preq,cu,
    //        ////                node.getStartPosition(),node.getEndPosition(),p,arg);
    //        //      }
    //        //    }
    //    }
    //
    //    public void getMySpecs(List<CUInfo> infoList, TypeInfo.State state, IProgressMonitor monitor) throws Exception {
    //        for (CUInfo info: infoList) {
    //            getMySpecs(info,state,monitor);
    //        }
    //    }
    //
    //    public void getMySpecs(CUInfo info, TypeInfo.State state, IProgressMonitor monitor) throws Exception {
    //        //      ICompilationUnit workingCopy = info.workingCopy;
    //        //      IType t = workingCopy.findPrimaryType();
    //        //      if (t == null ){
    //        //        // OLDFIXME - report that there are no types present
    //        //        // can happen if there are no declarations in a file
    //        //        return;
    //        //      }
    //        //      TypeInfo ti = pi.types.findNNTypeInfo(t);
    //        //      if (ti.state.compareTo(state) >= 0) return;
    //        //      // Need to get JML specs
    //        //      getJMLSpecs(info,monitor);
    //    }

    public void getJMLSpecs(IType t, IProgressMonitor monitor) throws Exception {
        //    if (t == null) return;
        //    ICompilationUnit icu = t.getCompilationUnit();
        //    if (icu != null) {
        //      // If the type has a ICompilationUnit, we process it, so all types declared
        //      // in the same compilation unit are processed together
        //      CUInfo cuinfo = getNNInfo(icu);
        //      getJMLSpecs(cuinfo,monitor);
        //      return;
        //    }
        //    // Likely a binary type - still might have spec files for just 
        //    // this type
        //
        //    String typename = t.getElementName();
        //    String packagename = t.getPackageFragment().getElementName();
        //
        //    CUInfo cuinfo = new CUInfo();
        //    cuinfo.packagename = packagename;
        //    cuinfo.primaryTypeName = typename;
        //    cuinfo.primaryType = t;
        //    getJMLSpecs(cuinfo,monitor);
        //    
        //    TypeInfo tyi = pi.types.findNNTypeInfo(t);
        //    tyi.cuinfo = cuinfo;
        //    tyi.state = TypeInfo.State.JML_SIGNATURE_ONLY;
    }

    public void getJMLSpecs(CUInfo cuinfo, IProgressMonitor monitor) throws Exception {
        //    if (cuinfo.packagename == null) {
        //      ICompilationUnit workingCopy = cuinfo.workingCopy;
        //      String typename = workingCopy.getElementName();  // includes the suffix
        //      int i = typename.lastIndexOf(".");
        //      if (i >= 0) typename = typename.substring(0,i); // remove the suffix
        //      IPackageDeclaration[] packages = workingCopy.getPackageDeclarations();
        //      String packagename;
        //      if (packages.length == 1) {
        //        packagename = packages[0].getElementName();
        //      } else if (packages.length == 0) {
        //        packagename = "";
        //      } else {
        //        packagename = packages[0].getElementName();
        //      }
        //      cuinfo.packagename = packagename;
        //      cuinfo.primaryTypeName = typename;
        //    }
        //    getJMLSpecsA(cuinfo,monitor);
        //    
        //    if (cuinfo.workingCopy != null) {
        //      for (IType tt: cuinfo.workingCopy.getTypes()) {
        //        TypeInfo tyi = pi.types.findNNTypeInfo(tt);
        //        tyi.cuinfo = cuinfo;
        //        tyi.state = TypeInfo.State.JML_SIGNATURE_ONLY;
        //      }
        //    } else {
        //      IType tt = cuinfo.primaryType;
        //      TypeInfo tyi = pi.types.findNNTypeInfo(tt);
        //      tyi.cuinfo = cuinfo;
        //      tyi.state = TypeInfo.State.JML_SIGNATURE_ONLY;
        //    }
    }

    //@ requires cuinfo != null;
    //@ requires cuinfo.packagename != null;
    //@ requires cuinfo.primaryTypeName != null;
    public void getJMLSpecsA(CUInfo cuinfo, IProgressMonitor monitor) throws Exception {
        //    // Get the specs file, if any
        //    // if (pi.options.verbosity > 2) Log.log("Getting specs for " + packagename + " " + typename);
        //    cuinfo.specssequence = new LinkedList<IFile>();
        //    cuinfo.specscusequence = new LinkedList<CompilationUnit>();
        //    String packagename = cuinfo.packagename;
        //    String typename = cuinfo.primaryTypeName;
        //    
        //    IFile f = pi.findSpecsLeader(packagename,typename);
        //    if (f == null) {
        //      // OLDFIXME - this means that if there is a java file it is not on the specs path
        //      if (pi.options.verbosity > 2) Log.log("No specs for " + packagename + ":" + typename);
        //      return ;
        //    } else {
        //      if (pi.options.verbosity > 2) Log.log("Specs leader " + f.getFullPath() + " for " + packagename + ":" + typename);
        //    }
        //    // We could use the following line to find the specs leader, it does not search for spec files in the
        //    // right order.  Plus, this call is less efficient.  Since the specsproject does
        //    // not contain class files, we can search it more directly.
        //    //IType rf = pi.specsproject.findType(packagename,typename);
        //    //Log.log("FINDTYPE: " + rf.getCompilationUnit() + " " + rf.getCompilationUnit().getCorrespondingResource());
        //
        //    ICompilationUnit specsicu;
        //    
        //    List<IPath> paths = new ArrayList<IPath>(10);
        //    int maxlength = 20; // This is here just as a check on circular refinement sequences
        //    while (true) {
        //      CompilationUnit specscu;
        //      // Caution: There may be multiple paths to the same physical file.
        //      // These are different resource handles, since resources are compared by
        //      // path.  In particular, the specsProject is a set of links to folders
        //      // and jar files; those folders may be in other projects as well and may be
        //      // in the principal project that the user is working in.  Also the file
        //      // in the editor is associated with a given resource, and confusing 
        //      // behavior can result if the file is manipulated through different resources.
        //      // For example, markers are associated with resources, not with the
        //      // underlying files.
        //      if (cuinfo.file != null && f.getLocation().equals(cuinfo.file.getLocation())) {
        //        // In this case, the resource found on the specspath (and linked into
        //        // the specsproject) refers to the same underlying file as the resource
        //        // generated from the set of files to be compiled/typechecked.  So we
        //        // use the latter.
        //        f = cuinfo.file;
        //        specsicu = cuinfo.workingCopy;
        //        specscu = cuinfo.parsedCU;
        //        if (specscu == null) {
        //          parser.setProject(pi.jproject());
        //          parser.setResolveBindings(true);
        //          parser.setSource(specsicu);
        //          // OLDFIXME - a cancellation can cause an OperationCanceledException from the following operation
        //          specscu = (CompilationUnit)parser.createAST(monitor == null ? null : new SubProgressMonitor(monitor,1));
        //          cuinfo.parsedCU = specscu;
        //        }
        //        cuinfo.inSpecsSequence = true;
        //        if (pi.options.verbosity > 2) Log.log("Found original icu in specs sequence");
        //        cuinfo.specsInserted = true;
        //      } else {
        //        // OLDFIXME - does this give the current working copy, if any?
        //        // OLDFIXME - should we create a working copy?
        //        specsicu = JavaModelManager.createCompilationUnitFrom(f,pi.specsproject);
        //        ICompilationUnit newicu = specsicu.getWorkingCopy(pi.owner,pi.problemRequestor,monitor);
        //        //Log.log("WORKING COPY NULL? " + (newicu==null));
        //        specsicu = (newicu==null ? specsicu : newicu);
        //
        //        if (specsicu == null || !specsicu.exists()) {
        //          String msg = "No compilation unit exists for " + f.getLocation() +
        //          ".  This might be because the suffix is not supported.  It might also be "
        //          + "because the file is not on the classpath of the specs project."
        //          + "  It might also be because the file and Eclipse resource are not in synch.";
        //          JmlEclipseProblem.report(pi.problemRequestor,Problems.INTERNAL_WARNING,  // OLDFIXME - better problem type
        //                  msg);
        //          Log.errorlog(msg,null);
        //          return;
        //        }
        //
        //        parser.setProject(pi.jproject());
        //        parser.setResolveBindings(true);
        //        parser.setSource(specsicu);
        //        // OLDFIXME - a cancellation can cause an OperationCanceledException from the following operation
        //        specscu = (CompilationUnit)parser.createAST(monitor == null ? null : new SubProgressMonitor(monitor,1));
        //      }
        //      if (pi.options.verbosity > 2) Log.log("ABOUT TO CALL parseJmlSpecifications");
        //      parseJmlSpecifications(null, jmlparser, specscu);
        //      
        //      cuinfo.specssequence.add(f);
        //      paths.add(f.getLocation());
        //      cuinfo.specscusequence.add(specscu);
        //      if (cuinfo.specsicu == null) {
        //        // Capture the first ones in the sequence
        //        cuinfo.specsicu = specsicu;
        //        cuinfo.specscu = specscu;
        //      }
        //      
        //      JmlSpecifications.CompUnitSpecs cuspecs = JmlSpecifications.findCUSpecs(specscu);
        //      if (cuspecs == null || cuspecs.refinesDeclaration == null) break; // No more refinements
        //      String refinename = cuspecs.refinesDeclaration.getFileName();
        //      --maxlength;
        //      f = pi.findSpecsFile(packagename,refinename);
        //      if (f == null) {
        //        JmlEclipseProblem.report(pi.problemRequestor,specscu,
        //                cuspecs.refinesDeclaration.getStartPosition(),
        //                cuspecs.refinesDeclaration.getEndPosition(),
        //                Problems.MISSING_REFINEMENT,
        //                cuinfo.specssequence.get(0).getLocation().toOSString(),
        //                cuinfo.specssequence.get(cuinfo.specssequence.size()-1).getLocation().toOSString(),
        //                refinename,
        //                packagename
        //                );
        //        break;
        //      } else if (paths.contains(f.getLocation())) {
        //        // Check whether we have a circular reference
        //        JmlEclipseProblem.report(pi.problemRequestor,specscu,
        //                cuspecs.refinesDeclaration.getStartPosition(),
        //                cuspecs.refinesDeclaration.getEndPosition(),
        //                Problems.CIRCULAR_REFINEMENT,
        //                cuinfo.specssequence.get(0).getLocation().toOSString(),
        //                cuinfo.specssequence.get(cuinfo.specssequence.size()-1).getLocation().toOSString(),
        //                refinename,
        //                packagename
        //                );
        //        break;
        //      } else if (--maxlength <= 0) {
        //        // OLDFIXME - do a JmlEclipseProblem report?
        //        Log.log("Refinement sequence too long");
        //        break;
        //      }
        //    }
        //    if (!cuinfo.inSpecsSequence && cuinfo.workingCopy != null) {
        //      JmlEclipseProblem.report(pi.problemRequestor,cuinfo.parsedCU,
        //              0,
        //              1,
        //              Problems.NOT_IN_REFINEMENT_SEQUENCE,
        //              cuinfo.workingCopy.getElementName(),
        //              cuinfo.specssequence.size() == 0 ?
        //                      "; in fact there are no spec files on the specs path, including this one."
        //                      : (", which begins with " + cuinfo.specssequence.get(0).getLocation().toOSString())
        //              );
        //      // If the .java file (or whatever is on the command-line) is not in the
        //      // refinement sequence, that usually indicates a problem with the specspath
        //      // (though it could also simply be a problem with refines declarations).
        //      // A common issue
        //    }
        //    
        //    // OLDFIXME - for now we presume that there is just one spec file - we 
        //    // follow the refine chain but we don't combine (and check) the specs from
        //    // the various refinements.
        //    
        //    /*
        //     * cuinfo.icu - The ICompilationUnit for the working copy of the Java source or null
        //     * cuinfo.cu - the AST of cuinfo.icu or the appropriate Java class file
        //     * cuinfo.specsicu - The ICompilationUnit for the first specs file parsed, with the
        //     *                  combined specifications in it.  
        //     * cuinfo.specscu - The CompilationUnit for cuinfo.specsicu
        //     * 
        //     * Note that the cu has type bindings resolved but the specscu does not
        //     */
        //    
        //    // We now need to transfer the parsed specs from specscu to the corresponding
        //    // IJavaElements and to the corresponding nodes in cuinfo.parsedCU
        //    
        //    if (cuinfo.workingCopy == null) {
        //      if (pi.options.verbosity > 2) Log.log("No specs stored for compunit " + cuinfo.specsicu.getElementName());
        //    } else {
        //      finalizeCUSpec(cuinfo);
        //      // Note - cuinfo.icu is a working copy, so it does not have a corresponding resource
        //    }
        //    // Copy specs from the cuinfo.specscu AST to the java elements (e.g. IType, IMethod, IField)
        //    // that are part of the ICompilationUnit cuinfo.workingCopy
        //    finalizeTypes(cuinfo,cuinfo.specscu.types());
        //    
        //    // And now we populate the nodes in cuinfo.parsedCU.  This actually overwrites
        //    // the specs previously stored in cuinfo.parsedCU when it was parsed as part
        //    // of the refinement sequence.  [ Do we want to do this?  OLDFIXME]
        //    
        //    //if (cuinfo.parsedCU != null) transferSpecs(cuinfo.specscu,cuinfo.parsedCU);
    }

    public void finalizeCUSpec(CUInfo cuinfo) {
        //    JmlSpecifications.CompUnitSpecs cuspecs = JmlSpecifications.getCUSpecs(cuinfo.specscu);
        //    cuspecs.specssequence = cuinfo.specssequence;
        //    JmlSpecifications.CompUnitSpecs cuspecs2 = JmlSpecifications.getCUSpecs(cuinfo.workingCopy);
        //    if (cuspecs != cuspecs2) {
        //      cuspecs2.specssequence = cuspecs.specssequence;
        //      cuspecs2.modelTypes = cuspecs.modelTypes; // OLDFIXME - really need the combination of all
        //      // Note: cuspecs2.refineDeclaration - do not change
        //      // Note: cuspecs2.modelImports - do not change - each file is resolved against its own imports
        //    }
        //    if (pi.options.verbosity > 2) Log.log("Stored specs for " + cuinfo.workingCopy.getElementName());
        //    // Note - cuinfo.workingCopy is a working copy, so it does not have a corresponding resource
    }

    public void finalizeTypes(CUInfo cuinfo, List list) {
        //    for (Object o: list) {
        //      IType itype = finalizeTypeSpec(cuinfo,(AbstractTypeDeclaration)o,null);
        //      // itype is the IJavaElement corresponding to the AbstractTypeDeclaration o
        //      if (itype != null) finalizeNestedContents(cuinfo,itype,o);
        //    }
    }

    public void finalizeNestedContents(CUInfo cuinfo, IType itype, Object o) {
        //    //if (pi.options.verbosity > 2) Log.log("ifnalizeNestedContents Type: " + itype.getElementName() + " " + o.getClass());
        //    if (o instanceof TypeDeclaration) {
        //      TypeDeclaration td = (TypeDeclaration)o;
        //      for (TypeDeclaration ttd: td.getTypes()) {
        //        IType jtype = finalizeTypeSpec(cuinfo,ttd,itype);
        //        if (jtype != null) finalizeNestedContents(cuinfo,jtype,ttd);
        //      }
        //      for (MethodDeclaration md: td.getMethods()) {
        //        finalizeMethodSpecs(cuinfo,md,itype);
        //      }
        //      for (FieldDeclaration fd: td.getFields()) {
        //        for (Object oo: fd.fragments()) {
        //          VariableDeclarationFragment f = (VariableDeclarationFragment)oo;
        //          finalizeFieldSpecs(cuinfo,fd,f,itype);
        //        }
        //      }
        //
        //    } else if (o instanceof EnumDeclaration) {
        //      // OLDFIXME
        //    } else if (o instanceof AnnotationTypeDeclaration) {
        //      // OLDFIXME
        //    } else {
        //      // OLDFIXME - unknown, unexpected type
        //    }
    }


    //  public IType finalizeTypeSpec(CUInfo cuinfo, AbstractTypeDeclaration specst, IType itype) {
    //    String name = specst.getName().getIdentifier();
    //    IType javat = null;
    //    if (itype != null) {
    //      javat = itype.getType(name);
    //      if (javat == null || !javat.exists()) {
    //        // OLDFIXME - this really should be a JmlEclipseProblem
    //        Log.errorlog("No Java type found to match the specification type " + itype.getFullyQualifiedName() + "." + name,null);  // OLDFIXME - match to location in specs file
    //        return null;
    //     }
    //    } else if (cuinfo.workingCopy != null) {
    //      javat = cuinfo.workingCopy.getType(name);
    //      if (javat == null) {
    //        // OLDFIXME - this really should be a JmlEclipseProblem
    //        Log.errorlog("No Java type found to match the specification type " + name + " in " + cuinfo.workingCopy.getElementName(),null);  // OLDFIXME - match to location in specs file
    //        return null;
    //      }
    //    } else {
    //      // OLDFIXME - can't we get this right out of cuinfo?
    //      PackageDeclaration p = cuinfo.specscu.getPackage();
    //      String pname = p == null ? "" : getPackageDotName(p.getName());
    //      try {
    //        javat = pi.jproject().findType(pname,name);
    //        if (javat == null) {
    //          // OLDFIXME - this really should be a JmlEclipseProblem
    //          Log.errorlog("No Java type found to match the specification type " + pname + "." + name,null);  // OLDFIXME - match to location in specs file
    //          return null;
    //        }
    //      } catch (JavaModelException e) {
    //        // OLDFIXME
    //        Log.errorlog("Exception in finalizeTypeSpec ",e);
    //        return null;
    //      }
    //    }
    //    if (javat != null) {
    //      JmlSpecifications.TypeDeclSpecs s = JmlSpecifications.getTypeSpecs(specst);
    //      JmlSpecifications.putTypeSpecs(javat, s);
    //      if (pi.options.verbosity > 2) Log.log("Stored specs for type " + javat.getFullyQualifiedName() + " " + javat.getKey() + "\n" + s.toString());
    //    }
    //    return javat;
    //  }

    //    /** OLDTODO
    //     * @param cuinfo
    //     * @param specsm
    //     * @param itype
    //     * @return
    //     */
    //    public IMethod finalizeMethodSpecs(CUInfo cuinfo, MethodDeclaration specsm, IType itype) {
    //        JmlSpecifications.MethodDeclSpecs s = JmlSpecifications.getMethodSpecs(specsm);
    //        //    if (pi.options.verbosity > 2) {
    //        //      JmlASTPrinter.print("METHOD " + specsm.getName().getIdentifier(),s.raw);
    //        //      JmlASTPrinter.print("METHOD " + specsm.getName().getIdentifier(),s.parsed);
    //        //    }
    //        // Need to find the IMethod that corresponds to the given MethodDeclaration
    //        // The MethodDeclaration has not been type resolved.
    //        // The IMethod belongs to the given IType.
    //        // OLDFIXME - need to find a better way to do this
    //
    //        String name = specsm.getName().getIdentifier();
    //        List params = specsm.parameters();
    //        int numargs = params.size();
    //        IMethod mm = null;
    //        IMethodBinding binding = specsm.resolveBinding();
    //        IMethod md = binding == null ? null : (IMethod)binding.getJavaElement();
    //        try {
    //            for (IMethod m: itype.getMethods()) {
    //                if (!m.getElementName().equals(name)) continue;
    //                if (m.getNumberOfParameters() != numargs) continue;
    //                if (md != null) {
    //                    if (!md.isSimilar(m)) continue;
    //                } else {
    //                    String[] ptypes = m.getParameterTypes();
    //                    for (int i=0; i<numargs; ++i) {
    //                        String sp = ptypes[i];
    //                        Type t = ((SingleVariableDeclaration)params.get(i)).getType();
    //                        Log.log("SAME TYPE ? " + sp + " " + t.toString());
    //                    }
    //                    // OLDFIXME
    //                }
    //                if (mm == null) mm = m;
    //                else {
    //                    Log.log("Ambiguous method resolution - OLDFIXME " + itype.getFullyQualifiedName() + " " + name + " " + numargs);
    //                }
    //            }
    //        } catch (JavaModelException e) {
    //            // OLDFIXME
    //            Log.errorlog("Failed to finalizeMethodSpecs for " + name, e);
    //        }
    //        if (mm != null) {
    //            JmlSpecifications.putMethodSpecs(mm,s);
    //            //      if (pi.options.verbosity > 2) Log.log("Saved specs for method " + name + " in " + itype.getFullyQualifiedName());
    //            //      if (pi.options.verbosity > 2) JmlASTPrinter.print("RAW SPECS",s.raw);
    //            //      if (pi.options.verbosity > 2) JmlASTPrinter.print("PARSED SPECS",s.parsed);
    //        } else {
    //            // OLDFIXME - this really should be a JmlEclipseProblem
    //            // The specs file has a method that the java file does not
    //            Log.errorlog("No Java method found to match " + name + " in type " + itype.getElementName(),null);  // OLDFIXME - match to location in specs file
    //        }
    //        return mm;
    //    }

    //    public IField finalizeFieldSpecs(CUInfo cuinfo, FieldDeclaration fd, VariableDeclarationFragment specsf, IType itype) {
    //        JmlSpecifications.FieldDeclSpecs s = JmlSpecifications.getFieldSpecs(specsf);
    //        // Need to find the IField that corresponds to the given FieldDeclaration
    //        // The FieldDeclaration has not been type resolved.
    //        // The IField belongs to the given IType.
    //        // OLDFIXME - need to find a better way to do this
    //
    //        String name = specsf.getName().getIdentifier();
    //        IField ff = null;
    //        try {
    //            for (IField f: itype.getFields()) {
    //                if (!f.getElementName().equals(name)) continue;
    //                ff = f;
    //                break;
    //            }
    //        } catch (JavaModelException e) {
    //            // OLDFIXME
    //            Log.errorlog("Failed to finalizeFieldSpecs for " + name, e);
    //        }
    //        if (ff != null) JmlSpecifications.putFieldSpecs(ff,s);
    //        else {
    //            // OLDFIXME - this really should be a JmlEclipseProblem
    //            // The specs file has a field that the java file does not
    //            Log.errorlog("No Java field found to match " + name + " in type " + itype.getFullyQualifiedName(),null);  // OLDFIXME - match to location in specs file
    //        }
    //        return ff;
    //    }

    static public String getPackageDotName(Name n) {
        if (n instanceof SimpleName) return ((SimpleName)n).getIdentifier();
        QualifiedName qn = (QualifiedName)n;
        return getPackageDotName(qn.getQualifier()) + "." + qn.getName().getIdentifier();
    }

    //    static public void transferSpecs(CompilationUnit specscu, CompilationUnit cu) {
    //        // The compilation unit
    //        JmlSpecifications.Specs s = JmlSpecifications.findSpecs(specscu);
    //        JmlSpecifications.putSpecs(cu,s);
    //        for (Object o: cu.types()) {
    //            AbstractTypeDeclaration t = (AbstractTypeDeclaration)o;
    //            transferSpecsForType(t);
    //        }
    //    }

    //    static public void transferSpecsForType(AbstractTypeDeclaration type) {
    //        IType ty = (IType)type.resolveBinding().getJavaElement();
    //        JmlSpecifications.putSpecs(type,JmlSpecifications.findTypeSpecs(ty));
    //        if (type instanceof TypeDeclaration) {
    //            TypeDeclaration td = (TypeDeclaration)type;
    //            for (TypeDeclaration t: td.getTypes()) {
    //                transferSpecsForType(t);
    //            }
    //            for (MethodDeclaration m: td.getMethods()) {
    //                // OLDFIXME - don't forget JML modifiers
    //            }
    //            for (FieldDeclaration f: td.getFields()) {
    //                // OLDFIXME - don't forget JML modifiers
    //            }
    //        } else if (type instanceof EnumDeclaration) {
    //            // OLDFIXME
    //        } else if (type instanceof AnnotationTypeDeclaration) {
    //            // OLDFIXME
    //        } else {
    //            // OLDFIXME - unexpected 
    //        }
    //    }

    ///** A counter to record how many periods havew been printed */
    //private int dotNumber;

    ///** Setting the period counter to 0 */
    //public void startDot() {
    //dotNumber = 0;
    //}

    ///** Prints a period, wrapping to a new line if 80 have been printed. */
    //public void dot() {
    //Log.log_noln(".");
    //if (((++dotNumber) % 80) == 0) Log.log("");
    //}

    ///** End printing periods - print a new line if needed. */
    //public void endDot() {
    //if ((dotNumber % 80) != 0) Log.log("");
    //}

}
