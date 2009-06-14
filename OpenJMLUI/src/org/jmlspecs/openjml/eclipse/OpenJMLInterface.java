/*
 * This file is part of the OpenJML plugin project. 
 * Copyright 2006-2009 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.io.PrintWriter;
import java.net.URL;
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
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.internal.compiler.problem.ProblemSeverities;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.jmlspecs.annotations.*;
import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.Main.JmlCanceledException;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.osgi.framework.Bundle;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.util.Context;

/**
 * This class is the interface between the Eclipse UI that serves as view and
 * controller and the openjml packages that executes operations on JML annotations.
 * Typically there is just one fairly persistent instance of this class for 
 * each Java project.  Note that we only allow .java files under the control of
 * one Java project to be compiled together - this is because Eclipse manages 
 * options on a per project basis.  Technically if all the relevant projects had
 * the same set of options, they could be combined, but that is currently not 
 * allowed.
 */
public class OpenJMLInterface {

    /** The API object corresponding to this Interface class. */
    @NonNull
    protected API api;
    
    /** The common instance of a Utils object that provides various
     * utility methods.  We initialize this when an OpenJMLInterface
     * object is created rather than making it static because the 
     * singleton object is not created until the plugin is actually
     * started.
     */
    @NonNull
    final protected Utils utils = Activator.getDefault().utils;

    /** Retrieves the descriptive version string from OpenJML 
     * @return returns the descriptive version string from OpenJML
     */
    @NonNull
    static public String version() { return API.version(); }

    /** The Java propject for this object. */
    @NonNull
    final protected IJavaProject jproject;

    protected List<File> specsPath;
    
    /** The problem requestor that reports problems it is told about to the user
     * in some fashion (here via Eclipse problem markers).
     */
    @NonNull
    protected JmlProblemRequestor preq;

    /** An Enum type that gives a choice of various tools to be executed. */
    public static enum Cmd { CHECK, ESC, RAC, JMLDOC};

    /** The constructor, which initializes all of the fields of the object.
    *
    * @param jproject The java project associated with this instance of OpenJMLInterface
    */
   public OpenJMLInterface(@NonNull IJavaProject pi) {
       this.jproject = pi;
       preq = new JmlProblemRequestor(pi); 
       specsPath = Utils.getSpecsPath(pi);
       PrintWriter w = new PrintWriter(((ConsoleLogger)Log.log.listener).getConsoleStream());
       try { api = new API(w,new EclipseDiagnosticListener(preq)); }
       catch (Exception e) {} // FIXME _ add an error
   }
   
    /** Executes the JML Check (syntax and typechecking) or the RAC compiler
     * operations on the given set of resources.
     * @param command either CHECK or RAC
     * @param files the set of files (or containers) to check
     * @param monitor the progress monitor the UI is using
     */
    public void executeExternalCommand(Cmd command, List<IResource> files, @Nullable IProgressMonitor monitor) {
        try {
            if (files.isEmpty()) {
                Log.log("Nothing applicable to process");
                Activator.getDefault().utils.showMessageInUI(null,"JML","Nothing applicable to process");
                return;
            }
            IJavaProject jp = JavaCore.create(files.get(0).getProject());
            List<String> args = getOptions(jp,command);
            args.add(JmlOptionName.DIRS.optionName());

            for (IResource r: files) {
                args.add(r.getLocation().toString());
            }
            Log.log(Timer.getTimeString() + " Executing openjml ");
            if (monitor != null) {
                monitor.setTaskName(command == Cmd.RAC ? "JML RAC" : "JML Checking");
                monitor.subTask("Executing openjml");
            }
            try {
                setMonitor(monitor);
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
    
    /** Executes the jmldoc tool on the given project, producing output according
     * to the current set of options.
     * @param p the project whose jmldocs are to be produced
     * @return 0 for success, 1 for command-line errors, 2 for system errors,
     *     3 for internal or otherwise catastrophic errors
     */
    public int generateJmldoc(IJavaProject p) {
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
        return ret;
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
            if (api == null) {
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
            setMonitor(monitor);
            if (monitor != null) monitor.subTask("Starting ESC");
           
            List<String> args = getOptions(jproject,Cmd.ESC);
            List<IJavaElement> elements = new LinkedList<IJavaElement>();
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
                    api = new API(w,new EclipseDiagnosticListener(preq));
                    api.setProgressReporter(new UIProgressReporter(api.context,monitor,null));
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
                    int ret = api.compile(args.toArray(new String[args.size()]));
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
                    api.doEsc(msym);
                } else if (je instanceof IType) {
                    ClassSymbol csym = convertType((IType)je);
                    api.doEsc(csym);
                }
            }
            if (monitor != null) {
                monitor.subTask("Completed ESC operation");
            }
            Log.log("Completed ESC operation");
        } catch (JmlCanceledException e) {
            Log.log("Canceled ESC operation");
            throw e;
        } catch (java.io.IOException e) {
            // FIXME - error dialog
        }
    }

    /** Converts Eclipse's representation of a type to OpenJML's, that is
     * from an IType to a ClassSymbol.
     * @param type the Eclipse representation of a type
     * @return the corresponding OpenJML ClassSymbol
     * @throws OpenJMLException if the corresponding class symbol does not exist in OpenJML
     * (e.g. the files have not been entered)
     */
    public @NonNull ClassSymbol convertType(IType type) throws Utils.OpenJMLException {
        String className = type.getFullyQualifiedName();
        ClassSymbol csym = api.getClassSymbol(className);
        if (csym == null) {
            String error = "No such class in OpenJML: " + className;
            Log.errorlog(error,null);
            throw new Utils.OpenJMLException(error);
        }
        return csym;
    }
    
    /** Converts Eclipse's representation of a method (an IMethod) to OpenJML's
     * (a MethodSymbol)
     * @param method the Eclipse IMethod for the method
     * @return OpenJML's MethodSymbol for the same method
     * @throws Utils.OpenJMLException if there is no match
     */
    public MethodSymbol convertMethod(IMethod method) throws Utils.OpenJMLException {
        ClassSymbol csym = convertType(method.getDeclaringType());
        try {
            com.sun.tools.javac.util.Name name = com.sun.tools.javac.util.Names.instance(api.context).fromString(
                    method.isConstructor() ? "<init>" : method.getElementName());
            Scope.Entry e = csym.members().lookup(name); // FIXME - Need to match types & number
            MethodSymbol firstsym = null;
            outer: while (e != null && e.sym != null) {
                Symbol sym = e.sym;
                e = e.sibling;    // FIXME - use next?
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
    
    // FIXME
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
    
    /** Returns the list of names of directories and jar files that constitute
     * the current specspath in openjml.
     * @return the current specspath
     */
    public @NonNull List<String> getSpecsPath() {
        return api.getSpecsPath();
    }
    
    /** Return the specs of the given type, pretty-printed as a String.  This
     * may be an empty String if there are no specifications.
     * @param type the Eclipse IType for the class whose specs are wanted
     * @return the corresponding specs, as a String
     */
    @NonNull
    public String getSpecs(IType type) throws Utils.OpenJMLException {
        ClassSymbol csym = convertType(type);
        try{
            TypeSpecs tspecs = api.getSpecs(csym);
            String smods = api.prettyPrint(tspecs.modifiers,false);
            return smods + "\n" + tspecs.toString();
        } catch (Exception e) { return "<Exception>: " + e; }
    }

    /** Return the specs of the given type, including all inherited specs,
     * pretty-printed as a String.  This
     * may be an empty String if there are no specifications.
     * @param type the Eclipse IType for the class whose specs are wanted
     * @return the corresponding specs, as a String
     */
    @NonNull
    public String getAllSpecs(@NonNull IType type) {
        ClassSymbol csym = convertType(type);
        List<TypeSpecs> typeSpecs = api.getAllSpecs(csym);
        try {
            StringBuilder sb = new StringBuilder();
            for (TypeSpecs ts: typeSpecs) {
                sb.append("From " + ts.file.getName() + "\n");
                sb.append(api.prettyPrint(ts.modifiers,false));
                sb.append("\n");
                sb.append(ts.toString());
                sb.append("\n");
            }
            return sb.toString();
        } catch (Exception e) { return "<Exception>: " + e; }
    }
    
    /** Return the specs of the given method, including all inherited specs,
     * pretty-printed as a String.  This
     * may be an empty String if there are no specifications.
     * @param type the Eclipse IMethod for the method whose specs are wanted
     * @return the corresponding specs, as a String
     */
    public @NonNull String getAllSpecs(@NonNull IMethod method) {
        MethodSymbol msym = convertMethod(method);
        List<JmlMethodSpecs> methodSpecs = api.getAllSpecs(msym);
        try {
            StringBuilder sb = new StringBuilder();
            for (JmlMethodSpecs ts: methodSpecs) {
                sb.append("From " + ts.decl.sourcefile.getName() + "\n");
                sb.append(api.prettyPrint(ts.decl.mods,false)); // FIXME - want the collected mods in the JmlMethodSpecs
                sb.append("\n");
                sb.append(api.prettyPrint(ts,false));
                sb.append("\n");
            }
            return sb.toString();
        } catch (Exception e) { return "<Exception>: " + e; }
        
    }

    /** Returns the specs of the given field as a String
     * @param field the Eclipse IField value denoting the field whose specs are wanted
     * @return the specs of the field, as a String
     */
    // FIXME - this does not include annotations - classic or Java
    public @NonNull String getSpecs(@NonNull IField field) {
        String s = field.getDeclaringType().getFullyQualifiedName();
        ClassSymbol csym = api.getClassSymbol(s);
        com.sun.tools.javac.util.Name name = com.sun.tools.javac.util.Names.instance(api.context).fromString(field.getElementName());
        Symbol sym = csym.members().lookup(name).sym;
        VarSymbol fsym = (VarSymbol)sym;
        FieldSpecs fspecs = api.getSpecs(fsym);
        try { 
            String smods = api.prettyPrint(fspecs.mods,false);
            return smods + "\n" + fspecs.toString(); // FIXME - use proper eol
        } catch (Exception e) { return "<Exception>: " + e; }
    }
    
    public File getLeadingSpecFile(IType t) {
        ClassSymbol csym = convertType(t);
        if (csym != null) {
            // FIXME go through API
            JavaFileObject f = JmlSpecs.instance(api.context).findLeadingSpecFile(csym);
            return null;
        }
        return null;
    }

    /** Show information about the most recent proof of the given method in a 
     * dialog box for the given Shell.  This information states whether the 
     * proof was performed, whether it was successful, and launches editor
     * windows containing the proof's counterexample context, trace, and
     * basic block program.
     * @param method the Eclipse IMethod for the method whose proof is wanted
     * @param shell the shell to be used to parent any dialog windows
     */
    public void showProofInfo(@NonNull IMethod method, @NonNull Shell shell) {
        if (api == null) { // This should not happen, but just in case
            utils.showMessageInUINM(shell,"JML Proof Results","There is no current proof result for " + method.getDeclaringType().getFullyQualifiedName() + "." + method.getElementName());
            return;
        }
        MethodSymbol msym = null;
        try { 
            msym = convertMethod(method);
        } catch (Exception e) { /* ignore, and let msym be null */ }
        if (msym == null) {
            utils.showMessageInUINM(shell,"JML Proof Results","The method " + method.getElementName() + " has not yet been checked (or a proof attempted)");
            return;
        }
        String methodName = msym.owner + "." + msym;
        String shortName = msym.owner.name + "." + msym.name;
        
        IProverResult r = api.getProofResult(msym);
        
        String s = api.getBasicBlockProgram(msym);
        utils.launchEditor(s,msym.owner.name + "." + msym.name);

        if (r == null) {
            utils.showMessageInUINM(shell,"JML Proof Results","There is no current proof result for " + methodName);
            return;
        }

        // Trace information, if any
        Object o = r.otherInfo();
        if (o != null) utils.launchEditor(o.toString(),shortName);


        if (r.result() == IProverResult.UNSAT) {
            utils.showMessageInUINM(shell,"JML Proof Results",
                    "The verification proof succeeded for " + methodName + "\n"
                    + "Prover: " + r.prover());
            return;
        }
        if (r.result() == IProverResult.INCONSISTENT) {
            utils.showMessageInUINM(shell,"JML Proof Results","The assumptions are INCONSISTENT for " + methodName + "\n"
            + "Prover: " + r.prover());
            return;
        }
        if (r.result() == IProverResult.UNKNOWN) {
            utils.showMessageInUINM(shell,"JML Proof Results","The verification was not provable for " + methodName + "\n"
            + "Prover: " + r.prover());
            return;
        }
        
        
        if (r.counterexample() == null) {
            utils.showMessageInUINM(shell,"JML Counterexample", "There is no counterexample information for method " + methodName);
        } else {
            Set<Map.Entry<String,String>> set = r.counterexample().sortedEntries();
            StringBuffer sb = new StringBuffer();
            sb.append("COUNTEREXAMPLE STATE FOR " + methodName + "  Prover: " + r.prover());
            for  (Map.Entry<String,String> entry : set) {
                sb.append(entry.getKey());
                sb.append(" = ");
                sb.append(entry.getValue());
                sb.append("\n");
            }
            utils.launchEditor(sb.toString(),shortName);
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

        /** When this listener hears a problem from openjml, 
         * it needs to report it to the problem to Eclipse, by calling report
         * on this IProblemRequestor
         */
        @NonNull @SpecPublic
        protected IProblemRequestor preq;

        /** Creates a listener which will translate any diagnostics it hears and
         * send them off to the given IProblemRequestor.
         * @param p the problem requestor that wants to receive any diagnostics
         */
        //@ assignable this.*;
        //@ ensures preq == p;
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
                //if (verbose) {
                    if (severity == ProblemSeverities.Error) Log.errorlog(diagnostic.toString(),null);
                    else Log.log(diagnostic.toString());
                //}
            }
        }

    }

    /** This class is a specific instantiation of the IProgressReporter interface;
     * it receives progress report calls and both logs them and displays them
     * in the progress monitor supplied by the Eclipse UI.
     * @author David R. Cok
     */
    public static class UIProgressReporter implements org.jmlspecs.openjml.Main.IProgressReporter {
        /** The associated Eclipse progress monitor */
        protected @Nullable IProgressMonitor monitor;
        /** The associated OpenJML compilation context */
        protected @NonNull Context context;
        /** The UI shell in which to display dialogs */
        protected @Nullable Shell shell = null;
        
        /** Instantiates a listener for progress reports that displays them in
         * the Eclipse UI.
         * @param context the OpenJML compilation context
         * @param monitor the Eclipse progress monitor
         * @param shell the Eclipse UI shell
         */
        //@ assignable this.*;
        public UIProgressReporter(@NonNull Context context, @Nullable IProgressMonitor monitor, @Nullable Shell shell) {
            this.monitor = monitor;
            this.context = context;
            this.shell = shell;
        }
        
        /** This is the method called by OpenJML when a progress message is sent.
         * The implementation here logs the message if the level is <=1 and
         * displays it in the progress monitor if one was supplied in the
         * constructor.  The UI work is done in a Runnable spawned from
         * Display.asyncExec .
         */
        //@ ensures not_assigned(this.*);
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
        
        /** Sets the OpenJML compilation context associated with this listener. */
        //JAVA16 @Override
        //@ assignable this.context;
        //@ ensures this.context == context;
        public void setContext(@NonNull Context context) { 
            this.context = context; 
        }
    }



    /** Sets the monitor to be used to show progress
     * @param monitor the monitor to be used
     */
    public void setMonitor(@Nullable IProgressMonitor monitor) {
        if (monitor != null) {
            api.setProgressReporter(new UIProgressReporter(api.context,monitor,null));
        } else {
            api.setProgressReporter(null);
        }
    }


//    /** Processes the given set of compilation units, parsing them and
//     * producing any error messages caused by bad syntax or semantics.
//     * FIXME - no JML checking or rac or jmldoc stuff is done as yet.
//     * 
//     * @param icus the set of compilation units to parse, created from source files
//     * @param monitor the IProgressMonitor on which to report progress and cancellations
//     * @throws Exception  ??? FIXME
//     */
//    public void doProcessing(ICompilationUnit[] icus, IProgressMonitor monitor) throws Exception {
//        Options options = jproject.options;
//        if (options.verbosity > 2) Log.log(Timer.getTimeString() + " parsing...");
//
//        // Make working copies.  Creating a working copy also "opens"
//        // the compilation unit, if it has not already been opened.
//        // Opening a CU includes parsing the file sufficient to obtain
//        // the basic Java structure of the CU - types, field and method
//        // signatures, so that inter-CU name resolution can be performed.
//
//        if (options.verbosity > 2) Log.log(Timer.getTimeString() + " Read compilation units");
//        if (monitor != null) monitor.subTask("Reading compilation units");
//
//        List<ICompilationUnit> workingCopyList = new ArrayList<ICompilationUnit>(icus.length);
//        List<CUInfo> infoList = new ArrayList<CUInfo>(icus.length*2);
//        for (ICompilationUnit icu: icus) {
//            if (monitor != null) monitor.subTask("Reading compilation units - " + icu.getElementName());
//            try {
//                ICompilationUnit wcu = icu.getWorkingCopy(jproject.owner,preq,null);  // FIXME - what are we supposed to do with problem requestors?
//                workingCopyList.add(wcu);
//                //                CUInfo cuinfo = new CUInfo();
//                //                cuinfo.file = (IFile)icu.getResource();
//                //                cuinfo.original = icu;
//                //                cuinfo.workingCopy = wcu;
//                //                putMap(cuinfo);
//                //                infoList.add(cuinfo);
//            } catch (Exception e) {
//                // FIXME - report properly
//                Log.log("Skipping " + icu.getElementName() + " because it does not appear to exist in the file system");
//                continue;
//            }
//            if (monitor != null) {
//                monitor.worked(1);
//                if (monitor.isCanceled()) {
//                    // Discard all of these working copies
//                    //          for (ICompilationUnit c: workingCopyList) {
//                    //            c.discardWorkingCopy();
//                    //          }
//                    return;
//                }
//            }
//        }
//        org.eclipse.jdt.core.IJavaElement e;
//        ICompilationUnit[] workingCopies = workingCopyList.toArray(new ICompilationUnit[workingCopyList.size()]);
//
//        try {
//            List<IResource> ics = new java.util.LinkedList<IResource>();
//            for (ICompilationUnit icu : workingCopies) {
//                ics.add(icu.getResource());
//            }
//            //                executeExternalCommand(Cmd.CHECK, ics,monitor);
//            //              List<CompilationUnit> parsedCUs = parseCUs(workingCopies,monitor);
//            //              if (monitor != null && monitor.isCanceled()) return; // see finally block below
//            //              getSpecs(infoList,TypeInfo.State.TYPECHECKED,monitor);
//            //              if (monitor!=null && monitor.isCanceled()) return; // see finally block below
//            //              typeCheck(infoList,parsedCUs,monitor);
//        } finally {
//            // Any cleanup - but we are not discarding the working copies
//            // we want to keep them so that work is not repeated on subsequent
//            // calls, and so that type and spec information is available for
//            // querying.  However, some sort of cleanup needs to be done 
//            // eventually, perhaps manually.  FIXME
//        }
//    }

    /** Retrieves the options from the preference page, determines the 
     * corresponding options for OPenJML and sends them.
     * @param jproject
     * @param cmd The command to be executed
     * @return
     */
    public @NonNull List<String> getOptions(IJavaProject jproject, Cmd cmd) {
        List<String> opts = new LinkedList<String>();
        if (cmd == Cmd.ESC) opts.add(JmlOptionName.ESC.optionName());
        if (cmd == Cmd.RAC) opts.add(JmlOptionName.RAC.optionName());
        Options opt = Activator.options;
        boolean verbose = opt.verbosity >= 1;
        if (opt.debug) opts.add(JmlOptionName.JMLDEBUG.optionName());
        // FIXME if (opt.verbosity != 0)  { opts.add(JmlOptionName.JMLVERBOSE.optionName()); opts.add(Integer.toString(opt.verbosity)); }
        if (opt.source != null && opt.source.length()!=0) { opts.add("-source"); opts.add(opt.source); }
        if (cmd != Cmd.JMLDOC && opt.destination != null && opt.destination.length()!=0)  { opts.add("-d"); opts.add(opt.destination); }
        if (!opt.checkPurity) opts.add(JmlOptionName.NOPURITYCHECK.optionName());
        // FIXME if (opt.parsePlus) opts.add(JmlOptionName.PARSEPLUS.optionName());
        if (opt.showNotImplemented) opts.add(JmlOptionName.SHOW_NOT_IMPLEMENTED.optionName());
        // FIXME if (opt.showNotExecutable) opts.add(JmlOptionName.SHOWNOTEXECUTABLE.optionName());
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

        List<File> files = specsPath;
        first = true;
        ss = new StringBuilder();
        if (files != null) { 
            for (File s: files) {
                if (first) first = false; else ss.append(java.io.File.pathSeparator);
                ss.append(s.toString());
            }
        }
        if (ss.toString().length()!=0) {
            opts.add(JmlOptionName.SPECS.optionName());
            opts.add(ss.toString());
        }
       
        // Now determine the location of library specs and the internal 
        // runtime library
        
        try {
            boolean somethingPresent = false;
            String versionString = System.getProperty("java.version");
            int version = 6; // the current default
            if (versionString.startsWith("1.6")) version = 6;
            else if (versionString.startsWith("1.5")) version = 5;
            else if (versionString.startsWith("1.4")) version = 4;
            else if (versionString.startsWith("1.7")) version = 7;
            else if (versionString.startsWith("1.8")) version = 8;
            else if (versionString.startsWith("1.9")) version = 9;
            else {
                Log.log("Unrecognized version: " + versionString);
                version = 6; // default, if the version string is in an unexpected format
            }

            String[] defspecs = new String[8]; // null entries OK

            Bundle specsBundle = Platform.getBundle(Activator.SPECS_PLUGIN_ID);
            if (specsBundle == null) {
                Log.log("No specification plugin " + Activator.SPECS_PLUGIN_ID);
            } else {
                String loc = null;
                URL url = FileLocator.toFileURL(specsBundle.getResource(""));
                File root = new File(url.toURI());
                loc = root.toString();
                Log.log("JMLSpecs plugin found " + root + " " + root.exists());
                if (root.isFile()) {
                    // Presume it is a jar or zip file
                    JarFile j = new JarFile(root);
                    int i = 0;
                    for (int v = version; v >=4; --v) {
                        JarEntry f = j.getJarEntry("java"+v);
                        if (f != null) defspecs[i++] = loc + "!java" + v;
                    }
                } else if (root.isDirectory()) {
                    // Normal file system directory
                    int i = 0;
                    for (int v = version; v >=4; --v) {
                        File f = new File(root,"java"+v);
                        if (f.exists()) defspecs[i++] = root + "/java" + v;
                    }
                } else {
                    Log.log("Expected contents (javaN subdirectories) not found in specs bundle at " + root);
                }
                for (String z: defspecs) if (z != null) somethingPresent = true;
                if (somethingPresent) {
                    API.setLibrarySpecsPath(defspecs);
                    Log.log("Set library specspath defaults from JMLspecs plugin");
                }
            }
            Bundle selfBundle = Platform.getBundle(Activator.PLUGIN_ID);
            if (selfBundle == null) {
                Log.log("No self plugin");
            } else {
                URL url = FileLocator.toFileURL(selfBundle.getResource(""));
                if (url != null) {
                    File root = new File(url.toURI());
                    if (verbose) Log.log("JMLSpecs folders found " + root + " " + root.exists());
                    if (root.isDirectory()) {
                        int i = 0;
                        for (int v = version; v >=4; --v) {
                            File f = new File(root,"../specs/java"+v);
                            if (f.exists()) defspecs[i++] = f.toString();
                        }
                    } else {
                        JarFile j = new JarFile(root);
                        int i = 0;
                        for (int v = version; v >=4; --v) {
                            JarEntry f = j.getJarEntry("specs/java"+v);
                            if (f != null) defspecs[i++] = root + "!specs/java" + v;
                        }
                    }
                    
                    if (root.isDirectory()) {
                        File f = new File(root,"../runtime");
                        if (f.exists()) {
                            API.setExternalRuntime(new String[]{ f.toString() });
                            Log.log("Internal runtime location: " + f.toString());
                        }
                    } else {
                        JarFile j = new JarFile(root);
                        JarEntry f = j.getJarEntry("runtime");
                        if (f != null) {
                            API.setExternalRuntime(new String[]{ root + "!runtime"} );
                            Log.log("Internal runtime location: " + root + "!runtime");
                        }
                    }
                }
            }
        } catch (Exception e) {
            Log.log("Failure finding specs: "  + e);
        }

        // FIXME - what about these options
        // specsProjectName
        // roots, nojml, nojavacompiler
        // trace subexpressions counterexample
        // specs , classpath , sourcepath, stopiferrors
        // Java options, Jmldoc options
        return opts;
    }
    
    /** Sets the value of a command-line option in the OpenJml object
     * @param name the name of the option, including any leading - sign
     * @param value the value of the option; you can use an empty string as a
     * value for options which are just on or off 
     */
    public void setOption(String name, String value) {
        api.setOption(name,value);
    }
    
    /** Removes an option if it was present - equivalent to the option not
     * having been named on the command-line
     * @param name the name of the option, including any leading - sign
     */
    public void removeOption(String name) {
        api.removeOption(name);
    }
    
    /** Gets a String representation of the BasicBlock encoding of the method
     * body for the given method.
     * @param msym the method whose body is to be returned
     * @return a String representation of the Basic Bloxk program for the method body
     */
    public @NonNull String getBasicBlockProgram(@NonNull MethodSymbol msym) {
        return api.getBasicBlockProgram(msym);
    }

//    /** Converts a name into a flatname with dots between the components; this
//     * is particularly suited to converting a tree-form of a package name into
//     * dot-separated name (as a String)
//     * @param n the input Name
//     * @return the output dot-separated name as a String
//     */
//    static public @NonNull String getPackageDotName(@NonNull Name n) {
//        if (n instanceof SimpleName) return ((SimpleName)n).getIdentifier();
//        QualifiedName qn = (QualifiedName)n;
//        return getPackageDotName(qn.getQualifier()) + "." + qn.getName().getIdentifier();
//    }

}
