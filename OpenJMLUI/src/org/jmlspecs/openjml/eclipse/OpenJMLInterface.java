/*
 * This file is part of the OpenJML plugin project. 
 * Copyright (c) 2006-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.io.PrintWriter;
import java.net.URI;
import java.net.URL;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.attribute.PosixFilePermissions;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

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
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.*;
import org.eclipse.jdt.internal.compiler.problem.ProblemSeverities;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.SpecPublic;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Main.JmlCanceledException;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.eclipse.Utils.OpenJMLException;
import org.jmlspecs.openjml.ext.OptionsInfer;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.osgi.framework.Bundle;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.PropagatedException;

// FIXME - needs review - OpenJMLInterface.java

/**
 * This class is the interface between the Eclipse UI that serves as view and
 * controller and the openjml packages that execute operations on JML annotations.
 * Typically there is just one fairly persistent instance of this class for 
 * each Java project.  Note that we only allow .java files under the control of
 * one Java project to be compiled together - this is because Eclipse manages 
 * options on a per project basis.  Technically if all the relevant projects had
 * the same set of options, they could be combined, but the implementation
 * currently does not do that.
 */
public class OpenJMLInterface implements IAPI.IProofResultListener {

    /** The API object corresponding to this Interface class. The api object changes 
     * for each invocation of OpenJML, with a new context, and possibly new input files, etc. 
     * The same API object can be used if all the input files are unchanged and only 
     * new proof attempts are being attempted. */
    @NonNull
    protected IAPI api;

    /** The common instance of a UI Utils object that provides various
     * utility methods.  We initialize this when an OpenJMLInterface
     * object is created rather than making it static because the 
     * singleton object is not created until the plugin is actually
     * started.
     */
    @NonNull
    final protected Utils utils = Activator.utils();

    /** Retrieves the descriptive version string from OpenJML 
     * @return returns the descriptive version string from OpenJML
     */
    @NonNull
    public String version() { return api.version(); }

    /** The Java project for this object. */
    @NonNull
    final protected IJavaProject jproject;

    /** The problem requestor that reports problems it is told about to the user
     * in some fashion (here via Eclipse problem markers).
     */
    @NonNull
    protected JmlProblemRequestor preq;

    /** The constructor, which initializes all of the fields of the object.
     *
     * @param jproject The java project associated with this instance of OpenJMLInterface
     */
    public OpenJMLInterface(@NonNull IJavaProject jproject) {
        this.jproject = jproject;
        initialize(null);
    }

    /** Initializes new OpenJMLInterface objects */
    protected void initialize(/*@nullable*/ Main.Cmd cmd) {
        preq = new JmlProblemRequestor(jproject); 
        PrintWriter w = Log.log.listener() != null ? 
                                new PrintWriter(Log.log.listener().getStream(),true) : null;
                                List<String> opts = getOptions(jproject,cmd);
                                try { 
                                    api = Factory.makeAPI(w,new EclipseDiagnosticListener(preq), null, opts.toArray(new String[0])); 
                                    api.setProofResultListener(this);
                                } catch (Exception e) {
                                    Log.errorlog("Failed to create an interface to OpenJML",e); //$NON-NLS-1$
                                }
    }

    /**
     * A private helper method that checks to see whether a given IFolder contains
     * at least one source file (that is, a file ending in .jml or .java, constants
     * declared in OpenJML's Strings class).
     * 
     * @param folder The folder to check.
     * @return true if the folder contains at least one source file, false otherwise.
     */
    private boolean hasAtLeastOneSourceFile(final IFolder folder) {
        boolean result = false;

        try {
            IResource[] members = folder.members();
            for (int i = 0; !result && i < members.length; i++) {
                if (members[i] instanceof IFolder) {
                    result |= hasAtLeastOneSourceFile((IFolder) members[i]);
                } else if (members[i] instanceof IFile) {
                    final IFile file = (IFile) members[i];
                    result |= file.getName().endsWith(Strings.javaSuffix);
                    result |= file.getName().endsWith(Strings.specsSuffix);
                }
            }
        } catch (final CoreException e) {
            // if we couldn't even check for the folder's members, obviously
            // something's wrong - we'll return false
        }

        return result;
    }

    /**
     * Adds appropriate arguments to a list of OpenJML command line arguments
     * for all the non-empty source folders in the specified IProject.
     * 
     * @param project The project.
     * @param args The argument list to add to; this is potentially changed by
     * calling this method.
     * @return the number of path and file arguments added to the argument list; this
     * does _not_ include OpenJML "-dir" arguments, which are also added as necessary.
     * If result == 0, the arguments were unchanged.
     */
    private int addSourceFoldersToCommandLine(final IProject project, final List<String> args) {
        int result = 0;
        if (JavaProject.hasJavaNature(project)) {
            // should always be true, we should always be in a Java project
            // so let's get all the source folders
            final IJavaProject javaProject = JavaCore.create(project);
            try {
                for (IClasspathEntry entry : javaProject
                                        .getResolvedClasspath(true)) {
                    // get the classpath for the project
                    if (entry.getContentKind() == IPackageFragmentRoot.K_SOURCE) {
                        // it's a source folder, let's see if it's empty
                        final IFolder folder = 
                                                ResourcesPlugin.getWorkspace().getRoot().getFolder(entry.getPath());

                        if (hasAtLeastOneSourceFile(folder)) {
                            // there are files in the source folder
                            args.add(JmlOption.DIR.optionName());
                            args.add(folder.getLocation().toOSString());
                            result = result + 1;
                        }
                    }
                }
            } catch (final JavaModelException e) {
                // ignore this exception for now
            }
        }
        return result;
    }

    /** Executes the JML Check (syntax and typechecking) or the RAC compiler
     * operations on the given set of resources, creating a new compilation context.
     * Must be called in a computational thread.
     * @param command either CHECK or RAC
     * @param files the set of files (or containers) to check
     * @param monitor the progress monitor the UI is using
     */
    public void executeExternalCommand(Main.Cmd command, Collection<IResource> files, @Nullable IProgressMonitor monitor, boolean auto) {
        boolean verboseProgress = utils.openjmlVerbose() >= Utils.NORMAL;
        try {
            if (files.isEmpty()) {
                if (!auto) {
                    if (verboseProgress) Log.log("Nothing applicable to process"); //$NON-NLS-1$
                    Activator.utils().showMessageInUI(null,"JML","Nothing applicable to process"); //$NON-NLS-1$ //$NON-NLS-2$
                }
                return;
            }
            IJavaProject jp = JavaCore.create(files.iterator().next().getProject());
            List<String> args;
            if (command == Main.Cmd.CHECK) {
                api.close();
                initialize(command);
                args = new ArrayList<String>();
                args = getOptions(jp,command); // FIXME - somehow the options are not propagating through
            } else {
                args = getOptions(jp,command);
                String racdir = utils.getRacDir();
                if (jp.getProject().findMember(racdir) == null) {
                    try {
                        // FIXME - is it a problem that this is done in the UI thread; is local=true correct?
                        jp.getProject().getFolder(racdir).create(IResource.FORCE,true,null);
                    } catch (CoreException e) {
                        if (verboseProgress) Log.errorlog("Failed to create the RAC output folder",e); //$NON-NLS-1$
                        Activator.utils().showExceptionInUI(null,"Failed to create the RAC output folder",e); //$NON-NLS-1$
                        return;
                    }
                }
                args.add(Strings.outputOptionName);
                args.add(jp.getProject().getLocation().append(racdir).toString());
            }

            boolean addedSomething = false;
            for (IResource r : files) {
                if (r instanceof IProject) {
                    addedSomething |= addSourceFoldersToCommandLine((IProject) r, args) > 0;
                } else if (r instanceof IFolder) {
                    // the user explicitly selected a folder, and we don't allow empty folders
                    if (hasAtLeastOneSourceFile((IFolder) r)) {
                        args.add(JmlOption.DIR.optionName());
                        args.add(r.getLocation().toString());
                        addedSomething = true;
                    }
                } else {
                    // the user explicitly selected a file, so presumably they know what they're doing
                    args.add(r.getLocation().toString());
                    addedSomething = true;
                }
            }
            if (!addedSomething) {
                if (monitor != null) monitor.subTask("OpenJML: No files to check"); //$NON-NLS-1$
                if (verboseProgress) Log.log(Timer.timer.getTimeString() + " No files to check"); //$NON-NLS-1$
                return; // we don't call OpenJML with no files
            }
            Timer.timer.markTime();
            if (verboseProgress) {
                String s = files.size() == 1 ? files.iterator().next().getName() : (files.size() + " items"); //$NON-NLS-1$
                Log.log(Timer.timer.getTimeString() + " Executing openjml on " + s); //$NON-NLS-1$
            }
            if (monitor != null) {
                monitor.setTaskName(command == Main.Cmd.RAC ? "JML RAC" : "JML Checking"); //$NON-NLS-1$ //$NON-NLS-2$
                monitor.subTask("Executing openjml"); //$NON-NLS-1$
            }
            try {
                setMonitor(monitor);
                int ret = api.execute(null,args.toArray(new String[args.size()]));
                if (ret == Main.Result.OK.exitCode) {
                    if (verboseProgress) Log.log(Timer.timer.getTimeString() + " Completed"); //$NON-NLS-1$
                }
                else if (ret == Main.EXIT_CANCELED) {
                    throw new Main.JmlCanceledException(Utils.emptyString);
                }
                else if (ret == Main.Result.ERROR.exitCode) {
                    if (verboseProgress) Log.log(Timer.timer.getTimeString() + " Completed with errors"); //$NON-NLS-1$
                }
                else if (ret == Main.Result.CMDERR.exitCode) {
                    StringBuilder ss = new StringBuilder();
                    for (String r: args) {
                        ss.append(r);
                        ss.append(Utils.space);
                    }
                    Log.errorlog("INVALID COMMAND LINE: return code = " + ret + "   Command: " + ss,null);  // FIXME - the reason for the bad command line is lost (it would be an internal error)  //$NON-NLS-1$//$NON-NLS-2$
                    Activator.utils().showMessageInUI(null,"Execution Failure","Invalid commandline - return code is " + ret + Strings.eol + ss);  //$NON-NLS-1$//$NON-NLS-2$
                }
                else if (ret >= Main.Result.SYSERR.exitCode) {
                    StringBuilder ss = new StringBuilder();
                    for (String r: args) {
                        ss.append(r);
                        ss.append(Utils.space);
                    }
                    Log.errorlog("INTERNAL ERROR: return code = " + ret + "   Command: " + ss,null);  // FIXME - when the error is the result of an exception, we don't see the result //$NON-NLS-1$ //$NON-NLS-2$
                    Activator.utils().showMessageInUI(null,"OpenJML Execution Failure","Internal failure in openjml - return code is " + ret + " " + ss);   //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
                }
            } catch (JmlCanceledException e) {
                throw e;
            } catch (PropagatedException e) {
                throw e.getCause();
            } catch (Throwable e) {
                StringBuilder ss = new StringBuilder();
                for (String c: args) {
                    ss.append(c);
                    ss.append(Utils.space);
                }
                Log.errorlog("Failure to execute openjml: "+ss,e);  //$NON-NLS-1$
                Activator.utils().showExceptionInUI(null,"Failure to execute openjml: " + ss,e); //$NON-NLS-1$
            }
            if (monitor != null) monitor.subTask("Completed openjml"); //$NON-NLS-1$
        } catch (JmlCanceledException e) {
            if (monitor != null) monitor.subTask("OpenJML Canceled: " + e.getMessage()); //$NON-NLS-1$
            if (verboseProgress) Log.log(Timer.timer.getTimeString() + " Operation canceled"); //$NON-NLS-1$
        }
        if (command == Main.Cmd.ESC) utils.refreshView();
    }

    /** Executes the jmldoc tool on the given project, producing output according
     * to the current set of options.
     * @param p the project whose jmldocs are to be produced
     * @return 0 for success, 1 for command-line errors, 2 for system errors,
     *     3 for internal or otherwise catastrophic errors
     */
    public int generateJmldoc(IJavaProject p) {
        List<String> args = getOptions(p,Main.Cmd.JMLDOC);
        args.add(Strings.outputOptionName);
        args.add(p.getProject().getLocation().toString() + File.separator + "docx"); //$NON-NLS-1$
        //args.add(JmlOption.DIRS.optionName());
        try {
            for (IPackageFragmentRoot pfr : p.getPackageFragmentRoots()) {
                // PackageFragmentRoots can be source folders or jar files
                // We want just the source folders
                IResource f = (IResource)pfr.getAdapter(IResource.class);
                if (!(f instanceof IFolder)) continue;
                IJavaElement[] packages = pfr.getChildren();
                for (IJavaElement je : packages) {
                    IPackageFragment pf = (IPackageFragment)je;
                    // FIXME - will the following include folders of .jml files? what is the guard trying to exclude?
                    if (pf.containsJavaResources()) args.add(pf.getElementName()); // getElementName gives the fully qualified package name
                }
            }
            // FIXME - we need to do the following in the computational thread
            int ret = Factory.makeAPI().jmldoc(args.toArray(new String[args.size()]));
            return ret;
        } catch (JavaModelException e) {
            Log.errorlog("INTERNAL EXCEPTION while generating jmldoc",e);  //$NON-NLS-1$
        } catch (Exception e) {
            Log.errorlog("INTERNAL EXCEPTION while generating jmldoc",e);  //$NON-NLS-1$
        }
        return 3;
    }


    public void executeInferCommand(Main.Cmd command, List<?> things, IProgressMonitor monitor) {
        try {
            if (things.isEmpty()) {
                Log.log("Nothing applicable to process");
                Activator.utils().showMessageInUI(null,"JML","Nothing applicable to process");
                return;
            }
            setMonitor(monitor);

            List<String> args = getOptions(jproject,Main.Cmd.INFER);
            api.initOptions(null,  args.toArray(new String[args.size()]));

            List<IJavaElement> elements = new LinkedList<IJavaElement>();

            IResource rr;
            int count = 0;
            utils.refreshView(); // Sets up the view - then each result is added incrementally
            for (Object r: things) {
                try {
                    if (r instanceof IPackageFragment) {
                        count += utils.countMethods((IPackageFragment)r);
                    } else if (r instanceof IJavaProject) {
                        count += utils.countMethods((IJavaProject)r);
                    } else if (r instanceof IProject) {
                        count += utils.countMethods((IProject)r);
                    } else if (r instanceof IPackageFragmentRoot) {
                        count += utils.countMethods((IPackageFragmentRoot)r);
                    } else if (r instanceof ICompilationUnit) {
                        count += utils.countMethods((ICompilationUnit)r);
                    } else if (r instanceof IType) {
                        count += utils.countMethods((IType)r);
                    } else if (r instanceof IMethod) {
                        count += 1;
                    } else if (r instanceof IFile || r instanceof IFolder) {
                        // If a file is not part of a source folder, then we
                        // don't have Java elements and it is not a ICompilationUnit
                        // So we can't really count the methods in it.
                        // The number used here is arbitrary, and will result in
                        // a bad estimate of the work to be done. 
                        // TODO - count the methods using the OpenJML AST.
                        count += 2;
                    } else {
                        Log.log("Can't count methods in a " + r.getClass());
                    }
                } catch (Exception e) {
                    // FIXME - record exception
                }
            }

            final int oldArgsSize = args.size();

            for (Object r: things) { 
                // an IType is adaptable to an IResource (the containing file), but we want it left as an IType
                if (!(r instanceof IType) && r instanceof IAdaptable 
                                        && (rr=(IResource)((IAdaptable)r).getAdapter(IResource.class)) != null) {
                    r = rr;
                }
                if (r instanceof IFolder) {
                    if (hasAtLeastOneSourceFile((IFolder) r)) {
                        // we don't process empty folders
                        args.add(JmlOption.DIR.optionName());
                        args.add(((IResource)r).getLocation().toString());
                    }
                } else if (r instanceof IProject) {
                    // we only want to add source folders, and only if they actually have source in them
                    addSourceFoldersToCommandLine((IProject) r, args);
                } else if (r instanceof IResource) {
                    args.add(((IResource)r).getLocation().toString());
                } else if (r instanceof IType) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else if (r instanceof IMethod) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else if (r instanceof IJavaElement) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else Log.log("Ignoring " + r.getClass() + Strings.space + r.toString()); //$NON-NLS-1$
            }
            if (args.size() == oldArgsSize && elements.isEmpty()) {
                Log.log("No files or elements to process");
                Activator.utils().showMessageInUI(null,"JML","No files or elements to process");
                return;
            }

            if (monitor != null) {
                monitor.beginTask("Doing inference in project " + jproject.getElementName(),  4*count); // 4 ticks per method being checked
                monitor.subTask("Starting Inference on " + jproject.getElementName());
            }

            Timer.timer.markTime();

            if (!args.isEmpty()) {
                if (Options.uiverboseness) {
                    Log.log(Timer.timer.getTimeString() + " Executing Inference");
                }
                try {
                    int ret = api.execute(null,args.toArray(new String[args.size()]));
                    //utils.refreshView(); 

                    if (ret == Main.Result.OK.exitCode) Log.log(Timer.timer.getTimeString() + " Completed");
                    else if (ret == Main.Result.ERROR.exitCode) Log.log(Timer.timer.getTimeString() + " Completed with errors");
                    else if (ret >= Main.Result.CMDERR.exitCode) {
                        StringBuilder ss = new StringBuilder();
                        for (String c: args) {
                            ss.append(c);
                            ss.append(" ");
                        }
                        Log.errorlog("INTERNAL ERROR: return code = " + ret + "   Command: " + ss,null);  // FIXME _ dialogs are not working
                        Activator.utils().showMessageInUI(null,"Execution Failure","Internal failure in openjml - return code is " + ret + " " + ss); // FIXME - fix line ending
                    } else if (ret == Main.EXIT_CANCELED) {
                        // Cancelled
                        throw new Main.JmlCanceledException("Inference Canceled");
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
                    Activator.utils().showMessageInUI(null,"JML Execution Failure","Failure to execute openjml: " + e + " " + ss);
                }
            }

            for(IProject project : ResourcesPlugin.getWorkspace().getRoot().getProjects()){
                try {
                    project.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
                } catch (CoreException e) {
                    e.printStackTrace();
                }
            }
            // Now do individual methods
            // Delete all markers first, so that subsequent proofs do not delete
            // the markers from earlier proofs
            /*if (!elements.isEmpty()) {
            	for (IJavaElement je: elements) {
            		utils.deleteMarkers(je.getResource(),null); // FIXME - would prefer to delete markers and highlighting on just the method.
            	}
            	for (IJavaElement je: elements) {
            		if (je instanceof IMethod) {
            			MethodSymbol msym = convertMethod((IMethod)je);
            			if (msym == null) {
            				IResource r = je.getResource();
            				String filename = null;
            				try {
            					filename = r.getLocation().toString();
            					int errors = api.typecheck(api.parseFiles(filename));
            					if (errors == 0) {
            						msym = convertMethod((IMethod)je);
            					} else {
            						utils.showMessageInUI(null,"JML Error","Inference could not be performed because of JML typechecking errors");
            						msym = null;
            					}
            				} catch (java.io.IOException e) {
            					// FIXME - record or show exception?
        						utils.showMessageInUI(null,"JML Error","Inference could not be performed because of JML typechecking errors");
            					msym = null;
            				}
            			}
            			if (msym != null) {
            				Timer t = new Timer();
            				if (Options.uiverboseness)
            					Log.log("Beginning Inference on " + msym);
            				if (monitor != null) monitor.subTask("Infer " + msym);
            				IProverResult res = api.doESC(msym);
            				highlightCounterexamplePath((IMethod)je,res,null);
            			}
            			else {} // ERROR - FIXME
            		} else if (je instanceof IType) {
            			ClassSymbol csym = convertType((IType)je);
            			if (csym != null) api.doESC(csym);
            			else {} // ERROR - FIXME
            		}
            	}
                if (Options.uiverboseness) Log.log(Timer.timer.getTimeString() + " Completed Inference operation on individual methods");
            }
             */
            if (monitor != null) {
                monitor.subTask("Completed Inference operation");                
            }
        } catch (Main.JmlCanceledException e) {
            if (monitor != null) {
                monitor.subTask("Canceled Inference operation");
            }
            if (Options.uiverboseness) Log.log(Timer.timer.getTimeString() + " Canceled Inference operation");
        }
    }


    /** Executes the JML ESC (static checking) operation
     * on the given set of resources; launches computational threads.
     * @param command should be ESC
     * @param things the set of files (or containers) or Java elements to check
     * @param monitor the progress monitor the UI is using
     */
    // TODO - Review this
    public void executeESCCommand(Main.Cmd command, List<?> things, IProgressMonitor monitor, String description) {
        try {
            Date start = new Date();
            if (things.isEmpty()) {
                Log.log("Nothing applicable to process");
                Activator.utils().showMessageInUI(null,"JML","Nothing applicable to process");
                return;
            }
            //            if (api == null) {
            //                // FIXME - presumes the listener is a ConsoleLogger
            //                PrintWriter w = new PrintWriter(((ConsoleLogger)Log.log.listener()).getConsoleStream());
            //                api = new API(w,new EclipseDiagnosticListener(preq));
            //                api.setProgressReporter(new UIProgressReporter(api.context(),monitor,null));
            //            }

            List<String> args = getOptions(jproject,Main.Cmd.ESC);
            api.initOptions(null,  args.toArray(new String[args.size()]));
            //            args.clear();

            setMonitor(monitor); // Must be set after the options are initialized
            List<IJavaElement> elements = new LinkedList<IJavaElement>();

            IResource rr;
            utils.refreshView(); // Sets up the view - then each result is added incrementally
            int count = utils.countMethods(things);
            final int oldArgsSize = args.size();
            for (Object r: things) { 
                // an IType is adaptable to an IResource (the containing file), but we want it left as an IType
                if (!(r instanceof IType) && r instanceof IAdaptable 
                                        && (rr=(IResource)((IAdaptable)r).getAdapter(IResource.class)) != null) {
                    if (r instanceof IPackageFragment && ((IPackageFragment)r).isDefaultPackage()) {
                        // Do not add subdirectories
                        try {
                            for (IResource rrr: ((IFolder)rr).members(IResource.NONE)) {
                                if (rrr instanceof IFile && ((IFile)rrr).getFileExtension().equals("java")) {
                                    args.add(((IResource)rrr).getLocation().toString());
                                }
                            }
                        } catch (CoreException e) {} // FIXME - log an error
                        continue;
                    }
                    r = rr;
                }
                if (r instanceof IFolder) {
                    if (hasAtLeastOneSourceFile((IFolder) r)) {
                        // we don't process empty folders
                        args.add(JmlOption.DIR.optionName());
                        args.add(((IResource)r).getLocation().toString());
                    }
                } else if (r instanceof IProject) {
                    // we only want to add source folders, and only if they actually have source in them
                    addSourceFoldersToCommandLine((IProject) r, args);
                } else if (r instanceof IResource) {
                    args.add(((IResource)r).getLocation().toString());
                } else if (r instanceof IType) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else if (r instanceof IMethod) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else if (r instanceof IJavaElement) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else Log.log("Ignoring " + r.getClass() + Strings.space + r.toString()); //$NON-NLS-1$
            }
            if (args.size() == oldArgsSize && elements.isEmpty()) {
                Log.log("No files or elements to process");
                Activator.utils().showMessageInUI(null,"JML","No files or elements to process");
                return;
            }

            if (monitor != null) {
                monitor.beginTask(description,  count); // 1 tick for each completion
                monitor.subTask("Starting ESC on " + jproject.getElementName());
            }

            Timer.timer.markTime();
            if (args.size() != oldArgsSize) {
                if (Options.uiverboseness) {
                    Log.log(Timer.timer.getTimeString() + " Executing static checks");
                }
                try {
                    int ret = api.execute(null,args.toArray(new String[args.size()]));
                    if (ret == Main.Result.OK.exitCode) Log.log(Timer.timer.getTimeString() + " Completed");
                    if (ret == Main.Result.CANCELLED.exitCode) Log.log(Timer.timer.getTimeString() + " Cancelled");
                    else if (ret == Main.Result.ERROR.exitCode) Log.log(Timer.timer.getTimeString() + " Completed with errors");
                    else if (ret >= Main.Result.CMDERR.exitCode) {
                        StringBuilder ss = new StringBuilder();
                        for (String c: args) {
                            ss.append(c);
                            ss.append(" ");
                        }
                        Log.errorlog("INTERNAL ERROR: return code = " + ret + "   Command: " + ss,null);  // FIXME _ dialogs are not working
                        Activator.utils().showMessageInUI(null,"Execution Failure","Internal failure in openjml - return code is " + ret + " " + ss); // FIXME - fix line ending
                    } else if (ret == Main.EXIT_CANCELED) {
                        // Cancelled
                        throw new Main.JmlCanceledException("ESC Canceled");
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
                    Activator.utils().showMessageInUI(null,"JML Execution Failure","Failure to execute openjml: " + e + " " + ss);
                }
            }
            // Now do individual methods
            // Delete all markers first, so that subsequent proofs do not delete
            // the markers from earlier proofs
            if (!elements.isEmpty()) {
                for (IJavaElement je: elements) {
                    utils.deleteMarkers(je.getResource(),null); // FIXME - would prefer to delete markers and highlighting on just the method.
                }

                args = getOptions(jproject,Main.Cmd.CHECK);
                //api.initOptions(null,  args.toArray(new String[args.size()]));
                //args.clear();
                for (IJavaElement je: elements) {
                    String filepath = je.getResource().getLocation().toOSString();
                    args.add(filepath);
                }
                int ret = api.execute(null,args.toArray(new String[args.size()]));
                if (ret != 0) {
                    Activator.utils().showMessageInUI(null,"JML Execution Failure","Static check aborted because of syntax errors");
                    Log.log(Timer.timer.getTimeString() + " Static check aborted because of syntax errors");
                } else {

                    args = getOptions(jproject,Main.Cmd.ESC);
                    api.initOptions(null,  args.toArray(new String[args.size()]));

                    for (IJavaElement je: elements) {
                        if (je instanceof IMethod) {
                            MethodSymbol msym = convertMethod((IMethod)je);
                            if (msym == null) {
                                IResource r = je.getResource();
                                String filename = null;
                                try {
                                    filename = r.getLocation().toString();
                                    int errors = api.typecheck(api.parseFiles(filename));
                                    if (errors == 0) {
                                        msym = convertMethod((IMethod)je);
                                    } else {
                                        utils.showMessageInUI(null,"JML Error","ESC could not be performed because of JML typechecking errors");
                                        msym = null;
                                    }
                                } catch (java.io.IOException e) {
                                    // FIXME - record or show exception?
                                    utils.showMessageInUI(null,"JML Error","ESC could not be performed because of JML typechecking errors");
                                    msym = null;
                                }
                            }
                            if (msym != null) {
                                Timer t = new Timer();
                                if (Options.uiverboseness)
                                    Log.log("Beginning ESC on " + msym);
                                if (monitor != null) monitor.subTask("ESChecking " + msym);
                                IProverResult res = api.doESC(msym);
                                highlightCounterexamplePath((IMethod)je,res,null);
                            }
                            else {} // ERROR - FIXME
                        } else if (je instanceof IType) {
                            ClassSymbol csym = convertType((IType)je);
                            if (csym != null) api.doESC(csym);
                            else {} // ERROR - FIXME
                        }
                    }
                    if (Options.uiverboseness) Log.log(Timer.timer.getTimeString() + " Completed ESC operation on individual methods");
                }
            }
            if (monitor != null) {
                monitor.subTask("Completed ESC operation");
            }
        } catch (Main.JmlCanceledException e) {
            if (monitor != null) {
                monitor.subTask("Canceled ESC operation");
            }
            if (Options.uiverboseness) Log.log(Timer.timer.getTimeString() + " Canceled ESC operation");
        } finally {
            OpenJMLView.stop();
        }
    }

    //    public void highlightCounterexamplePath(IMethod je) {
    //		MethodSymbol msym = convertMethod(je);
    //		if (msym != null) highlightCounterexamplePath(je, msym, null);
    //    }

    public void highlightCounterexamplePath(IMethod je, IProverResult res, ICounterexample cce) {
        if (res == null) {
            utils.deleteHighlights(je.getResource(), null);
            return;
        }
        //    	Log.log("TIMES " + je.getResource().getLocalTimeStamp() + " " +  res.timestamp().getTime() + " " + (je.getResource().getLocalTimeStamp() > res.timestamp().getTime()));
        if (je.getResource().getLocalTimeStamp() > res.timestamp().getTime()) {
            utils.showMessageInUI(null, "OpenJML", "The file is newer than the counterexample information - the highlighting may be offset.");
        }
        utils.deleteHighlights(je.getResource(), null);
        if (res != null) {
            IProverResult.ICounterexample ce = cce != null ? cce : res.counterexample();
            if (ce != null && ce.getPath() != null) {
                for (IProverResult.Span span: ce.getPath()) {
                    if (span.end > span.start) { // The test is just defensive
                        utils.highlight(je.getResource(), span.start, span.end, span.type);
                    } else {
                        Log.log("BAD HIGHLIGHT RANGE " + span.start + " " + span.end + " " + span.type);
                    }
                }
            }
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
        String className = type.getFullyQualifiedName(); // FIXME - for files that are not actually Java files, the fully qualified name does not include the package ???
        if (className.indexOf('.') == -1) {
            // No dot in the name.  The class might be in the default package,
            // but also if the IType came from a file that is not in a source
            // folder, then the fullyQualifiedName does not include the package
            // I don't know whether this a bug or whether it is the intended
            // behavior for a non-real Java file such as a specification file.
            // In any case, we try to make amends.
            try {
                //System.out.println("NAME OF " + type.getElementName() + " " + className);
                ICompilationUnit cu = type.getCompilationUnit();
                //String s = type.getTypeQualifiedName();
                IPackageDeclaration[] pks = cu.getPackageDeclarations();
                if (pks.length > 0) {
                    // Documentation says not to expect more than one
                    String pname = pks[0].getElementName();
                    className = pname + Strings.dot + className;
                }
            } catch (Exception e) {
                throw new Utils.OpenJMLException("Could not find a class symbol for " + className,e); //$NON-NLS-1$
            }
        }
        ClassSymbol csym = api.getClassSymbol(className);
        return csym;
    }

    public IResource getResourceFor(Symbol sym) {
        if (sym instanceof MethodSymbol) sym = sym.owner;
        if (sym instanceof ClassSymbol) {
            IType t = convertType((ClassSymbol)sym);
            return t.getResource();
        }
        return null;
    }



    /** Converts Eclipse's representation of a method (an IMethod) to OpenJML's
     * (a MethodSymbol)
     * @param method the Eclipse IMethod for the method
     * @return OpenJML's MethodSymbol for the same method
     * @throws Utils.OpenJMLException if there is no match
     */
    public @Nullable MethodSymbol convertMethod(IMethod method) {
        ClassSymbol csym = convertType(method.getDeclaringType());
        if (csym == null) return null;
        try {
            com.sun.tools.javac.util.Name name = com.sun.tools.javac.util.Names.instance(api.context()).fromString(
                                    method.isConstructor() ? "<init>" : method.getElementName()); //$NON-NLS-1$
            Scope.Entry e = csym.members().lookup(name); // FIXME - Need to match types & number
            MethodSymbol firstsym = null;
            outer: while (e != null && e.sym != null) {
                Symbol sym = e.sym;
                e = e.next();
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
            String error = "No matching method in OpenJML: " + method.getDeclaringType().getFullyQualifiedName() + Strings.dot + method; //$NON-NLS-1$
            Log.errorlog(error,null);
            throw new Utils.OpenJMLException(error);
        } catch (JavaModelException e) {
            throw new Utils.OpenJMLException("Unable to convert method " + method.getElementName() + " of " + method.getDeclaringType().getFullyQualifiedName(),e); 
        }
    }

    public IMethod convertMethod(MethodSymbol msym) {
        try {
            String className = msym.owner.getQualifiedName().toString();
            IType eClass = jproject.findType(className); // FIXME - OK for nested classes?
            String mname = msym.name.toString();
            int nargs = msym.params.size();
            // FIXME - finds first match on name, not on tyep signature
            if (eClass == null) return null; // FIXME - this can happen if the class is not in a source folder
            for (IMethod m: eClass.getMethods()) {
                if (nargs == m.getNumberOfParameters() && mname.equals(m.getElementName())) return m;
            }
            return null;
            //eClass.getMethod(msym.name,toString(),)
        } catch (Exception e) {
            return null;
        }
    }

    public IType convertType(ClassSymbol sym) {
        try {
            String className = sym.getQualifiedName().toString();
            IType eClass = jproject.findType(className); // FIXME - OK for nested classes?
            return eClass;
        } catch (Exception e) {
            return null;
        }
    }

    // FIXME - review and document
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
                //String rest = tstring.substring(p+1);
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

    /** Return the specs of the given type, including all inherited specs,
     * pretty-printed as a String.  This
     * may be an empty String if there are no specifications.
     * @param type the Eclipse IType for the class whose specs are wanted
     * @return the corresponding specs, as a String
     */
    public @Nullable String getAllSpecs(@NonNull IType type) {
        ClassSymbol csym = convertType(type);
        if (csym == null) {
            return null;
        }
        List<TypeSpecs> typeSpecs = api.getAllSpecs(csym);
        try {
            StringBuilder sb = new StringBuilder();
            for (TypeSpecs ts: typeSpecs) {
                sb.append("From " + ts.file.getName() + Strings.eol); //$NON-NLS-1$
                sb.append(api.prettyPrintJML(ts.modifiers));
                sb.append(Strings.eol);
                sb.append(ts.toString());
                sb.append(Strings.eol);
            }
            return sb.toString();
        } catch (Exception e) { 
            return "<Exception>: " + e; //$NON-NLS-1$
        }
    }

    /** Return the specs of the given method, including all inherited specs,
     * pretty-printed as a String.  This
     * may be an empty String if there are no specifications.
     * @param method the Eclipse IMethod for the method whose specs are wanted
     * @return the corresponding specs, as a String
     */
    public @Nullable String getAllSpecs(@NonNull IMethod method) {
        MethodSymbol msym = convertMethod(method);
        if (msym == null) return null;
        List<JmlSpecs.MethodSpecs> methodSpecs = api.getAllSpecs(msym);
        try {
            StringBuilder sb = new StringBuilder();
            for (JmlSpecs.MethodSpecs ts: methodSpecs) {
                sb.append("From " + ts.cases.decl.sourcefile.getName()); //$NON-NLS-1$
                sb.append(Strings.eol);
                sb.append(api.prettyPrintJML(ts.mods)); // FIXME - want the collected mods in the JmlMethodSpecs
                sb.append(Strings.eol);
                sb.append(api.prettyPrintJML(ts.cases));
                sb.append(Strings.eol);
            }
            return sb.toString();
        } catch (Exception e) { 
            return "<Exception>: " + e;  //$NON-NLS-1$
        }

    }

    /** Returns the specs of the given field as a String
     * @param field the Eclipse IField value denoting the field whose specs are wanted
     * @return the specs of the field, as a String; or null, if specs not available
     */
    public @NonNull String getSpecs(@NonNull IField field) {
        String s = field.getDeclaringType().getFullyQualifiedName();
        ClassSymbol csym = api.getClassSymbol(s);
        if (csym == null)  return null;
        VarSymbol fsym = api.getVarSymbol(csym,field.getElementName());
        FieldSpecs fspecs = api.getSpecs(fsym);
        try { 
            return fspecs.toString();
        } catch (Exception e) { 
            return "<Exception>: " + e;  //$NON-NLS-1$
        }
    }

    // FIXME - revise this
    /** Show information about the most recent proof of the given method in a 
     * dialog box for the given Shell.  This information states whether the 
     * proof was performed, whether it was successful, and launches editor
     * windows containing the proof's counterexample context, trace, and
     * basic block program.
     * @param method the Eclipse IMethod for the method whose proof is wanted
     * @param shell the shell to be used to parent any dialog windows
     */
    public void showProofInfo(@NonNull IMethod method, @NonNull Shell shell, boolean showDetails) {
        IProverResult r = getProofResult(method);
        MethodSymbol msym = r.methodSymbol();

        utils.setTraceView(keyForSym(msym), method.getJavaProject());

        if (!showDetails) return;

        utils.showMessage(shell, "OpenJML", "Detailed proof information is not yet implemented");
        // DETAILS
        // FIXME - show altered program, basic block program, SMT program

        //        String s = ((API)api).getBasicBlockProgram(msym);
        //        utils.launchEditor(s,msym.owner.name + Strings.dot + msym.name);

        return;
    }

    // FIXME - documentation
    public String getCEValue(int pos, int end, String text, IResource r) {
        IJavaElement je = (IJavaElement)r.getAdapter(IJavaElement.class);
        ClassSymbol csym = convertType(((ICompilationUnit)je).findPrimaryType());
        if (api == null) return "No proof information available";
        com.sun.tools.javac.comp.Env<AttrContext> env = Enter.instance(api.context()).getEnv(csym);
        if (env == null) return "No proof information available";
        JmlCompilationUnit tree = (JmlCompilationUnit)env.toplevel;
        if (tree == null) return "No proof information available";
        API.Finder finder = api.findMethod(tree,pos,end,text,r.getLocation().toString());
        JmlMethodDecl parentMethod = finder.parentMethod;
        JCTree node = finder.found;
        if (parentMethod == null) return  "No containing method found";
        //      if (parentMethod.sym != mostRecentProofMethod) {
        //          return "Selected text is not within the method of the most recent proof (which is " + mostRecentProofMethod + ")";
        //      }
        String out;
        if (node instanceof JmlVariableDecl) {
            // This happens when we have selected a method parameter or the variable within a declaration
            // continue
            String name = ((JmlVariableDecl)node).name.toString();
            out = text == null ? null : ("Found declaration: " + name + "\n");
            //node = ((JmlVariableDecl)node).ident;
            if (text == null) out = "Declaration " + name + " <B>is</B> ";
        } else if (!(node instanceof JCTree.JCExpression)) {
            return text == null ? null : ("Selected text is not an expression (" + node.getClass() + "): " + text);
        } else {
            if (text == null) out = node.toString().replace("<", "&lt;") + " <B>is</B> ";
            else    out = "Found expression node: " + node.toString() + "\n";
        }

        IProverResult res = getProofResult(parentMethod.sym);

        if (res != null) {
            ICounterexample ce = res.counterexample();
            if (ce == null) return null;
            String value = ce.get(node);
            if (value != null) {
                if (text == null) out = out + value;
                else out = out + "Value " + node.type + " : " + value;
                if (node.type.getTag() == TypeTag.CHAR) {
                    try {
                        out = out + " ('" + (char)Integer.parseInt(value) + "')"; 
                    } catch (NumberFormatException e) {
                        // ignore
                    }
                } else if (value.startsWith("#x")) {
                    try {
                        value = value.substring(2);
                        if (value.length() > 2*Integer.BYTES) {
                            long i = Long.parseLong(value,16);
                            out = out + " (" + i + ")";
                        } else {
                            int i = (int)Long.parseLong(value,16);
                            if (i == Integer.MIN_VALUE) {
                                out = out + " (" + i + " == MININT)";

                            } else if (i == Integer.MAX_VALUE) {
                                out = out + " (" + i + " == MAXINT)";
                            } else {
                                out = out + " (" + i + ")";
                            }
                        }
                    } catch (Exception e) {
                        Object o = e;
                    }
                }
            }
            else out = text == null ? null : (out + "Value is unknown (type " + node.type + ")");
            return out;
        }
        return null;
        //return "No counterexample information available";

    }

    /** Instances of this class can be registered as OpenJML DiagnosticListeners (that is,
     * listeners for errors from tools in the javac framework); they then convert
     * any diagnostic into an Eclipse problem (a JmlEclipseProblem) of the 
     * appropriate severity, which is
     * then fed to the given IProblemRequestor.
     * 
     * @author David Cok
     *
     */
    static public class EclipseDiagnosticListener implements DiagnosticListener<JavaFileObject> {

        /** When this listener hears a problem from OpenJML, 
         * it needs to report the problem to Eclipse, by calling report
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
        @Override
        @SuppressWarnings("restriction")
        public void report(@NonNull Diagnostic<? extends JavaFileObject> diagnostic) {
            JavaFileObject javaFileObject = diagnostic.getSource();
            String message = diagnostic.getMessage(null); // uses default locale
            int id = 0; // TODO - we are not providing numerical ids for problems
            Diagnostic.Kind kind = diagnostic.getKind();
            // Here the Diagnostic.Kind is the categorization of errors from OpenJDK
            //  We use: ERROR - compilation and JML typechecking errors
            //          WARNING - less serious JML typechecking errors (e.g. deprecated syntax)
            //          NOTE - informational - e.g. features not implemented and hence ignored
            //          OTHER - used for static checking warnings
            // The ProblemSeverities are Eclipse's categorization of errors
            //          There are various kinds of errors, of which we only use Error (e.g. also Fatal, Abort, ...)
            //          As you see we map  ERROR -> Error, WARNING -> Warning,
            //                             NOTE -> Ignore, OTHER (static check warnings) -> SecondaryError
            // Static check warnings could be mapped to Warning, but we want to 
            // distinguish them from Errors and Warnings.  This is a little problem 
            // prone.  Also, I think that some compiler options might turn off
            // the NOTE/Ignore markers - check this - TODO
            int severity = 
                                    kind == Diagnostic.Kind.ERROR ? ProblemSeverities.Error :
                                        kind == Diagnostic.Kind.WARNING ? ProblemSeverities.Warning :
                                            kind == Diagnostic.Kind.MANDATORY_WARNING ? ProblemSeverities.Error : 
                                                kind == Diagnostic.Kind.NOTE ? ProblemSeverities.Ignore : 
                                                    kind == Diagnostic.Kind.OTHER ? ProblemSeverities.SecondaryError : 
                                                        ProblemSeverities.Error; // There should not be anything else, but we'll call it an error just in case.

            long pos = diagnostic.getPosition();
            long col = diagnostic.getColumnNumber();// 1-based, from beginning of line
            long line = diagnostic.getLineNumber(); // 1-based
            long startPos = diagnostic.getStartPosition();  //0-based, from beginning of file
            long endPos = diagnostic.getEndPosition();
            if (endPos <= 0) endPos = startPos; // This is defensive - sometimes there is no end position set

            int ENOPOS = -1; // Eclipse value for not having position information

            long startPosition = pos == Diagnostic.NOPOS ? ENOPOS : (startPos-pos) + col; // FIXME - a hack - what if crosses lines
            long endPosition = pos == Diagnostic.NOPOS ? ENOPOS : (endPos-pos) + col; // FIXME - a hack - what if crosses lines

            long lineStart = pos == Diagnostic.NOPOS ? ENOPOS : (pos - col); // FIXME - a hack
            long lineEnd = pos == Diagnostic.NOPOS ? ENOPOS : lineStart + 100; // FIXME - a real hack

            IWorkspace workspace = ResourcesPlugin.getWorkspace();
            IWorkspaceRoot root = workspace.getRoot();
            IFile resource = null;
            if (javaFileObject != null) { // if null, there is no source file
                URI filename = javaFileObject.toUri(); // This should be the full, absolute path 
                IPath path = new Path(filename.getPath());
                resource = root.getFileForLocation(path); // For this to be non-null, 
                // the file must be in the workspace.  This means that all
                // source AND SPECS must be in open projects in the workspace.
                //FIXME - linked resources will not work here I think
            }

            if (resource == null) {
                // This can happen when the file to which the diagnostic points
                // is not an IResource. For example, the Associated Declaration
                // to an error may be in a system specifications file.
                // FIXME - we should load a read-only text file, with the markers
                // for this case.
                if (!diagnostic.toString().contains("Associated declaration")) {
                    if (severity == ProblemSeverities.Error) Log.errorlog(diagnostic.toString(),null);
                    else Log.log(diagnostic.toString());
                }
            } else {
                String text = null;
                // FIXME - the following does not work
                //            	try {
                //            		text = javaFileObject == null ? null : javaFileObject.getCharContent(true).toString();
                //            	} catch (java.io.IOException e) {
                //            		// ignore - just leave text as null;
                //            	}
                JmlEclipseProblem problem = new JmlEclipseProblem(resource, message, id,  severity,
                                        (int)startPosition, (int)endPosition, (int)line, 
                                        text,
                                        (int)lineStart, (int)lineEnd);
                problem.sourceSymbol = currentMethod;
                preq.acceptProblem(problem);
                // Log it as well
                if (Options.uiverboseness) {
                    if (severity == ProblemSeverities.Error) Log.errorlog(diagnostic.toString(),null);
                    else Log.log(diagnostic.toString());
                }
            }
        }

    }

    /** This class is a specific instantiation of the IProgressReporter interface;
     * it receives progress report calls and both logs them and displays them
     * in the progress monitor supplied by the Eclipse UI.
     * @author David R. Cok
     */
    public static class UIProgressListener implements org.jmlspecs.openjml.Main.IProgressListener {
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
        public UIProgressListener(@NonNull Context context, @Nullable IProgressMonitor monitor, @Nullable Shell shell) {
            this.monitor = monitor;
            this.context = context;
            this.shell = shell;
        }

        /** This is the method called by OpenJML when a progress message is sent.
         * The implementation here logs the message if the level is <=1 and
         * displays it in the progress monitor if one was supplied in the
         * constructor.  The UI work is done in a Runnable spawned from
         * Display.asyncExec .
         * @return true if the progress reporter was canceled
         */
        //@ ensures not_assigned(this.*);
        @Override
        public boolean report(final int level, final String message) {
            Display d = shell == null ? Display.getDefault() : shell.getDisplay();
            String summary = OpenJMLView.exportProofResults(null);
            final String message2 = summary == null ? message : (summary + Strings.eol + message);
            // Singleton reported that with asynExec, this would hang
            d.syncExec(new Runnable() {
                public void run() {
                    if (monitor != null) {
                        if (level <= 1) monitor.subTask(message2);
                    }
                    Log.log(message);
                }
            });
            boolean cancel = monitor != null && monitor.isCanceled();
            //            if (cancel) {
            //            	cancel = true;
            //            	//throw new Main.JmlCanceledException("Operation cancelled"); //$NON-NLS-1$
            //            	//throw new PropagatedException(new Main.JmlCanceledException("Operation cancelled")); //$NON-NLS-1$
            //            }
            return cancel;
        }

        @Override
        public void worked(int ticks) {
            if (monitor != null) monitor.worked(ticks);
        }

        /** Sets the OpenJML compilation context associated with this listener. */
        @Override
        //@ assignable this.context;
        //@ ensures this.context == context;
        public void setContext(@NonNull Context context) { 
            this.context = context; 
        }
    }

    Map<String,IProverResult> proofResults = new HashMap<String,IProverResult>();
    Map<IMethod,String> methodResults = new HashMap<IMethod,String>();

    protected String keyForSym(Symbol sym) {
        if (sym instanceof MethodSymbol) {
            return sym.owner.getQualifiedName().toString() + Strings.dot + sym.toString();
        } else if (sym.name.isEmpty()) {
            return ((ClassSymbol)sym).flatname.toString(); // for anonymous types
        } else {
            return sym.getQualifiedName().toString();
        }
    }

    @Override
    public void reportProofResult(MethodSymbol msym, IProverResult result) {
        if (result.result() == IProverResult.RUNNING) {
            currentMethod = msym;
        }
        if (result.result() == IProverResult.COMPLETED) {
            currentMethod = null;
            return;
        }
        if (result.result() == IProverResult.ERROR) {
            if (result.otherInfo() == null) {
                List<String> messages = Log.collect(true);
                String text = String.join(Strings.eol, messages);
                result.setOtherInfo(text);
            } else {
                Log.collect(true);
            }
        }
        String key = keyForSym(msym);
        proofResults.put(key,result);
        IMethod m = convertMethod(msym);
        methodResults.put(m, key);
        Runnable runnable = new Runnable() {
            public void run() {
                utils.refreshView(jproject,key);
            }
        };
        Display.getDefault().asyncExec(runnable);
    }

    static MethodSymbol currentMethod;


    public @Nullable IProverResult getProofResult(MethodSymbol msym) {
        return proofResults.get(keyForSym(msym));
    }

    public @Nullable IProverResult getProofResult(IMethod m) {
        String key = methodResults.get(m);
        if (key == null) return null;
        return proofResults.get(key);
    }

    public @Nullable Map<String,IProverResult> getProofResults() {
        return proofResults;
    }

    public void clearProofResults(IJavaProject currentProject) {
        proofResults.clear();
        methodResults.clear();
    }




    /** Sets the monitor to be used to show progress
     * @param monitor the monitor to be used, if any
     */
    public void setMonitor(@Nullable IProgressMonitor monitor) {
        if (monitor != null) {
            api.setProgressListener(new UIProgressListener(api.context(),monitor,null));
        } else {
            api.setProgressListener(null);
        }
    }

    /** Retrieves the options from the preference page, determines the 
     * corresponding options for OpenJML, tailored to the given Cmd.
     * If cmd is null, all options are retrieved.
     * @param jproject
     * @param cmd The command to be executed, or null to get all options
     * @return the list of options and arguments
     */
    public @NonNull List<String> getOptions(IJavaProject jproject, /*@nullable*/Main.Cmd cmd) {

        //com.sun.tools.javac.util.Options openjmlOptions = com.sun.tools.javac.util.Options.instance(api.context());
        String eq = "="; //$NON-NLS-1$

        //Options opt = Activator.options;
        List<String> opts = new LinkedList<String>();
        if (cmd != null) {
            opts.add(JmlOption.COMMAND.optionName() +eq+ cmd);
        }
        {
            opts.add(JmlOption.LANG.optionName() +eq+ Options.value(Options.strictKey));
            opts.add(JmlOption.PURITYCHECK.optionName() +eq+ Options.isOption(Options.purityCheckKey));
            opts.add(JmlOption.SHOW.optionName() +eq+ Options.isOption(Options.showKey));
        }
        if (cmd == Main.Cmd.ESC || cmd == null) {
            String prover = Options.value(Options.defaultProverKey);
            opts.add(JmlOption.PROVER.optionName() +eq+ prover);

            String internal_external = Options.value(SolversPage.execLocKeyPrefix + prover);
            String exec = null;
            if ("internal".equals(internal_external)) {
                //Log.log("Using internal solver. Default is " + prover);
                URL url = null;
                try {
                    String osname = org.jmlspecs.openjml.Utils.identifyOS(null);
                    Bundle bundle = Platform.getBundle("org.jmlspecs.Solvers");
                    if (bundle != null) {
                        String ex = osname.equals("windows") ? "/z3-4.3.2.exe" : "/z3-4.3.1";
                        url = FileLocator.find(bundle, new Path("Solvers-"+osname+ex), Collections.EMPTY_MAP);
                        if (url != null) url = FileLocator.toFileURL(url);
                        if (url != null) {
                            exec = url.getFile();
                            Files.setPosixFilePermissions(java.nio.file.Paths.get(url.toURI()), PosixFilePermissions.fromString("rwxr-xr-x"));
                        }
                    }
                } catch (Exception e) {
                    exec = null;
                    Log.log("Internal solver exception " + e.toString());
                }
                java.nio.file.Path path = FileSystems.getDefault().getPath(exec);
                if (exec == null || !Files.exists(path)) {
                    utils.showMessageInUI(null,"OpenJML error","Internal solver for " + prover + "is not found");
                } else if (!Files.isExecutable(path)) {
                    utils.showMessageInUI(null,"OpenJML error","Internal solver for " + prover + "is not executable");
                }
            } else {
                exec = Options.value(Options.proverPrefix + prover);
                Log.log("Using external solver " + exec);
            }
            opts.add(JmlOption.PROVEREXEC.optionName() +eq+ exec);
            opts.add(JmlOption.ESC_MAX_WARNINGS.optionName() +eq+ Options.value(Options.escMaxWarningsKey));
            opts.add(JmlOption.TRACE.optionName() +eq+ "true");
            opts.add(JmlOption.SUBEXPRESSIONS.optionName() +eq+ "true");
            opts.add(JmlOption.FEASIBILITY.optionName() +eq+ Options.value(Options.feasibilityKey));
            String v = Options.value(Options.timeoutKey);
            if (v != null && !v.isEmpty()) opts.add(JmlOption.TIMEOUT.optionName() +eq+ v);
            // FIXME - add an actual option
            opts.add("-code-math=safe");
            opts.add("-spec-math=bigint");
        }

        if (cmd == Main.Cmd.INFER) {
            String prover = Options.value(Options.defaultProverKey);
            opts.add(JmlOption.PROVER.optionName() +eq+ prover);
            opts.add(JmlOption.PROVEREXEC.optionName() +eq+ Options.value(Options.proverPrefix + prover));

            //TODO -- make these options
            if(StrongarmPage.getDefaultBoolean(Options.inferDebug).equalsIgnoreCase("true")){
                opts.add(OptionsInfer.INFER_DEBUG.optionName());
            }
            opts.add(OptionsInfer.INFER_TIMEOUT.optionName() +eq+ StrongarmPage.getDefaultInt(Options.inferTimeout));

            opts.add(OptionsInfer.INFER_MAX_DEPTH.optionName() +eq+ StrongarmPage.getDefaultInt(Options.inferMaxDepth));


            if(StrongarmPage.getDefaultBoolean(Options.inferDevTools).equalsIgnoreCase("true")){
                opts.add(OptionsInfer.INFER_DEV_MODE.optionName());
            }

            if(StrongarmPage.getDefaultBoolean(Options.inferDefaultPrecondition).equalsIgnoreCase("true")){
                opts.add(OptionsInfer.INFER_PRECONDITIONS.optionName() +eq+ StrongarmPage.getDefaultBoolean(Options.inferDefaultPrecondition));
            }


            if(StrongarmPage.getDefaultString(Options.inferPersistSpecsTo).equalsIgnoreCase(StrongarmPage.WEAVE_SEPERATE)){
                opts.add(OptionsInfer.INFER_PERSIST.optionName() + eq+ "jml");
            }else{
                opts.add(OptionsInfer.INFER_PERSIST.optionName() + eq+ "java");
            }

        }

        if (cmd == Main.Cmd.RAC || cmd == null) {
            opts.add(JmlOption.RAC_SHOW_SOURCE.optionName() +eq+ Options.isOption(Options.racShowSource));
            opts.add(JmlOption.RAC_CHECK_ASSUMPTIONS.optionName() +eq+ Options.isOption(Options.racCheckAssumptions));
            opts.add(JmlOption.RAC_PRECONDITION_ENTRY.optionName() +eq+ Options.isOption(Options.racPreconditionEntry));
            opts.add(JmlOption.RAC_JAVA_CHECKS.optionName() +eq+ Options.isOption(Options.racCheckJavaFeatures));
            opts.add(JmlOption.RAC_COMPILE_TO_JAVA_ASSERT.optionName() +eq+ Options.isOption(Options.compileToJavaAssert));
        }

        String v = Options.value(Options.verbosityKey);
        opts.add(JmlOption.VERBOSENESS.optionName()+eq+"2"); // If not at least progress, the monitors will be stuck

        if (Options.isOption(Options.javaverboseKey)) {
            opts.add(com.sun.tools.javac.main.Option.VERBOSE.getText());
        }

        if (Options.isOption(Options.showNotImplementedKey)) opts.add(JmlOption.SHOW_NOT_IMPLEMENTED.optionName());
        if (Options.isOption(Options.showNotExecutableKey)) opts.add(JmlOption.SHOW_NOT_EXECUTABLE.optionName());
        if (Options.isOption(Options.checkSpecsPathKey)) opts.add(JmlOption.CHECKSPECSPATH.optionName());
        opts.add(JmlOption.NULLABLEBYDEFAULT.optionName()+eq+Options.isOption(Options.nullableByDefaultKey));

        String other = Options.value(Options.otherOptionsKey);
        if (other != null) {
            other = other.trim();
            // Split by whitespace (won't handle quoted strings with whitespace)
            if (!other.isEmpty()) for (String o : other.split("\\s")) { //$NON-NLS-1$
                opts.add(o);
            }
        }


        if (cmd == Main.Cmd.JMLDOC) {
            // jmldoc specific options
            opts.add("-private"); //$NON-NLS-1$
        }

        // The plug-in adds the internal specs (or asks the user for external specs)
        // So, openjml itself never needs to
        opts.add("-no"+JmlOption.INTERNALSPECS.getText());
        opts.add(JmlOption.SPECS.optionName());
        opts.add(PathItem.getAbsolutePath(jproject,Env.specsKey));

        opts.add(com.sun.tools.javac.main.Option.SOURCEPATH.getText()); 
        opts.add(PathItem.getAbsolutePath(jproject,Env.sourceKey));


        // Handle the classpath and internal runtime library if needed

        List<String> cpes = utils.getClasspath(jproject);
        boolean first = true;
        StringBuilder ss = new StringBuilder();
        for (String s: cpes) {
            if (first) first = false; else ss.append(File.pathSeparator);
            ss.append(s);
        }

        // The runtime library is always either in the classpath or added 
        // here by the plugin, so openjml itself never adds it
        opts.add("-no"+JmlOption.INTERNALRUNTIME.optionName());
        if (Options.isOption(Options.useInternalRuntimeKey)) {
            String runtime = utils.fetchRuntimeLibEntry();
            if (runtime != null) {
                ss.append(File.pathSeparator);
                ss.append(runtime);
            }
        }

        opts.add(Strings.classpathOptionName);
        opts.add(ss.toString());

        // FIXME - what about these options
        // roots, nojml, nojavacompiler
        // trace subexpressions counterexample
        // specs, stopiferrors
        // Java options, Jmldoc options
        if (Options.uiverboseness) {
            StringBuilder s = new StringBuilder();
            s.append("Options collected by UI to send to OpenJML: "); //$NON-NLS-1$
            for (String opt: opts) {
                s.append(Strings.space);
                s.append(opt);
            }
            Log.log(s.toString());
        }

        return opts;
    }

    /** Adds additional command-line options in the OpenJml object
     */
    public void addOptions(String... args) {
        api.addOptions(args);
    }

    /** Gets a String representation of the BasicBlock encoding of the method
     * body for the given method.
     * @param msym the method whose body is to be returned
     * @return a String representation of the Basic Bloxk program for the method body
     */
    public @NonNull String getBasicBlockProgram(@NonNull MethodSymbol msym) {
        return ""; // FIXME: ((API)api).getBasicBlockProgram(msym);
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
