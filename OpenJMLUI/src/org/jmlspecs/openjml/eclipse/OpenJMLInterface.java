/*
 * This file is part of the OpenJML plugin project. 
 * Copyright (c) 2006-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.io.PrintWriter;
import java.net.URI;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
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
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageDeclaration;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IProblemRequestor;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.compiler.problem.ProblemSeverities;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.SpecPublic;
import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Main.JmlCanceledException;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.eclipse.Utils.OpenJMLException;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.osgi.framework.Bundle;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
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
public class OpenJMLInterface {
	
    /** The API object corresponding to this Interface class. */
    @NonNull
    protected IAPI api;
    
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
   
   public void initialize(/*@nullable*/ Main.Cmd cmd) {
       preq = new JmlProblemRequestor(jproject); 
       PrintWriter w = Log.log.listener() != null ? 
    		   new PrintWriter(Log.log.listener().getStream(),true) : null;
       List<String> opts = getOptions(jproject,cmd);
       try { 
    	   api = Factory.makeAPI(w,new EclipseDiagnosticListener(preq), null, opts.toArray(new String[0])); //, new String[]{/*"-noInternalRuntime"*/}); 
       } catch (Exception e) {
    	   Log.errorlog("Failed to create an interface to OpenJML",e);
       }
   }
   
   /** Executes the JML Check (syntax and typechecking) or the RAC compiler
    * operations on the given set of resources.
    * @param command either CHECK or RAC
    * @param files the set of files (or containers) to check
    * @param monitor the progress monitor the UI is using
    */
   public void executeExternalCommand(Main.Cmd command, Collection<IResource> files, @Nullable IProgressMonitor monitor) {
	   boolean verboseProgress = Utils.verboseness >= Utils.NORMAL;
       try {
           if (files.isEmpty()) {
               if (verboseProgress) Log.log("Nothing applicable to process");
               Activator.getDefault().utils.showMessageInUI(null,"JML","Nothing applicable to process");
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
        			   // FIXME - error
        		   }
        	   }
        	   args.add("-d");
        	   args.add(jp.getProject().getLocation().append(racdir).toString());
           }

           for (IResource r: files) {
           	if (r instanceof IProject) {
           		args.add(JmlOption.DIR.optionName());
                   args.add(r.getLocation().toString());
           	} else {
           		if (r instanceof IFolder) args.add(JmlOption.DIR.optionName());
                args.add(r.getLocation().toString());
           	}
           }
           Timer.timer.markTime();
           if (verboseProgress) {
        	   String s = files.size() == 1 ? files.iterator().next().getName() : (files.size() + " items");
        	   Log.log(Timer.timer.getTimeString() + " Executing openjml on " + s);
           }
           if (monitor != null) {
               monitor.setTaskName(command == Main.Cmd.RAC ? "JML RAC" : "JML Checking");
               monitor.subTask("Executing openjml");
           }
           try {
               setMonitor(monitor);
               int ret = api.execute(null,args.toArray(new String[args.size()]));
               if (ret == Main.EXIT_OK) {
            	   if (verboseProgress) Log.log(Timer.timer.getTimeString() + " Completed");
               }
               else if (ret == Main.EXIT_CANCELED) {
            	   throw new Main.JmlCanceledException(Utils.emptyString);
               }
               else if (ret == Main.EXIT_ERROR) {
            	   if (verboseProgress) Log.log(Timer.timer.getTimeString() + " Completed with errors");
               }
               else if (ret == Main.EXIT_CMDERR) {
                   StringBuilder ss = new StringBuilder();
                   for (String r: args) {
                       ss.append(r);
                       ss.append(Utils.space);
                   }
                   Log.errorlog("INVALID COMMAND LINE: return code = " + ret + "   Command: " + ss,null);  // FIXME - the reason for the bad command line is lost (it would be an internal error)
                   Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Invalid commandline - return code is " + ret + eol + ss);
               }
               else if (ret >= Main.EXIT_SYSERR) {
                   StringBuilder ss = new StringBuilder();
                   for (String r: args) {
                       ss.append(r);
                       ss.append(Utils.space);
                   }
                   Log.errorlog("INTERNAL ERROR: return code = " + ret + "   Command: " + ss,null);  // FIXME - when the error is the result of an exception, we don't see the result
                   Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Internal failure in openjml - return code is " + ret + " " + ss); 
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
               Log.errorlog("Failure to execute openjml: "+ss,e); 
               Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Failure to execute openjml: " + e + " " + ss);
           }
           if (monitor != null) monitor.subTask("Completed openjml");
       } catch (JmlCanceledException e) {
           if (monitor != null) monitor.subTask("OpenJML Canceled: " + e.getMessage());
    	   if (verboseProgress) Log.log(Timer.timer.getTimeString() + " Operation canceled");
       }
   }
   
//   /** Executes the JML Check (syntax and typechecking) or the RAC compiler
//    * operations on the given set of resources.
//    * @param command either CHECK or RAC
//    * @param files the set of files (or containers) to check
//    * @param monitor the progress monitor the UI is using
//    */
//   public void executeTypeCheck(List<IResource> files, @Nullable IProgressMonitor monitor) {
//       try {
//           if (files.isEmpty()) {
//               Log.log("Nothing applicable to process");
//               Activator.getDefault().utils.showMessageInUI(null,"JML","Nothing applicable to process");
//               return;
//           }
//           IJavaProject jp = JavaCore.create(files.get(0).getProject());
//           //List<String> args = getOptions(jp,Cmd.CHECK);
//           List<String> args = new ArrayList<String>();
//
//           // FIXME - need to expand into all files
//           
//           for (IResource r: files) {
//           	if (r instanceof IProject) {
//           		args.add(JmlOption.DIR.optionName());
//                   args.add(r.getLocation().toString());
//           	} else {
//           		if (r instanceof IFolder) args.add(JmlOption.DIR.optionName());
//                   args.add(r.getLocation().toString());
//           	}
//           }
//           if (Utils.uiverbose >= Utils.NORMAL) Log.log(Timer.timer.getTimeString() + " Executing openjml ");
//           if (monitor != null) {
//               monitor.setTaskName("JML Checking");
//               monitor.subTask("Executing openjml");
//           }
//           try {
//               setMonitor(monitor);
//               int ret = api.typecheck(api.parseFiles(args.toArray(new String[args.size()])));
//               if (ret == 0) Log.log(Timer.timer.getTimeString() + " Completed");
//               else if (ret == 1) Log.log(Timer.timer.getTimeString() + " Completed with errors");
//               else if (ret >= 2) {
//                   StringBuilder ss = new StringBuilder();
//                   for (String r: args) {
//                       ss.append(r);
//                       ss.append(" ");
//                   }
//                   Log.errorlog("INVALID COMMAND LINE: return code = " + ret + "   Command: " + ss,null);  // FIXME _ dialogs are not working
//                   Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Invalid commandline - return code is " + ret + eol + ss);
//               }
//               else if (ret >= 3) {
//                   StringBuilder ss = new StringBuilder();
//                   for (String r: args) {
//                       ss.append(r);
//                       ss.append(" ");
//                   }
//                   Log.errorlog("INTERNAL ERROR: return code = " + ret + "   Command: " + ss,null);  // FIXME _ dialogs are not working
//                   Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Internal failure in openjml - return code is " + ret + " " + ss); // FIXME - fix line ending
//               }
//           } catch (JmlCanceledException e) {
//               throw e;
//           } catch (Throwable e) {
//               StringBuilder ss = new StringBuilder();
//               for (String c: args) {
//                   ss.append(c);
//                   ss.append(" ");
//               }
//               Log.errorlog("Failure to execute openjml: "+ss,e); 
//               Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Failure to execute openjml: " + e + " " + ss);
//           }
//           if (monitor != null) monitor.subTask("Completed openjml");
//       } catch (JmlCanceledException e) {
//           if (monitor != null) monitor.subTask("OpenJML Canceled: " + e.getMessage());
//       }
//   }
   
    /** Executes the jmldoc tool on the given project, producing output according
     * to the current set of options.
     * @param p the project whose jmldocs are to be produced
     * @return 0 for success, 1 for command-line errors, 2 for system errors,
     *     3 for internal or otherwise catastrophic errors
     */
    public int generateJmldoc(IJavaProject p) {
        List<String> args = getOptions(p,Main.Cmd.JMLDOC);
        args.add("-d");
        args.add(p.getProject().getLocation().toString() + File.separator + "docx");
        //args.add(JmlOption.DIRS.optionName());
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
            int ret = Factory.makeAPI().jmldoc(args.toArray(new String[args.size()]));
            return ret;
        } catch (JavaModelException e) {
            Log.errorlog("INTERNAL EXCEPTION while generating jmldoc",e); 
        } catch (Exception e) {
            Log.errorlog("INTERNAL EXCEPTION while generating jmldoc",e); 
        }
        return -1;
    }

    /** Executes the JML ESC (static checking) operation
     * on the given set of resources.
     * @param command should be ESC
     * @param things the set of files (or containers) or Java elements to check
     * @param monitor the progress monitor the UI is using
     */
    public void executeESCCommand(Main.Cmd command, List<Object> things, IProgressMonitor monitor) {
        try {
            if (things.isEmpty()) {
                Log.log("Nothing applicable to process");
                Activator.getDefault().utils.showMessageInUI(null,"JML","Nothing applicable to process");
                return;
            }
//            if (api == null) {
//                // FIXME - presumes the listener is a ConsoleLogger
//                PrintWriter w = new PrintWriter(((ConsoleLogger)Log.log.listener()).getConsoleStream());
//                api = new API(w,new EclipseDiagnosticListener(preq));
//                api.setProgressReporter(new UIProgressReporter(api.context(),monitor,null));
//            }
            setMonitor(monitor);
           
            List<String> args = getOptions(jproject,Main.Cmd.ESC);
            api.addOptions(null,  args.toArray(new String[args.size()]));
            args.clear();
            
            List<IJavaElement> elements = new LinkedList<IJavaElement>();
            
            IResource rr;
            int count = 0;
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
            		} else {
            			Log.log("Can't count methods in a " + r.getClass());
            		}
            	} catch (Exception e) {}
            }
            for (Object r: things) { // an IType is adaptable to an IResource (the containing file), but we want it left as an IType
                if (!(r instanceof IType) && r instanceof IAdaptable 
                		&& (rr=(IResource)((IAdaptable)r).getAdapter(IResource.class)) != null) {
                	r = rr;
                }
                if (r instanceof IFolder) {
                	args.add(JmlOption.DIR.optionName());
                	args.add(((IResource)r).getLocation().toString());
                } else if (r instanceof IProject) {
                	args.add(JmlOption.DIR.optionName());
                    args.add(((IResource)r).getLocation().toString());
                } else if (r instanceof IResource) {
                    args.add(((IResource)r).getLocation().toString());
                } else if (r instanceof IType) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else if (r instanceof IMethod) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else if (r instanceof IJavaElement) {  // Here we want types and methods, but a JavaProject is also an IJavaElement
                    elements.add((IJavaElement)r);
                } else Log.log("Ignoring " + r.getClass() + " " + r.toString());
            }
            if (args.isEmpty() && elements.isEmpty()) {
                Log.log("No files or elements to process");
                Activator.getDefault().utils.showMessageInUI(null,"JML","No files or elements to process");
                return;
            }
            
            if (monitor != null) {
            	monitor.beginTask("Static checks in project " + jproject.getElementName(),  4*count); // 4 ticks per method being checked
            	monitor.subTask("Starting ESC on " + jproject.getElementName());
            }

        	Timer.timer.markTime();
            if (!args.isEmpty()) {
            	if (Utils.verboseness >= Utils.NORMAL) {
            		Log.log(Timer.timer.getTimeString() + " Executing static checks");
            	}
                try {
                    int ret = api.execute(null,args.toArray(new String[args.size()]));
                    if (ret == Main.EXIT_OK) Log.log(Timer.timer.getTimeString() + " Completed");
                    else if (ret == Main.EXIT_ERROR) Log.log(Timer.timer.getTimeString() + " Completed with errors");
                    else if (ret >= Main.EXIT_CMDERR) {
                        StringBuilder ss = new StringBuilder();
                        for (String c: args) {
                            ss.append(c);
                            ss.append(" ");
                        }
                        Log.errorlog("INTERNAL ERROR: return code = " + ret + "   Command: " + ss,null);  // FIXME _ dialogs are not working
                        Activator.getDefault().utils.showMessageInUI(null,"Execution Failure","Internal failure in openjml - return code is " + ret + " " + ss); // FIXME - fix line ending
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
                    Activator.getDefault().utils.showMessageInUI(null,"JML Execution Failure","Failure to execute openjml: " + e + " " + ss);
                }
            }
            // Now do individual methods
            // Delete all markers first, so that subsequent proofs do not delete
            // the markers from earlier proofs
            if (!elements.isEmpty()) {
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
            					api.typecheck(api.parseFiles(filename));
            					msym = convertMethod((IMethod)je);
            				} catch (java.io.IOException e) {
            					// ERROR
            				}
            			}
            			if (msym != null) {
            				Timer t = new Timer();
            				if (Utils.verboseness >= Utils.VERBOSE)
            					Log.log("Beginning ESC on " + msym);
            				if (monitor != null) monitor.subTask("Checking " + msym);
            				IProverResult res = api.doESC(msym);
            				if (res != null) {
            					IProverResult.ICounterexample ce = res.counterexample();
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
            			else {} // ERROR - FIXME
            		} else if (je instanceof IType) {
            			ClassSymbol csym = convertType((IType)je);
            			if (csym != null) api.doESC(csym);
            			else {} // ERROR - FIXME
            		}
            	}
                if (Utils.verboseness >= Utils.NORMAL) Log.log(Timer.timer.getTimeString() + " Completed ESC operation on individual methods");
            }
            if (monitor != null) {
                monitor.subTask("Completed ESC operation");
            }
        } catch (Main.JmlCanceledException e) {
        	if (monitor != null) {
                monitor.subTask("Canceled ESC operation");
            }
            if (Utils.verboseness >= Utils.NORMAL) Log.log(Timer.timer.getTimeString() + " Canceled ESC operation");
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
                    // Not sure what we do with more than one
                    String pname = pks[0].getElementName();
                    className = pname + "." + className;
                }
            } catch (JavaModelException e) {}
        }
        ClassSymbol csym = api.getClassSymbol(className);
        return csym;
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
    
//    /** Returns the list of names of directories and jar files that constitute
//     * the current specspath in openjml.
//     * @return the current specspath
//     */
//    public @NonNull List<String> getSpecsPath() {
//        return api.getSpecsPath();
//    }
    
    /** Return the specs of the given type, pretty-printed as a String.  This
     * may be an empty String if there are no specifications.
     * @param type the Eclipse IType for the class whose specs are wanted
     * @return the corresponding specs, as a String
     */
    @NonNull
    public String getSpecs(IType type) throws Utils.OpenJMLException {
        ClassSymbol csym = convertType(type);
        if (csym == null) {
            return "Either JML checking has not been run or type " + type + " does not exist";
        }
        try{
            TypeSpecs tspecs = api.getSpecs(csym);
            String smods = api.prettyPrintJML(tspecs.modifiers);
            return smods + eol + tspecs.toString();
        } catch (Exception e) { return "<Exception>: " + e; }
    }
    
    /** Convenience field to hold the line termination string */
    final static private String eol = "\n";

    /** Return the specs of the given type, including all inherited specs,
     * pretty-printed as a String.  This
     * may be an empty String if there are no specifications.
     * @param type the Eclipse IType for the class whose specs are wanted
     * @return the corresponding specs, as a String
     */
    public @Nullable String getAllSpecs(@NonNull IType type) {
        ClassSymbol csym = convertType(type);
        if (csym == null) return null;
        List<TypeSpecs> typeSpecs = api.getAllSpecs(csym);
        try {
            StringBuilder sb = new StringBuilder();
            for (TypeSpecs ts: typeSpecs) {
                sb.append("From " + ts.file.getName() + eol);
                sb.append(api.prettyPrintJML(ts.modifiers));
                sb.append(eol);
                sb.append(ts.toString());
                sb.append(eol);
            }
            return sb.toString();
        } catch (Exception e) { return "<Exception>: " + e; }
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
                sb.append("From " + ts.cases.decl.sourcefile.getName() + eol);
                sb.append(api.prettyPrintJML(ts.mods)); // FIXME - want the collected mods in the JmlMethodSpecs
                sb.append(eol);
                sb.append(api.prettyPrintJML(ts.cases));
                sb.append(eol);
            }
            return sb.toString();
        } catch (Exception e) { return "<Exception>: " + e; }
        
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
            return fspecs.toString(); // FIXME - use proper eol
        } catch (Exception e) { return "<Exception>: " + e; }
    }
    
    // FIXME - documentation
    public File getLeadingSpecFile(IType t) {
        ClassSymbol csym = convertType(t);
        if (csym != null) {
            // FIXME go through API
            //JavaFileObject f = JmlSpecs.instance(api.context()).findSpecFile(csym);
            return null;
        }
        // FIXME - no check run?
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
        
        String s = ((API)api).getBasicBlockProgram(msym);
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
                    "The verification proof succeeded for " + methodName + eol
                    + "Prover: " + r.prover());
            return;
        }
        if (r.result() == IProverResult.INCONSISTENT) {
            utils.showMessageInUINM(shell,"JML Proof Results","The assumptions are INCONSISTENT for " + methodName + eol
            + "Prover: " + r.prover());
            return;
        }
        if (r.result() == IProverResult.UNKNOWN) {
            utils.showMessageInUINM(shell,"JML Proof Results","The verification was not provable for " + methodName + eol
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
                sb.append(eol);
            }
            utils.launchEditor(sb.toString(),shortName);
        }
        return;
    }

    // FIXME - documentation
    public String getCEValue(int pos, int end, String text, IResource r) {
        return api.getCEValue(pos,end,text,r.getLocation().toString());
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
                preq.acceptProblem(problem);
                // Log it as well
                if (Utils.verboseness >= Utils.VERBOSE) {
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
        public boolean report(final int ticks, final int level, final String message) {
            Display d = shell == null ? Display.getDefault() : shell.getDisplay();
            d.asyncExec(new Runnable() {
                public void run() {
                    if (monitor != null) {
                    	monitor.subTask(message);
                    	monitor.worked(ticks);
                    }
                    if (level <= 1) Log.log(message);
                }
            });
            boolean cancel = monitor != null && monitor.isCanceled();
            if (cancel) throw new PropagatedException(new Main.JmlCanceledException("Operation cancelled"));
            return cancel;
        }
        
        /** Sets the OpenJML compilation context associated with this listener. */
        @Override
        //@ assignable this.context;
        //@ ensures this.context == context;
        public void setContext(@NonNull Context context) { 
            this.context = context; 
        }
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

    String[] optionsToCopy = new String[] {
    		Options.showNotImplementedKey,
    		Options.noCheckPurityKey,
    		Options.nonnullByDefaultKey
    };


    /** Retrieves the options from the preference page, determines the 
     * corresponding options for OpenJML and sends them.
     * @param jproject
     * @param cmd The command to be executed
     * @return the list of options and arguments
     */
    public @NonNull List<String> getOptions(IJavaProject jproject, Main.Cmd cmd) {
    	
    	//com.sun.tools.javac.util.Options openjmlOptions = com.sun.tools.javac.util.Options.instance(api.context());
    	
        //Options opt = Activator.options;
        List<String> opts = new LinkedList<String>();
        if (cmd != null) {
            opts.add(JmlOption.COMMAND.optionName() +"="+ cmd);
            opts.add(JmlOption.NOPURITYCHECK.optionName() +"="+ Options.isOption(Options.noCheckPurityKey));
            opts.add(JmlOption.SHOW.optionName() +"="+ Options.isOption(Options.showKey));
        }
        if (cmd == Main.Cmd.ESC) {
            opts.add(JmlOption.ASSOCINFO.optionName());
            String prover = Options.value(Options.defaultProverKey);
            opts.add(JmlOption.PROVER.optionName() +"="+ prover);
            opts.add(JmlOption.PROVEREXEC.optionName() +"="+ Options.value(Options.proverPrefix + prover));
            opts.add(JmlOption.MAXWARNINGS.optionName() +"="+ Options.value(Options.maxWarningsKey));
            opts.add(JmlOption.TRACE.optionName() +"="+ Options.isOption(Options.traceKey));
            opts.add(JmlOption.SUBEXPRESSIONS.optionName() +"="+ Options.isOption(Options.subexpressionsKey));
            opts.add(JmlOption.FEASIBILITY.optionName() +"="+ Options.value(Options.feasibilityKey));
        }
        
        if (cmd == Main.Cmd.RAC) {
            opts.add(JmlOption.NO_RAC_SOURCE.optionName() +"="+ Options.isOption(Options.racNoShowSource));
            opts.add(JmlOption.NO_RAC_CHECK_ASSUMPTIONS.optionName() +"="+ Options.isOption(Options.racNoCheckAssumptions));
            opts.add(JmlOption.NO_RAC_JAVA_CHECKS.optionName() +"="+ Options.isOption(Options.racNoCheckJavaFeatures));
            opts.add(JmlOption.RAC_COMPILE_TO_JAVA_ASSERT.optionName() +"="+ Options.isOption(Options.compileToJavaAssert));
        }
        
//        for (String key: optionsToCopy) {
//        	String value = Options.value(key);
//        	if (key.startsWith(Strings.optionPropertyPrefix)) {
//        		if ("false".equals(value)) value = null;
//        		openjmlOptions.put(key, value);
//        		String arg = "-" + key.substring(Strings.optionPropertyPrefix.length());
//        		openjmlOptions.put(arg, value);
//        	} else {
//        		openjmlOptions.put(key, value);
//        	}
//        }
        // FIXME
//        if (cmd == Cmd.RAC) {
//            opts.add(JmlOption.RAC.optionName());
//            opts.add("-d");
//            IFolder f = jproject.getProject().getFolder(opt.racbin);
//            if (!f.exists()) {
//                try {
//                    f.create(IResource.FORCE,true,null);
//                    f.refreshLocal(IResource.DEPTH_INFINITE,null);
//                } catch (CoreException e) {
//                    Log.errorlog("Exception in creating RAC output directory " + opt.racbin,e);
//                }
//            }
//            opts.add(f.getLocation().toString());
//        }
        boolean verbose = Utils.verboseness >= Utils.NORMAL;

        opts.add(JmlOption.VERBOSENESS.optionName()+"="+Integer.toString(Utils.verboseness));
        
        if (Options.isOption(Options.javaverboseKey)) {
        	opts.add("-verbose"); // FIXME - no hard string
        }
        
        if (Options.isOption(Options.showNotImplementedKey)) opts.add(JmlOption.SHOW_NOT_IMPLEMENTED.optionName());
        if (Options.isOption(Options.showNotExecutableKey)) opts.add(JmlOption.SHOW_NOT_EXECUTABLE.optionName());
        if (!Options.isOption(Options.checkSpecsPathKey)) opts.add(JmlOption.NOCHECKSPECSPATH.optionName());
        opts.add(JmlOption.NONNULLBYDEFAULT.optionName()+"="+Options.isOption(Options.nonnullByDefaultKey));
            
        String other = Options.value(Options.otherOptionsKey);
        if (other != null) {
        	other = other.trim();
        	if (!other.isEmpty()) for (String o : other.split("\\s")) {
        		opts.add(o);
        	}
        }
        
        
        if (cmd == Main.Cmd.JMLDOC) {
            // jmldoc specific options
            opts.add("-private");
        }

//        List<IResource> files = specsPath;
//        boolean first = true;
//        StringBuilder ss = new StringBuilder();
//        if (files != null) { 
//            for (IResource s: files) {
//                if (first) first = false; else ss.append(File.pathSeparator);
//                ss.append(s.getLocation().toString());
//            }
//        }
//        // Now determine the location of library specs and the internal 
//        // runtime library
//        
//        // The plug-in always supplies the specs - either with the code below
//        // or because the user added it to the specspath. So we always tell
//        // openjml itself not to add specs
//        opts.add(JmlOption.NOINTERNALSPECS.optionName());
//        if (!Options.isOption(Options.noInternalSpecsKey)) {
//            String sysSpecs = getInternalSystemSpecs();
//            if (sysSpecs != null && !sysSpecs.isEmpty()) {
//            	if (first) first = false; else ss.append(File.pathSeparator);
//                ss.append(sysSpecs);
//            }
//        }
//
//        if (ss.toString().length()!=0) {
//            opts.add(JmlOption.SPECS.optionName());
//            opts.add(ss.toString());
//        }
        
        // The plug-in adds the internal specs (or asks the user for external specs)
        // So, openjml itself never needs to
        opts.add(JmlOption.NOINTERNALSPECS.optionName());
        opts.add(JmlOption.SPECS.optionName());
        opts.add(PathItem.getAbsolutePath(jproject,PathItem.specsKey));

        opts.add(Strings.sourcepathOptionName); 
        opts.add(PathItem.getAbsolutePath(jproject,PathItem.sourceKey));

        
        // Handle the classpath and internal runtime library if needed
       
        List<String> cpes = utils.getClasspath(jproject);
        boolean first = true;
        StringBuilder ss = new StringBuilder();
        for (String s: cpes) {
            //Log.log("CPE " + s );
            if (first) first = false; else ss.append(File.pathSeparator);
            ss.append(s);
        }

        // The runtime library is always either in the classpath or added 
        // here by the plugin, so openjml itself never adds it
        opts.add(JmlOption.NOINTERNALRUNTIME.optionName());
        if (!Options.isOption(Options.noInternalRuntimeKey)) {
        	String runtime = utils.findInternalRuntime();
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
        // specs , classpath , sourcepath, stopiferrors
        // Java options, Jmldoc options
		if (Utils.verboseness >= Utils.DEBUG) {
			StringBuilder s = new StringBuilder();
			s.append("Options collected by UI to send to OpenJML: ");
			for (String opt: opts) {
				s.append(" ");
				s.append(opt);
			}
			Log.log(s.toString());
		}

        return opts;
    }

//    /**
//     * Update the value of the property openjml.prover.yices, using
//     * the value given by prover editor.
//     */
//    public static void setYicesLocation() {
//      Bundle yicesBundle = Platform.getBundle("yices.editor");
//      if (yicesBundle != null) try {
//        Class<?> editor = yicesBundle.loadClass("mobius.prover.yices.YicesEditor");
//        Method meth = editor.getMethod("getYicesLocation");
//        String loc = (String) meth.invoke(null);
//        System.setProperty("openjml.prover.yices", loc);
//      } catch (ClassNotFoundException e) {
//      } catch (SecurityException e) {
//      } catch (NoSuchMethodException e) {
//      } catch (IllegalArgumentException e) {
//      } catch (IllegalAccessException e) {
//      } catch (InvocationTargetException e) {
//      }
//    }
    
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
        return ((API)api).getBasicBlockProgram(msym);
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
