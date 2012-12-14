package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;

// FIXME - document
// FIXME - would like to have paths with variables, e.g. ${user.dir}
// FIXME - Source paths do not include items in referenced projects
// FIXME - Source paths ignore the included/excluded declarations in the Java Build Path

abstract public class PathItem {
	
	public final static String sep = "#"; // Presumed to be a single character
	public final static QualifiedName sourceKey = new QualifiedName(Activator.PLUGIN_ID,"sourcepath");
	public final static QualifiedName specsKey = new QualifiedName(Activator.PLUGIN_ID,"specspath");
	public final static String split = ",";

	
	public static PathItem create(String pureString) {
		return new AbsolutePath(pureString);
	}
	
	public static PathItem parse(String encodedString) {
		int k = encodedString.indexOf(sep);
		if (k == -1) return null;
		String s = encodedString.substring(0,k);
		String rest = encodedString.substring(k+sep.length());
		if (s.equals(AbsolutePath.prefix)) {
			return new AbsolutePath(rest);
		} else if (s.equals(ProjectPath.prefix)) {
			return new ProjectPath(rest);
		} else if (s.equals(WorkspacePath.prefix)) {
			return new WorkspacePath(rest);
		} else if (s.equals(SpecialPath.prefix)) {
			return new SpecialPath(rest);
		} else {
			return null; // FIXME - error
		}
	}
	
	abstract public String display();
	
	abstract public String toAbsolute(IJavaProject jproject);
	
	abstract public String toEncodedString();
	
	static public String getEncodedPath(IJavaProject jproject, QualifiedName key) {
		try {
			String prop = jproject.getProject().getPersistentProperty(key);
			if (prop == null) {
				if (key == sourceKey) prop = new SpecialPath(SpecialPath.Kind.ALL_SOURCE_FOLDERS).toEncodedString(); 
				else if (key == specsKey) {
					prop = new SpecialPath(SpecialPath.Kind.SOURCEPATH).toEncodedString()
							+ split
							+ new SpecialPath(SpecialPath.Kind.SYSTEM_SPECS).toEncodedString();
				} else {
					prop = "";
				}
			}
			return prop;
		} catch (CoreException e) {
			// FIXME - report Error
			return "";
		}
	}
	
	static public String getAbsolutePath(IJavaProject jproject, QualifiedName key) {
		String stored = getEncodedPath(jproject,key);
		String[] paths = stored.split(split);
		StringBuilder sb = new StringBuilder();
		for (String s: paths) {
			sb.append(parse(s).toAbsolute(jproject));
			sb.append(File.pathSeparator);
		}
		if (paths.length != 0) sb.setLength(sb.length()-File.pathSeparator.length());
		return sb.toString();
	}

    public static class AbsolutePath extends PathItem {
    	
    	final static String prefix = "abs";
    	
    	String location;
    	
    	public AbsolutePath(String pureString) {
    		location = pureString;
    	}
    	
    	public String toEncodedString() {
    		return prefix + sep + location;
    	}
    	
    	public String toAbsolute(IJavaProject jproject) {
    		return location;
    	}
    	
    	public String display() {
    		return location;
    	}
    	
    }
    
    public static class ProjectPath extends PathItem {
 
    	final static String prefix = "prj";

    	String projectRelativeLocation;
    	
    	public ProjectPath(String projectRelativeLocation) {
    		this.projectRelativeLocation = projectRelativeLocation;
    	}
    	
    	public String toEncodedString() {
    		return prefix + sep + projectRelativeLocation;
    	}
    	
    	public String toAbsolute(IJavaProject jproject) {
    		return null;
    	}

    	public String display() {
    		return "PROJECT " + projectRelativeLocation;
    	}

    }
    
    public static class WorkspacePath extends PathItem {
    	
    	final static String prefix = "wsp";
    	
    	String workspaceRelativeLocation;
    	
    	public WorkspacePath(String workspaceRelativeLocation) {
    		this.workspaceRelativeLocation = workspaceRelativeLocation;
    	}
    	
    	public String toEncodedString() {
    		return prefix + sep + workspaceRelativeLocation;
    	}
    	
    	public String toAbsolute(IJavaProject jproject) {
    		return null;
    	}

    	public String display() {
    		return "WORKSPACE " + workspaceRelativeLocation;
    	}
    }

    public static class SpecialPath extends PathItem {
    	
    	public static enum Kind {
    		ALL_SOURCE_FOLDERS("sf","... all source folders ..."),
    		CLASSPATH("cp","... classpath ..."), 
    		SOURCEPATH("sp","... sourcepath ..."), 
    		SYSTEM_SPECS("ss","... internal system specifications folders ...");
    		String key;
    		String description;
    		private Kind(String key, String d) { this.key = key; description = d; }
    	}
    	
    	final static String prefix = "spc";
    	
    	Kind kind;
    	
    	public SpecialPath(Kind kind) {
    		this.kind = kind;
    	}
    	
    	public SpecialPath(String rest) {
    		for (Kind k : Kind.values()) {
    			if (rest.equals(k.key)) { kind = k; return; }
    		}
    		// FIXME - error
    	}
    	
    	public String toEncodedString() {
    		return prefix + sep + kind.key;
    	}
    	
    	public String toAbsolute(IJavaProject jproject) {
    		String out;
    		switch (kind) {
    		case ALL_SOURCE_FOLDERS:
    			try {
    				StringBuilder sb = new StringBuilder();
    	            IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    				IClasspathEntry[] entries = jproject.getResolvedClasspath(true);
    				for (IClasspathEntry cpe : entries) {
    					if (cpe.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
	                        IResource r = root.getFolder(cpe.getPath());
	                        IPath p = r.getLocation();
	                        if (p != null) {
	                        	sb.append(p.toString());
	                        	sb.append(File.pathSeparator);
	                        } else {
	                        	// FIXME - error
	                        }
    					}
    				}
    				if (sb.length() > 0) sb.setLength(sb.length() - File.pathSeparator.length());
    				out = sb.toString();
    			} catch (JavaModelException e) {
    				// FIXME - error
    				out = "";
    			}
    			break;
    			
    		case CLASSPATH:
    			StringBuilder sb = new StringBuilder();
    			List<String> cp = Activator.getDefault().utils.getClasspath(jproject);
    			for (String s : cp) {
    				sb.append(s);
    				sb.append(File.pathSeparator);
    			}
				if (sb.length() > 0) sb.setLength(sb.length() - File.pathSeparator.length());
				out = sb.toString();
    			break;
    			
    		case SOURCEPATH:
    			out = getAbsolutePath(jproject,sourceKey);
    			break;
    			
    		case SYSTEM_SPECS:
    			// Choose between internal and external specs
    			out = Activator.getDefault().utils.getInternalSystemSpecs();
    			break;
    			
    		default:
    			// FIXME - report error
    			out = "";
    		}
    		return out;
    	}
    	
    	public String display() {
    		return kind.description;
    	}
    }


}