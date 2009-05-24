/*
 * Copyright (c) 2006 David R. Cok
 * @author David R. Cok
 * Created Dec 16, 2006
 */
package org.jmlspecs.openjml.eclipse;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.dom.CompilationUnit;

/**
 * This class holds related information about a Java compilation unit.
 * There is at most one of these objects for each Java compilation unit
 * and each binary type without a source file within the project.
 */
public class CUInfo {
  
  String packagename = null;
  
  String primaryTypeName = null;
  
  /** True if the compilation unit being compiled, namely 'file', is
   * on the specs sequence.
   */
  boolean inSpecsSequence = false;
  
  /** True if the JML specs have been parsed and added to the parsedCU AST. */
  boolean specsInserted = false;
  
  /** The type when we are looking at a binary type , and consequently 
   * there is no compilation unit (original and workingCopy and file are null)
   */
  IType primaryType;

  /** The file containing the source implementation, if any */
  IFile file;
  
  /** The ICompilationUnit corresponding to the file; might be null (when? FIXME) */
  org.eclipse.jdt.core.ICompilationUnit original;
  
  //@ invariant workingCopy.getJavaElement() == original;
  //@ invariant original.getResource() == file;
  
  /** The workingCopy corresponding to 'original'. */
  org.eclipse.jdt.core.ICompilationUnit workingCopy;
  
  /** The AST corresponding to 'workingCopy'; null if parsing has
   * not yet been performed.
   */
  org.eclipse.jdt.core.dom.CompilationUnit parsedCU;
  
  /** The sequence of resources the constitute the specification sequence for
   * this compilation unit.  This will be null if the specs have not yet been
   * requested.
   */
  LinkedList<IFile> specssequence = new LinkedList<IFile>();
  
  //@ invariant specssequence == null <==> specscusequence == null;
  //@ invariant specssequence != null ==> specssequence.size() == specscusequence.size();
  
  /** The sequence of ASTs corresponding to the working copies that correspond
   * to the resources in 'specssequence'.
   */
  LinkedList<CompilationUnit> specscusequence = new LinkedList<CompilationUnit>();
  
  /** The ICompilationUnit of the workingCopy of the first element in 
   * 'specssequence', if any.
   */
  org.eclipse.jdt.core.ICompilationUnit specsicu;
  
  /** The AST corresponding to specsicu, if any. */
  org.eclipse.jdt.core.dom.CompilationUnit specscu;
  
  void check(String s, ProjectInfo pi) {
    if (original != null && original.getResource() != file) {
      System.out.println("CU " + s + ": ORIGINAL = " + original.getResource().getFullPath() + " FILE = " + (file == null ? "NULL" : file.getFullPath().toString()));
    }
    if (original != null && original.findWorkingCopy(pi.owner) != workingCopy) {
      System.out.println("CU " + s + ": ORIGINAL != WORKINGCOPY");
    }
    if (parsedCU != null && parsedCU.getJavaElement() != workingCopy) {
      System.out.println("CU " + s + ": PARSEDCU does not match WORKINGCOPY");
    }
    if ((specscusequence == null) != (specssequence == null)) {
      System.out.println("CU " + s + ": SPECSSEQUENCE does not match SPECSCUSEQUENCE");
    }
    if (specscusequence != null && specssequence != null) {
      if (specssequence.size() != specscusequence.size()) {
        System.out.println("CU " + s + ": SIZES DO NOT MATCH " + specssequence.size() + " " + specscusequence.size());
      } else {
        for (int i=0; i<specssequence.size(); ++i) {
          IFile f = specssequence.get(i);
          CompilationUnit c = specscusequence.get(i);
          ICompilationUnit icu = (ICompilationUnit)c.getJavaElement();
          if (!icu.getResource().equals(f)) {
            System.out.println("CU " + s + ": SPECS MISMATCH " + icu.getResource() + " " + f);
          }
        }
      }
    }
  }

}
