/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.Strings;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

// TODO: Complete, use and document

public class ModifierExtension extends IJmlClauseKind {

    protected Class<?> clazz;
    protected ProgramLocation[] locations;
    protected ClassSymbol annotationSymbol;
    
    protected ModifierExtension(String name, Class<?> clazz) {
        super(name);
        this.clazz = clazz;
        this.locations = null;
        this.annotationSymbol = null;
    }
    
    protected ModifierExtension(String name, Class<?> clazz, ProgramLocation[] locations) {
        super(name);
        this.clazz = clazz;
        this.locations = locations;
        this.annotationSymbol = null;
    }
    
    public static void register(Context context) { }
    public void register() { annotationSymbol = null; Extensions.modifierKinds.put(this.name(), this);}
    
    /** Returns the keyword representing the modifier, or null if there is none (only an annotation) */
    public @Nullable String jmlKeyword() { return keyword; }
    
    /** Returns the Class object for the Annotation class that represents this modifier. */
    public @Nullable Class<?> javaAnnotation() { return clazz; }
    
    /** Returns the Class object for the Annotation class that represents this modifier. */
    public @Nullable ClassSymbol annotationSymbol(Context context) { 
        if (annotationSymbol == null) {
            Name nm = Names.instance(context).fromString(clazz.getName());
            annotationSymbol = ClassReader.instance(context).enterClass(nm);
        }
        return annotationSymbol;
    }
    
    /** Helper function that returns true if the given loc is in the given array. */
    public boolean isInArray(ProgramLocation loc, ProgramLocation[] locs) {
        for (ProgramLocation p: locs) if (p==loc) return true;
        return false;
    }
    
    /** Returns true if the modifier is allowed at the given location. */
    public boolean isAllowed(ProgramLocation loc, boolean isInJML) {
        return isInArray(loc,locations());
    }

    public ProgramLocation[] locations() {
        return locations;
    }
    
    @Override
    public JCTree parse(JCModifiers mods, String keyword,
            IJmlClauseKind clauseType, JmlParser parser) {
        return null;
    }
    @Override
    public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
        return null;
    }

    
    
}
