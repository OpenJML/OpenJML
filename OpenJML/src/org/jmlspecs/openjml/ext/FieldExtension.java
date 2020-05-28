package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.VAL;

import org.jmlspecs.openjml.JmlExtension;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;

/** This class enables adding predefined fields to types for use within
 *  JML expressions. An example of such a field in Java is 'length'.
 *  Generally such a field represents a property of the object
 *  and is readonly.
 *  No parsing extensions are needed for such fields. 
 *  It is a type-checking error if the field is used inappropriately.
 *  Note that this extension is rarely needed because regular classes
 *  can include model fields defined in JML.
 */
public abstract class FieldExtension extends JmlExtension {

    abstract Type typecheck(JmlAttr attr, Env<AttrContext> env, JCFieldAccess tree);
    
    public Type typecheck(JmlAttr attr, Env<AttrContext> env, JCFieldAccess tree, Attr.ResultInfo resultInfo) {
        Type t = typecheck(attr, env, tree);
        t = attr.check(tree, t, VAL, resultInfo);
        tree.type = t;
        return t;
    };

}
