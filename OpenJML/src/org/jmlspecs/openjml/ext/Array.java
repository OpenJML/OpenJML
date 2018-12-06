package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.VAL;

import org.jmlspecs.openjml.JmlTokenKind;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

/** This extension allows the field .array to be used on array objects
 * (like 'length'). It produces a model value of type array<E>, which
 * is an immutable fixed- (finite-) length array.
 *
 */
public class Array extends FieldExtension {

    public static void register(Context context) {}

    static public String[] ids() { return new String[]{
            "array"}; }
    
    public Type typecheck(JmlAttr attr, Env<AttrContext> env, JCFieldAccess tree) {
        Context context = attr.context;
        attr.attribExpr(tree.selected, env, Type.noType); // Any type is allowed
        Type atype = tree.selected.type;
        Type t;
        if (atype instanceof Type.ArrayType) { 
            Type elemtype = ((Type.ArrayType)atype).elemtype;
            Type at = ClassReader.instance(context).enterClass(attr.names.fromString("org.jmlspecs.lang.array")).type;
            t = new ClassType(Type.noType,List.<Type>of(elemtype),at.tsym);
        } else if (atype.isErroneous()) {
            t = atype;
        } else {
            Log.instance(context).error(tree,"jml.message","The .array suffix is permitted only for array expressions: " );
            t = JmlTypes.instance(context).createErrorType(atype);
        }
        return t;
    }
}
