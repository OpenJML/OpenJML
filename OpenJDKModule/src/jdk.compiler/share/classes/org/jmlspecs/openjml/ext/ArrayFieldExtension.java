package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

/** This extension allows the field .array to be used on array objects
 * (like 'length'). It produces a model value of type array<E>, which
 * is an immutable fixed- (finite-) length array.
 *
 */
public class ArrayFieldExtension extends JmlExtension {

    public static final String arrayID = "array";
    
    public static final IJmlClauseKind arrayFieldKind = new JmlField(arrayID);
    
    public static class JmlField extends IJmlClauseKind {

        public JmlField(String keyword) { super(keyword);}

        @Override
        public JCTree parse(JCModifiers mods, String keyword,
                IJmlClauseKind clauseKind, JmlParser parser) {
            // TODO Auto-generated method stub
            return null;
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
            JCFieldAccess fa = (JCFieldAccess)tree;
            Context context = attr.context;
            attr.attribExpr(fa.selected, env, Type.noType); // Any type is allowed
            Type atype = fa.selected.type;
            Type t;
            if (atype instanceof Type.ArrayType) { 
                Type elemtype = ((Type.ArrayType)atype).elemtype;
                Type at = ClassReader.instance(context).enterClass(attr.names.fromString("org.jmlspecs.lang.array")).type;
                t = new ClassType(Type.noType,List.<Type>of(elemtype),at.tsym);
            } else if (atype.isErroneous()) {
                t = atype;
            } else {
                error(tree,"jml.message","The .array suffix is permitted only for array expressions: " );
                t = JmlTypes.instance(context).createErrorType(atype);
            }
            return t;
        }
    }
}
