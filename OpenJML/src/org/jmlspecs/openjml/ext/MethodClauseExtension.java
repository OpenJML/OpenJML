/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;

/* FIXME - do more to implement extensions */

/* TODO - needs documentation */
abstract public class MethodClauseExtension extends JmlExtension {
    protected static final Context.Key<MethodClauseExtension> methodClauseExtensionsKey =
            new Context.Key<MethodClauseExtension>();

    /** A constructor needed by derived classes; this class should not be
     * instantiated directly by users.
     */
    protected MethodClauseExtension(Context context) {
        super(context);
    }
    
    /** Sets the end position of the given tree node to be the end position of
     * the previously scanned token.
     * @param <T> the type of the node being set
     * @param tree the node whose end position is being set
     * @return returns the same node
     */
    public <T extends JCTree> T toP(T tree) {
        return parser.toP(tree);
    }
    
}
