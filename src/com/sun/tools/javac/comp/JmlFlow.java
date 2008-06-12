package com.sun.tools.javac.comp;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

/** This extends FLow to add flow checks to specifications.  FLow checks for:<BR>
 * uninitialized statements<BR>
 * assignments to final variables<BR>
 * unreachable statements<BR>
 * forward references<BR>
 * fall-through in cases<BR>
 * improper use of checked exceptions<BR>
 * exception never thrown in try<BR>
 * The JML additions just make sure that ghost fields, model methods and model classes
 * are visited by the flow tree walker.
 * @author David Cok
 *
 */
public class JmlFlow extends Flow {

    /** Registers a singleton factory for JmlFlow against the flowKey, so that there is
     * just one instance per context.
     * @param context the context in which to register the instance
     */
    public static void preRegister(final Context context) {
        context.put(Flow.flowKey, new Context.Factory<Flow>() {
            public Flow make() { 
                return new JmlFlow(context);
            }
        });
    }
    
    /** Returns the instance for the given context
     * 
     * @param context the context in which we are working
     * @return the non-null instance of JmlAttr for this context
     */
    public static JmlFlow instance(Context context) {
        Flow instance = context.get(flowKey); 
        if (instance == null)
            instance = new JmlFlow(context); // Registers itself in the super constructor
        return (JmlFlow)instance; // If the registered instance is only an Flow, something is catastrophically wrong
    }
    
    /** The compilation context of this instance */
    protected Context context;
    
    /** A constructor, but use instance() to generate new instances of this class. */
    protected JmlFlow(Context context) {
        super(context);
        this.context = context;
    }
    
    /** Overridden to be sure that ghost/model declarations within the class are
     * visited by the flow checker.
     */
    @Override
    public void visitClassDef(JCClassDecl tree) {
        super.visitClassDef(tree);
        if (tree.sym == null) return;
        if (Utils.isInstrumented(tree.mods.flags)) return;
        JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(tree.sym);
        if (tspecs == null) return;
        JavaFileObject prev = Log.instance(context).currentSource();
        for (JmlTypeClause c : tspecs.clauses) {
            if (c instanceof JmlTypeClauseDecl) {
                JCTree d = ((JmlTypeClauseDecl)c).decl;
                Log.instance(context).useSource(c.source());
                if (c.modifiers != null && (c.modifiers.flags & Flags.SYNTHETIC) != 0) {
                    continue;
                }
                d.accept(this);
            }
        }
        Log.instance(context).useSource(prev);
    }
}
