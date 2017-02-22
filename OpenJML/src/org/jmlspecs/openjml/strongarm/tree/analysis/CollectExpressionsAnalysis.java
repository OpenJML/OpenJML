package org.jmlspecs.openjml.strongarm.tree.analysis;

import org.jmlspecs.openjml.strongarm.tree.PropTreeScanner;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;

public class CollectExpressionsAnalysis extends JmlTreeAnalysis {

    public CollectExpressionsAnalysis(Context context) {
        super(context);
    }

    
    
    
    public static void analyze(JCTree tree, Context ctx){
        
        CollectExpressionsAnalysis analysis = new CollectExpressionsAnalysis(ctx);
        
        
        analysis.scan(tree);
        
    }
}
