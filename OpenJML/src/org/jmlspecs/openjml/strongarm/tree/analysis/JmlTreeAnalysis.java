package org.jmlspecs.openjml.strongarm.tree.analysis;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.strongarm.transforms.SubstituteTree;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class JmlTreeAnalysis extends JmlTreeScanner{

    public JCTree                          currentReplacement;
    public static SubstituteTree           instance;
    
    final public Log                    log;
    final public Utils                  utils;
    final public JmlTreeUtils           treeutils;
    final public JmlTree.Maker          M;
    final public Context                context;
    final Symtab                           syms;
    public static boolean                  inferdebug; 
    public static boolean                  verbose; 
        
    public JmlTreeAnalysis(Context context){
        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);
        this.inferdebug = JmlOption.isOption(context, org.jmlspecs.openjml.ext.OptionsInfer.INFER_DEBUG);           
        
        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
    }

    

    
}
