package com.sun.tools.javac.parser;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class JmlTreeInfo extends TreeInfo {

    Context context;
    Log log;
    
    public static JmlTreeInfo instance(Context context) {
        TreeInfo instance = context.get(treeInfoKey);
        if (instance == null)
            instance = new JmlTreeInfo(context);
        return (JmlTreeInfo)instance;
    }
    
    public static void preRegister(final Context context) {
        instance(context);
    }

    
    protected JmlTreeInfo(Context context) {
        super(context); // super class registers the instance in context
        this.context = context;
        this.log = Log.instance(context);
    }

    public static int getStartPos(JCTree n) {
        return TreeInfo.getStartPos(n);
    }

    public int getEndPos(JCTree n) {
        return TreeInfo.getEndPos(n,log.currentSource().getEndPosTable());
    }
}
