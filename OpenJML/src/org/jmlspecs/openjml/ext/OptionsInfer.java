package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlOption;

public abstract class OptionsInfer extends JmlExtension {

    // Options Related to Specification Inference
    public static final JmlOption INFER = new JmlOption("-infer",true,"POSTCONDITIONS","Infer missing contracts (postconditions (default), preconditions)","-command=infer");
    public static final JmlOption INFER_DEBUG = new JmlOption("-infer-debug", false, false, "Enable debugging of contract inference", null);
    public static final JmlOption INFER_TAG = new JmlOption("-infer-tag", true, true, "If true, inferred specifications are tagged with the key INFERRED", null);
    public static final JmlOption INFER_PRECONDITIONS = new JmlOption("-infer-preconditions", true, true, "If not specified, the precondition of methods lacking preconditions will be set to true (otherwise inference is skipped).", null);
    public static final JmlOption INFER_NO_EXIT = new JmlOption("-noexit",true,false,"Infer contracts (suppress exiting)","-command=infer-no-exit");
    public static final JmlOption INFER_MINIMIZE_EXPRS = new JmlOption("-infer-minimize-expressions", false, false, "Minimize expressions where possible.", null);
    public static final JmlOption INFER_DUMP_GRAPHS = new JmlOption("-infer-dump-graphs", false, false, "Dump any specification that would have been inferred to a file for offline analysis", null);
    
    //
    // Inference decides to write specs based on the following conditions
    // 1) If -infer-persist-path is specified, specs are written to that directory (base)
    // 2) Else, if -specspath is specified, specs are written to that directory (base)
    // 3) Otherwise, we write the specs to the same directory were the java class source exists
    //
    public static final JmlOption INFER_PERSIST = new JmlOption("-infer-persist", true, "jml", "Persist inferred specs. If \"java\" specs are written to the source files. If \"jml\" (default) they are written to seperate .jml files (defaults to location of class source and can be overridden with -infer-persist-path and -specspath)", null);
    public static final JmlOption INFER_PERSIST_PATH = new JmlOption("-infer-persist-path", true, null, "Specify output directory of specifications (overrides -specspath)", null);
    public static final JmlOption INFER_MAX_DEPTH = new JmlOption("-infer-max-depth", true, 300, "The largest CFG we will agree to process", null);
    public static final JmlOption INFER_TIMEOUT = new JmlOption("-infer-timeout", true, 300, "Give up inference after this many seconds. A value of -1 will wait indefinitely", null);
    public static final JmlOption INFER_DEV_MODE = new JmlOption("-infer-dev-mode", false, false, "Special features for developers.", null);
    
    //
    // Options for turning on and off various inference techniques 
    //
    public static final JmlOption INFER_ANALYSIS_TYPES = new JmlOption("-infer-analysis-types", true, "ALL", "Enables specific analysis types. Takes a comma seperated list of analysis types. Support kinds are: REDUNDANT, UNSAT, TAUTOLOGIES, FRAMES, PURITY, and VISIBILITY", null);

}
