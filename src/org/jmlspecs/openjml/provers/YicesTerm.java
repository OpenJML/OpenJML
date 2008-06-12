package org.jmlspecs.openjml.provers;

import org.jmlspecs.openjml.proverinterface.Sort;
import org.jmlspecs.openjml.proverinterface.Term;

public class YicesTerm extends Term {
    
    protected String yicesString;
    
    public YicesTerm(Sort sort, String string) {
        super(sort);
        this.yicesString = string;
    }
    
    public String toString() {
        return yicesString;
    }
}
