package com.sun.tools.javac.code;

import com.sun.tools.javac.util.List;

public class JmlListType extends Type {
    public List<Type> types;

    public JmlListType(List<Type> types) {
        super(null);
        this.types = types;
    }

    @Override
    public TypeTag getTag() {
        // TODO Auto-generated method stub
        return TypeTag.UNKNOWN;
    }
    
    @Override
    public String toString() {
        String s = "tuple<";
        boolean first = true;
        for (Type t: types) {
            if (first) first = false; else s += ",";
            s += t.toString();
        }
        s += ">";
        return s;
    }

}
