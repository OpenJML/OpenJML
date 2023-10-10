package com.sun.tools.javac.code;

import com.sun.tools.javac.util.List;

public class JmlListType extends Type {
    public List<Type> types;

    public JmlListType(List<Type> types, List<TypeMetadata> metadata) {
        super(null, metadata);
        this.types = types;
    }

    public JmlListType(List<Type> types) { // OPENJML - added
        this(types, List.<TypeMetadata>nil());
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
    
    @Override
    public JmlListType cloneWithMetadata(List<TypeMetadata> metadata) {
    	JmlListType t = new JmlListType(types, metadata);
    	t.tsym = this.tsym;
    	return t;
    }


}
