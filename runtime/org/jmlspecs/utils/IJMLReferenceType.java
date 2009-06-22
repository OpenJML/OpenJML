package org.jmlspecs.utils;

import java.util.Map;

import org.jmlspecs.annotations.*;

@Pure
public interface IJMLReferenceType extends IJMLType {
    public static final IJMLReferenceType[] emptyArgs = new IJMLReferenceType[0];
    
    IJMLReferenceType baseType();
    
    IJMLReferenceType[] args();
    
    int numArgs();
    
    boolean equals(IJMLReferenceType t, Map<IJMLTypeVar,IJMLTypeVar> map);

}
