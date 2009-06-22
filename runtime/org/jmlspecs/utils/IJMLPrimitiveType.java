package org.jmlspecs.utils;

import org.jmlspecs.annotations.Pure;

@Pure
public interface IJMLPrimitiveType extends IJMLType {
    
    public IJMLPrimitiveType INT();
    public IJMLPrimitiveType BOOLEAN();
    public IJMLPrimitiveType SHORT();
    public IJMLPrimitiveType LONG();
    public IJMLPrimitiveType FLOAT();
    public IJMLPrimitiveType DOUBLE();
    public IJMLPrimitiveType CHAR();
    public IJMLPrimitiveType BYTE();
    public IJMLPrimitiveType REAL();
    public IJMLPrimitiveType BIGINT();
}
