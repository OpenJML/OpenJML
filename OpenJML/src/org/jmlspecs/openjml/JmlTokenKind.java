/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;

import com.sun.tools.javac.parser.Tokens.ITokenKind;
import com.sun.tools.javac.tree.JCTree;

/**
 * This class defines the scanner tokens that represent JML syntax.
 * 
 * @author Alexander Weigl
 */
public interface JmlTokenKind extends ITokenKind{
    String internedName();
    Class<?> getAnnotationType();

    boolean isRedundant();
}
