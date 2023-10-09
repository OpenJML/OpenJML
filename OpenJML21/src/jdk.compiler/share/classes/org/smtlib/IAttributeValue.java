package org.smtlib;

/** This interface represents the general class of attribute values; 
 * that is, it is the super-interface of any class that may be an attribute value;
 * in the abstract syntax it has no particular structure, though it does include
 * true, false, string literals, numerals, and various pre-defined constants.
 */
public interface IAttributeValue extends IResponse, IPos.IPosable {
}