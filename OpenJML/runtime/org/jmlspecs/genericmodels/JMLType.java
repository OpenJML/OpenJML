// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.


package org.jmlspecs.genericmodels;
import org.jmlspecs.annotation.*;

/** This is an interface shared by all the immutable types of the model classes.
 * Immutable containers must contain immutable objects.
 * JMLObjectType and JMLValueType are refinements
 * for object and value containers (respectively).
 * @version $Revision: 1.20 $
 * @author Gary T. Leavens and Albert L. Baker., DRCok
 * @see JMLObjectType
 * @see JMLValueType
 */
@Pure
public interface JMLType extends Cloneable, java.io.Serializable {

    /** Return a clone of this object. */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null;
      @     ensures \typeof(\result) == \typeof(this);
      @     ensures ((JMLType)\result).equals(this);
      @*/
    @NonNull public Object clone();    

    /** Test whether this object's value is equal to the given argument.
     */
    /*@ also
      @   public normal_behavior
      @   {|
      @      requires ob2 != null && ob2 instanceof JMLType;
      @      ensures ((JMLType)ob2).equals(this) == \result;
      @    also
      @      requires ob2 == null || !(ob2 instanceof JMLType);
      @      ensures !\result;
      @    also
      @      requires ob2 == this;
      @      ensures \result <==> true;
      @   |}
      @ implies_that also
      @   public normal_behavior
      @     ensures (* \result ==>
      @             ob2 != null
      @             &&  ob2 is not distinguishable from this,
      @                   except by using mutation or == *);
      @*/
    public boolean equals(@Nullable Object ob2);    

    /** Return a hash code for this object. */
    //@ normal_behavior
    //@   ensures (* equal objects imply equal hash codes *);
    public int hashCode();
}
