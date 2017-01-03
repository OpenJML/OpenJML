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


package org.jmlspecs.lang;
import org.jmlspecs.annotation.*;

/** A type with one element, for use in declaring "data groups".
 *  Note that there is only one equivalence class of objects of this type;
 *  that is, all objects of this type are considered .equal to each other.
 *
 * @version $Revision: 1.4 $
 * @author Gary T. Leavens, based on an idea of Rustan Leino
 */
public @Pure final class JMLDataGroup implements Cloneable {

    /** Initialize this object.
     * @see #IT
     */
    /*@ private normal_behavior
      @   assignable owner;
      @   ensures owner == null;
      @*/
    private JMLDataGroup() {
        //@ set owner = null;
    } 

    /** The only object of this type.
     */
    public static final @NonNull JMLDataGroup IT = new JMLDataGroup();

    /** Return this object.
     */
    @NonNull
    public Object clone() {
        return this;
    }

    /** Test whether the given argument is a non-null object of type
     *  JMLDataGroup.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result <==> oth != null && oth instanceof JMLDataGroup;
      @*/
    public boolean equals(@Nullable Object oth) {
        return oth != null && oth instanceof JMLDataGroup;
    } 
    
    /** Return a hash code for this object.
     */
    public int hashCode() {
        return 0;
    }

    /** Return a string representation of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null
      @          && (* result is a string representation of this *);
      @*/
    @NonNull
    public String toString() {
        return "JMLDataGroup.IT";
    }
    
}
