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

package org.jmlspecs.models;

/** A class with static methods that safely work with null objects.
 *
 * @version $Revision: 1.8 $
 * @author Katie Becker and Gary T. Leavens
 */
//-@ immutable
public class JMLNullSafe {

    /** No instances of this class can be created. */
    private JMLNullSafe() {}
		
    /** Test for equality of o1 and o2, allowing either to be null. */
    //@ ensures \result <==> (o1 == null ? o2 == null : o1.equals(o2));
    public static /*@ pure @*/ boolean equals(/*@ nullable @*/ Object o1,
                                              /*@ nullable @*/ Object o2) {
        return o1 == null ? o2 == null : o1.equals(o2);
    }

    /** Return a string representation for the argument, which may be null. */
    /*@  public normal_behavior
       @   requires o == null;
       @   assignable \nothing;
       @   ensures \result != null && \result.equals("null");
       @ also
       @   requires o != null;
       @   ensures \result != null;
       @ also
       @   public model_program {
       @     return o == null ? "null" : o.toString();
       @   }
       @*/
    public static String toString(/*@ nullable @*/ Object o) {
        return o == null ? "null" : o.toString();
    }

    /** Return a hash code for the argument, which may be null. */
    /*@  public normal_behavior
       @   requires o == null;
       @   assignable \nothing;
       @   ensures \result == 0;
       @ also
       @  public model_program {
       @    return o == null ? 0 : o.hashCode();
       @  }
       @*/
    public static int hashCode(/*@ nullable @*/ Object o) {
        return o == null ? 0 : o.hashCode();
    }
}
