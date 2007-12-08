// @(#)$Id: Key.spec,v 1.1 2005/11/04 21:13:20 leavens Exp $
//
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

package java.security;

/** JML's specification of Key.
 * @author Tabitha Johnson
 * @author Gary T. Leavens
 */
public interface Key extends java.io.Serializable {

    public static final long serialVersionUID;

    /*@ ensures \result != null ==> \result.length != 0; 
      @*/
    public byte[] getEncoded();

    /*@ ensures \result != null && !(\result.equals("")); 
      @*/
    public /*@ pure @*/ String getAlgorithm();

    /*@
      @ ensures \result != null ==> !(\result.equals("")); 
      @*/
    public /*@ pure @*/ String getFormat();
}
