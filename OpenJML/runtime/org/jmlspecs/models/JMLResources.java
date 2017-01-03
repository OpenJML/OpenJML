// @(#)$Id: JMLResources.java,v 1.11 2005/07/07 21:03:08 leavens Exp $

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

import java.math.BigInteger;

/** Model variables for reasoning &agrave; la Eric Hehner.
 *
 * @version $Revision: 1.11 $
 * @author Gary T. Leavens
 * @see JMLInfiniteInteger
 * @see Runtime
 */
//-@ immutable
public /*@ pure @*/ class JMLResources {

    /** The number of JVM cycles used since beginning execution.
     *
     *  <p> A cycle is defined to be the time unit used (in the worst
     *  case) by the fastest source-level instruction in Java code.
     *  When such an instruction is executed, machineCycles increases
     *  by 1.  All other instructions increase machineCycles by an
     *  appropriate amount, sometimes greater than 1.
     *
     *  <p> Multiply machineCycles by the speed of your JVM to get the
     *  time used.  For example, if your JVM executes one cycle every
     *  2 milliseconds, then the number of milliseconds spent in
     *  execution is 2 * machineCycles.
     *
     *  <p>We imagine that the number of machine cycles is infinite
     *  when the program goes into an infinite loop.
     *  
     *  @see JMLInfiniteInteger
     *  @see JMLPositiveInfinity
     */
    //@ ghost public static JMLInfiniteInteger machineCycles;

    static {
        //@ set machineCycles = JMLFiniteInteger.ZERO;
    }

    //@ public static invariant machineCycles != null;
    /*@ public static invariant machineCycles.greaterThanOrEqualTo(
      @                                  JMLFiniteInteger.ZERO);
      @ public static constraint machineCycles.greaterThanOrEqualTo(
      @                                       \old(machineCycles));
      @*/

    //@ public static model long bytesUsed;
    /*@ public static represents bytesUsed
      @             <- (long)(Runtime.getRuntime().totalMemory()
      @                       - Runtime.getRuntime().freeMemory());
      @*/
}
