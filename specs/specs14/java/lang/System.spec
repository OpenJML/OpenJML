// @(#)$Id: System.spec 2251 2006-12-18 03:35:16Z chalin $

// Copyright (C) 1998-2006 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.lang;

import java.io.*;
import java.util.Properties;

/** JML's specification of java.lang.System.
 *
 * @version $Revision: 2251 $
 * @author Gary T. Leavens
 * @author David R. Cok
 * @author Joseph R. Kiniry
 */
public final class System {

    private /*@ pure @*/ System();

    //@ public final ghost static boolean allowNullStreams = false;

    /*  In declaring allowNullStreams to be final, we restrict beyond what
        the JDK requires.  The JDK allows in, out and err to be set to null
        streams, in which case a NullPointerException is raised on any
        attempt to read or write to in, out or err.  By declaring 
        allowNullStreams final we introduce the invariant that it is always
        non-null.  If we don't do this, we will need to include in preconditions
        whereever in, out and err are used that they are non null.  This is
        a decided nuisance, and I think the programmer would rather be
        warned that a possibly null stream is being assigned. 

	Since allowNullStreams = false and is declared as final, this means
	that in, out and err are effectively non-null.  The only way to allow
	them to be nullable is to modify this specification (or make a copy of
	it) and change the value of allowNullStreams.  Since changing the
	nullity requires changing the spec, and since some tools can do more
	if in, out and err are explicitly declared non-null, we are going one
	step further and annotating in, out and err as non_null.  If ever you
	change allowNullStreams to be true, then you will need to change the
	annotations of in, out and err to be nullable.
    */

    public final static /*@non_null*//*see note above*/ InputStream in;
        /*@ public initially in != null; @*/ 
        //@ public invariant !allowNullStreams ==> in != null;
    public final static /*@non_null*//*see note above*/ PrintStream out;
        /*@ public initially out != null; @*/ 
        //@ public invariant !allowNullStreams ==> out != null;
    public final static /*@non_null*//*see note above*/ PrintStream err;
        /*@ public initially err != null; @*/ 
        //@ public invariant !allowNullStreams ==> err != null;

    //@ requires allowNullStreams || i != null;
    //@ assignable in;  // strangely enough, in is like a read-only var.
    //@ ensures in == i;
    public static void setIn(InputStream i);

    //@ requires allowNullStreams || o != null;
    //@ assignable out;
    //@ ensures out == o;
    public static void setOut(PrintStream o);

    //@ requires allowNullStreams || e != null;
    //@ assignable err;
    //@ ensures err == e;
    public static void setErr(PrintStream e);


    //@ public model static nullable SecurityManager systemSecurityManager;

    /*@  public normal_behavior
      @    requires s == null;
      @    assignable \nothing;
      @    ensures \not_modified(systemSecurityManager);
      @ also
      @  public behavior
      @    requires s != null;
      @    assignable systemSecurityManager;
      @    ensures  systemSecurityManager == s;
      @    signals (SecurityException) (* if the change is not permitted *);
      @*/
    public static void setSecurityManager(/*@nullable*/ SecurityManager s) throws SecurityException;

    //@ public normal_behavior
    //@   ensures \result == systemSecurityManager;
    public /*@ pure @*/ static /*@nullable*/ SecurityManager getSecurityManager();

    /** The last value of currentTimeMillis() that was returned */

    //@ public static ghost long time;

    // FIXME - need to show that the value is volatile ?
    //@ public normal_behavior
    //@  modifies time;
    //@  ensures \result >= 0;
    //@  ensures time >= \old(time);
    //@  ensures \result == time;
    public static native long currentTimeMillis();

    /*@ // public exceptional_behavior
      @ //   requires src == null || dest == null;
      @ //   assignable \nothing;
      @ //   signals_only NullPointerException;
      @ // also
      @  public exceptional_behavior
      @    // requires !(src == null || dest == null);
      @    requires !(src.getClass().isArray()) || !(dest.getClass().isArray());
      @    assignable \nothing;
      @    signals_only ArrayStoreException;
      @ also // FIXME - unify with the previous spec case
      @ public exceptional_behavior
      @   // requires (* neither array is null *);
      @   // requires !(src == null || dest == null);
      @   requires (* either the src or dest are not arrays, or
      @               both src and dest are primitive arrays, but not of the sam
e primitive type, or
      @               one of them is a primitive type, but the other is an objec
t *);
      @   requires !src.getClass().isArray() || !dest.getClass().isArray()
      @            || (!(\elemtype(\typeof(src)) <: \type(Object))
      @                && !(\elemtype(\typeof(dest)) <: \type(Object))
      @                && !(\elemtype(\typeof(src)) == \elemtype(\typeof(dest)))
)
      @            || (\elemtype(\typeof(src)) <: \type(Object)
      @                && !(\elemtype(\typeof(dest)) <: \type(Object)))
      @            || (!(\elemtype(\typeof(src)) <: \type(Object))
      @                && \elemtype(\typeof(dest)) <: \type(Object));
      @   assignable \nothing;
      @   signals_only ArrayStoreException;
      @ also
      @  public exceptional_behavior
      @    // requires !(src == null || dest == null);
      @    requires !(!(src.getClass().isArray()) || !(dest.getClass().isArray()));
      @    requires (srcPos < 0 || destPos < 0 || length < 0
      @                  || srcPos + length > ((Object[])src).length
      @                  || destPos + length > ((Object[])dest).length);
              // FIXME - need the length restriction for primitive type arrays also
      @    assignable \nothing;
      @    signals_only ArrayIndexOutOfBoundsException;
      @ also
      @  public normal_behavior
      @    // requires !(src == null || dest == null);
      @    requires src.getClass().isArray() && dest.getClass().isArray();
      @    requires !(    srcPos < 0 || destPos < 0 || length < 0 );
             // FIXME - need the length restrictions for all primitive types
	   {| requires \elemtype(\typeof(src)) <: \type(Object) &&
			\elemtype(\typeof(dest)) <: \type(Object) &&
      @                 srcPos + length <= ((Object[])src).length
      @                && destPos + length <= ((Object[])dest).length;
      @   {|
      @      old Object [] sa = (Object[]) src;
      @      old Object [] da = (Object[]) dest;
      @      assignable da[destPos .. destPos + length - 1];
      @      ensures (\forall int i; 0 <= i && i < length;
      @                \old(sa[(int)(srcPos+i)]) == da[(int)(destPos+i)]);
      @   |}
	   also
		requires \elemtype(\typeof(src)) == \type(int) &&
			 \elemtype(\typeof(dest)) == \type(int) &&
      @                 srcPos + length <= ((int[])src).length
      @                && destPos + length <= ((int[])dest).length;
      @   {|
      @      old int [] sa = (int[]) src;
      @      old int [] da = (int[]) dest;
      @      assignable da[destPos .. destPos + length - 1];
      @      ensures (\forall int i; 0 <= i && i < length;
      @                 sa[(int)(srcPos+i)] == da[(int)(destPos+i)]);
      @   |}
	   also
		requires \elemtype(\typeof(src)) == \type(long) &&
			 \elemtype(\typeof(dest)) == \type(long) &&
      @                 srcPos + length <= ((long[])src).length
      @                && destPos + length <= ((long[])dest).length;
      @   {|
      @      old long [] sa = (long[]) src;
      @      old long [] da = (long[]) dest;
      @      assignable da[destPos .. destPos + length - 1];
      @      ensures (\forall int i; 0 <= i && i < length;
      @                 sa[(int)(srcPos+i)] == da[(int)(destPos+i)]);
      @   |}
	   |}
      @*/
    //@ implies_that
    //@   requires length >= 0 && 0 <= srcPos && 0 <= destPos;
    public static native void arraycopy(/*@non_null*/ Object src,
                                        int srcPos,
                                        /*@non_null*/ Object dest,
                                        int destPos,
                                        int length);

    // Note: Unequal objects are not required to have unequal hashCodes
    // There is no good, modularly provable way to express that anyway
    //@ public normal_behavior
    //@   ensures x == null ==> \result == 0;
    //-@ function
    public /*@ pure @*/ static native int identityHashCode(/*@nullable*/ Object x);

    //@ public model static non_null Properties systemProperties;
    //@    initially systemProperties.containsKey("java.home");
    //@    initially systemProperties.getProperty("java.home") != null;
    //@    initially !systemProperties.containsKey("xxxxxx");

    /* Models the set of properties that you get when setProperties is called
       with a null argument.  This is not the same as the default (original)
       set of system properties, but it appears to be the same (per equals)
       throughout a program.
     */
    //+@ public model static non_null Properties nullSystemProperties;
    //-@ public model static final non_null Properties nullSystemProperties;

    /*@ public normal_behavior
      @    ensures \result == systemProperties;
      @    //signals (SecurityException) (* if access is not permitted *);
      @*/
    //-@ function
    public /*@ pure @*/ static /*@ non_null @*/ Properties getProperties();

    /*@ public behavior
      @    requires props == null;
      @    assignable systemProperties;
      @    ensures systemProperties.equals(nullSystemProperties);
      @    signals_only SecurityException;
      @    signals (SecurityException) (* if access is not permitted *) &&
                                       \not_modified(systemProperties);
      @ also public behavior
      @    requires props != null;
      @    assignable systemProperties;
      @    ensures systemProperties == props;
      @    signals_only SecurityException;
      @    signals (SecurityException) (* if access is not permitted *) &&
                                       \not_modified(systemProperties);
      @*/
    public static void setProperties(Properties props);


// FIXME - conflict between exceptions
    //@ public behavior
    //@   requires key != null;
    //@   ensures \result == getProperties().getProperty(key);
    //@   signals (SecurityException) (* if access is not permitted *);
    //@ also public exceptional_behavior
    //@   requires key == null;
    //@   signals_only NullPointerException;
    public /*@ pure @*/ static /*@nullable*/ String getProperty(/*@non_null*/ String key) throws RuntimeException;


// FIXME - conflict between exceptions
    //@ public behavior
    //@   requires key != null;
    //@   ensures \result == getProperties().getProperty(key,def);
    //@
    //@    signals (SecurityException) (* if access is not permitted *);
    //@ also public exceptional_behavior
    //@   requires key == null;
    //@   signals_only NullPointerException;
    public /*@ pure @*/ static /*@nullable*/ String getProperty(/*@non_null*/ String key, /*@nullable*/ String def) throws RuntimeException;    


// FIXME - conflict between exceptions
    /*@ public behavior
      @    requires key != null && value != null;
      @    assignable systemProperties;
      @    signals (SecurityException) (* if access is not permitted *);
      @ also public exceptional_behavior
      @   requires key == null || value == null;
      @   assignable \not_specified;
      @   signals_only NullPointerException;
      @*/
    public static /*@nullable*/ String setProperty(/*@non_null*/ String key, /*@nullable*/ String value) throws RuntimeException;


    /** @deprecated use java.lang.System.getProperty. */
    public static /*@ pure nullable @*/ String getenv(/*@non_null*/ String name);

    /*@ public behavior
      @    diverges true;
      @    assignable \nothing;
      @    ensures false;
      @    signals_only SecurityException;
      @    signals (SecurityException) (* if exiting is not permitted *);
      @*/
    public static void exit(int status);

    public static void gc();

    public static void runFinalization();

    /** @deprecated this is unsafe. */
    public static void runFinalizersOnExit(boolean value);

    public static void load(/*@ non_null @*/ String filename);

    public static void loadLibrary(/*@ non_null @*/ String libname);

    public /*@ pure @*/ static native String mapLibraryName(/*@non_null*/ String libname);

}
