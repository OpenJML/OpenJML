/*
 * This file is part of the OpenJML plugin project. 
 * Copyright (c) 2006-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Date;

// Maintenance note: This class is roughly duplicated from
// org.jmlspecs.openjml.Utils.Timer to avoid dependencies
// (if this plug-in were to be used independently)

/**
 * A class that provides some timing routines for performance
 * checking.
 */
public class Timer {

	/** A static timer that may be used when threading is not an issue */
	static public final /*@ non_null */ Timer timer = new Timer();

	/** The private value holding the time at the beginning of the timed 
	 * period, that is, when markTime was called.
	 */
	//@ non_null
	private Date date = new Date();

	/** Sets this timer to 0. */
	public void markTime() {
		date = new Date();
	}

	/** 
	 * @return the number of seconds since the last call of markTime()
	 */
	public double getTime() {
		return (new Date().getTime() - date.getTime())/1000.;
	}

	/** 
	 * @return the number of seconds since the last call of markTime()
	 * as a String enclosed in [ ]
	 */
	public String getTimeString() {
		return "[" + String.format("%.2f",getTime()) + "]";   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
	}

}
