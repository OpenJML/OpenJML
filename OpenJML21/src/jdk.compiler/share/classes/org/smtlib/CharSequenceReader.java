/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.Reader;

/** This class implements a CharSequence that obtains its characters from a Reader.  The characters 
 * read are held in an internal char array, whose size grows as needed; it starts as initialSize and
 * is expanded to currentSize*sizeMultiple + sizeIncrease whenever needed.
 * 
 * The CharSequenceReader is an unconventional CharSequence in that its length() is not known; 
 * whether this will cause problems
 * in some uses of the CharSequenceReader is unknown.  The user should not use the value of length()
 * directly; it seems to work in the ways it is called from Pattern.matcher.
 * @author David R. Cok
 *
 */
public class CharSequenceReader extends CharSequenceInfinite implements CharSequence {

	/** Constructor for a new instance
	 * 
	 * @param rdr the Reader that supplies characters on demand
	 * @param initialSize the beginning size of the internal char array
	 * @param sizeIncrease the amount to add to the current size of the internal char array when the array needs expanding
	 * @param sizeMultiple the factor by which to multiply the current size of the internal char array when it needs expanding
	 */
	//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
	//@ requires !(sizeIncrease == 0 && sizeMultiple == 1)
	public CharSequenceReader(/*@NonNull*/Reader rdr, int initialSize, int sizeIncrease, double sizeMultiple) {
		super(initialSize, sizeIncrease, sizeMultiple);
		this.rdr = rdr;
	}
	
	/** Constructor for a new instance
	 * 
	 * @param rdr the Reader that supplies characters on demand
	 */
	public CharSequenceReader(/*@NonNull*/Reader rdr) {
		this(rdr, 100000, 100, 2);
	}
	
	/** The Reader that supplies characters for the CharSequence */
	protected /*@NonNull*/ Reader rdr;
	
	@Override
	protected boolean readChars() throws java.io.IOException {
		int nread;
		// It appears that rdr.ready() can be false when a file has been completely
		// read and the next read will return -1 - there does not appear to be a way
		// to determine that the reader is at the end of file without issuing the
		// final read (which might block if we are interactive)
		if (!rdr.ready() && prompter != null) {
			prompter.prompt();
		}
		do {
			nread = rdr.read(buf,amountRead,buf.length-amountRead);
			if (nread == -1) {
				return false;
			}
			amountRead += nread;
		} while (amountRead < buf.length && rdr.ready());
		return true;
	}
}
