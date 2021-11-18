/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.IOException;
import java.nio.CharBuffer;

/** This class implements a CharSequence that obtains its characters from a source of characters
 * of unknown length; it also provides some functionality to retain the characters and compute line numbers.  
 * <P>
 * The characters 
 * read are held in an internal char array, whose size grows as needed; it starts as initialSize and
 * is expanded to currentSize*sizeMultiple + sizeIncrease whenever needed.
 * <P>
 * The CharSequenceReader is an unconventional CharSequence in that its length() is not known; 
 * whether this will cause problems
 * in some uses of the CharSequenceReader is unknown.  The user should not use the value of length()
 * directly; it seems to work in the ways it is called from Pattern.matcher.
 * @author David R. Cok
 *
 */
public abstract class CharSequenceInfinite implements CharSequence {

	/** This interface is used to create prompters.  A CharSequenceInfinite object needs on occasion to
	 * obtain new input, which it does by calling readChars().  readChars() invokes the prompter to 
	 * communicate to the source of input that more data is needed.  As an example, if the input comes from
	 * interactive input, the prompter may print out prompt characters.
	 */
	public static interface IPrompter {
		/** Implement this call-back to do whatever user actions are needed to
		 * cause more input to be available.
		 */
		void prompt();
	}
	
	/** The prompter object */
	public /*@Nullable*/ IPrompter prompter = null;
	
	/** Constructor for a new instance
	 * 
	 * @param initialSize the beginning size of the internal char array
	 * @param sizeIncrease the amount to add to the current size of the internal char array when the array needs expanding
	 * @param sizeMultiple the factor by which to multiply the current size of the internal char array when it needs expanding
	 */
	//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
	//@ requires !(sizeIncrease == 0 && sizeMultiple == 1)
	public CharSequenceInfinite(int initialSize, int sizeIncrease, double sizeMultiple) {
		this.sizeIncrease = sizeIncrease;
		this.sizeMultiple = sizeMultiple;
		buf = new char[initialSize];
		this.amountRead = 0;
		this.length = Integer.MAX_VALUE;
	}

	/** The amount by which to increase the internal char array when needed */
	//@ invariant sizeIncrease >= 0;
	protected int sizeIncrease;

	/** The factor by which to increase the size of the internal char array when needed */
	//@ invariant sizeMultiple >= 1 && (sizeIncrease==0 ==> sizeMultiple > 1);
	protected double sizeMultiple;

	/** The internal char array that holds characters as they are read */
	protected char /*@NonNull*/[] buf;

	/** The number of characters read so far (and in the char array) */
	//@ invariant amountRead >= 0 && amountRead <= buf.length;
	protected int amountRead;

	/** The implicit length of the CharSequence; note that this length may change as characters are read */
	//@ invariant length >= 0 && length >= amountRead;
	protected int length;

	/** The character to use to mark the end of input */
	final public static char endChar = (char)25;

	//@ constraint (\forall int i; 0 <= i < \old(amountRead); \old(buf[i]) == buf[i]);
	//@ constraint amountRead >= \old(amountRead);
	
	/** Returns the char at the given index; this may block while input is read if the char has
	 * not been read before.  An IOException that occurs while reading input is converted to an
	 * undeclared RuntimeException. 
	 */
	//@ requires index >= 0;
	//@ assigns buf, buf[amountRead..], amountRead, length;
	//@ ensures index < amountRead;
	@Override
	public char charAt(int index) {
		if (index >= amountRead) {
			if (index >= buf.length) {
				// We need +1 because one needs a buffer of at least size 2 to include index=1
				// We add an additional +1 so that there is room to hold an End-of-input character if necessary
				expandBuffer(index+2);
			}
			try {
				while (amountRead <= index) {
					if (!readChars()){
						//SMT.out.println("END OF INPUT READ");
						buf[amountRead++] = endChar;
						length = amountRead;
						return endChar;
					}
				}
			} catch (IOException e) {
				// Note: we catch IOException and turn it into a RuntimeException
				// (so it does not have to be declared) because the inherited 
				// signature for charAt(int) does not declare any thrown exceptions
				throw new RuntimeException(e);
			}
		}
		return buf[index];
	}
	
	/** Reads more characters into the buffer; may block until some are read;
	 * returns false if end of input has been reached,
	 * in which case no additional chars should have been read.  Does not expand the
	 * buffer, so the buffer must have extra space in it when readChars() is called.
	 * @return true if characters were read, false if no chars were read and end of input was reached
	 */
	//@ requires buf.length > amountRead;
	//@ modifies buf,buf[amountRead..],amountRead;
	//@ ensures \result => amountRead > \old(amountRead);
	//@ ensures !\result ==> amountRead == \old(amountRead);
	//@ ensures buf[0..\old(amountRead)-1] == \old(buf[0..amountRead-1]);
	abstract protected boolean readChars() throws java.io.IOException ;
	
	/** This expands the buffer to be at least as large as the argument; the buffer is expanded
	 * even if it is already of adequate size.
	 * 
	 * @param newSize minimum size of the expanded buffer
	 */
	//@ requires newSize > 0;
	//@ modifies buf;
	//@ ensures buf.length >= newSize && buf.length > \old(buf.length);
	//@ ensures (\forall int i; 0<=i && i<amountRead; buf[i] == \old(buf[i]));
	private void expandBuffer(int newSize) {
		int newlength = buf.length;
		do {
			int k = (int) Math.ceil(newlength*sizeMultiple+sizeIncrease);
			newlength = (k <= newlength) ? newlength+100 : k; // check for both bad parameters and for integer overflow
		} while (newSize > newlength);
		char[] nbuf = new char[newlength];
		System.arraycopy(buf,0,nbuf,0,amountRead);
		buf = nbuf;
	}

	/** Returns the length of the CharSequence; for this implementation, the return value is at
	 * least as great as the unknown length of the CharSequence.  The value is correct once the
	 * end of input has been reached.
	 * @return the length of the CharSequence
	 */
	@Override
	public int length() {
		return this.length;
	}

	/** Returns a subsequence of this CharSequence, of length end-start.
	 * CAUTION: This method can wrap a portion of the internal char array, but then
	 * the char array can be expanded, allocating a new char array - so just don't rely on
	 * changes to the sub-sequence to be reflected in the parent array.
	 * @param start the starting index of the subsequence
	 * @param end one past the last character included in the subsequence
	 * 
	 */
	@Override
	public CharSequence subSequence(int start, int end) {
		charAt(end-1); // Just to be sure it has been read
		return CharBuffer.wrap(buf,start,end-start);
	}
	
}
