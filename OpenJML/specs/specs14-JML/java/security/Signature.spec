/* @(#)$Id: Signature.spec,v 1.3 2006/03/04 02:27:54 leavens Exp $
 *
 * Copyright (C) 2006 The University of Texas at El Paso
 *
 * This file is part of the runtime library of the Java Modeling Language.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1,
 * of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JML; see the file LesserGPL.txt.  If not, write to the Free
 * Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
 * 02110-1301  USA.
 */

package java.security;

import java.security.spec.AlgorithmParameterSpec;
import java.security.cert.Certificate;
//@ model import org.jmlspecs.models.*;

/** JML's specification of <code>Signaure</code>.
 *
 * @author Yoonsik Cheon
 */
public abstract class Signature extends SignatureSpi {
    /* @ only in UTJML
      @ public call_sequence 
      @   (initSign (initSign | update | sign)* |
      @    initVerify (initVerify | update | verify)*)*;
      @*/
      
    //@ public model non_null JMLValueSequence data; 
    //@   initially data.isEmpty();
    
    //@ public model Key key;

    /*@ requires bytes != null;
      @ public static model pure JMLValueSequence toSeq(byte[] bytes) {
      @   JMLValueSequence result = new JMLValueSequence();
      @   for (int i = 0; i < bytes.length; i++)
      @       result = result.insertBack(new JMLByte(bytes[i]));
      @   return result;
      @ }
      @ */

    /*@ requires bytes != null && offset >= 0 && length > 0 &&
      @    (offset + length) <= bytes.length;
      @ public static model pure 
      @   JMLValueSequence toSeq(byte[] bytes, int offset, int length) {
      @   JMLValueSequence result = new JMLValueSequence();
      @   for (int i = offset; i < offset + length; i++)
      @       result = result.insertBack(new JMLByte(bytes[i]));
      @   return result;
      @ }
      @*/

    /*@ public model pure boolean isPristine() {
      @   return data.isEmpty() && key == null && state == UNINITIALIZED;
      @ }
      @*/
    
    /*@ protected normal_behavior
      @   requires (* algorithm is available *);
      @   assignable this.algorithm;
      @   ensures this.algorithm == algorithm;
      @   ensures_redundantly state == UNINITIALIZED;
      @*/
    protected Signature(/*@ non_null @*/ String algorithm);

    /*@ public normal_behavior
      @   requires (* algorithm is available *);
      @   assignable \nothing;
      @   ensures \fresh(\result) && \result.isPristine() &&
      @           \result.algorithm == algorithm;
      @ also 
      @  public exceptional_behavior
      @   requires (* algorithm is not available *);
      @   assignable \nothing;
      @   signals (NoSuchAlgorithmException e) true;
      @*/
    public static Signature getInstance(/*@ non_null @*/ String algorithm)
        throws NoSuchAlgorithmException;

    /*@ public normal_behavior
      @   requires !provider.equals("");
      @   requires (* algorithm is available from provider *);
      @   assignable \nothing;
      @   ensures \fresh(\result) && \result.isPristine() &&
      @           \result.algorithm == algorithm &&
      @           \result.provider.getName().equals(provider);
      @ also 
      @  public exceptional_behavior
      @   requires (* provider is not available *);
      @   assignable \nothing;
      @   signals (NoSuchProviderException e) true;
      @ also 
      @  public exceptional_behavior
      @   requires (* algorithm is not available from provider*);
      @   assignable \nothing;
      @   signals (NoSuchAlgorithmException e) true;
      @*/
    public static Signature getInstance(/*@ non_null @*/ String algorithm, 
                                        String provider) 
        throws NoSuchAlgorithmException, NoSuchProviderException;

    /*@ public normal_behavior
      @   requires (* algorithm is available from provider *);
      @   assignable \nothing;
      @   ensures \fresh(\result) && \result.isPristine() &&
      @           \result.algorithm == algorithm &&
      @           \result.provider == provider;
      @ also 
      @  public exceptional_behavior
      @   requires (* algorithm is not available from provider*);
      @   assignable \nothing;
      @   signals (NoSuchAlgorithmException e) true;
      @*/
    public static Signature getInstance(String algorithm, 
                                        /*@ non_null @*/ Provider provider) 
        throws NoSuchAlgorithmException;

    /*@ public normal_behavior
      @   ensures \result == provider;
      @*/
    public final /*@ pure @*/ Provider getProvider();

    /*@ public normal_behavior
      @   requires (* publicKey is valid *);
      @   assignable data, key, state;
      @   ensures data.isEmpty() && key == publicKey && state == VERIFY;
      @ also
      @  public exceptional_behavior
      @   requires (* publicKey is invalid *);
      @   assignable \nothing;
      @   signals (InvalidKeyException) true;
      @*/
    public final void initVerify(/*@ non_null @*/ PublicKey publicKey) 
        throws InvalidKeyException;

    /*@ public normal_behavior
      @   requires (* certificate.getPublicKey() is valid *);
      @   assignable data, key, state;
      @   ensures data.isEmpty() && key == certificate.getPublicKey() && 
      @           state == VERIFY;
      @ also
      @  public exceptional_behavior
      @   requires (* certificate.getPublicKey() is invalid *);
      @   assignable \nothing;
      @   signals (InvalidKeyException) true;
      @*/
    public final void initVerify(/*@ non_null @*/ Certificate certificate) 
        throws InvalidKeyException;

    /*@ public normal_behavior
      @   requires (* privateKey is valid *);
      @   assignable data, key, state;
      @   ensures data.isEmpty() && key == privateKey && state == SIGN;
      @ also
      @  public exceptional_behavior
      @   requires (* privateKey is invalid *);
      @   assignable \nothing;
      @   signals (InvalidKeyException) true;
      @*/
    public final void initSign(/*@ non_null @*/ PrivateKey privateKey)
        throws InvalidKeyException;

    /*@ public normal_behavior
      @   requires (* privateKey is valid *);
      @   assignable data, key, state;
      @   ensures data.isEmpty() && key == privateKey && state == SIGN;
      @ also
      @  public exceptional_behavior
      @   requires (* privateKey is invalid *);
      @   assignable \nothing;
      @   signals (InvalidKeyException) true;
      @*/
    public final void initSign(/*@ non_null @*/ PrivateKey privateKey, 
                               /*@ non_null @*/ SecureRandom random)
        throws InvalidKeyException;

    /*@ public normal_behavior
      @   requires state == SIGN;
      @   assignable data;
      @   ensures data.isEmpty() && (* \result is signature of \old(data) *);
      @ also
      @  public exceptional_behavior
      @   requires state != SIGN;
      @   assignable \nothing;
      @   signals (SignatureException) true;
      @*/
    public final /*@ non_null @*/ byte[] sign() throws SignatureException;

    /*@ public normal_behavior 
      @   requires state == SIGN;
      @   assignable data;
      @   ensures data.isEmpty() &&
      @     (* outbuf[offset..] contains signature of size \result *);
      @ also
      @  public exceptional_behavior
      @   requires state != SIGN;
      @   assignable \nothing;
      @   signals (SignatureException) true;
      @*/
    public final int sign(byte[] outbuf, int offset, int len) 
        throws SignatureException;

    /*@ public normal_behavior
      @   requires state == VERIFY && (* signature improperly encoded *);
      @   assignable data;
      @   ensures data.isEmpty() &&
      @     \result <==> (* singature is authentic w.r.t. \old(data) *);
      @ also 
      @  public exceptional_behavior
      @   requires state != VERIFY || (* signature improperly encoded *);
      @   assignable \nothing;
      @   signals (SignatureException e) true;
      @*/
    public final boolean verify(byte[] signature) throws SignatureException;

    /*@ public normal_behavior
      @   requires offset >= 0 && length > 1 &&
      @            (offset + length) <= signature.length &&
      @            (* signature improperly encoded *);
      @   requires state == VERIFY;
      @   assignable data;
      @   ensures data.isEmpty() &&
      @     \result <==> (* singature[offset..offset+length-1] is authentic *);
      @ also 
      @  public exceptional_behavior
      @   requires state != VERIFY || (* signature improperly encoded *);
      @   assignable \nothing;
      @   signals (SignatureException e) true;
      @*/
    public final boolean verify(byte[] signature, int offset, int length)
        throws SignatureException;

    /*@ public normal_behavior
      @   requires state == VERIFY || state == SIGN;
      @   assignable data;
      @   ensures data.equals(\old(data.insertBack(new JMLByte(b))));
      @ also 
      @  public exceptional_behavior
      @   requires state != VERIFY && state != SIGN;
      @   assignable \nothing;
      @   signals (SignatureException e) true;
      @*/
    public final void update(byte b) throws SignatureException;

    /*@ public normal_behavior
      @   requires data.length > 0;
      @   requires state == VERIFY || state == SIGN;
      @   assignable this.data;
      @   ensures this.data.equals(\old(this.data.concat(toSeq(data))));
      @ also 
      @  public exceptional_behavior
      @   requires state != VERIFY && state != SIGN;
      @   assignable \nothing;
      @   signals (SignatureException e) true;
      @*/
    public final void update(/*@ non_null @*/ byte[] data) 
        throws SignatureException;

    /*@ public normal_behavior
      @   requires off >= 0 && len > 1 && (off + len) <= data.length;
      @   requires state == VERIFY || state == SIGN;
      @   assignable this.data;
      @   ensures this.data.equals(
      @           \old(this.data.concat(toSeq(data,off,len))));
      @ also 
      @  public exceptional_behavior
      @   requires state != VERIFY && state != SIGN;
      @   assignable \nothing;
      @   signals (SignatureException e) true;
      @*/
    public final void update(/*@ non_null @*/ byte[] data, int off, int len) 
        throws SignatureException;

    /*@ public normal_behavior
      @   ensures \result == algorithm;
      @*/
    public final /*@ pure @*/ String getAlgorithm();

    public /*@ non_null @*/ String toString();

    public final void setParameter(
        /*@ non_null @*/ AlgorithmParameterSpec params) 
        throws InvalidAlgorithmParameterException;

    public final /*@ pure @*/ AlgorithmParameters getParameters();

    /*@ also
      @  public normal_behavior
      @   requires this instanceof Cloneable;
      @   assignable \nothing;
      @   ensures (* \result is a clone of this *);
      @ also
      @  public exceptional_behavior
      @   requires !(this instanceof Cloneable);
      @   signals (CloneNotSupportedException e) true;
      @*/    
    public /*@ non_null pure @*/ Object clone() 
        throws CloneNotSupportedException;

    protected /*@ spec_public @*/ static final int UNINITIALIZED; 
    /*@ initially UNINITIALIZED == 0; @*/

    protected /*@ spec_public @*/ static final int SIGN; 
    /*@ initially SIGN == 2; @*/

    protected /*@ spec_public @*/ static final int VERIFY; 
    /*@ initially VERIFY == 3; @*/

    protected /*@ spec_public @*/ int state; 
    /*@ initially state == UNINITIALIZED; @*/

    /** @deprecated use getParameters() */
    public final Object getParameter(String param)
        throws InvalidParameterException;

    /** @deprecated use setParameter(AlgorithmParameterSpec) */
    public final void setParameter(String param,
                                   Object value)
        throws InvalidParameterException;

    private /*@ spec_public @*/ String algorithm;

    private /*@ spec_public @*/ Provider provider;
}
