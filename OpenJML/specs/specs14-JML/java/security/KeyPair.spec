/* @(#)$Id: KeyPair.spec,v 1.1 2006/02/17 22:25:57 cheon Exp $
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

import java.util.*;

/** JML's specification of <code>KeyPair</code>.
 *
 * @author Poonam Agarwal
 * @author Yoonsik Cheon
 */
public final class KeyPair implements java.io.Serializable {

    private /*@ spec_public*/ PrivateKey privateKey;
    private /*@ spec_public*/ PublicKey publicKey;
    
    /*@ public normal_behavior
      @   assignable this.publicKey, this.privateKey;
      @   ensures this.publicKey == publicKey &&
      @           this.privateKey == privateKey;
      @*/
    public KeyPair(PublicKey publicKey, PrivateKey privateKey);

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == this.publicKey;
      @*/
    public /*@ pure @*/ PublicKey getPublic();

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == this.privateKey;
      @*/
    public /*@ pure @*/ PrivateKey getPrivate();
}

