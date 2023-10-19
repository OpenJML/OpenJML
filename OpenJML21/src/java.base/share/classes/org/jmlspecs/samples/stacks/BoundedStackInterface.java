// Copyright (C) 2009 University of Central Florida

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


package org.jmlspecs.samples.stacks;

//@ model import org.jmlspecs.models.*;
import org.jmlspecs.annotation.*;

@Model("public instance JMLObjectSequence theStack; in size;") // syntax?
@Initially(header="public", value=" theStack != null && theStack.isEmpty();")
@Represents(header="public instance", value="size <- theStack.int_length();")
@InvariantDefinitions({
        @Invariant(header="public instance", value="theStack != null;"),
        @Invariant(header="public instance", redundantly=true,
                   value="theStack.int_length() <= MAX_SIZE;"),
        @Invariant(header="public instance",
                   value="(#forall int i; 0 <= i && i < theStack.int_length();"
                   +      "theStack.itemAt(i) != null);")
})
public interface BoundedStackInterface extends BoundedThing {

  @Also({@SpecCase(header="public normal_behavior",
                   requires="!theStack.isEmpty();",
                   assignable="size, theStack;",
                   ensures="theStack.equals(#old(theStack.trailer()));"),
         @SpecCase(header="public exceptional_behavior",
                   requires="theStack.isEmpty();",
                   assignable="#nothing;",
                   signalsOnly="BoundedStackException;")})
  public void pop( ) throws BoundedStackException;

  @Also({@SpecCase(header="public normal_behavior",
                   requires="theStack.int_length() < MAX_SIZE && x != null;",
                   assignable="size, theStack;",
                   ensures="theStack.equals(#old(theStack.insertFront(x)));",
                   ensuresRedundantly="theStack != null && top() == x"
                   +                   "&& theStack.int_length()"
                   +                   "== #old(theStack.int_length()+1);"),
         @SpecCase(header="public exceptional_behavior",
                   requires="theStack.int_length() >= MAX_SIZE || x == null;",
                   assignable="#nothing;",
                   signalsOnly="BoundedStackException, NullPointerException;",
                   signals="(Exception e)"
                   +       "((e instanceof BoundedStackException)"
                   +       " ==> theStack.int_length() == MAX_SIZE)"
                   +    "&& ((e instanceof NullPointerException)"
                   +       " ==> x == null));")})
  public void push(Object x )
         throws BoundedStackException, NullPointerException;

    @Also({@SpecCase(header="public normal_behavior",
                    requires="!theStack.isEmpty();",
                    ensures="#result == theStack.first() && #result != null;"),
          @SpecCase(header="public exceptional_behavior",
                    requires="theStack.isEmpty();",
                    signalsOnly="BoundedStackException;",
                    signals="(BoundedStackException e)"
                    +        "#fresh(e) && e != null && e.getMessage() != null"
                    +        "&& e.getMessage().equals(\"empty stack\");")})
  public /*@ pure @*/ Object top( ) throws BoundedStackException;
}
