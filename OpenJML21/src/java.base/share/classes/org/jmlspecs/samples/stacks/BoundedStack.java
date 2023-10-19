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

@RepresentsDefinitions({
       @Represents(header="private", value="MAX_SIZE <- maxSize;"),
       @Represents(header="protected", value="theStack <- theStackRep;"),
       @Represents(header="protected", redundantly=true,
                   value="theStack #such_that theStack != null"
                   +     "&& theStack.int_length() == nextFree"
                   +     "&& (#forall int i; 0 <= i && i < nextFree;"
                   +     "        theStack.itemAt(i) == theItems[i]);")
})
@InvariantDefinitions({
        @Invariant(header="protected",
                   value="0 <= nextFree && nextFree <= theItems.length;"),
        @Invariant(header="protected",
                   value="theItems != null;"),
        @Invariant(header="protected",
                   value="(#forall int i; 0 <= i && i < nextFree;"
                         +"theItems[i] != null);")
})
@ModelMethod("protected pure model JMLObjectSequence theStackRep() {"
       + "   JMLObjectSequence ret = new JMLObjectSequence();"
       + "   int i;"
       + "   for (i = 0; i < nextFree; i++) {"
       + "      ret = ret.insertFront(theItems[i]);"
       + "   }"
       + "   return ret;"
       + "}")
public class BoundedStack implements BoundedStackInterface {

  // implementation data structures
  @In("theStack") @Maps("theItems[*] #into theStack;")
  protected java.lang.Object[] theItems;

  @In("theStack;")
  protected int nextFree;

  @In("MAX_SIZE;")
  protected int maxSize;


  @SpecCase(header="public normal_behavior",
            assignable="MAX_SIZE, size, theStack;",
            ensures="theStack.equals(new JMLObjectSequence());",
            ensuresRedundantly="theStack.isEmpty() && size == 0;")
  public BoundedStack( )
  { 
    maxSize = 10;
    theItems = new Object[maxSize];
    nextFree = 0;
    /*@ assert \fresh(theItems) && nextFree == 0
      @   && theItems.length == maxSize;
      @*/
  }

  @SpecCase(header="public normal_behavior",
            assignable="MAX_SIZE, size, theStack;",
            ensures="theStack.equals(new JMLObjectSequence());",
            ensuresRedundantly="theStack.isEmpty() && size == 0"
            +                    "&& MAX_SIZE == maxSize;")
  public BoundedStack(int maxSize)
  { 
    theItems = new Object[maxSize];
    nextFree = 0;
    this.maxSize = maxSize;
    /*@ assert \fresh(theItems) && nextFree == 0
      @   && theItems.length == maxSize;
      @*/
  }

  public Object clone ()
  {
    BoundedStack retValue = new BoundedStack(maxSize);
    retValue.nextFree = nextFree;
    for (int k = 0; k < nextFree; k++) {
      retValue.theItems[k] = theItems[k];
    }
    /*@ assert \fresh(retValue) && retValue.nextFree == nextFree
      @     && (\forall int k; 0 <= k && k <= retValue.theItems.length - 1;
      @                        retValue.theItems[k] == theItems[k]);
      @*/
    return retValue;
  }

  public int getSizeLimit()
  {
    return maxSize;
  }

  public boolean isEmpty( )
  {
    return (nextFree == 0);
  }

  public boolean isFull()
  {
    return (nextFree == maxSize);
  }

  public void pop( ) throws BoundedStackException
  {
    if (nextFree == 0) {
      throw new BoundedStackException("Tried to pop an empty stack.");
    } else {
      nextFree--;
      //@ assert nextFree == \old(nextFree) - 1;
      return;
    }   
  }

  public void push(Object x ) throws BoundedStackException
  {
    if (nextFree == maxSize) {
      throw new BoundedStackException("Tried to push onto a full stack");
    } else if (x == null) {
      throw new NullPointerException("Argument x to push is null");
    } else {
      theItems[nextFree++] = x;
      /*@ assert theItems[\old(nextFree)] == x 
        @        && nextFree == \old(nextFree) + 1;
        @*/
      return;
    }   
  }

  public Object top( ) throws BoundedStackException
  {
    if (nextFree == 0) {
      throw new BoundedStackException("empty stack");
    } else {
      return theItems[nextFree - 1];
    }
  }

  @Also({@SpecCase(header="public normal_behavior",
                   assignable="#nothing;",
                   ensures="#result != null"
                   +       "&& (* a string encoding of this is returned *);") })
  public String toString()
  {
    StringBuffer ret = new StringBuffer(this.getClass().toString() + " [");
    boolean first = true;
    for (int k = nextFree - 1; k >= 0; k--) {
        if (first) {
            first = false;
        } else {
            ret.append(", ");
        }
        if (theItems[k] != null) {
            ret.append(theItems[k]);
        } else {
            ret.append("null");
        }
    } 
    ret.append("]");
    /*@ assert (* returnString is of the form 
      @            "[<top item>, <next item>, ...]" *);
      @*/
    return ret.toString();
  }

  @SpecCase(header="protected normal_behavior",
            assignable="System.out;",
            ensures="(* prints a version of stack to System.out *);")
  protected void printStack ( )
  {
    System.out.println("The stack items are (top first):");
    System.out.println(toString());
    //@ assert (* toString() is appended to System.out *);
  }
}
