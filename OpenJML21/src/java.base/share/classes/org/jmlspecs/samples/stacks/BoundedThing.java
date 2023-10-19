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

import org.jmlspecs.annotation.*;

    @ModelDefinitions({
        @Model("public instance int MAX_SIZE;"),
        @Model("public instance int size;") })
    @InvariantDefinitions({
        @Invariant(header="public instance",
                   value="MAX_SIZE > 0;"),
        @Invariant(header="public instance",
                   value="0 <= size && size <= MAX_SIZE;") })
    @Constraint(header="public instance",
                value="MAX_SIZE == #old(MAX_SIZE);")
public interface BoundedThing {

    @SpecCase(header="public normal_behavior",
              ensures="#result == MAX_SIZE;")
    @Pure public int getSizeLimit();

    @SpecCase(header="public normal_behavior",
              ensures="#result <==> size == 0;")
    @Pure public boolean isEmpty();

    @SpecCase(header="public normal_behavior",
              ensures="#result <==> size == MAX_SIZE;")
    @Pure public boolean isFull();

    @Also({ @SpecCase(header="public behavior",
                      assignable="#nothing;",
                      ensures="#result instanceof BoundedThing"
                      +       "&& size == ((BoundedThing)#result).size;",
                      signalsOnly="CloneNotSupportedException;") })
    public Object clone ()
       throws CloneNotSupportedException;
}
