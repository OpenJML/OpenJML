package org.jmlspecs.openjml.esc;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlRange;

import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.util.List;

public class StoreRefGroup {

    public enum Kind { NOTHING, EVERYTHING, STATIC_FIELD, INSTANCE_FIELD, ARRAY_ELEMENTS, EXPRESSION, LOCAL };
    
    public static class Item {
        public Kind kind;
        public JCExpression expression; // for EXPRESSION
        public JCExpression receiver; // for INSTANCE_FIELD or ARRAY_ELEMENTS
        public Symbol.VarSymbol field; // STATIC_FIELD, INSTANCE_FIELD, LOCAL
        public JmlRange range;  // ARRAY_ELEMENTS
        
        public Item(Kind kind) { this.kind = kind; }
        public Item(JCExpression r, Symbol.VarSymbol field) { this(Kind.INSTANCE_FIELD); this.receiver = r; this.field = field; }
        public Item(Symbol.VarSymbol field) { this(field.owner instanceof Symbol.ClassSymbol ? Kind.STATIC_FIELD : Kind.LOCAL ); this.receiver = null; this.field = field; }
        public Item(JCExpression a, JmlRange range) { this(Kind.ARRAY_ELEMENTS); this.receiver = a; this.range = range; }
        public Item(JCExpression e) { this(Kind.EXPRESSION); this.expression = e; }
        
        public String toString() {
            return switch (this.kind) {
                case NOTHING -> "\\nothing";
                case EVERYTHING -> "\\everything";
                case LOCAL -> field.toString();
                case STATIC_FIELD -> field.owner + "." + field;
                case INSTANCE_FIELD -> receiver + "." + field;
                case ARRAY_ELEMENTS -> receiver + "[" + range + "]";
                case EXPRESSION -> expression.toString();
            };
        }
    }
    
    public StoreRefGroup(JCExpression guard, List<Item> items) {
        this.guard = guard;
        this.items = items;
    }
    
    /** Only for NOTHING and EVERYTHING */
    public StoreRefGroup(JCExpression guard, StoreRefGroup.Kind k) {
        this.guard = guard;
        this.items = List.<StoreRefGroup.Item>of(new StoreRefGroup.Item(k));
    }
    
    public JCExpression guard;
    
    public List<Item> items = List.<Item>nil();
    
    public String toString() {
        return "[" + guard + " -> " + Utils.join(", ", items) + "]";
    }
}
