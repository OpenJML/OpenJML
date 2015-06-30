import java.util.Collection;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import freeboogie.ast.*;

// TODO: Some nonnullness assertions need to be added

// NOTE A bunch of provers are supposed to reuse the same builder.
// NOTE Sort constructors (such as * -> *) should be necessary only if
//      the prover is higher-order. That is not supported.
// NOTE I don't want to distinguish axioms from assumptions.
// NOTE The prover does not know about the `background predicate';
//      that is the responsability of the VCgen

class TermType {
  private Class cls;
  private Sort[] argSorts;
  private Sort naryArgSort;
  private Sort retSort;

  public Class cls() { return cls; }
  public Sort[] argSorts() { return argSorts; }
  public Sort naryArgSort() { return naryArgSort; }
  public Sort retSort() { return retSort; }
  
  public TermType(Sort[] argSorts, Sort retSort) {
    this.argSorts = argSorts;
    this.retSort = retSort;
  }
  public TermType(Sort naryArgSort, Sort retSort) {
    this.naryArgSort = retSort;
    this.retSort = retSort;
  }
  public TermType(Class cls, Sort retSort) {
    this.cls = cls;
    this.retSort = retSort;
  }
}

// NOTE Sorts don't vary too much from prover to prover. 
enum Sort {
  ANY(null),
  PRED(ANY),
  VALUE(ANY),
  INT(VALUE),
  BOOL(VALUE),
  REAL(VALUE),
  REF(VALUE);

  public final Sort superSort;
  Sort(Sort superSort) {
    this.superSort = superSort;
  }
  public boolean isSubSortOf(Sort other) {
    if (this == other) return true;
    if (superSort == null) return false;
    return superSort.isSubSortOf(other);
  }
  public Sort superSort() {
    return superSort;
  }
}

class Term {
  private Sort sort;
  public Term(Sort sort) {
    this.sort = sort;
  }
  public Sort sort() {
    return sort;
  }
}

// A standard utility, not really related to the prover backend.
class StackedHashMap<K, V> implements Map<K, V> {
  private LinkedList<LinkedHashMap<K, V>> data = 
    new LinkedList<LinkedHashMap<K, V>>();

  // The extra methods
  public void push() {
    data.addFirst(new LinkedHashMap<K, V>());
  }
  public void pop() {
    data.removeFirst();
  }
  
  // The Map<K, V> interface implementation
  public void clear() { data.clear(); }
  public boolean containsKey(Object key) { return get(key) != null; }
  public boolean containsValue(Object value) {
    for (LinkedHashMap<K, V> h : data) 
      if (h.containsValue(value)) return true;
    return false;
  }
  public Set<Map.Entry<K, V>> entrySet() {
    Set<Map.Entry<K, V>> r = new LinkedHashSet<Map.Entry<K, V>>();
    for (LinkedHashMap<K, V> h : data)
      r.addAll(h.entrySet());
    return r;
  }
  public boolean equals(Object other) {
    return false; // todo
  }
  public V get(Object key) {
    return null; // todo
  }
  public int hashCode() {
    return 0; // todo
  }
  public boolean isEmpty() { return size() == 0; }
  public Set<K> keySet() {
    return null; // todo
  }
  public V put(K key, V value) {
    return null; // todo
  }
  public void putAll(Map<? extends K, ? extends V> m) {
    // todo
  }
  public V remove(Object key) {
    return null; // todo
  }
  public int size() {
    return 0; // todo
  }
  public Collection<V> values() {
    return null; // todo
  }
}

public abstract class Builder {
  private StackedHashMap<String, TermType> termTypes =
    new StackedHashMap<String, TermType>();

  public void reg(String name, Sort[] argSorts, Sort retSort) {
    assert termTypes.get(name) == null; // attempted to register `name' twice
    termTypes.put(name, new TermType(argSorts, retSort));
  }
  public void reg(String name, Sort naryArgSort, Sort retSort) {
    assert termTypes.get(name) == null; // attempted to register `name' twice
    termTypes.put(name, new TermType(naryArgSort, retSort));
  }
  public void reg(String name, Class cls, Sort retSort) {
    assert termTypes.get(name) == null; // attempted to register `name' twice
    termTypes.put(name, new TermType(cls, retSort));
  }
  public void unreg(String name) {
    termTypes.remove(name);
  }

  public void pushReg() { termTypes.push(); }
  public void popReg() { termTypes.pop(); }

  public TermType getTermType(String name) {
    TermType r = termTypes.get(name);
    assert r != null; // attempted to use an unregistered name
    return r;
  }

  public final Term mk(String termId, Object a) { 
    TermType type = getTermType(termId);
    assert type.cls() != null;
    assert type.cls().isInstance(a);
    Term r = reallyMk(termId, a);
    assert r.sort().isSubSortOf(type.retSort());
    return r; 
  }
  public final Term mk(String termId, Term a) {
    return mk(termId, new Term[] {a});
  }
  public final Term mk(String termId, Term a, Term b) {
    return mk(termId, new Term[] {a, b});
  }
  public final Term mk(String termId, Term[] a) {
    TermType type = getTermType(termId);
    if (type.naryArgSort() != null) {
      for (int i = 0; i < a.length; ++i)
        assert a[i].sort().isSubSortOf(type.naryArgSort());
      Term r = reallyMkNary(termId, a);
      assert r.sort().isSubSortOf(type.retSort());
      return r;
    }
    if (type.argSorts() != null) {
      assert type.argSorts().length == a.length;
      for (int i = 0; i < a.length; ++i)
        assert a[i].sort().isSubSortOf(type.argSorts()[i]);
      Term r = reallyMk(termId, a);
      assert r.sort().isSubSortOf(type.retSort());
      return r;
    }
    assert false;
    return null;
  }

  protected abstract Term reallyMk(String termId, Object a);
  protected abstract Term reallyMk(String termId, Term[] a);
  protected abstract Term reallyMkNary(String termId, Term[] a);
}

interface ProverAnswer {}

class ProverException extends Exception {
  private ProverAnswer answer;
  public ProverException(String reason) { this(reason, null); }
  public ProverException(ProverAnswer answer) { this("", answer); }
  public ProverException(String reason, ProverAnswer answer) {
    super(reason);
    this.answer = answer;
  }
}

// NOTE Prover handles things like introducing definitions,
//      exploiting stuff like bg_push and bg_pop, and so on.
interface Prover {
  public Builder getBuilder();
  // TODO Check that t is a predicate here?
  public void makeAssumption(Term t) throws ProverException;
  public void retractAssumption() throws ProverException;
  public boolean isSat(Term t) throws ProverException;
  public ProverAnswer getDetailedAnswer();

  // also, resend all the previous assumptions
  public void restartProver() throws ProverException;
}


class ConcreteBuilder extends Builder {
  public ConcreteBuilder() {
    // built-in operators
    reg("and", Sort.BOOL, Sort.BOOL);

    // built-in functions?

    // constants
    reg("const_int", Integer.class, Sort.INT);
    reg("const_bool", Boolean.class, Sort.BOOL);

    // to-be-bound variables
    reg("var_int", String.class, Sort.INT);
    reg("var_bool", String.class, Sort.BOOL);

    // quantifiers
    reg("any_int", new Sort[]{Sort.INT, Sort.PRED}, 
      Sort.PRED);
    reg("exists_int", new Sort[]{Sort.INT, Sort.PRED}, 
      Sort.PRED);
    // (idea: a bunch of provers reuse the same builder)
  }

  protected Term reallyMk(String termId, Object a) { return new Term(null); }
  protected Term reallyMk(String termId, Term[] a) { return new Term(null); }
  protected Term reallyMkNary(String termId, Term[] a) { return new Term(null); }
}

class ConcreteProver implements Prover {
  public ConcreteBuilder getBuilder() { 
    return new ConcreteBuilder(); 
  }
  public void makeAssumption(Term t) {
    assert t.sort() == Sort.PRED;
    // todo
  }
  public void retractAssumption() {
    // todo
  }
  public boolean isSat(Term t) {
    return false; // todo
  }
  public ProverAnswer getDetailedAnswer() {
    return null; // todo
  }
  public void restartProver() throws ProverException {
    // todo
  }
}

// NOTE The VCgen is responsible for high-level decisions such as
//      whether an axiomatization of integerAdd is necessary or the
//      built in `+' is used.
class VcGen {
  private Prover p;
  private Builder b;

  public VcGen(Prover p) {
    this.p = p;
    b = p.getBuilder();
  }

  public Term visitBinaryOp(BinaryOp bo, BinaryOp.Op op, Expr left, Expr right) {
    return b.mk("and", visitExpr(left), visitExpr(right));
  }

  public Term visitExpr(Expr expr) {
    return b.mk("var_int", "x"); // an integer named "x"
  }
}

