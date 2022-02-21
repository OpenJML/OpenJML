class Value<T> {
  public T value;

  Value(T t) { value = t; }
  
  void check() {
    //@ assert \typeof(value) <: \type(T); 
  }
}

