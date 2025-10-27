
public class Test<T,U> {
    
    static <T,U extends Test> void m(U x) {}
    void p(T y, U x) {  }
    
    Class<?> m() { return null; }
    
}

class ClassType {
}

interface InterfaceType {
}


class ZZ<T extends ClassType & InterfaceType> {}  // FIXME - not an intersection type