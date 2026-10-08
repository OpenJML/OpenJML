import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

class AnnoTypeVarBounds {
    @Target(value = {ElementType.TYPE_USE})
    @interface A{}
    class Sup<X, Y> { }
    class Sub<U extends @A V, @A V extends String> extends Sup<U, V> { }
}
