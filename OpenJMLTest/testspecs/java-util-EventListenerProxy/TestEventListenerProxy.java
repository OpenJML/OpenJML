import java.util.EventListener;
import java.util.EventListenerProxy;

public class TestEventListenerProxy {

    static class Listener implements EventListener {
        //@ public normal_behavior
        //@ pure
        public Listener() {}
    }

    static class Proxy extends EventListenerProxy<Listener> {
        //@ public normal_behavior
        //@   ensures getListener() == l;
        //@ pure
        public Proxy(/*@ nullable */ Listener l) { super(l); }
    }

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        listener();
        nullListener();
        System.out.println("DONE");
    }

    public static void listener() {
        Listener l = new Listener();
        Proxy p = new Proxy(l);
        //@ assert p.getListener() == l;
        EventListener e = p;
    }

    public static void nullListener() {
        Proxy p = new Proxy(null);
        //@ assert p.getListener() == null;
    }
}
