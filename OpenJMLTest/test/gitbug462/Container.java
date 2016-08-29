public class Container {
    /*@ private normal_behavior
      @   assignable \nothing;
      @*/
    private /*@ helper @*/ Container() {}

    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public static /*@ pure @*/ Container allocate() {
        Container c = new Container();
        return c;
    }
    
    public static class ContainerUser {
        private /*@ non_null @*/ Container c;

        /*@ private normal_behavior
          @   assignable \nothing;
          @*/
        private /*@ helper @*/ ContainerUser() {}

        /*@ public normal_behavior
          @   assignable \nothing;
          @*/
        public static ContainerUser allocate() {
            ContainerUser user = new ContainerUser();
            user.c = Container.allocate();
            return user;
        }

        public void test() {
            ContainerUser user = allocate();
            //@ assert user.c instanceof Container;
        }
    }
}