public class adopt {

void m() {

   Object x;
   x = new adopt();

   A a = new A () { void p() { System.out.println(x.hashCode()); } };
   a.p();

   x = null;
   a.p();

   a = new A () { void p() { System.out.println(x.hashCode()); } };
   a.p();

   
   a  = new A () { void p() { System.out.println("42"); } };
   a.p();
}

}

class A {
  
   void p() {
   }

}
