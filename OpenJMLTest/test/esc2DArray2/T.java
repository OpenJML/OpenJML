public class T {

void m(int[] a, int[][] aa) {
   //@ assume a.length == 10;
   //@ assume \nonnullelements(aa);
   //@ assume aa.length == 20;
   //@ assume \forall int i; 0 <= i < aa.length; aa[i] != null && aa[i].length > 10;

   a[3] = 4;
   aa[5][6] = 7;
   //@ havoc a[8];
   //@ assert a.length == 10;
   //@ havoc a[*];
   //@ assert a.length == 10;
   //@ havoc aa[1][2];
}

void mm(int[][] aa) {
   //@ assume \nonnullelements(aa);
   //@ assume aa.length == 20;
   //@ assume \forall int i; 0 <= i < aa.length; aa[i] != null && aa[i].length == i;

   //@ assert aa[2].length == 2;
   //@ havoc aa[2][1];
   //@ assert aa[2].length == 2;
}
}
