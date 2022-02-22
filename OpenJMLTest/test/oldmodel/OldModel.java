// Tests that model fields inside \old work OK
public class OldModel {

  public int data; //@ in value;
  public int other;

  //@ public model int value;
  //@ public represents value = data + 1;

  //@ requires data == 9;
  public void test() {
    other = 5;
    //@ assert value == \old(value);
    //@ assert value == \old(value, Pre);
    data = 19;
    //@ assert value == 20;
    //@ assert \old(value) == 10;
    //@ assert value == 10 + \old(value, Pre);
  }

  //@ requires data == 9;
  public void testerr() {
    other = 5;
    data = 19;
    //@ assert value ==  \old(value, Pre); // ERROR
  }
}

    
