public class TickTockClock {
//@ public model int _time_state;

//@ protected invariant 0 <= hour && hour <= 23;
protected int hour; //@ in _time_state;
//@ protected invariant 0 <= minute && minute <= 59;
protected int minute; //@ in _time_state;
//@ protected invariant 0 <= second && second <= 59;
protected int second; //@ in _time_state;

 //@ assignable this.*;
 //@ ensures getHour() == 12 && getMinute() == 0 && getSecond() == 0;
 public /*  @ pure @*/ TickTockClock() {
 hour = 12; minute = 0; second = 0;
 }

 //@ requires true;
 //@ ensures 0 <= \result && \result <= 23; 
 //@ ensures \result == hour;
 public /*@ pure @*/ int getHour() { return hour; }

 //@ ensures 0 <= \result && \result <= 59; 
 //@ ensures \result == minute;
 public /*@ pure @*/ int getMinute() { return minute; }

 //@ ensures 0 <= \result;
 //@ ensures \result <= 59; 
 //@ ensures \result == second;
 public /*@ pure @*/ int getSecond() { return second; }

 /*@ requires getSecond() < 59;
 @ assignable hour, minute, second; // NB for expository purposes only
 @ assignable _time_state;
 @ ensures getSecond() == \old(getSecond() + 1) &&
 @ getMinute() == \old(getMinute()) &&
 @ getHour() == \old(getHour());
 @ also
 @ requires getSecond() == 59;
 @ assignable _time_state;
 @ assignable hour, minute, second; // NB for expository purposes only
 @ ensures getSecond() == 0;
 @*/
 public void tick() {
 second++;
 if (second == 60) { second = 0; minute++; }
 if (minute == 60) { minute = 0; hour++; }
 if (hour == 24) { hour = 0; }
 }
 }
