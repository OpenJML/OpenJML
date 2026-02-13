public class Calculator2 {
    //@ requires operator == '+' || operator == '-' || operator == '*' || operator == '/' || operator == '%';
    //@ requires (operator != '/' && operator != '%') || num2 != 0;
    //@ ensures (operator == '+') ==> (\result == (long)num1 + num2);
    //@ ensures (operator == '-') ==> (\result == (long)num1 - num2);
    //@ ensures (operator == '*') ==> (\result == (long)num1 * num2);
    //@ ensures (operator == '/') ==> (\result == (long)num1 / num2);
    //@ ensures (operator == '%') ==> (\result == (long)num1 % num2);
    //@ also
    //@ requires operator != '+' && operator != '-' && operator != '*' && operator != '/' && operator != '%';
    //@ ensures \result == -1;
    //@ behaviors disjoint;
    //@ behaviors complete;
    //@ pure
    public static long calculate(int num1, int num2, char operator) {

        long output;

        switch (operator) {
        case '+':
            output = (long)num1 + num2;
            break;

        case '-':
            output = (long)num1 - num2;
            break;

        case '*':
            output = (long)num1 * num2;
            break;

        case '/':
            // @ requires num2 != 0;
            //@ refining
            output = (long)num1 / num2;
            break;

        case '%':
            // @ requires num2 != 0;
            //@ refining
            output = (long)num1 % num2;
            break;

        default:
            return -1;
        }
        return output;
    }
    
    //@ requires operator == '+' || operator == '-' || operator == '*' || operator == '/' || operator == '%';
    //@ requires (operator != '/' && operator != '%') || num2 != 0;
    //@ requires operator == '/' ==> (num1 != Integer.MIN_VALUE || num2 != -1);
    //@ ensures (operator == '+') ==> (\result == (long)num1 + num2);
    //@ ensures (operator == '-') ==> (\result == (long)num1 - num2);
    //@ ensures (operator == '*') ==> (\result == (long)num1 * num2);
    //@ ensures (operator == '/') ==> (\result == (long)num1 / num2);
    //@ ensures (operator == '%') ==> (\result == (long)num1 % num2);
    //@ also
    //@ requires operator != '+' && operator != '-' && operator != '*' && operator != '/' && operator != '%';
    //@ ensures \result == -1;
    //@ behaviors disjoint;
    // @ behaviors complete; // No. not complete, because of the tests for zero, etc.
    //@ pure code_safe_math spec_bigint_math
    public static long calculateOK(int num1, int num2, char operator) {

        long output;

        switch (operator) {
        case '+':
            output = (long)num1 + num2;
            break;

        case '-':
            output = (long)num1 - num2;
            break;

        case '*':
            output = (long)num1 * num2;
            break;

        case '/':
            //@ refining
            //@ requires num2 != 0;
            output = (long)num1 / num2;
            //@ show operator, num1, num2, output;
            break;

        case '%':
            //@ refining
            //@ requires num2 != 0;
            output = (long)num1 % num2;
            //@ show operator, num1, num2, output;
           break;

        default:
            return -1;
        }
        return output;
    }

}
