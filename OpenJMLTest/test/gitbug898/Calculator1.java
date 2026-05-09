public class Calculator1 {
    //@ requires operator == '+' || operator == '-' || operator == '*' || operator == '/' || operator == '%';
    //@ requires operator != '/' || num2 != 0;
    //@ assigns \nothing;
    //@ ensures (\result == num1 + num2 && operator == '+') 
    //@       || (\result == num1 - num2 && operator == '-') 
    //@       || (\result == num1 * num2 && operator == '*') 
    //@       || (\result == num1 / num2 && operator == '/') 
    //@       || (\result == num1 % num2 && operator == '%') 
    //@       || (\result == -1 && operator != '+' && operator != '-' && operator != '*' && operator != '/' && operator != '%');
    public static int calculate(int num1, int num2, char operator) {
        int output;

        switch (operator) {
            case '+':
                output = num1 + num2;
                break;

            case '-':
                output = num1 - num2;
                break;

            case '*':
                output = num1 * num2;
                break;

            case '/':
                //@ requires num2 != 0;
                output = num1 / num2;
                //@ ensures \result == num1 / num2;
                break;

            case '%':
                //@ requires num2 != 0;
                output = num1 % num2;
                //@ ensures \result == num1 % num2;
                break;

            default:
                return -1;
        }
        return output;
    }
}
