import java.util.Scanner;
//@ model import org.jmlspecs.models.JMLFloat;

    
class FahrenheitToCelsius {
	/*@ spec_public */static double Celsius;
     
    //@ requires Float.isFinite(temperature);
    //@ assignable Celsius;
    //@ ensures Double.isFinite(Celsius) && Float.isFinite(\result);
    //@ ensures JMLFloat.approximatelyEqualTo(\result, (((temperature - 32)*5)/9), 0.1f) == true;
	public static float Temperature(float temperature) {
	
       
     
        Celsius = ((temperature - 32)*5)/9;
     
        System.out.println("temperature in Celsius = " + Celsius);
	    return (float)Celsius;
    }
     public static void main(String[] args) {
	     float temperature;
         Scanner in = new Scanner(System.in);
     
         System.out.println("Enter temperature in Fahrenheit");
         temperature = in.nextFloat();
	     Temperature(temperature);
       }
    }
