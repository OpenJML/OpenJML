
public class NumberArithmetic
{

    public static void int_lt_constant_tests()
    {
    //@ assert 3 < 4;
    //@ assert -4 < -3;
    //@ assert -100 < -99;
    //@ assert -544 < 456;
    }
    
    public static void int_gt_constant_tests()
    {
    //@ assert 7 > 1;
    //@ assert 18 > -5;
    //@ assert -55940 > -66705;
    //@ assert 58530 > -59033;
    }
    
    public static void int_lte_constant_tests()
    {
    //@ assert 3 <= 3;
    //@ assert -596 <= -596;
    //@ assert -5843 <= 69343;
    //@ assert 6853 <= 9953;
    //@ assert -229402 <= -50493;
    }
    
    public static void int_gte_constant_tests()
    {
    //@ assert 643 >= 643;
    //@ assert -6043 >= -6043;
    //@ assert 69402 >= -693392;
    //@ assert 20420 >= 10193;
    //@ assert -3482 >= -5942;
    }
    
    public static void int_eq_constant_tests()
    {
    //@ assert 443 == 443;
    //@ assert -50493 == -50493;
    //@ assert 0 == 0;
    //@ assert 124423 == 124423;
    //@ assert !(3 == 6);
    //@ assert !(-5534 == 5534);
    //@ assert 15 != 18;
    }
    
    public static void float_lt_constant_tests()
    {
    //@ assert 3.0f < 4.0f;
    //@ assert 3.0f < 3.1f;
    //@ assert 3.0f < 3.01f;
    //@ assert 3.0f < 3.001f;
    //@ assert 3.0f < 3.0001f;
    //@ assert 3.0f < 3.00001f;
    //@ assert 3.0f < 3.000001f;
    }

    public static void float_gt_constant_tests()
    {
    //@ assert   39694.23f > -58.3f;
    //@ assert -5194.333f > -5483.456f;
    //@ assert 3.44435f > -3.44435f;
    //@ assert 23.322f > -134443.4f;
    }
    
    public static void float_gte_constant_tests()
    {
    //@ assert 3.0f >= 3.0f;
    //@ assert 384.24f >= 50.00992f;
    //@ assert 2828.55f >= -3954.28f;
    //@ assert -6434.54f >= -7964.99f;
    //@ assert 6.03E-3f >= 9.32E-4f;
    }
    
    public static void float_lte_constant_tests()
    {
    //@ assert -3.0f <= -3.0f;
    //@ assert -384.24f <= 50.00992f;
    //@ assert -2828.55f <= 3954.28f;
    //@ assert -6434.54f <= 7964.99f;
    }
    
    public static void float_eq_constant_tests()
    {
    //@ assert -3.245f == -3.245f;
    //@ assert 0.0f == 0.0f;
    //@ assert 1059.593f == 1059.593f;
    }

    public static void float_scientific_test_0()
    {
    //@ assert 562.03424E2f == 562.03424E2f;
    //@ assert 56.203424E3f == 56.203424E3f;
    //@ assert 5.6203424E4f == 5.6203424E4f;
    //@ assert 56.203424E4f == 56.203424E4f;
    //@ assert 56.203424E5f == 56.203424E5f;   
    //@ assert 3.323E3f == 3.323E3f;
    //@ assert 3239423942324.322342f == 3239423942324.322342f;
    //@ assert 0.0643433f == 0.0643433f;
    //@ assert 64.3433E-3f == 64.3433E-3f;
    //@ assert 64.3433E-4f == 64.3433E-4f;
    //@ assert 64.3433E-5f == 64.3433E-5f;
    //@ assert 64.3433E-6f == 64.3433E-6f;
    //@ assert 64.3433E-7f == 64.3433E-7f;
    //@ assert 0.385E-5f == 0.385E-5f;
    //@ assert -0.385E-5f == -0.385E-5f;
    //@ assert 3.85E-6f == 3.85E-6f;
    //@ assert -3.85E-6f == -3.85E-6f;
    //@ assert 38.5E-7f == 38.5E-7f;
    }
    
    public static void float_scientific_test_1()
    {
    //@ assert 0.56203424E8f == 0.56203424E8f;
    //@ assert 5.6203424E7f == 5.6203424E7f;
    //@ assert 56.203424E6f == 56.203424E6f;
    //@ assert 53234.234E3f == 53234.234E3f;
    //@ assert 3.2034E12f == 3.2034E12f; 
    //@ assert 5.6203424E8f == 5.6203424E8f;
    //@ assert 0.00043643E8f == 0.00043643E8f;
    //@ assert 56.203424E7f == 56.203424E7f;
    //@ assert -62E13f == -62E13f;
    //@ assert 3.2E12f == 3.2E12f;
    //@ assert 62E13f == 62E13f;
    }
   
    public static void float_scientific_test_2()
    {
    //@ assert 0.323E3f == 0.323E3f;
    //@ assert 88.3E1f == 88.3E1f;
    //@ assert -562.0E-2f == -562.0E-2f;
    //@ assert 562.0E-2f == 562.0E-2f;
    //@ assert 64.3433E-2f == 64.3433E-2f;
    //@ assert 0.3433E-2f == 0.3433E-2f;
    }
    
    public static void float_scientific_test_3()
    {
    //@ assert 64.3433E-9f == 64.3433E-9f;
    //@ assert 64.3433E-10f == 64.3433E-10f;
    //@ assert 64.3433E-11f == 64.3433E-11f;
    //@ assert 64.3433E-12f == 64.3433E-12f;
    //@ assert 38.5E-8f == 38.5E-8f;
    //@ assert 3.85E-7f == 3.85E-7f;
    }
        
    public static void double_lt_constant_tests()
    {
    //@ assert 3.0 < 4.0;
    //@ assert 3.0 < 3.1;
    //@ assert 3.0 < 3.01;
    //@ assert 3.0 < 3.001;
    //@ assert 3.0 < 3.0001;
    //@ assert 3.0 < 3.00001;
    //@ assert 3.0 < 3.000001;
    //@ assert 3.0 < 3.0000001;
    //@ assert 3.0000001 < 3.0000002;
    }

    public static void double_gt_constant_tests()
    {
    //@ assert 16.3 > 15.3;
    //@ assert 19.483 > -1928.255;
    //@ assert 1082292.224 > 40.4592;
    //@ assert -833.528 > -9844.34;
    }

    public static void double_scientific_test_0()
    {
    //@ assert 562.03424E2 == 562.03424E2;
    //@ assert 56.203424E3 == 56.203424E3;
    //@ assert 5.6203424E4 == 5.6203424E4;
    //@ assert 56.203424E4 == 56.203424E4;
    //@ assert 56.203424E5 == 56.203424E5;   
    //@ assert 3.323E3 == 3.323E3;
    //@ assert 3239423942324.322342 == 3239423942324.322342;
    //@ assert 0.0643433 == 0.0643433;
    //@ assert 64.3433E-3 == 64.3433E-3;
    //@ assert 64.3433E-4 == 64.3433E-4;
    //@ assert 64.3433E-5 == 64.3433E-5;
    //@ assert 64.3433E-6 == 64.3433E-6;
    //@ assert 64.3433E-7 == 64.3433E-7;
    //@ assert 0.385E-5 == 0.385E-5;
    //@ assert -0.385E-5 == -0.385E-5;
    //@ assert 3.85E-6 == 3.85E-6;
    //@ assert -3.85E-6 == -3.85E-6;
    //@ assert 38.5E-7 == 38.5E-7;
    }
    
    public static void double_scientific_test_1()
    {
    //@ assert 0.56203424E8 == 0.56203424E8;
    //@ assert 5.6203424E7 == 5.6203424E7;
    //@ assert 56.203424E6 == 56.203424E6;
    //@ assert 53234.234E3 == 53234.234E3;
    //@ assert 3.2034E12 == 3.2034E12; 
    //@ assert 5.6203424E8 == 5.6203424E8;
    //@ assert 0.00043643E8 == 0.00043643E8;
    //@ assert 56.203424E7 == 56.203424E7;
    //@ assert -62E13 == -62E13;
    //@ assert 3.2E12 == 3.2E12;
    //@ assert 62E13 == 62E13;
    }
   
    public static void double_scientific_test_2()
    {
    //@ assert 0.323E3 == 0.323E3;
    //@ assert 88.3E1 == 88.3E1;
    //@ assert -562.0E-2 == -562.0E-2;
    //@ assert 562.0E-2 == 562.0E-2;
    //@ assert 64.3433E-2 == 64.3433E-2;
    //@ assert 0.3433E-2 == 0.3433E-2;
    }
    
    public static void double_scientific_test_3()
    {
    //@ assert 64.3433E-9 == 64.3433E-9;
    //@ assert 64.3433E-10 == 64.3433E-10;
    //@ assert 64.3433E-11 == 64.3433E-11;
    //@ assert 64.3433E-12 == 64.3433E-12;
    //@ assert 38.5E-8 == 38.5E-8;
    //@ assert 3.85E-7 == 3.85E-7;
    }
    
    public static void double_lte_constant_tests()
    {
    //@ assert 155.2553 <= 90394.493;
    //@ assert 186.9395 <= 186.9395;
    //@ assert 12.2 <= 13.2;
    //@ assert -12958.35835 <= 30394.3432;
    //@ assert -19299.4382 <= -924.2;
    }
    
    public static void double_gte_constant_tests()
    {
    //@ assert 582.3483 >= 493.3822;
    //@ assert -5043.304 >= -409293.43234;
    //@ assert 58342.342 >= -5835.23;
    }
    
    public static void double_eq_constant_tests()
    {
    //@ assert 3.141592 == 3.141592;
    //@ assert 3.1111 == 3.1111;
    //@ assert 0.0 == 0.0;
    //@ assert !(3.15252 == 3.15251);
    //@ assert 3.29595 != 302.425624;
    }

    // testing equality of positive and negative zero
    public static void int_zero_tests()
    {
        //@ assert +0 == -0;
        //@ assert +0 == 0;
        //@ assert -0 == 0;
	//@ assert +0 <= -0;
	//@ assert -0 >= 0;
	//@ assert 0 == 0;
    }
    
    public static void float_zero_tests()
    {
        //@ assert +0f == -0f;
        //@ assert +0f == 0f;
        //@ assert +0f <= -0f;
        //@ assert -0f >= 0f;
        //@ assert -0f == 0f;
        //@ assert 0 == 0.0f;
    }
    
    public static void double_zero_tests()
    {
        //@ assert +0.0 == -0.0;
        //@ assert +0.0 == 0.0;
        //@ assert -0.0 == 0.0;
        //@ assert 0 == 0.0;
    }
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c);
    public static void equivalence_properties(float a, float b, float c)
    {
    	// == tests:
	//@ assert a == a; //reflexive
	//@ assert (a == b) <==> (b == a); //symmetric
	//@ assert (a == b && b == c) ==> a == c; //transitive
	//@ assert (a == b) <==> !(a != b); //partition of pairs of numbers into equal or not equal
	//@ assert a != b <==> b != a; //inequality is symmetric
    }

    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);
    public static void equivalence_properties(double a, double b, double c)
    {
    	// == tests:
	//@ assert a == a; //reflexive
	//@ assert (a == b) <==> (b == a); //symmetric
	//@ assert (a == b && b == c) ==> a == c; //transitive
	//@ assert (a == b) <==> !(a != b); //partition of pairs of numbers into equal or not equal
	//@ assert a != b <==> b != a; //inequality is symmetric
    }

    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c);
    public static void partial_order_properties(float a, float b, float c)
    {
	//@ assert a <= a; //reflexive
	//@ assert (a <= b && b <= c) ==> (a <= c); //transitive
	//@ assert (a <= b) || (b <= a); //all numbers are comparable
	//@ assert (a <= b) <==> (b >= a); //equivalence of <= and >=
	//@ assert (a <= b) <==> !(a > b); //partition of pairs a, b into <= and > relations
    }

    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);
    public static void partial_order_properties(double a, double b, double c)
    {
	//@ assert a <= a; //reflexive
	//@ assert (a <= b && b <= c) ==> (a <= c); //transitive
	//@ assert (a <= b) || (b <= a); //all numbers are comparable
	//@ assert (a <= b) <==> (b >= a); //equivalence of <= and >=
	//@ assert (a <= b) <==> !(a > b); //partition of pairs a, b into <= and > relations
    }

    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c);
    public static void strict_inequality_properties(float a, float b, float c)
    {
	//@ assert !(a < a); //anti-reflexive
	//@ assert (a < b) ==> !(b < a); //anti-symmetric
	//@ assert (a < b && b < c) ==> a < c; //transitive
    }
    
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);
    public static void strict_inequality_properties(double a, double b, double c)
    {
	//@ assert !(a < a); //anti-reflexive
	//@ assert (a < b) ==> !(b < a); //anti-symmetric
	//@ assert (a < b && b < c) ==> a < c; //transitive
    }

    // This method tests OpenJML's ability to prove the basic properties
    // of the ==, <=, and < binary relations on numbers only
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c);
    public static void binary_relation_test_1(float a, float b, float c)
    {
	 //@ assert a == b || a <= b || a > b;
        //@ assert a == b || a != b;
        //@ assert a <= b ==> (a == b || a < b);
	//@ assert a != b ==> (a > b || a < b);
    }
    
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);
    public static void binary_relation_test_1(double a, double b, double c)
    {
	 //@ assert a == b || a <= b || a > b;
        //@ assert a == b || a != b;
        //@ assert a <= b ==> (a == b || a < b);
	//@ assert a != b ==> (a > b || a < b);
    }   
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c);
    public static void binary_relation_test_2(float a, float b, float c)
    {
        //@ assert a < b ==> a <= b;
        //@ assert !(a < b && b < a);
        //@ assert (a <= b && b <= a) ==> a == b;
        //@ assert (a <= b && b < c) ==> a < c;
    }

    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);
    public static void binary_relation_test_2(double a, double b, double c)
    {
        //@ assert a < b ==> a <= b;
        //@ assert !(a < b && b < a);
        //@ assert (a <= b && b <= a) ==> a == b;
        //@ assert (a <= b && b < c) ==> a < c;
    }

    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c);
    public static void add_associativity(float a, float b, float c)
    {
    	//@ assert (a + b) + c == a + (b + c); //associativity
    }
    
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);
    public static void add_associativity(double a, double b, double c)
    {
    	//@ assert (a + b) + c == a + (b + c); //associativity
    }
    
    //@ requires Float.isFinite(a) && Float.isFinite(b);
    public static void add_commutative(float a, float b)
    {
	//@ assert a + b == b + a; //commutative
    }   
    
    //@ requires Double.isFinite(a) && Double.isFinite(b);
    public static void add_commutative(double a, double b)
    {
	//@ assert a + b == b + a; //commutative
    }   
    
    //@ requires Float.isFinite(a);
    public static void add_identity(float a)
    {
	//@ assert a + 0 == a; //identity
	//@ assert a + 0.0 == a;
	//@ assert a + 0.0f == a;
    }
    
    //@ requires Double.isFinite(a);
    public static void add_identity(double a)
    {
	//@ assert a + 0 == a; //identity
	//@ assert a + 0.0 == a;
	//@ assert a + 0.0f == a;
    }

    //@ requires Float.isFinite(a);
    public static void add_inverse(float a)
    {
	//@ assert a - a == 0; //inverse
	//@ assert a + -a == 0;
    }   

    //@ requires Double.isFinite(a);
    public static void add_inverse(double a)
    {
	//@ assert a - a == 0; //inverse
	//@ assert a + -a == 0;
    }   

    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d);    
    public static void add_ordering(float a, float b, float c, float d)
    {
	//@ assert (a < b && c < d) ==> (a + c) <= (b + d); //ordering
    }
    
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d);    
    public static void add_ordering(double a, double b, double c, double d)
    {
	//@ assert (a < b && c < d) ==> (a + c) <= (b + d); //ordering
    }
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d); 
    public static void add_equality(float a, float b, float c, float d)
    {
	//@ assert a == b ==> a + c == b + c; //preservation of equality
	//@ assert ( a == b && c == d) ==> ( a + c == b + d && a + d == b + c);
	//@ assert a == b ==> a - c == b - c;
    }
    
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d); 
    public static void add_equality(double a, double b, double c, double d)
    {
	//@ assert a == b ==> a + c == b + c; //preservation of equality
	//@ assert ( a == b && c == d) ==> ( a + c == b + d && a + d == b + c);
	//@ assert a == b ==> a - c == b - c;
    }
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d); 
    public static void add_sign(float a, float b, float c, float d)
    {
        //@ assert (a > 0 && b > 0) ==> (a + b > 0); //sign tests
        //@ assert (a < 0 && b < 0) ==> ( a + b < 0);
	//@ assert (a >= 0 && b >= 0) ==> a + b >= 0;
	//@ assert (a <= 0 && b <= 0) ==> a + b <= 0;
	//@ assert (a > 0 && b > 0) ==> a + b > 0;
	//@ assert (a < 0 && b < 0) ==> a + b < 0;
	//@ assert (a == 0 && a == b) ==> (b == 0 && a + b == 0);
    }
    
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d); 
    public static void add_sign(double a, double b, double c, double d)
    {
        //@ assert (a > 0 && b > 0) ==> (a + b > 0); //sign tests
        //@ assert (a < 0 && b < 0) ==> ( a + b < 0);
	//@ assert (a >= 0 && b >= 0) ==> a + b >= 0;
	//@ assert (a <= 0 && b <= 0) ==> a + b <= 0;
	//@ assert (a > 0 && b > 0) ==> a + b > 0;
	//@ assert (a < 0 && b < 0) ==> a + b < 0;
	//@ assert (a == 0 && a == b) ==> (b == 0 && a + b == 0);
    }
        
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c);     
    public static void mult_associativity(float a, float b, float c)
    {
    	//@ assert (a * b) * c == a * (b * c); //associativity
    }


    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);     
    public static void mult_associativity(double a, double b, double c)
    {
    	//@ assert (a * b) * c == a * (b * c); //associativity
    }
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c); 
    public static void mult_distributive(float a, float b, float c)
    {
        //@ assert a * (b + c) == a * b + a * c; //distributivity
    }

    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c);     
    public static void mult_distributive(double a, double b, double c)
    {
        //@ assert a * (b + c) == a * b + a * c; //distributivity
    }    
    

    //@ requires Float.isFinite(a); 
    public static void mult_identity(float a)
    {
    	//@ assert a * 1 == a;
	//@ assert a * 1.0 == a;
	//@ assert a * 1.0f == a;
    }
    
    //@ requires Double.isFinite(a);     
    public static void mult_identity(double a)
    {
    	//@ assert a * 1 == a;
	//@ assert a * 1.0 == a;
	//@ assert a * 1.0f == a;
    }
    
    //@ requires Float.isFinite(a); 
    public static void mult_inverse(float a)
    {
    	//@ assert a != 0 ==> a * (1 / a) == 1; //inverse
    }

    //@ requires Double.isFinite(a);     
    public static void mult_inverse(double a)
    {
    	//@ assert a != 0 ==> a * (1 / a) == 1; //inverse
    }

    //@ requires Float.isFinite(a); 
    public static void mult_commutative(float a, float b)
    {
    	//@ assert a * b == b * a; //commutative
    }
    
    //@ requires Double.isFinite(a);     
    public static void mult_commutative(double a, double b)
    {
    	//@ assert a * b == b * a; //commutative
    }
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d); 
    public static void mult_ordering(float a, float b, float c, float d)
    {
    	//@ assert a < b && 0 <= c ==> a * c <= b * c; //ordering property
    }
    
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d);     
    public static void mult_ordering(double a, double b, double c, double d)
    {
    	//@ assert a < b && 0 <= c ==> a * c <= b * c; //ordering property
    }
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d); 
    public static void mult_equality(float a, float b, float c, float d)
    {
	//@ assert a == b ==> a * c == b * c; //preservation of equality
	//@ assert (a == b && c != 0) ==> a / c == b / c;
	//@ assert (a == b && c == d) ==> a * c == b * d;
	//@ assert (a * c == b * d && d != 0 && c != 0) ==> a / d == b / c;
        //@ assert (b != 0 && d != 0) ==> (a / b) * (c / d) == (a * c) / (b * d);
    }
    
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d);     
    public static void mult_equality(double a, double b, double c, double d)
    {
	//@ assert a == b ==> a * c == b * c; //preservation of equality
	//@ assert (a == b && c != 0) ==> a / c == b / c;
	//@ assert (a == b && c == d) ==> a * c == b * d;
	//@ assert (a * c == b * d && d != 0 && c != 0) ==> a / d == b / c;
        //@ assert (b != 0 && d != 0) ==> (a / b) * (c / d) == (a * c) / (b * d);
    }
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d); 
    public static void mult_sign(float a, float b, float c, float d)
    {
        //@ assert (a > 0 && b > 0) ==> (a * b > 0); //sign tests
        //@ assert (a > 0 && b < 0) ==> (a * b < 0);
        //@ assert (a < 0 && b < 0) ==> (a * b > 0);
        //@ assert (a < 0 && b > 0) ==> (a * b < 0);
	//@ assert a * b == 0 ==> (a == 0 || b == 0);
    }

    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d);     
    public static void mult_sign(double a, double b, double c, double d)
    {
        //@ assert (a > 0 && b > 0) ==> (a * b > 0); //sign tests
        //@ assert (a > 0 && b < 0) ==> (a * b < 0);
        //@ assert (a < 0 && b < 0) ==> (a * b > 0);
        //@ assert (a < 0 && b > 0) ==> (a * b < 0);
	//@ assert a * b == 0 ==> (a == 0 || b == 0);
    }

    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d);     
    public static void quadratic_expansions(float a, float b, float c, float d)
    {
    	// quadratic expansions
	//@ assert (a + b) * (c + d) == a * c + a * d + b * c + b * d;
	//@ assert (a + b) * (c - d) == a * c - a * d + b * c - b * d;
	//@ assert (a + b) * (a - b) == a * a - b * b;
    }
 
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d);   
    public static void quadratic_expansions(double a, double b, double c, double d)
    {
    	// quadratic expansions
	//@ assert (a + b) * (c + d) == a * c + a * d + b * c + b * d;
	//@ assert (a + b) * (c - d) == a * c - a * d + b * c - b * d;
	//@ assert (a + b) * (a - b) == a * a - b * b;
    }

    //@ requires Float.isFinite(a) && Float.isFinite(b); 
    public static void cubic_expansions(float a, float b)
    {
	// cubic expansions
	//@ assert a * a * a + b * b * b == (a + b) * (a * a - a * b + b * b); //sum of cubes
	//@ assert a * a * a - b * b * b == (a - b) * (a * a + a * b  + b * b); //difference of cubes
    }
 
    //@ requires Double.isFinite(a) && Double.isFinite(b);   
    public static void cubic_expansions(double a, double b)
    {
	// cubic expansions
	//@ assert a * a * a + b * b * b == (a + b) * (a * a - a * b + b * b); //sum of cubes
	//@ assert a * a * a - b * b * b == (a - b) * (a * a + a * b  + b * b); //difference of cubes
    }
    
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d); 
    public static void linear_equation(float a, float b, float c, float d)
    {
    	//@ assert (a == b * c + d && b != 0 ) ==>  c == (a - d) / b;
    }
    
    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d);   
    public static void linear_equation(double a, double b, double c, float d)
    {
	//@ assert (a == b * c + d && b != 0 ) ==>  c == (a - d) / b;
    }
    
    //@ requires Float.isFinite(a) && Float.isFinite(b) && Float.isFinite(c) && Float.isFinite(d) && Float.isFinite(e) && Float.isFinite(f); 
    public static void linear_system(float a, float b, float c, float d, float e, float f)
    {
    	//@ assert (1 == a * e + b * f && 1 == c * e + d * f && a * d != b * c ) ==> ( e == 1 / (a * d - b * c) * (d - b) && f == 1 / (a * d - b * c) * ( a - c)  );
    }

    //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(c) && Double.isFinite(d) && Double.isFinite(e) && Double.isFinite(f);    
    public static void linear_system(double a, double b, double c, double d, double e, double f)
    {
    	//@ assert (1 == a * e + b * f && 1 == c * e + d * f && a * d != b * c ) ==> ( e == 1 / (a * d - b * c) * (d - b) && f == 1 / (a * d - b * c) * ( a - c)  );
    }

}
