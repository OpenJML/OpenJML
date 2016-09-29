
public class E1 {
    
    //@ requires true;
    public static int m0(int a, int b){
	
	if(a < 0 || b < 0 || a + b < 0){
	    return a - b;
	}

	return a + b;
	
    }
    
    
    // - spec transformation patterns
    // - bridge paper
    // - evaluation (first ever showing of postcondition for real code)
    
    // requires true;
    //public static int m1(int a, int b){
//	
//	boolean t1, t2, t3;
//	
//	t1 = (a < 0);
//	
//	if(t1) { t2 = true; } else { t2 = b < 0; }
//	if(t2) { t3 = true; } else { t3 = a + b < 0; }
//	if(t3) { return a - b; } else { return a + b; }
//	
	
//	int d = a;
//	int c = b;
//	int g = 0;
//	int f = 0;
//	
//	if(d < b){
//	    g = d * 5;
//	}else{
//	    f = d *10;
//	}
//	
//	
//	if(d < a){
//	    a++;
//	}else{
//	    b++;
//	}
//	
//	
//	
//	d = c* d *100;
//	
//	return d;
//	
	
	
//	int d = a;
//	
//	if(d < b){
//	    d = d * 5;
//	}else{
//	    d = d *10;
//	}
//	
//	d = d *100;
//	
//	return d;
//	
	
//	if(a < 0 || b < 0 || a + b < 10){
//	    return a - b;
//	}
//	
//	return a + b;
//    }

    
    // requires true;
//    public static int m2(int a, int b){
//	
//	
//	if(a < 0){
//	    return a - b;
//	}else if(b < 0){
//	    return a - b;
//	}else if(a + b < 10){
//	    return a - b;
//	}
//
//	
//	return a + b;
//    }

}
