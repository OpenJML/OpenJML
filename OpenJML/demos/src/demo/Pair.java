package demo;


public class Pair {



    public int leq(String a, String b){
        if(a.length() < b.length()){
            return -1;
        }else{
            if(a.length() > b.length()){
                return 1;
            }
            return 0;
        }
    }


}