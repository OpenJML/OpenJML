public class QueueUBR {
    
    private /*@ spec_public */ int[] zone;
    private /*@ spec_public */ int  start;
    private /*@ spec_public */ int   end;

    //@ public invariant zone != null;
    //@ public invariant zone.length < Integer.MAX_VALUE-10;
    //@ public invariant zone.length > 0;
    //@ public invariant  start >= 0;
    //@ public invariant  start <= end;
    //@ public invariant end >= 0;
    //@ public invariant  end <= zone.length;

    //@ public normal_behavior
    //@ ensures zone != null & end == 0 & start == 0 & zone.length == 2;
    //@ pure
    public QueueUBR (){
        zone = new int[2]; 
        start = 0;
        end = 0;
    }
    
    //@ public normal_behavior
    //@ requires taille > 0;
    //@ requires taille < Integer.MAX_VALUE -20;
    //@ ensures zone != null & start == 0 & end == 0 & zone.length == taille;
    //@ pure
    public QueueUBR (int taille){
        zone = new int[taille]; 
        end = 0;
        start = 0;
    }

    //@ ensures \result == zone.length;
    //@ pure
    public int getsize() { return zone.length; }



    //@ requires t2.length >= zone.length;
    //@ assigns t2[*];
    //@ ensures \forall int j;  start  <= j < zone.length; t2[j-start] == zone[j];
    public void copySuffix(int[] t2) {
        if (start >= zone.length) return;
        int i = start;
        //@ loop_invariant i >= start;
        //@ loop_invariant i <= zone.length;
        //@ loop_invariant (\forall int j;  start  <= j < i; t2[j-start] == zone[j]);
        //@ loop_writes t2[i-start];
        //@ decreases zone.length - i;
        while(i < zone.length) {
            t2[i-start] = zone[i]; 
            i++;
        }
    }

    //@ assigns  zone, zone[*], end, start;
    //@ ensures  end == \old(end)-\old(start);
    //@ ensures  start == 0;
    //@ ensures (\forall int i; 0 <= i < end; zone[i] == \old(zone[i+\old(start)]));
    public void recycling() {
        if (start == 0) return;
        if (start < end) {
            int[] zoneBis = new int[zone.length];
            copySuffix(zoneBis);  
            zone = zoneBis; } 
        end = end - start; start = 0;    
    }


    /*@   requires zone.length < Integer.MAX_VALUE-20;
        @ requires end < zone.length;
        @ assigns zone, zone[*], end;
        @ ensures  end == \old(end)+1;
        @ ensures \forall int i; 0 < i < \old(end); zone[i] == \old(zone[i]);
        @ ensures  zone[end-1] == elt;
        @ ensures end < zone.length;
    */
    public void add(int elt){
        zone[end] = elt;
        end++; 
        if (end < zone.length) { return; }
        int taille = zone.length+5;
        int[] zoneBis = new int[taille];
        int i = 0;
	    //@ loop_invariant i>=0;
	    //@ loop_invariant i <= zone.length;
	    //@ loop_invariant (\forall int j; 0 <= j < i; zoneBis[j] == zone[j]);
        //@ decreases zone.length - i;
        while( i < zone.length) { zoneBis[i] = zone[i]; i++;}
        zone = zoneBis;	
    }

    //@ modifies start, end;
    //@ ensures \old(start) < \old(end) ==> \result == zone[\old(start)];
    //@ ensures \old(start) < \old(end)  ==> start == \old(start) +1;
    //@ ensures \old(start) < \old(end)  ==> end == \old(end);
    //@ ensures  \old(start) == \old(end) ==> start == 0;
    //@ ensures \old(start) == \old(end) ==> end == 0;  
    //@ ensures \old(start) == \old(end) ==> \result == -1;  
    public int remove(){
        if (start == end) { start = 0; end = 0; return -1;}
        start++;
        return zone[start-1]; 
    }


}
