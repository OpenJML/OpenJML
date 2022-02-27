package sv_esc;



public class LoopExercises2 {
	/*@ normal_behavior
	  @ requires x != null;
	  @ requires x.length > 0;
	  @ ensures (\forall int k; 0 <= k && k < x.length; x[k] <= \result);
	 */
	public int max(int [] x){
		int max = x[0];
		int i = 1;
		while (i < x.length) {
			if (x[i] > max) {
				max = x[i];
			}
			i++;
		}
		return max;
	}
}