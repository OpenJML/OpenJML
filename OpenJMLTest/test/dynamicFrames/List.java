abstract public class List<T> {
	
	abstract List addToTail();
	abstract List deleteTail();
}

class LinkedList<T> extends List<T> {
	
	class Element<T> {
		public T value;
		public Element<T> next;

		void addToTail(T t) {
			if (next == null) {
				next = new Element<T>(t);
			} else {
				next.addToTail(t);
			}
		}
		
		void deleteTail() {
			if (next == null) {
				
			} else if (next.next != null) {
				next.deleteTail();
			} else {
				next = null;
			}
		}
	}
	
	public Element<T> head = new Element<T>(null); // not in list; so head is never null
	
	
	public List addToTail(T t) {
		head.addToTail(t);
	}
	
	public List deleteTail() {
		head.deleteTail();
	}
	
}