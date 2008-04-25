package de.tum.in.jmoped.underbone;

import java.util.Arrays;

/**
 * A raw method argument.
 * 
 * @author suwimont
 *
 */
public class RawArgument {

	Object[] lv;
	Object[] heap;
	
	RawArgument(int nlv, int nheap) {
		lv = new Object[nlv];
		heap = new Object[nheap];
	}
	
	public Object getLocalVariable(int index) {
		return lv[index];
	}
	
	public Object getHeapElement(int index) {
		return heap[index];
	}
	
	public String toString() {
		return String.format("lv: %s, heap: %s", Arrays.toString(lv), Arrays.toString(heap));
	}
}
