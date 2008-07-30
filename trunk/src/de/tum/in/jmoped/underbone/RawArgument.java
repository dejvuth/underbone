package de.tum.in.jmoped.underbone;

import java.util.Arrays;

/**
 * A raw method argument.
 * 
 * @author suwimont
 *
 */
public class RawArgument {

	/**
	 * The values of local variables.
	 */
	Object[] lv;
	
	/**
	 * The values of the heap.
	 */
	Object[] heap;
	
	/**
	 * Constructs a raw argument.
	 * 
	 * @param nlv the number of local variables.
	 * @param nheap the heap size.
	 */
	RawArgument(int nlv, int nheap) {
		lv = new Object[nlv];
		heap = new Object[nheap];
	}
	
	/**
	 * Gets the value of the local variable specified by <code>index</code>.
	 * 
	 * @param index the index of the local variable.
	 * @return the value.
	 */
	public Object getLocalVariable(int index) {
		return lv[index];
	}
	
	/**
	 * Gets the heap element at <code>index</code>.
	 * 
	 * @param index the index of the heap.
	 * @return the heap element.
	 */
	public Object getHeapElement(int index) {
		return heap[index];
	}
	
	/**
	 * Retruns the string representation of this argument values.
	 * 
	 * @return the string representation of this argument values.
	 */
	public String toString() {
		return String.format("lv: %s, heap: %s", Arrays.toString(lv), Arrays.toString(heap));
	}
}
