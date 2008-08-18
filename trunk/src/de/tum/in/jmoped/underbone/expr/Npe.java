/**
 * 
 */
package de.tum.in.jmoped.underbone.expr;

public class Npe {
	
	/**
	 * Indicates the position of objectref in the operand stack.
	 * For example, 0 means s0, 1 means s1.
	 */
	public int depth;
	
	public Npe(int depth) {
		this.depth = depth;
	}
	
	public String toString() {
		return String.valueOf(depth);
	}
}