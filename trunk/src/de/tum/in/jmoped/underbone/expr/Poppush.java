package de.tum.in.jmoped.underbone.expr;

import de.tum.in.jmoped.underbone.ExprType;

/**
 * Value for {@link ExprType#POPPUSH}.
 */
public class Poppush {
	
	public int pop;
	public int push;
	
	public Poppush(int pop, int push) {
		this.pop = pop;
		this.push = push;
	}
	
	/**
	 * Returns <code>true</code> if neither push nor pop.
	 * 
	 * @return <code>true</code> if neither push nor pop.
	 */
	public boolean nochange() {
		return pop == 0 && push == 0;
	}
	
	public boolean push() {
		return push > 0;
	}
	
	public String toString() {
		return String.format("pop:%d, push:%d", pop, push);
	}
}