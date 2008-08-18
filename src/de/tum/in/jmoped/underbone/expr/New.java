package de.tum.in.jmoped.underbone.expr;

import de.tum.in.jmoped.underbone.ExprType;

/**
 * Value for {@link ExprType#NEW}.
 */
public class New {
	
	public int id;
	public int size;
	
	public New(int id, int size) {
		this.id = id;
		this.size = size;
	}
	
	public String toString() {
		return String.format("id:%d size:%d", id, size);
	}
}