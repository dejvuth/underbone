package de.tum.in.jmoped.underbone.expr;

/**
 * Value for {@link de.tum.in.jmoped.underbone.ExprType#INC}.
 */
public class Inc {
	
	public int index;
	public int value;
	
	public Inc(int index, int value) {
		this.index = index;
		this.value = value;
	}
	
	public String toString() {
		return index + " by " + value;
	}
}