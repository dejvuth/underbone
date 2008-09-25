package de.tum.in.jmoped.underbone.expr;

/**
 * Increment information.
 * 
 * Value for {@link de.tum.in.jmoped.underbone.expr.ExprType#INC}.
 */
public class Inc implements Expr {
	
	/**
	 * The local variable index.
	 */
	public int index;
	
	/**
	 * The value to be incremented with.
	 */
	public int value;
	
	/**
	 * Constructs an increment information.
	 * 
	 * @param index the local variable index.
	 * @param value the value to be incremented with.
	 */
	public Inc(int index, int value) {
		this.index = index;
		this.value = value;
	}
	
	public int hashCode() {
		return 31*(31*7 + index) + value;
	}
	
	public boolean equals(Object o) {
		if (o == null) return false;
		if (!(o instanceof Inc)) return false;
		
		Inc that = (Inc) o;
		return index == that.index && value == that.value;
	}
	
	public String toString() {
		return index + " by " + value;
	}
}