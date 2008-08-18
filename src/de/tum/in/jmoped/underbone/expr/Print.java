package de.tum.in.jmoped.underbone.expr;

/**
 * Value for {@link de.tum.in.jmoped.underbone.ExprType#PRINT}.
 */
public class Print {
	
	public int type;
	public boolean newline;
	
	public Print(int type, boolean newline) {
		this.type = type;
		this.newline = newline;
	}
	
	public String toString() {
		return type + " " + newline;
	}
	
	public static final int INTEGER = 0;
	public static final int FLOAT = 1;
	public static final int CHARACTER = 2;
	public static final int STRING = 3;
}