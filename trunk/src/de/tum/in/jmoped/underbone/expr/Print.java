package de.tum.in.jmoped.underbone.expr;

/**
 * Print information. Value for {@link de.tum.in.jmoped.underbone.expr.ExprType#PRINT}.
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
	
	public static final int NOTHING = 0;
	public static final int INTEGER = 1;
	public static final int LONG = 2;
	public static final int FLOAT = 3;
	public static final int DOUBLE = 4;
	public static final int CHARACTER = 5;
	public static final int STRING = 6;
}