package de.tum.in.jmoped.underbone.expr;

/**
 * Comparison.
 * 
 * @author suwimont
 *
 */
public class Comp {

	public static final int EQ = 0;
	public static final int NE = 1;
	public static final int LT = 2;
	public static final int GE = 3;
	public static final int GT = 4;
	public static final int LE = 5;
	
	public static String toString(int type) {
		switch (type) {
		case EQ: return "==";
		case NE: return "!=";
		case LT: return "<";
		case GE: return ">=";
		case GT: return ">";
		case LE: return "<=";
		}
		
		throw new ExprError("Unkwown comparison type");
	}
}
