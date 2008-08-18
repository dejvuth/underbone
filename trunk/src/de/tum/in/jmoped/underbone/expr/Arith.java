package de.tum.in.jmoped.underbone.expr;

/**
 * Arithmetic expression.
 * 
 * @author suwimont
 *
 */
public class Arith implements Expr {
	
	public static final int ADD = 0;
	public static final int AND = 1;
	public static final int CMP = 2;
	public static final int DIV = 3;
	public static final int MUL = 4;
	public static final int OR = 5;
	public static final int REM = 6;
	public static final int SHL = 7;
	public static final int SHR = 8;
	public static final int SUB = 9;
	public static final int USHR = 10;
	public static final int XOR = 11;
	public static final int FADD = 12;
	public static final int FCMPG = 13;
	public static final int FCMPL = 14;
	public static final int FDIV = 15;
	public static final int FMUL = 16;
	public static final int FREM = 17;
	public static final int FSUB = 18;
	public static final int NDT = 19;
	
	private int type;
	private Category category;
	
	public Arith(int type, Category cat) {
		this.type = type;
		this.category = cat;
	}
	
	public int getType() {
		return type;
	}
	
	public Category getCategory() {
		return category;
	}
}
