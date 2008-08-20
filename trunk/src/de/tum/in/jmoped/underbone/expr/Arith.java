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
	
	private static String toString(int type) {
		switch(type) {
		case ADD: return "ADD";
		case AND: return "AND";
		case CMP: return "CMP";
		case DIV: return "DIV";
		case MUL: return "MUL";
		case OR: return "OR";
		case REM: return "REM";
		case SHL: return "SHL";
		case SHR: return "SHR";
		case SUB: return "SUB";
		case USHR: return "USHR";
		case XOR: return "XOR";
		case FADD: return "FADD";
		case FCMPG: return "FCMPG";
		case FCMPL: return "FCMPL";
		case FDIV: return "FDIV";
		case FMUL: return "FMUL";
		case FREM: return "FREM";
		case FSUB: return "FSUB";
		case NDT: return "NDT";
		}
		
		throw new ExprError("Unexpected arithmetic type %d", type);
	}
	
	public String toString() {
		return String.format("%s %s", toString(type), category.toString());
	}
}
