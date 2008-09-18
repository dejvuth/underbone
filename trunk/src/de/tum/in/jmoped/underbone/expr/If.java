package de.tum.in.jmoped.underbone.expr;

import java.util.Set;

public class If extends Comp {

	public static final int ID = 6;
	public static final int IS = 7;
	public static final int LG = 8;
	public static final int NOT = 9;
	
	private int type;
	private Object value;
	private int high;
	
	/**
	 * Comparison with zero.
	 * 
	 * @param type the comparison type.
	 */
	public If(int type) {
		this.type = type;
	}
	
	/**
	 * Determines equality with the given value.
	 * Used with {@link Type#IS}.
	 * 
	 * @param value the value.
	 */
	public If(int type, int value) {
		if (type != ID && type != IS)
			throw new ExprError("Internal error");
		this.type = type;
		this.value = value;
	}
	
	public If(int type, int low, int high) {
		if (type != LG)
			throw new ExprError("Internal error");
		this.type = LG;
		this.value = low;
		this.high = high;
	}
	
	public If(Set<Integer> value) {
		this.type = NOT;
		this.value = value;
	}
	
	public int getType() {
		return type;
	}
	
	public boolean isStandard() {
		return value == null;
	}
	
	/**
	 * Gets the constant value to be compared with the top-of-stack.
	 * Used with {@link Type#IS}. 
	 * 
	 * @return the constant value.
	 */
	public int getValue() {
		return (Integer) value;
	}
	
	public int getLowValue() {
		return (Integer) value;
	}
	
	public int getHighValue() {
		return high;
	}
	
	@SuppressWarnings("unchecked")
	public Set<Integer> getNotSet() {
		return (Set<Integer>) value;
	}
	
	public static String toString(int type) {
		switch (type) {
		case EQ: return "EQ";
		case NE: return "NE";
		case LT: return "LT";
		case GE: return "GE";
		case GT: return "GT";
		case LE: return "LE";
		case ID: return "ID";
		case IS: return "IS";
		case LG: return "LG";
		case NOT: return "NOT";
		}
		
		throw new ExprError("Unkwown comparison type");
	}
	
	public String toString() {
		StringBuilder out = new StringBuilder(toString(type));
		out.append(" ");
		out.append(value);
		if (type == LG) {
			out.append(" ").append(high);
		}
		
		return out.toString();
	}
}
