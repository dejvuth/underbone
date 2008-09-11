package de.tum.in.jmoped.underbone.expr;

import java.util.Set;

/**
 * Unary operation.
 * 
 * Value for {@link ExprType#UNARYOP}.
 */
public class Unaryop {
	
	/**
	 * Operation type.
	 */
	public int type;
	
	public Category pop;
	
	public Category push;
	
	public Set<Integer> set;
	
	public static final int DNEG = 0;
	public static final int FNEG = 1;
	public static final int INEG = 2;
	public static final int LNEG = 3;
	public static final int D2F = 4;
	public static final int D2I = 5;
	public static final int D2L = 6;
	public static final int F2D = 7;
	public static final int F2I = 8;
	public static final int F2L = 9;
	public static final int I2D = 10;
	public static final int I2F = 11;
	public static final int I2L = 12;
	public static final int L2D = 13;
	public static final int L2F = 14;
	public static final int L2I = 15;
	public static final int CONTAINS = 16;
	
	public Unaryop(int type) {
		this.type = type;
		switch (type) {
		case FNEG:
		case INEG: 
		case F2I:
		case I2F:
		case CONTAINS:
			pop = Category.ONE; push = Category.ONE; break;
		case DNEG:
		case LNEG:
		case D2L:
		case L2D:
			pop = Category.TWO; push = Category.TWO; break;
		case D2F:
		case D2I:
		case L2F:
		case L2I:
			pop = Category.TWO; push = Category.ONE; break;
		case F2D:
		case F2L:
		case I2D:
		case I2L:
			pop = Category.ONE; push = Category.TWO; break;
		}
	}
	
	public Unaryop(int type, Set<Integer> set) {
		this(type);
		if (type != CONTAINS)
			throw new ExprError("Internal error: " +
					"A Unary operation of type CONTAINS expected");
		if (set == null)
			throw new ExprError("Internal error: " +
					"A set of integers expected");
		this.set = set;
	}
	
	private static String toString(int type) {
		switch (type) {
		case DNEG: return "DNEG";
		case FNEG: return "FNEG";
		case INEG: return "INEG";
		case LNEG: return "LNEG";
		case D2F: return "D2F";
		case D2I: return "D2I";
		case D2L: return "D2L";
		case F2D: return "D2L";
		case F2I: return "F2I";
		case F2L: return "F2L";
		case I2D: return "I2D";
		case I2F: return "I2F";
		case I2L: return "I2L";
		case L2D: return "L2D";
		case L2F: return "L2F";
		case L2I: return "L2I";
		case CONTAINS: return "CONTAINS";
		}
		throw new ExprError("Unexpected unary operation type: %d", type);
	}
	
	public String toString() {
		if (set == null) return toString(type);
		return String.format("%s %s", type, set);
	}
	
//	/**
//	 * Unary operation type: negation and type conversion.
//	 */
//	public static enum Type {
//		
//		DNEG(Category.TWO, Category.TWO),
//		
//		/**
//		 * Negates float
//		 */
//		FNEG(Category.ONE, Category.ONE),
//		
//		/**
//		 * Negates
//		 */
//		INEG(Category.ONE, Category.ONE),
//		
//		LNEG(Category.TWO, Category.TWO),
//		
//		D2F(Category.TWO, Category.ONE),
//		D2I(Category.TWO, Category.ONE),
//		D2L(Category.TWO, Category.TWO),
//		
//		F2D(Category.ONE, Category.TWO),
//		
//		/**
//		 * Converts float to int
//		 */
//		F2I(Category.ONE, Category.ONE),
//		
//		F2L(Category.ONE, Category.TWO),
//		
//		I2D(Category.ONE, Category.TWO),
//		
//		/**
//		 * Converts int to float
//		 */
//		I2F(Category.ONE, Category.ONE),
//		
//		I2L(Category.ONE, Category.TWO),
//		
//		L2D(Category.TWO, Category.TWO),
//		
//		L2F(Category.TWO, Category.ONE),
//		
//		L2I(Category.TWO, Category.ONE),
//		
//		/**
//		 * Pushes one the set in <code>aux</code> contains the top-of-stack;
//		 * or zero otherwise. Note that this is different from 
//		 * {@link Condition.ConditionType#CONTAINS} which considers
//		 * the object id pointed the top-of-stack.
//		 */
//		CONTAINS(Category.ONE, Category.ONE);
//		
//		public Category pop;
//		public Category push;
//		
//		Type(Category pop, Category push) {
//			this.pop = pop;
//			this.push = push;
//		}
//	}
}