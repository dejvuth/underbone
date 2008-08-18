package de.tum.in.jmoped.underbone.expr;

import java.util.Set;

/**
 * Value for {@link ExprType#UNARYOP}.
 */
public class Unaryop {
	
	/**
	 * Operation type.
	 */
	public Unaryop.Type type;
	
	public Set<Integer> set;
	
	public Unaryop(Unaryop.Type type) {
		this.type = type;
	}
	
	public Unaryop(Unaryop.Type type, Set<Integer> set) {
		if (type != Type.CONTAINS)
			throw new ExprError("Internal error: " +
					"A Unary operation of type CONTAINS expected");
		if (set == null)
			throw new ExprError("Internal error: " +
					"A set of integers expected");
		this.type = type;
		this.set = set;
	}
	
	public String toString() {
		if (set == null) return type.toString();
		return String.format("%s %s", type, set);
	}
	
	/**
	 * Unary operation type: negation and type conversion.
	 */
	public static enum Type {
		
		DNEG(Category.TWO, Category.TWO),
		
		/**
		 * Negates float
		 */
		FNEG(Category.ONE, Category.ONE),
		
		/**
		 * Negates
		 */
		INEG(Category.ONE, Category.ONE),
		
		LNEG(Category.TWO, Category.TWO),
		
		D2F(Category.TWO, Category.ONE),
		D2I(Category.TWO, Category.ONE),
		D2L(Category.TWO, Category.TWO),
		
		F2D(Category.ONE, Category.TWO),
		
		/**
		 * Converts float to int
		 */
		F2I(Category.ONE, Category.ONE),
		
		F2L(Category.ONE, Category.TWO),
		
		I2D(Category.ONE, Category.TWO),
		
		/**
		 * Converts int to float
		 */
		I2F(Category.ONE, Category.ONE),
		
		I2L(Category.ONE, Category.TWO),
		
		L2D(Category.TWO, Category.TWO),
		
		L2F(Category.TWO, Category.ONE),
		
		L2I(Category.TWO, Category.ONE),
		
		/**
		 * Pushes one the set in <code>aux</code> contains the top-of-stack;
		 * or zero otherwise. Note that this is different from 
		 * {@link Condition.ConditionType#CONTAINS} which considers
		 * the object id pointed the top-of-stack.
		 */
		CONTAINS(Category.ONE, Category.ONE);
		
		public Category pop;
		public Category push;
		
		Type(Category pop, Category push) {
			this.pop = pop;
			this.push = push;
		}
	}
}