package de.tum.in.jmoped.underbone.expr;

/**
 * Value for {@link de.tum.in.jmoped.underbone.ExprType#JUMP}.
 */
public enum Jump {
	/**
	 * Unconditional jump
	 */
	ONE, 
	
	/**
	 * Catches an exception. The top-of-stack becomes the only element.
	 * and resets the error status {@link Remopla#e} to 0.
	 */
	THROW;
}