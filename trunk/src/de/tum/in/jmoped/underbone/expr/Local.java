package de.tum.in.jmoped.underbone.expr;

/**
 * Local variable.
 * Value for {@link de.tum.in.jmoped.underbone.ExprType#LOAD} and 
 * {@link de.tum.in.jmoped.underbone.ExprType#STORE}.
 */
public class Local {
	
	/**
	 * Category 1 or 2
	 */
	public Category category;
	
	/**
	 * The index
	 */
	public int index;
	
	/**
	 * Constructs a local variable information.
	 * 
	 * @param category the category.
	 * @param index the local variable index.
	 */
	public Local(Category category, int index) {
		this.category = category;
		this.index = index;
	}
	
	public String toString() {
		return String.format("%s index:%d", category, index);
	}
}