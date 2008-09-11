package de.tum.in.jmoped.underbone.expr;

/**
 * Local variable information.
 * 
 * Value for {@link de.tum.in.jmoped.underbone.expr.ExprType#LOAD} and 
 * {@link de.tum.in.jmoped.underbone.expr.ExprType#STORE}.
 */
public class Local implements Expr {
	
	/**
	 * Category 1 or 2.
	 */
	private Category category;
	
	/**
	 * The index of this local variable.
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
	
	/**
	 * Gets the computational type category of this local.
	 * 
	 * @return the category.
	 */
	public Category getCategory() {
		return category;
	}
	
	public String toString() {
		return String.format("%s index:%d", category, index);
	}
}