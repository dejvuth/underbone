package de.tum.in.jmoped.underbone.expr;

/**
 * Computational type category. Long and double are of type 2.
 * The rest is of type 1.
 * 
 * @author suwimont
 *
 */
public class Category implements Expr {
	
	/**
	 * Category zero, representing the void return type.
	 */
	public static final Category ZERO = new Category(0);
	
	/**
	 * Category one.
	 */
	public static final Category ONE = new Category(1);
	
	/**
	 * Category two.
	 */
	public static final Category TWO = new Category(2);
	
	private int cat;
	
	private Category(int cat) {
		this.cat = cat;
	}
	
	public int intValue() {
		return cat;
	}
	
	public boolean one() {
		return cat == 1;
	}
	
	public boolean two() {
		return cat == 2;
	}
	
	public String toString() {
		return String.format("category:%d", cat);
	}
}
