package de.tum.in.jmoped.underbone.expr;

/**
 * Computational type category. Long and double are of type 2.
 * The rest is of type 1.
 * 
 * @author suwimont
 *
 */
public enum Category implements Expr {

//	public static final int ZERO = 0;
//	public static final int ONE = 1;
//	public static final int TWO = 2;
//	
//	public static String toString(int cat) {
//		return String.format("cat:%d", cat);
//	}
	
	ZERO(0), ONE(1), TWO(2);
	
	private int value;
	
	private Category(int value) {
		this.value = value;
	}
	
	public int intValue() {
		return value;
	}
	
	public boolean one() {
		return value == 1;
	}
	
	public boolean two() {
		return value == 2;
	}
	
	public String toString() {
		return String.format("category:%d", value);
	}
}
