package de.tum.in.jmoped.underbone.expr;

import java.util.Arrays;


/**
 * Value for {@link ExprType#NEWARRAY}.
 * 
 * @author suwimont
 *
 */
public class Newarray {
	
	public Value init;
	public int dim;
	public int[] types;
	
	/**
	 * One-dimensional array initialized with zero
	 */
	public Newarray() {
		this(new Value(Category.ONE, 0));
	}
	/**
	 * Zero array with the dimensions specified by <code>dim</code>.
	 * 
	 * @param dim the dimensions.
	 */
	public Newarray(int dim) {
		this(new Value(Category.ONE, 0), dim);
	}
	
	/**
	 * One-dimensional array initialized with the value specified by 
	 * <code>init</code>
	 * 
	 * @param init the initial value of all array elements.
	 */
	public Newarray(Value init) {
		this(init, 1);
	}
	
	public Newarray(Value init, int dim) {
		this(init, dim, new int[] { 0 });
	}
	
	public Newarray(Value init, int dim, int[] types) {
		this.init = init;
		this.dim = dim;
		this.types = types;
	}
	
	public void setType(int[] types) {
		this.types = types;
	}
	
	public String toString() {
		return String.format("%s dim: %d type: %s", 
				init.toString(), dim, Arrays.toString(types));
	}
}