package de.tum.in.jmoped.underbone.expr;


import de.tum.in.jmoped.underbone.NullSemiring;
import de.tum.in.wpds.Semiring;

/**
 * An implementation of Semiring encoding expression types.
 * 
 * @author suwimont
 *
 */
public class ExprSemiring extends NullSemiring {
	
	/**
	 * The type of the expression.
	 */
	public int type;
	
	/**
	 * The value of the expression.
	 */
	public Object value;
	
	/**
	 * The auxiliary value of the expression.
	 */
	public Object aux;
	
	/**
	 * Constructs an expression semiring.
	 * 
	 * @param type the type of the expression.
	 */
	public ExprSemiring(int type) {
		this(type, null, null);
	}
	
	/**
	 * Constructs an expression semiring.
	 * The meaning of <code>value</code> depends on the <code>type</code>
	 * of the expression.
	 * 
	 * @param type the type of the expression.
	 * @param value the value of the expression.
	 */
	public ExprSemiring(int type, Object value) {
		this(type, value, null);
	}
	
	/**
	 * Constructs an expression semiring.
	 * The meaning of <code>value</code> and <code>aux</code>
	 * depends on the <code>type</code> of the expression.
	 * 
	 * @param type the type of the expression.
	 * @param value the value of the expression.
	 * @param aux the auxiliary value of the expression.
	 */
	public ExprSemiring(int type, Object value, Object aux) {
		this.type = type;
		this.value = value;
		this.aux = aux;
	}
	
	/**
	 * Returns the string representation of this expression.
	 * 
	 * @return the string representation of this expression.
	 */
	public String toString() {
		StringBuilder out = new StringBuilder(ExprType.toString(type));
		if (value != null) out.append(" ").append(value.toString());
		if (aux != null) out.append(" ").append(aux.toString());
		
		return out.toString();
	}

	/**
	 * Copies the expression.
	 */
	public Semiring id() {
		return new ExprSemiring(type, value, aux);
	}
}
