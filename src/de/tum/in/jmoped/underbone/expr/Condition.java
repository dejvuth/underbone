package de.tum.in.jmoped.underbone.expr;

import java.util.Set;

/**
 * Conditions that must be fulfilled during extend.
 * 
 * @author suwimont
 *
 */
public class Condition {
	
	/**
	 * The field <code>value</code> is a global variable name.
	 * The condition is fulfilled if the variable is equal to zero.
	 */
	public static final int ZERO = 0;
	
	/**
	 * The field <code>value</code> is a global variable name.
	 * The condition is fulfilled if the variable is equal to one.
	 */
	public static final int ONE = 1;
	
	/**
	 * The field <code>value</code> is a set of integers (Set<Integer>)
	 * The condition is fulfilled if the class id is contained in
	 * the set. Note that the class id is obtained from the heap
	 * where the stack representing the first argument points to.
	 * Note that this different from {@link Unaryop.Type#CONTAINS}
	 * which considers the directly the value of the top-of-stack 
	 * (i.e. the top-of-stack is not a pointer).
	 */
	public static final int CONTAINS = 2;
	
	/**
	 * Opposite to CONTAINS.
	 */
	public static final int NOTCONTAINS = 3;
	
	/**
	 * The condition type.
	 */
	private int type;
	
	/**
	 * The value.
	 */
	private Object value;
	
	/**
	 * The constructor.
	 * 
	 * @param type the condition type.
	 * @param value the value.
	 */
	public Condition(int type, Object value) {
		switch (type) {
		case ZERO:
		case ONE:
			if (!(value instanceof String))
				throw new IllegalArgumentException("Argument of type String expected");
			break;
		case CONTAINS:
		case NOTCONTAINS:
			if (!(value instanceof Set))
				throw new IllegalArgumentException("Argument of type Set expected");
			break;
		}
		this.type = type;
		this.value = value;
	}
	
	public int getType() {
		return type;
	}
	
	@SuppressWarnings("unchecked")
	public Set<Integer> getSetValue() {
		return (Set<Integer>) value;
	}
	
	public String getStringValue() {
		return (String) value;
	}
	
	/**
	 * Returns the string representing this condition.
	 * 
	 * @return the string representing this condition.
	 */
	public String toString() {
		return String.format("[CONDITION %s %s]", getTypeString(), value);
	}
	
	private String getTypeString() {
		switch (type) {
		case ZERO: return "ZERO";
		case ONE: return "ONE";
		case CONTAINS: return "CONTAINS";
		case NOTCONTAINS: return "NOTCONTAINS";
		}
		
		throw new ExprError("Unknown condition: " + type);
	}
	
	public int hashCode() {
		int hash = 31*7 + type;
		if (value != null) hash = 31*hash + value.hashCode();
		return hash;
	}
	
	public boolean equals(Object o) {
		if (o == null) return false;
		if (!(o instanceof Condition)) return false;
		
		Condition that = (Condition) o;
		if (type != that.type) return false;
		if (value == null)
			return that.value == null;
		return value.equals(that.value);
	}
}