package de.tum.in.jmoped.underbone.expr;

public class Monitorenter {
	
	public Monitorenter.Type type;
	public Object value;
	
	/**
	 * Constructor for POP.
	 * 
	 * @param type
	 */
	public Monitorenter(Monitorenter.Type type) {
		if (type != Monitorenter.Type.POP)
			throw new IllegalArgumentException(
					"Internal jMoped error: Type POP expected");
		this.type = type;
		this.value = 1;
	}
	
	/**
	 * Constructor for TOUCH and STATIC
	 * 
	 * @param type
	 * @param value
	 */
	public Monitorenter(Monitorenter.Type type, Object value) {
		if (type != Monitorenter.Type.TOUCH && type != Monitorenter.Type.STATIC)
			throw new IllegalArgumentException(
					"Internal jMoped error: Type TOUCH or STATIC expected");
		this.type = type;
		this.value = value;
	}
	
	public int intValue() {
		return (Integer) value;
	}
	
	public String stringValue() {
		return (String) value;
	}
	
	public String toString() {
		return String.format("%s %s", type, value);
	}
	
	public static enum Type {
		POP, TOUCH, STATIC
	}
}