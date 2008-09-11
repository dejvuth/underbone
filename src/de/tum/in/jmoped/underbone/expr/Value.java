package de.tum.in.jmoped.underbone.expr;


/**
 * Value information.
 * 
 * Value for {@link ExprType#PUSH}
 * and argument of {@link Newarray}.
 * 
 * @author suwimont
 *
 */
public class Value {
	
	/**
	 * Category 1 or 2
	 */
	private Category category;
	
	private Object value;
	public Number next;
	public Number to;
			
	/**
	 * Creates a nondeterministic value.
	 */
	public Value(Category category) {
		this.category = category;
		value = null;
	}
	
	/**
	 * Creates a deterministic value.
	 * 
	 * @param value the value.
	 */
	public Value(Category category, Number value) {
		this(category, value, null, null);
	}
	
	/**
	 * Creates a nondeterministic value [<code>from</code>,<code>to</code>].
	 * 
	 * @param from min value.
	 * @param next ignored.
	 * @param to max value.
	 */
	public Value(Category category, Number from, Number next, Number to) {
		this.category = category;
		this.value = from;
		this.next = next;
		this.to = to;
	}
	
	/**
	 * Creates a value of type string.
	 * 
	 * @param value the value
	 */
	public Value(String value) {
		this.category = Category.ONE;
		this.value = value;
	}
	
	public Category getCategory() {
		return category;
	}
	
	public void setValue(Object value) {
		this.value = value;
	}
	
	public boolean isInteger() {
		return value instanceof Integer || value instanceof Long;
	}
	
	public boolean isReal() {
		return value instanceof Float || value instanceof Double;
	}
	
	public boolean isString() {
		return value instanceof String;
	}
	
	public Object getValue() {
		return value;
	}
	
	/**
	 * Returns the integer value.
	 * 
	 * @return the integer value.
	 */
	public int intValue() {
		if (!isInteger()) 
			throw new ExprError("value is not an integer");
		return ((Number) value).intValue();
	}
	
	public float floatValue() {
		if (!isReal()) 
			throw new ExprError("value is not a real number");
		return ((Number) value).floatValue();
	}
	
	public String stringValue() {
		if (!isString())
			throw new ExprError("value is not a String");
		return (String) value;
	}
	
	/**
	 * Returns <code>true</code> if the value is nondeterministic over
	 * all range.
	 * 
	 * @return <code>true</code> if the value is nondeterministic over
	 * all range.
	 */
	public boolean all() {
		return value == null;
	}
	
	public boolean deterministic() {
		return (value != null && next == null && to == null)
				|| to != null && 
					(isInteger() && intValue() == to.intValue()
					|| isReal() && floatValue() == to.floatValue());
	}
	
	public String toString() {
		if (value == null) return String.format("%s value:all", category.toString());
		if (next == null) return String.format("%s value:%s", category.toString(), value.toString());
		return String.format("%s value:[%s, %s, ..., %s]", category.toString(), value, next, to);
	}
}