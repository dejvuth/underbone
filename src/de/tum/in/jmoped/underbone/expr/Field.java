package de.tum.in.jmoped.underbone.expr;


/**
 * Field information.
 * 
 * Value for {@link ExprType#CONSTLOAD}, 
 * {@link ExprType#CONSTSTORE},
 * {@link ExprType#GLOBALLOAD}, 
 * {@link ExprType#GLOBALSTORE},
 * {@link ExprType#FIELDLOAD}, 
 * {@link ExprType#FIELDSTORE}.
 *
 */
public class Field {
	
	/**
	 * Category 1 or 2
	 */
	private Category category;
	
	/**
	 * Id or offset of this field
	 */
	private int id;
	
	/**
	 * Name of this field.
	 */
	private String name;
	
	/**
	 * Constructs a static field information.
	 * 
	 * @param category the field category.
	 * @param name the field name.
	 */
	public Field(Category category, String name) {
		this.category = category;
		this.name = name;
	}
	
	/**
	 * Constructs an instance field information.
	 * 
	 * @param category the field category.
	 * @param id the field id.
	 */
	public Field(Category category, int id) {
		this.category = category;
		this.id = id;
	}
	
	/**
	 * Gets the computational type category of this field.
	 * 
	 * @return the category.
	 */
	public Category getCategory() {
		return category;
	}
	
	/**
	 * Gets the id of this field.
	 * 
	 * @return the id.
	 */
	public int getId() {
		return id;
	}
	
	/**
	 * Gets the name of this field.
	 * 
	 * @return the name.
	 */
	public String getName() {
		return name;
	}
	
	/**
	 * Returns the string representation of this field information.
	 * 
	 * @return the string representation of this field information.
	 */
	public String toString() {
		return String.format("%s id:%d name:%s", category.toString(), id, name);
	}
}