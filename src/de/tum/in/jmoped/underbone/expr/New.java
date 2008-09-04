package de.tum.in.jmoped.underbone.expr;


/**
 * New information. Value for {@link ExprType#NEW}.
 */
public class New {
	
	public int id;
	public String name;
	public int size;
	
	/**
	 * The constructor.
	 * 
	 * @param id the class id.
	 * @param name the class name.
	 * @param size the class size.
	 */
	public New(int id, String name, int size) {
		this.id = id;
		this.name = name;
		this.size = size;
	}
	
	public String toString() {
		return String.format("id:%d(%s) size:%d", id, name, size);
	}
}