package de.tum.in.jmoped.underbone;

/**
 * The Remopla variable.
 * 
 * @author suwimont
 *
 */
public class Variable {

	protected int type;
	protected String name;
	private int bits;
//	private int alength;
	private int index;
//	private int savedIndex;
	private boolean shared;
	
	public static final int BOOLEAN = 0;
	public static final int INT = 1;
	
	/**
	 * Creates a variable having an undefined number of bits.
	 * 
	 * @param type the variable type.
	 * @param name the variable name.
	 */
	public Variable(int type, String name) {
		this.type = type;
		this.name = name;
	}
	
	/**
	 * Creates a variable.
	 * 
	 * @param type the variable type.
	 * @param name the variable name.
	 * @param bits the number of bits.
	 */
	public Variable(int type, String name, int bits) {
		this.type = type;
		this.name = name;
		this.bits = bits;
	}
	
	public Variable(int type, String name, int bits, boolean shared) {
		this.type = type;
		this.name = name;
		this.bits = bits;
		this.shared = shared;
	}
	
	/**
	 * Returns the name of this variable.
	 * 
	 * @return the name of this variable.
	 */
	public String getName() {
		return name;
	}
	
	/**
	 * Returns the number of bits of this variable.
	 * If undefined, the method returns <code>defaultBits</code>.
	 * 
	 * @param defaultBits the default number of bits.
	 * @return the number of bits.
	 */
	public int getBits(int defaultBits) {
		if (type == BOOLEAN) return 1;
		if (bits == 0) return defaultBits;
		return bits;
	}
	
	protected int getIndex() {
		return index;
	}
	
	protected void setIndex(int index) {
		this.index = index;
	}
	
//	public int getSavedIndex() {
//		
//		return savedIndex;
//	}
//	
//	public void setSavedIndex(int savedIndex) {
//		
//		this.savedIndex = savedIndex;
//	}
	
	public boolean isShared() {	
		return shared;
	}
	
	public void setShared(boolean shared) {
		this.shared = shared;
	}
	
	public String toString() {
		
		StringBuilder out = new StringBuilder();
		out.append(String.format("%s%s %s(%d)", 
				(shared) ? "shared " : "", type, name, bits));
//		if (alength != 0)
//			out.append(String.format("[%d]", alength));
		
		return out.toString();
	}
}
