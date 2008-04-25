package de.tum.in.jmoped.underbone;

/**
 * The Remopla variable.
 * 
 * @author suwimont
 *
 */
public class Variable {

	protected VariableType type;
	protected String name;
	private int bits;
	private int alength;
	private int index;
	private int savedIndex;
	private boolean shared;
	
	public Variable(VariableType type, String name) {
		
		this.type = type;
		this.name = name;
	}
	
	public Variable(VariableType type, String name, int bits) {
		
		this.type = type;
		this.name = name;
		this.bits = bits;
	}
	
	public Variable(VariableType type, String name, int bits, boolean shared) {
		
		this.type = type;
		this.name = name;
		this.bits = bits;
		this.shared = shared;
	}
	
	/**
	 * Returns the name of the variable.
	 * 
	 * @return the name of the variable.
	 */
	public String getName() {
		return name;
	}
	
	public int getBits(int defaultBits) {
		
		if (type == VariableType.BOOLEAN) return 1;
		if (bits == 0) return defaultBits;
		return bits;
	}
	
	public int getIndex() {
		
		return index;
	}
	
	public void setIndex(int index) {
		
		this.index = index;
	}
	
	public int getSavedIndex() {
		
		return savedIndex;
	}
	
	public void setSavedIndex(int savedIndex) {
		
		this.savedIndex = savedIndex;
	}
	
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
		if (alength != 0)
			out.append(String.format("[%d]", alength));
		
		return out.toString();
	}
}
