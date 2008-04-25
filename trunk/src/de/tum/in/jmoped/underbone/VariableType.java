package de.tum.in.jmoped.underbone;

public enum VariableType {

	BOOLEAN("boolean"),
	INT("int"),
	UINT("unsigned int");
	
	private String type;
	
	VariableType(String type) {
		
		this.type = type;
	}
	
	public String toString() {
		
		return type;
	}
}
