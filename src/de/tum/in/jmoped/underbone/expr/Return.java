package de.tum.in.jmoped.underbone.expr;

import java.util.Set;


/**
 * Return information.
 * 
 * Value for {@link ExprType#RETURN}.
 */
public class Return {
	
	public static final int VOID = 0;
	public static final int SOMETHING = 1;
	
	public int type;
	private Category category;
	
	public Return(int type) {
		this(type, null);
	}
	
	public Return(int type, Category category) {
		this.type = type;
		this.category = category;
	}
	
	public Category getCategory() {
		return category;
	}
	
	public String toString() {
		if (type == VOID) return "void";
		return category.toString();
	}
	
//	public static enum Type {
//		VOID, SOMETHING;
//	}
	
//	public static class ThrowInfo {
//		Set<Integer> set;
//		String var;
//		
//		public ThrowInfo(Set<Integer> set, String var) {
//			this.set = set;
//			this.var = var;
//		}
//		
//		public String toString() {
//			return String.format("set: %s var: %s", set, var);
//		}
//	}
}