package de.tum.in.jmoped.underbone.expr;

import java.util.Set;

import de.tum.in.jmoped.underbone.ExprType;

/**
	 * Value for {@link ExprType#RETURN}.
	 */
	public class Return {
		
		public Return.Type type;
		private Object value;
		
		public Return(Return.Type type) {
			this(type, null);
		}
		
		public Return(Return.Type type, Object value) {
			this.type = type;
			this.value = value;
		}
		
		public Category getCategory() {
			return (Category) value;
		}
		
//		public ThrowInfo getThrowInfo() {
//			return (ThrowInfo) value;
//		}
		
		public String toString() {
			if (type == Type.VOID) return "void";
			return getCategory().toString();
		}
		
		public static enum Type {
			VOID, SOMETHING;
		}
		
		public static class ThrowInfo {
			Set<Integer> set;
			String var;
			
			public ThrowInfo(Set<Integer> set, String var) {
				this.set = set;
				this.var = var;
			}
			
			public String toString() {
				return String.format("set: %s var: %s", set, var);
			}
		}
	}