package de.tum.in.jmoped.underbone;

import java.util.Arrays;
import java.util.Set;

import de.tum.in.wpds.Semiring;

/**
 * An implementation of Semiring encoding expression types.
 * 
 * @author suwimont
 *
 */
public class ExprSemiring extends NullSemiring {
	
	/**
	 * The type of the expression.
	 */
	public ExprType type;
	
	/**
	 * The value of the expression.
	 */
	public Object value;
	
	/**
	 * The auxiliary value of the expression.
	 */
	public Object aux;
	
	/**
	 * Constructs an expression semiring.
	 * 
	 * @param type the type of the expression.
	 */
	public ExprSemiring(ExprType type) {
		
		this(type, null, null);
	}
	
	/**
	 * Constructs an expression semiring.
	 * The meaning of <code>value</code> depends on the <code>type</code>
	 * of the expression.
	 * 
	 * @param type the type of the expression.
	 * @param value the value of the expression.
	 */
	public ExprSemiring(ExprType type, Object value) {
		
		this(type, value, null);
	}
	
	/**
	 * Constructs an expression semiring.
	 * The meaning of <code>value</code> and <code>aux</code>
	 * depends on the <code>type</code> of the expression.
	 * 
	 * @param type the type of the expression.
	 * @param value the value of the expression.
	 * @param aux the auxiliary value of the expression.
	 */
	public ExprSemiring(ExprType type, Object value, Object aux) {
		
		this.type = type;
		this.value = value;
		this.aux = aux;
	}
	
	/**
	 * Returns the string representation of this expression.
	 * 
	 * @return the string representation of this expression.
	 */
	public String toString() {
		
		StringBuilder out = new StringBuilder(type.toString());
		if (value != null) out.append(" ").append(value.toString());
		if (aux != null) out.append(" ").append(aux.toString());
		
		return out.toString();
	}

	public Semiring id() {
		
		return new ExprSemiring(type, value, aux);
	}
	
	/**
	 * The arithmetic types.
	 * 
	 * @author suwimont
	 *
	 */
	public enum ArithType {
		ADD, AND, CMP, DIV, MUL, OR, REM, SHL, SHR, SUB, USHR, XOR,
		FADD, FCMPG, FCMPL, FDIV, FMUL, FREM, FSUB
	}
	
	public static enum CompType {
		EQ("=="), NE("!="), LT("<"), GE(">="), GT(">"), LE("<=");
		
		String name;
		CompType(String name) {
			this.name = name;
		}
		
		public String getName() {
			return name;
		}
	}
	
	/**
	 * Conditions that must be fulfilled during extend.
	 * 
	 * @author suwimont
	 *
	 */
	public static class Condition {
		
		/**
		 * The condition type.
		 */
		ConditionType type;
		
		/**
		 * The value.
		 */
		Object value;
		
		/**
		 * The constructor.
		 * 
		 * @param type the condition type.
		 * @param value the value.
		 */
		public Condition(ConditionType type, Object value) {
			switch (type) {
			case ZERO:
			case ONE:
				if (!(value instanceof String))
					throw new IllegalArgumentException("Argument of type String expected");
				break;
			case CONTAINS:
				if (!(value instanceof Set))
					throw new IllegalArgumentException("Argument of type Set expected");
				break;
			}
			this.type = type;
			this.value = value;
		}
		
		/**
		 * Returns the string representing this condition.
		 * 
		 * @return the string representing this condition.
		 */
		public String toString() {
			return String.format("%s %s", type, value);
		}
		
		/**
		 * Types of conditions that must be fulfilled during extend.
		 * 
		 * @author suwimont
		 *
		 */
		public static enum ConditionType {
			
			/**
			 * The field <code>value</code> is a global variable name.
			 * The condition is fulfilled if the variable is equal to zero.
			 */
			ZERO,
			
			/**
			 * The field <code>value</code> is a global variable name.
			 * The condition is fulfilled if the variable is equal to one.
			 */
			ONE, 
			
			/**
			 * The field <code>value</code> is a set of integers (Set<Integer>)
			 * The condition is fulfilled if the class id is contained in
			 * the set. Note that the class id is obtained from the heap
			 * where the stack representing the first argument points to.
			 */
			CONTAINS;
		}
	}
	
	public static enum DupType {
		DUP, DUP_X1, DUP_X2, DUP2, DUP2_X1, DUP2_X2;
	}
	
	public static class If {
		
		Type type;
		Object value;
		int high;
		
		public If(CompType type) {
			switch (type) {
			case EQ:	this.type = Type.EQ; break;
			case GE:	this.type = Type.GE; break;
			case GT:	this.type = Type.GT; break;
			case LE:	this.type = Type.LE; break;
			case LT:	this.type = Type.LT; break;
			case NE:	this.type = Type.NE; break;
			}
		}
		
		public If(int value) {
			this.type = Type.IS;
			this.value = value;
		}
		
		public If(int low, int high) {
			this.type = Type.LG;
			this.value = low;
			this.high = high;
		}
		
		public If(Set<Integer> value) {
			this.type = Type.NOT;
			this.value = value;
		}
		
		public boolean isStandard() {
			return value == null;
		}
		
		public int getValue() {
			return (Integer) value;
		}
		
		public int getLowValue() {
			return (Integer) value;
		}
		
		public int getHighValue() {
			return high;
		}
		
		@SuppressWarnings("unchecked")
		public Set<Integer> getNotSet() {
			return (Set<Integer>) value;
		}
		
		public String toString() {
			StringBuilder out = new StringBuilder(type.toString());
			out.append(" ");
			out.append(value);
			if (type == Type.LG) {
				out.append(" ").append(high);
			}
			
			return out.toString();
		}
		
		public static enum Type {
			EQ, NE, LT, GE, GT, LE, IS, LG, NOT
		}
	}
	
	public static class Inc {
		
		int index;
		int value;
		
		public Inc(int index, int value) {
			this.index = index;
			this.value = value;
		}
		
		public String toString() {
			return index + " by " + value;
		}
	}
	
	public static class Invoke {
		
		boolean isStatic;
		
		/**
		 * The number of arguments.
		 */
		boolean[] params;
		
		/**
		 * <code>True</code> iff the invoked method is the initial method.
		 */
		boolean init;
		
		public Invoke() {
			this(true, new boolean[0]);
		}
		
		public Invoke(boolean isStatic, boolean[] params) {
			this(isStatic, params, false);
		}
		
		public Invoke(boolean isStatic, boolean[] params, boolean init) {
			this.isStatic = isStatic;
			this.params = params;
			this.init = init;
		}
		
		public String toString() {
			StringBuilder out = new StringBuilder();
			
			out.append(Arrays.toString(params));
			
			if (init) out.append(" init");
			return out.toString();
		}
	}
	
	public static class Monitorenter {
		
		Monitorenter.Type type;
		Object value;
		
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
	
	/**
	 * Value for {@link ExprType#NEW}.
	 * 
	 * @author suwimont
	 *
	 */
	public static class New {
		
		int id;
		int size;
		
		public New(int id, int size) {
			this.id = id;
			this.size = size;
		}
		
		public String toString() {
			return String.format("id:%d size:%d", id, size);
		}
	}
	
	/**
	 * Value for {@link ExprType#NEWARRAY}.
	 * 
	 * @author suwimont
	 *
	 */
	public static class Newarray {
		
		Value init;
		int dim;
		int[] types;
		
		public Newarray() {
			this(new Value(0));
		}
		
		public Newarray(int dim) {
			this(new Value(0), dim);
		}
		
		/**
		 * One-dimensional array initialized with the value specified by 
		 * <code>init</code>
		 * 
		 * @param init the initial value of all array elements.
		 */
		public Newarray(Value init) {
			this(init, 1);
		}
		
		public Newarray(Value init, int dim) {
			this(init, dim, new int[] { 0 });
		}
		
		public Newarray(Value init, int dim, int[] types) {
			this.init = init;
			this.dim = dim;
			this.types = types;
		}
		
		public void setType(int[] types) {
			this.types = types;
		}
		
		public String toString() {
			return String.format("value: %s, dim: %d, type: %s", 
					init.toString(), dim, Arrays.toString(types));
		}
	}
	
	public static enum NotifyType {
		NOTIFY, NOTIFYALL;
	}
	
	public static class Npe {
		
		/**
		 * Indicates the position of objectref in the operand stack.
		 * For example, 0 means s0, 1 means s1.
		 */
		int depth;
		
		public Npe(int depth) {
			this.depth = depth;
		}
		
		public String toString() {
			return String.valueOf(depth);
		}
	}
	
	/**
	 * Used in PRINT
	 * 
	 * @author suwimont
	 *
	 */
	public static class Print {
		
		Type type;
		boolean newline;
		
		public Print(Type type, boolean newline) {
			this.type = type;
			this.newline = newline;
		}
		
		public String toString() {
			return type + " " + newline;
		}
		
		public static enum Type {
			INTEGER, FLOAT, CHARACTER, STRING
		}
	}
	
	public static class Stub {
		
		String className;
		String methodName;
		String methodDesc;
		
		public String toString() {
			return className + "." + methodName + methodDesc;
		}
	}
	
	/**
	 * Used in PUSH and NEWARRAY.
	 * 
	 * @author suwimont
	 *
	 */
	public static class Value {
		
		private Object value;
		Number next;
		Number to;
		
		/**
		 * Creates a nondeterministic value.
		 */
		public Value() {
			value = null;
		}
		
		public Value(Number value) {
			this(value, null, null);
		}
		
		public Value(Number value, Number next, Number to) {
			
			this.value = value;
			this.next = next;
			this.to = to;
		}
		
		public Value(String value) {
			this.value = value;
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
		
//		public Number numberValue() {
//			if (isString()) throw new RemoplaError("value is a string");
//			return (Number) value;
//		}
		
		public Object getValue() {
			return value;
		}
		
		public int intValue() {
			if (!isInteger()) 
				throw new RemoplaError("value is not an integer");
			return ((Number) value).intValue();
		}
		
		public float floatValue() {
			if (!isReal()) 
				throw new RemoplaError("value is not a real number");
			return ((Number) value).floatValue();
		}
		
		public String stringValue() {
			if (!isString())
				throw new RemoplaError("value is not a String");
			return (String) value;
		}
		
		/**
		 * Returns <code>true</code> if push all values.
		 * 
		 * @return <code>true</code> if push all values.
		 */
		public boolean all() {
			return value == null;
		}
		
		public boolean deterministic() {
			return value != null && next == null && to == null;
		}
		
		public String toString() {
			if (value == null) return "all";
			if (next == null) return value.toString();
			return String.format("[%s, %s, ..., %s]", value, next, to);
		}
	}
	
	public static enum UnaryOpType {
		NEG, FNEG, F2I, I2F
	}
}
