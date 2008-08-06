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
		FADD, FCMPG, FCMPL, FDIV, FMUL, FREM, FSUB, NDT;
	}
	
	/**
	 * The category types.
	 * 
	 * @author suwimont
	 *
	 */
	public enum CategoryType {
		ZERO(0), ONE(1), TWO(2);
		
		int category;
		CategoryType(int category) {
			this.category = category;
		}
		
		public int intValue() {
			return category;
		}
		
		public boolean one() {
			return category == 1;
		}
		
		public boolean two() {
			return category == 2;
		}
		
		public String toString() {
			return String.format("category:%d", category);
		}
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
			case NOTCONTAINS:
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
			CONTAINS,
			
			/**
			 * Opposite to CONTAINS.
			 */
			NOTCONTAINS;
		}
	}
	
	/**
	 * Value for {@link ExprType#DUP}.
	 */
	public static enum DupType {
		DUP(1, 1), DUP_X1(2, 1), DUP_X2(3, 1), DUP2(2, 2), DUP2_X1(3, 2), DUP2_X2(4, 2);
		
		int down;
		int push;
		DupType(int down, int push) {
			this.down = down;
			this.push = push;
		}
	}
	
	/**
	 * Field information.
	 * Value for {@link ExprType#GLOBALLOAD}, {@link ExprType#GLOBALSTORE},
	 * {@link ExprType#FIELDLOAD}, {@link ExprType#FIELDSTORE}.
	 *
	 */
	public static class Field {
		
		/**
		 * Category 1 or 2
		 */
		CategoryType category;
		
		/**
		 * Id or offset of this field
		 */
		int id;
		
		/**
		 * Name of this field.
		 */
		String name;
		
		/**
		 * Constructs a static field information.
		 * 
		 * @param category the field category.
		 * @param name the field name.
		 */
		public Field(CategoryType category, String name) {
			this.category = category;
			this.name = name;
		}
		
		/**
		 * Constructs an instance field information.
		 * 
		 * @param category the field category.
		 * @param id the field id.
		 */
		public Field(CategoryType category, int id) {
			this.category = category;
			this.id = id;
		}
		
		/**
		 * Returns <code>true</code> if this field type is of category 2.
		 * 
		 * @return <code>true</code> if this field type is of category 2.
		 */
		public boolean categoryTwo() {
			return category.two();
		}
		
		/**
		 * Returns the string representation of this field information.
		 * 
		 * @return the string representation of this field information.
		 */
		public String toString() {
			return String.format("%s, id: %d, name: %s", category, id, name);
		}
	}
	
	public static class If {
		
		Type type;
		Object value;
		int high;
		
		/**
		 * Comparison with zero.
		 * 
		 * @param type the comparison type.
		 */
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
		
		/**
		 * Determines equality with the given value.
		 * 
		 * @param value the value.
		 */
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
	
	/**
	 * Invoke information.
	 */
	public static class Invoke {
		
		/**
		 * <code>True</code> if the invoked method is static.
		 */
		boolean isStatic;
		
		/**
		 * Number of arguments
		 */
		int nargs;
		
		/**
		 * <code>True</code> iff the invoked method is the initial method.
		 */
		boolean init;
		
		public Invoke() {
			this(true, 0);
		}
		
		public Invoke(boolean isStatic, int nargs) {
			this(isStatic, nargs, false);
		}
		
		public Invoke(boolean isStatic, int nargs, boolean init) {
			this.isStatic = isStatic;
			this.nargs = nargs;
			this.init = init;
		}
		
		public String toString() {
			StringBuilder out = new StringBuilder();
			
			out.append(String.format("nargs:%d", nargs));
			
			if (init) out.append(" init");
			return out.toString();
		}
	}
	
	public static enum JumpType {
		ONE, THROW;
	}
	
	/**
	 * Value for {@link ExprType#LOAD} and {@link ExprType#STORE}.
	 */
	public static class Local {
		
		/**
		 * Category 1 or 2
		 */
		CategoryType category;
		
		/**
		 * The index
		 */
		int index;
		
		/**
		 * Constructs a local variable information.
		 * 
		 * @param category the category.
		 * @param index the local variable index.
		 */
		public Local(CategoryType category, int index) {
			this.category = category;
			this.index = index;
		}
		
		public String toString() {
			return String.format("%s index:%d", category, index);
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
		
		/**
		 * One-dimensional array initialized with zero
		 */
		public Newarray() {
			this(new Value(CategoryType.ONE, 0));
		}
		/**
		 * Zero array with the dimensions specified by <code>dim</code>.
		 * 
		 * @param dim the dimensions.
		 */
		public Newarray(int dim) {
			this(new Value(CategoryType.ONE, 0), dim);
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
			return String.format("%s dim: %d type: %s", 
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
	 * Value for {@link ExprType#POPPUSH}.
	 */
	public static class Poppush {
		
		int pop;
		int push;
		
		public Poppush(int pop, int push) {
			this.pop = pop;
			this.push = push;
		}
		
		public boolean nochange() {
			return pop == 0 && push == 0;
		}
		
		public boolean push() {
			return push > 0;
		}
		
		public String toString() {
			return String.format("pop:%d, push:%d", pop, push);
		}
	}
	
	/**
	 * Value for {@link ExprType#PRINT}.
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
	
	/**
	 * Value for {@link ExprType#RETURN}.
	 */
	public static class Return {
		
		Type type;
		private Object value;
		
		public Return(Type type) {
			this(type, null);
		}
		
		public Return(Type type, Object value) {
			this.type = type;
			this.value = value;
		}
		
		public CategoryType getCategory() {
			return (CategoryType) value;
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
	
	public static class Stub {
		
		String className;
		String methodName;
		String methodDesc;
		
		public String toString() {
			return className + "." + methodName + methodDesc;
		}
	}
	
	/**
	 * Value for {@link ExprType#PUSH}
	 * and argument of {@link Newarray}.
	 * 
	 * @author suwimont
	 *
	 */
	public static class Value {
		
		/**
		 * Category 1 or 2
		 */
		CategoryType category;
		
		private Object value;
		Number next;
		Number to;
		
		/**
		 * Creates a nondeterministic value.
		 */
		public Value(CategoryType category) {
			this.category = category;
			value = null;
		}
		
		/**
		 * Creates a deterministic value.
		 * 
		 * @param value the value.
		 */
		public Value(CategoryType category, Number value) {
			this(category, value, null, null);
		}
		
		/**
		 * Creates a nondeterministic value [<code>from</code>,<code>to</code>].
		 * 
		 * @param from min value.
		 * @param next ignored.
		 * @param to max value.
		 */
		public Value(CategoryType category, Number from, Number next, Number to) {
			this.category = category;
			this.value = from;
			this.next = next;
			this.to = to;
		}
		
		public Value(CategoryType category, String value) {
			this.category = category;
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
			if (value == null) return String.format("%s value:all", category);
			if (next == null) return String.format("%s value:%s", category, value.toString());
			return String.format("%s value:[%s, %s, ..., %s]", category, value, next, to);
		}
	}
	
	/**
	 * Value for {@link ExprType#UNARYOP}.
	 */
	public static class Unaryop {
		
		/**
		 * Operation type.
		 */
		Type type;
		
		Set<Integer> set;
		
		public Unaryop(Type type) {
			this.type = type;
		}
		
		public Unaryop(Type type, Set<Integer> set) {
			if (type != Type.CONTAINS)
				throw new RemoplaError("Internal error: " +
						"A Unary operation of type CONTAINS expected");
			if (set == null || set.isEmpty())
				throw new RemoplaError("Internal error: " +
						"A set of integers expected");
			this.type = type;
			this.set = set;
		}
		
		public String toString() {
			if (set == null) return type.toString();
			return String.format("%s %s", type, set);
		}
		
		/**
		 * Unary operation type: negation and type conversion.
		 */
		public static enum Type {
			
			DNEG(CategoryType.TWO, CategoryType.TWO),
			
			/**
			 * Negates float
			 */
			FNEG(CategoryType.ONE, CategoryType.ONE),
			
			/**
			 * Negates
			 */
			INEG(CategoryType.ONE, CategoryType.ONE),
			
			LNEG(CategoryType.TWO, CategoryType.TWO),
			
			D2F(CategoryType.TWO, CategoryType.ONE),
			D2I(CategoryType.TWO, CategoryType.ONE),
			D2L(CategoryType.TWO, CategoryType.TWO),
			
			F2D(CategoryType.ONE, CategoryType.TWO),
			
			/**
			 * Converts float to int
			 */
			F2I(CategoryType.ONE, CategoryType.ONE),
			
			F2L(CategoryType.ONE, CategoryType.TWO),
			
			I2D(CategoryType.ONE, CategoryType.TWO),
			
			/**
			 * Converts int to float
			 */
			I2F(CategoryType.ONE, CategoryType.ONE),
			
			I2L(CategoryType.ONE, CategoryType.TWO),
			
			L2D(CategoryType.TWO, CategoryType.TWO),
			
			L2F(CategoryType.TWO, CategoryType.ONE),
			
			L2I(CategoryType.TWO, CategoryType.ONE),
			
			/**
			 * Pushes one the set in <code>aux</code> contains the top-of-stack;
			 * or zero otherwise.
			 */
			CONTAINS(CategoryType.ONE, CategoryType.ONE);
			
			CategoryType pop;
			CategoryType push;
			
			Type(CategoryType pop, CategoryType push) {
				this.pop = pop;
				this.push = push;
			}
		}
	}
	

}
