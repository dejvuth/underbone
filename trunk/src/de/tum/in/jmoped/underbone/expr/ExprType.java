package de.tum.in.jmoped.underbone.expr;

import de.tum.in.jmoped.underbone.RemoplaError;

/**
 * The expression type. Use in {@link ExprSemiring}.
 * 
 * History: this class is not implemented as an enum because
 * enum consumes much more memory which makes it not suitable
 * for testing with jMoped.
 * 
 * @author suwimont
 *
 */
public class ExprType {

	/**
	 * Performs arithmetic.
	 * The field <code>value</code> is of type {@link Arith}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., value1, value2 -&gt; ..., result
	 * </pre>
	 */
	public static final int ARITH = 0;
	
	/**
	 * Loads arary length.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., arrayref -&gt; ..., length
	 * </pre>
	 */
	public static final int ARRAYLENGTH = 1;
	
	/**
	 * Loads from array.
	 * The field <code>value</code> is of type {@link Category}.
	 * 
	 * <pre>
	 * Operand Stack:
	 * 		..., arrayref, index -&gt; ..., value
	 * </pre>
	 */
	public static final int ARRAYLOAD = 2;
	
	/**
	 * Stores into array.
	 * The field <code>value</code> is of type {@link Category}.
	 * 
	 * <pre>
	 * Operand Stack:
	 * 		..., arrayref, index, value -&gt; ...
	 * </pre>
	 */
	public static final int ARRAYSTORE = 3;
	
	/**
	 * Pushes the constant from static field.
	 * The field <code>value</code> is of type {@link Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		... -&gt; ..., value
	 * </pre>
	 */
	public static final int CONSTLOAD = 4;
	
	/**
	 * Pops and stores constant to static field.
	 * The field <code>value</code> is of type {@link Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., value -&gt; ...
	 * </pre>
	 */
	public static final int CONSTSTORE = 5;
	
	/**
	 * Duplicates the stack.
	 * The field <code>value</code> is of type {@link Dup}.
	 */
	public static final int DUP = 6;
	
	/**
	 * Indicates the dynamic rule.
	 */
	public static final int DYNAMIC = 7;
	
	/**
	 * This special expression type is used in error rules.
	 * Its behavior is application-specific.
	 * For virtual machine: the execution will return to an initial state
	 * for beginning the next execution.
	 * For BDD: it is considered as an identity function, i.e. just like ONE.
	 */
	public static final int ERROR = 8;
	
	/**
	 * Pushes the field of the instance specified by the top-of-stack.
	 * The field <code>value</code> is of type {@link Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., objectref -&gt; ..., value
	 * </pre>
	 */
	public static final int FIELDLOAD = 9;
	
	/**
	 * Pops to the field of the instance specified by the second top-of-stack.
	 * The field <code>value</code> is of type {@link Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., objectref, value -&gt; ...,
	 * </pre>
	 */
	public static final int FIELDSTORE = 10;
	
	/**
	 * Pushes the return value.
	 * The field <code>value</code> is of type {@link Category}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		... -&gt; ..., value
	 * </pre>
	 */
	public static final int GETRETURN = 11;
	
	/**
	 * Pushes global variable into the stack.
	 * The field <code>value</code> is of type {@link Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		... -&gt; ..., value
	 * </pre>
	 */
	public static final int GLOBALLOAD = 12;
	
//	/**
//	 * Stores constant into global variable.
//	 * The field <code>value</code> is of type {@link Field}.
//	 * The field <code>aux</code> determines the constant.
//	 */
//	public static final int GLOBALPUSH = 13;
	
	/**
	 * Pops to global variable.
	 * The field <code>value</code> is of type {@link Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., value -&gt; ...,
	 * </pre>
	 */
	public static final int GLOBALSTORE = 14;
	
//	/**
//	 * Pushes heap element pointed by the top-of-stack.
//	 */
//	public static final int HEAPLOAD = 15;
	
	/**
	 * Checks for heap overflow.
	 * The field <code>value</code> is again of type ExprType: 
	 * either {@link #NEW} or {@link #NEWARRAY}.
	 * The field <code>aux</code> corresponds to the field <code>value</code>,
	 * i.e. either {@link New} or {@link Newarray}.
	 */
	public static final int HEAPOVERFLOW = 16;
	
	/**
	 * Resets the heap elements to zero.
	 * For virtual machine only.
	 */
	public static final int HEAPRESET = 17;
	
	/**
	 * Loads the heap to the last-saved state.
	 * For virtual machine only.
	 */
	public static final int HEAPRESTORE = 18;
	
	/**
	 * Saves the current state of the heap.
	 * For virtual machine only.
	 */
	public static final int HEAPSAVE = 19;
	
	/**
	 * Compares the top-of-stack with a constant.
	 * The field <code>value</code> is of type {@link If}.
	 */
	public static final int IF = 20;
	
	/**
	 * Compares the two top elements on the stack.
	 * The field <code>value</code> is of type Integer with the meaning
	 * defined in {@link Comp}.
	 */
	public static final int IFCMP = 21;
	
	/**
	 * Increments a local variable.
	 */
	public static final int INC = 22;
	
	/**
	 * Invokes a module.
	 * The field <code>value</code> is of type {@link Invoke}.
	 */
	public static final int INVOKE = 23;
	
	/**
	 * Checks for index-out-of-bound exception.
	 */
	public static final int IOOB = 24;
	
	/**
	 * Pushes from a local variable.
	 * The field <code>value</code> is of type {@link Local}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		... -&gt; ..., value
	 * </pre>
	 */
	public static final int LOAD = 25;
	
	/**
	 * Locks.
	 */
	public static final int MONITORENTER = 26;
	
	/**
	 * Release the lock.
	 */
	public static final int MONITOREXIT = 27;
	
	/**
	 * Creates a new object.
	 */
	public static final int NEW = 28;
	
	/**
	 * Creates a new array.
	 * The field <code>value</code> is of type {@link Newarray}.
	 */
	public static final int NEWARRAY = 29;
	
	/**
	 * Notifies waiting threads.
	 */
	public static final int NOTIFY = 30;
	
	/**
	 * Checks for null-pointer exception.
	 */
	public static final int NPE = 31;
	
	/**
	 * Jumps.
	 * The field <code>value</code> is of type {@link Jump}.
	 * The field <code>aux</code> is of type {@link Condition}.
	 */
	public static final int JUMP = 32;
	
	/**
	 * Pops and pushes the stack.
	 * The field <code>value</code> is of type {@link Poppush}.
	 * The virtual machine always pushes zero.
	 */
	public static final int POPPUSH = 33;
	
	/**
	 * Prints.
	 */
	public static final int PRINT = 34;
	
	/**
	 * Pushes a constant.
	 * The field <code>value</code> is of type {@link Value}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		... -&gt; ..., value
	 * </pre>
	 */
	public static final int PUSH = 35;
	
	/**
	 * Returns from a module.
	 * The field <code>value</code> is of type {@link Return}.
	 */
	public static final int RETURN = 36;
	
	/**
	 * Pops and stores in a local variable.
	 * The field <code>value</code> is of type {@link Local}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., value -&gt; ...
	 * </pre>
	 */
	public static final int STORE = 37;
	
	/**
	 * Performs unary operation.
	 * The field <code>value</code> is of type {@link Unaryop}.
	 */
	public static final int UNARYOP = 38;
	
	/**
	 * Swaps the top two operand stack values.
	 */
	public static final int SWAP = 39;
	
	/**
	 * Waits.
	 */
	public static final int WAITINVOKE = 40;
	
	/**
	 * Returns from waiting.
	 */
	public static final int WAITRETURN = 41;
	
	public static String toString(int type) {
		switch (type) {
		case ARITH: return "ARITH";
		case ARRAYLENGTH: return "ARRAYLENGTH";
		case ARRAYLOAD: return "ARRAYLOAD";
		case ARRAYSTORE: return "ARRAYSTORE";
		case CONSTLOAD: return "CONSTLOAD";
		case CONSTSTORE: return "CONSTSTORE";
		case DUP: return "DUP";
		case DYNAMIC: return "DYNAMIC";
		case ERROR: return "ERROR";
		case FIELDLOAD: return "FIELDLOAD";
		case FIELDSTORE: return "FIELDSTORE";
		case GETRETURN: return "GETRETURN";
		case GLOBALLOAD: return "GLOBALLOAD";
//		case GLOBALPUSH: return "GLOBALPUSH";
		case GLOBALSTORE: return "GLOBALSTORE";
//		case HEAPLOAD: return "HEAPLOAD";
		case HEAPOVERFLOW: return "HEAPOVERFLOW";
		case HEAPRESET: return "HEAPRESET";
		case HEAPRESTORE: return "HEAPRESTORE";
		case HEAPSAVE: return "HEAPSAVE";
		case IF: return "IF";
		case IFCMP: return "IFCMP";
		case INC: return "INC";
		case INVOKE: return "INVOKE";
		case IOOB: return "IOOB";
		case JUMP: return "JUMP";
		case LOAD: return "LOAD";
		case MONITORENTER: return "MONITORENTER";
		case MONITOREXIT: return "MONITOREXIT";
		case NEW: return "NEW";
		case NEWARRAY: return "NEWARRAY";
		case NOTIFY: return "NOTIFY";
		case NPE: return "NPE";
		case POPPUSH: return "POPPUSH";
		case PRINT: return "PRINT";
		case PUSH: return "PUSH";
		case RETURN: return "RETURN";
		case STORE: return "STORE";
		case SWAP: return "SWAP";
		case UNARYOP: return "UNARYOP";
		case WAITINVOKE: return "WAITNVOKE";
		case WAITRETURN: return "WAITRETURN";
		}
		
		throw new RemoplaError("Unknown expression type: %d", type);
	}
}
