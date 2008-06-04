package de.tum.in.jmoped.underbone;

/**
 * The expression type. Use in {@link ExprSemiring}.
 * 
 * @author suwimont
 *
 */
public enum ExprType {

	/**
	 * Performs arithmetic.
	 * The field <code>value</code> is of type {@link ExprSemiring.ArithType}.
	 * The field <code>aux</code> is of type {@link ExprSemiring.CategoryType}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., value1, value2 -&gt; ..., result
	 * </pre>
	 */
	ARITH,
	
	/**
	 * Loads arary length
	 * 
	 * Operand stack:
	 * 		..., arrayref -&gt; ..., length
	 */
	ARRAYLENGTH,
	
	/**
	 * Loads from array.
	 * The field <code>value</code> is of type {@link ExprSemiring.CategoryType}.
	 * 
	 * <pre>
	 * Operand Stack:
	 * 		..., arrayref, index -> ..., value
	 * </pre>
	 */
	ARRAYLOAD,
	
	/**
	 * Stores into array.
	 * The field <code>value</code> is of type {@link ExprSemiring.CategoryType}.
	 * 
	 * <pre>
	 * Operand Stack:
	 * 		..., arrayref, index, value -> ...
	 * </pre>
	 */
	ARRAYSTORE,
	
	/**
	 * Pushes the constant from static field.
	 * The field <code>value</code> is of type {@link ExprSemiring.Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., -> ..., value
	 * </pre>
	 */
	CONSTLOAD,
	
	/**
	 * Pops and stores constant to static field.
	 * The field <code>value</code> is of type {@link ExprSemiring.Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., value -> ...,
	 * </pre>
	 */
	CONSTSTORE,
	
	/**
	 * Duplicates the stack.
	 * The field <code>value</code> is of type {@link ExprSemiring.DupType}.
	 */
	DUP,
	
	/**
	 * Indicates the dynamic rule.
	 */
	DYNAMIC,
	
	/**
	 * This special expression type is used in error rules.
	 * Its behavior is application-specific.
	 * For virtual machine: the execution will return to an initial state
	 * for beginning the next execution.
	 * For BDD: it is considered as an identity function, i.e. just like ONE.
	 */
	ERROR,
	
	/**
	 * Pushes the field of the instance specified by the top-of-stack.
	 * The field <code>value</code> is of type {@link ExprSemiring.Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., objectref -> ..., value
	 * </pre>
	 */
	FIELDLOAD,
	
	/**
	 * Pops to the field of the instance specified by the second top-of-stack.
	 * The field <code>value</code> is of type {@link ExprSemiring.Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., objectref, value -> ...,
	 * </pre>
	 */
	FIELDSTORE,
	
	/**
	 * Pushes the return value.
	 * The field <code>value</code> is of type {@link ExprSemiring.CategoryType}.
	 */
	GETRETURN,
	
	/**
	 * Pushes global variable into the stack.
	 * The field <code>value</code> is of type {@link ExprSemiring.Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., -> ..., value
	 * </pre>
	 */
	GLOBALLOAD,
	
	/**
	 * Stores constant into global variable.
	 * The field <code>value</code> determines the global variable name.
	 * The field <code>aux</code> determines the constant.
	 */
	GLOBALPUSH,
	
	/**
	 * Pops to global variable.
	 * The field <code>value</code> is of type {@link ExprSemiring.Field}.
	 * 
	 * <pre>
	 * Operand stack:
	 * 		..., value -> ...,
	 * </pre>
	 */
	GLOBALSTORE,
	
	/**
	 * Pushes heap element pointed by the top-of-stack.
	 */
	HEAPLOAD,
	
	/**
	 * Checks for heap overflow.
	 * The field <code>value</code> is again of type ExprType: 
	 * either {@link #NEW} or {@link #NEWARRAY}.
	 * The field <code>aux</code> corresponds to the field <code>value</code>,
	 * i.e. either {@link ExprSemiring.New} or {@link ExprSemiring.Newarray}.
	 */
	HEAPOVERFLOW,
	
	/**
	 * Resets the heap elements to zero.
	 * For virtual machine only.
	 */
	HEAPRESET,
	
	/**
	 * Loads the heap to the last-saved state.
	 * For virtual machine only.
	 */
	HEAPRESTORE,
	
	/**
	 * Saves the current state of the heap.
	 * For virtual machine only.
	 */
	HEAPSAVE,
	
	/**
	 * Compares the top-of-stack with zero.
	 */
	IF,
	
	/**
	 * Compares the two top elements on the stack.
	 * The field <code>value</code> is of type {@link ExprSemiring.CompType}.
	 */
	IFCMP,
	
	/**
	 * Increments a local variable.
	 */
	INC,
	
	/**
	 * Invokes a module.
	 */
	INVOKE,
	
	/**
	 * Checks for index-out-of-bound exception.
	 */
	IOOB,
	
	/**
	 * Pushes from a local variable.
	 * The field <code>value</code> is of type {@link ExprSemiring.Local}.
	 */
	LOAD,
	
	/**
	 * Locks.
	 */
	MONITORENTER,
	
	/**
	 * Release the lock.
	 */
	MONITOREXIT,
	
	/**
	 * Creates a new object.
	 */
	NEW,
	
	/**
	 * Creates a new array.
	 * The field <code>value</code> is of type {@link ExprSemiring.Newarray}.
	 */
	NEWARRAY,
	
	/**
	 * Notifies waiting threads.
	 */
	NOTIFY,
	
	/**
	 * Checks for null-pointer exception.
	 */
	NPE,
	
	/**
	 * Changes nothing.
	 */
	ONE,
	
	/**
	 * Pops the stack <code>value</code> times, 
	 * and pushes iff <code>aux</code> is <code>true</code>.
	 * The virtual machine always pushes zero.
	 */
	POPPUSH,
	
	/**
	 * Prints.
	 */
	PRINT,
	
	/**
	 * Pushes a constant.
	 * The field <code>value</code> is of type {@link ExprSemiring.Value}.
	 */
	PUSH,
	
	/**
	 * Returns from a module.
	 * The field <code>value</code> is of type {@link ExprSemiring.Return}
	 */
	RETURN,
	
	/**
	 * Pops and stores in a local variable.
	 * The field <code>value</code> is of type {@link ExprSemiring.Local}.
	 */
	STORE,
	
	/**
	 * Performs unary operation.
	 * The field <code>value</code> is of type {@link ExprSemiring.UnaryOpType}.
	 */
	UNARYOP,
	
	/**
	 * Swaps the top two operand stack values.
	 */
	SWAP,
	
	/**
	 * Waits.
	 */
	WAITINVOKE,
	
	/**
	 * Returns from waiting.
	 */
	WAITRETURN;
}
