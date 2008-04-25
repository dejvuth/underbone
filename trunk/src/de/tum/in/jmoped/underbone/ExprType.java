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
	 * 
	 * Operand stack:
	 * 		..., value1, value2 -&gt; ..., result
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
	 * Loads from array
	 * 
	 * Operand Stack:
	 * 		..., arrayref, index -> ..., value
	 */
	ARRAYLOAD,
	
	/**
	 * Stores into array
	 * 
	 * Operand Stack:
	 * 		..., arrayref, index, value -> ...
	 */
	ARRAYSTORE,
	
	/**
	 * Pushes the constant specified by the field <code>value</code>.
	 * 
	 * Operand stack:
	 * 		..., -> ..., value
	 */
	CONSTLOAD,
	
	/**
	 * Pops and stores to the constant specified by the field <code>value</code>.
	 * 
	 * Operand stack:
	 * 		..., value -> ...,
	 */
	CONSTSTORE,
	
	/**
	 * Duplicates the stack.
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
	 * The field <code>value</code> determines the field id.
	 * 
	 * Operand stack:
	 * 		..., objectref -> ..., value
	 */
	FIELDLOAD,
	
	/**
	 * Pops to the field of the instance specified by the second top-of-stack.
	 * The field <code>value</code> determines the field id.
	 * 
	 * Operand stack:
	 * 		..., objectref, value -> ...,
	 */
	FIELDSTORE,
	
	/**
	 * Pushes the return value.
	 */
	GETRETURN,
	
	/**
	 * Pushes global variable into the stack.
	 * The field <code>value</code> determines the global variable name.
	 * 
	 * Operand stack:
	 * 		..., -> ..., value
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
	 * The field <code>value</code> determines the global variable name.
	 * 
	 * Operand stack:
	 * 		..., value -> ...,
	 */
	GLOBALSTORE,
	
	/**
	 * Pushes heap element pointed by the top-of-stack.
	 */
	HEAPLOAD,
	
	/**
	 * Checks for heap overflow.
	 * The field <code>value</code> is again of type ExprType: 
	 * either {@link #NEW} or {@link NEWARRAY}.
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
	 */
	PUSH,
	
	/**
	 * Returns from a module.
	 */
	RETURN,
	
	/**
	 * Pops and stores in a local variable.
	 */
	STORE,
	
	/**
	 * Performs unary operation.
	 */
	UNARYOP,
	
	/**
	 * Waits.
	 */
	WAITINVOKE,
	
	/**
	 * Returns from waiting.
	 */
	WAITRETURN;
}
