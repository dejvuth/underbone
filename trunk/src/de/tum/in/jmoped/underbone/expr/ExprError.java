package de.tum.in.jmoped.underbone.expr;

public class ExprError extends Error {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructs an error with the <code>message</code>.
	 * 
	 * @param message the error message.
	 * @param args the message arguments.
	 */
	public ExprError(String message, Object... args) {
		this(String.format(message, args));
	}

	/**
	 * Constructs an error with the <code>message</code>.
	 * 
	 * @param message the error message.
	 */
	public ExprError(String message) {
		super(message);
	}
}
