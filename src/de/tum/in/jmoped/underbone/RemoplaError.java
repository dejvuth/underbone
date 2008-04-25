package de.tum.in.jmoped.underbone;

/**
 * Error in Remopla model.
 * 
 * @author suwimont
 *
 */
public class RemoplaError extends Error {

	/**
	 * Default serial id.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructs an error with the <code>message</code>.
	 * 
	 * @param message the error message.
	 * @param args the message arguments.
	 */
	public RemoplaError(String message, Object... args) {
		this(String.format(message, args));
	}

	/**
	 * Constructs an error with the <code>message</code>.
	 * 
	 * @param message the error message.
	 */
	public RemoplaError(String message) {
		super(message);
	}
}
