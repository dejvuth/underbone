package de.tum.in.jmoped.underbone.expr;

import de.tum.in.jmoped.underbone.ExprType;

/**
 * Invoke information.
 * Value for {@link ExprType#INVOKE}.
 */
public class Invoke {
	
	/**
	 * <code>True</code> if the invoked method is static.
	 */
	public boolean isStatic;
	
	/**
	 * Number of arguments
	 */
	public int nargs;
	
	/**
	 * <code>True</code> iff the invoked method is the initial method.
	 */
	public boolean init;
	
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