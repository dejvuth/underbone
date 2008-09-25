package de.tum.in.jmoped.underbone.expr;


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
	
	public int hashCode() {
		int hash = 31*7 + ((isStatic) ? 1 : 0);
		hash = 31*hash + nargs;
		hash = 31*hash + ((init) ? 1 : 0);
		return hash;
	}
	
	public boolean equals(Object o) {
		if (o == null) return false;
		if (!(o instanceof Invoke)) return false;
		
		Invoke that = (Invoke) o;
		return isStatic == that.isStatic && nargs == that.nargs && init == that.init;
	}
	
	public String toString() {
		StringBuilder out = new StringBuilder();
		
		out.append(String.format("nargs:%d", nargs));
		
		if (init) out.append(" init");
		return out.toString();
	}
}