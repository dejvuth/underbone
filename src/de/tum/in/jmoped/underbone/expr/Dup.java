package de.tum.in.jmoped.underbone.expr;


/**
 * Stack duplication. 
 * 
 * Value for {@link ExprType#DUP}.
 */
public enum Dup {
	DUP(1, 1), DUP_X1(2, 1), DUP_X2(3, 1), DUP2(2, 2), DUP2_X1(3, 2), DUP2_X2(4, 2);
	
	public int down;
	public int push;
	Dup(int down, int push) {
		this.down = down;
		this.push = push;
	}
}