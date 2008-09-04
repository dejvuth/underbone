package de.tum.in.jmoped.underbone;

import java.util.Arrays;
import java.util.Set;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDVarSet;
import net.sf.javabdd.BDD.BDDIterator;

import de.tum.in.jmoped.underbone.expr.Condition;
import de.tum.in.jmoped.underbone.expr.ExprSemiring;
import de.tum.in.jmoped.underbone.expr.ExprType;
import de.tum.in.jmoped.underbone.expr.Field;
import de.tum.in.jmoped.underbone.expr.Invoke;
import de.tum.in.jmoped.underbone.expr.Value;
import de.tum.in.wpds.CancelMonitor;
import de.tum.in.wpds.Sat;
import de.tum.in.wpds.Semiring;

public class PoolSemiring implements Semiring {

	PoolManager manager;
	BDD bdd;
	
	public PoolSemiring(PoolManager manager, BDD bdd) {
		this.manager = manager;
		this.bdd = bdd;
	}
	
	public Semiring andWith(Semiring arg0) {
		// TODO Auto-generated method stub
		return null;
	}
	
	private void ext(BDD bdd, int[] ivar1, int[] ivar2) {
		if (Arrays.equals(ivar1, ivar2))
			return;
		
		BDDFactory factory = bdd.getFactory();
		BDD a = factory.one();
		for (int j = ivar1.length - 1; j < ivar2.length; j++) {
			a.andWith(factory.ithVar(ivar2[j]));
		}
		
		BDD b = factory.one();
		for (int j = ivar1.length - 1; j < ivar2.length; j++) {
			b.andWith(factory.nithVar(ivar2[j]));
		}
		
		bdd.andWith(a.orWith(b));
	}
	
	private PoolSemiring ext(PoolManager thatmanager) {
		BDDFactory factory = bdd.getFactory();
		BDD newbdd = bdd.id();
		
		int[][] ivars = manager.iglobal;
		int[][] thativars = thatmanager.iglobal;
		if (ivars != null) {
			for (int i = 0; i < ivars.length; i++) {
				ext(newbdd, ivars[i], thativars[i]);
			}
		}
		
		ivars = manager.iheap;
		thativars = thatmanager.iheap;
		if (ivars != null) {
			for (int i = 0; i < ivars.length; i++) {
				ext(newbdd, ivars[i], thativars[i]);
			}
		}
		
		return new PoolSemiring(thatmanager, newbdd);
	}

	public Semiring combine(Semiring a) {
		PoolSemiring that = (PoolSemiring) a;
		PoolManager newmanager = manager.combine(that.manager);
		
		PoolSemiring newthis = ext(newmanager);
		PoolSemiring newthat = ext(newmanager);
		BDD newbdd = newthis.bdd.orWith(newthat.bdd);
		return newthis;
	}

	public Semiring extendDynamic(Semiring arg0, CancelMonitor arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring extendPop(Semiring arg0, CancelMonitor arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring extendPush(Semiring arg0, CancelMonitor arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	public void free() {
		// TODO Auto-generated method stub

	}

	public Semiring getEqClass(int arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring getEqRel(int arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring getGlobal() {
		// TODO Auto-generated method stub
		return null;
	}

	public Set<Semiring> getGlobals() {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring id() {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean isZero() {
		// TODO Auto-generated method stub
		return false;
	}

	public Semiring lift(Semiring arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring orWith(Semiring arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring restrict(Semiring arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public void sliceWith(Semiring arg0, int arg1) {
		// TODO Auto-generated method stub

	}

	public String toRawString() {
		return bdd.toString();
	}

	public void updateGlobal(Semiring arg0) {
		// TODO Auto-generated method stub

	}

	public Semiring extend(Semiring a, CancelMonitor monitor) {
		ExprSemiring A = (ExprSemiring) a;
		log();
		
//		switch (A.type) {
//		case ExprType.ARITH:
//			return arith(A);
//		case ExprType.ARRAYLENGTH:
//			return arraylength(A);
//		case ExprType.ARRAYLOAD:
//			return arrayload(A);
//		case ExprType.ARRAYSTORE:
//			return arraystore(A);
//		case ExprType.CONSTLOAD:
//			return constload(A);
//		case ExprType.CONSTSTORE:
//			return conststore(A);
//		case ExprType.DUP:
//			return dup(A);
//		case ExprType.DYNAMIC:
//			return dynamic(A);
//		case ExprType.ERROR:
//			return error(A);
//		case ExprType.FIELDLOAD:
//			return fieldload(A);
//		case ExprType.FIELDSTORE:
//			return fieldstore(A);
//		case ExprType.GETRETURN:
//			return getreturn(A);
//		case ExprType.GLOBALLOAD:
//			return globalload(A);
////		case ExprType.GLOBALPUSH:
////			return globalpush(A);
//		case ExprType.GLOBALSTORE:
//			return globalstore(A);
////		case ExprType.HEAPLOAD:
////			return heapload(A);
//		case ExprType.HEAPOVERFLOW:
//			return heapoverflow(A);
//		case ExprType.IF:
//			return ifExpr(A);
//		case ExprType.IFCMP:
//			return ifcmp(A);
//		case ExprType.INC:
//			return inc(A);
//		case ExprType.INVOKE:
//			return invoke(A);
//		case ExprType.IOOB:
//			return ioob(A);
//		case ExprType.JUMP:
//			return jump(A);
//		case ExprType.LOAD:
//			return load(A);
////		case ExprType.MONITORENTER:
////			return monitorenter(A);
////		case ExprType.MONITOREXIT:
////			return monitorexit(A);
//		case ExprType.NEW:
//			return newExpr(A);
//		case ExprType.NEWARRAY:
//			return newarray(A);
////		case ExprType.NOTIFY:
////			return notify(A);
//		case ExprType.NPE:
//			return npe(A);
//		case ExprType.POPPUSH:
//			return poppush(A);
//		case ExprType.PRINT:
//			return print(A);
//		case ExprType.PUSH:
//			return push(A);
//		case ExprType.RETURN:
//			return returnExpr(A);
//		case ExprType.STORE:
//			return store(A);
//		case ExprType.SWAP:
//			return swap(A);
//		case ExprType.UNARYOP:
//			return unaryop(A);
////		case ExprType.WAITINVOKE:
////			return waitinvoke(A);
////		case ExprType.WAITRETURN:
////			return waitreturn(A);
//		}
		
		return null;
	}
	
	private Semiring push(ExprSemiring A) {
		// Checks condition
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new PoolSemiring(manager, c);
		
		Value value = (Value) A.value;
		int category = value.getCategory().intValue();
		
		int sp = manager.sptr(bdd);
		BDDVarSet varset = manager.sptrSet().unionWith(manager.stackSet(sp));
		if (category == 2)
			varset.unionWith(manager.stackSet(sp + 1));
		BDD d = c.exist(varset);
		varset.free();
		c.free();
		
		// Updates the stack
		d.andWith(manager.ithVarSptr(sp + category));
		d.andWith(bddOf(value, manager.istack[sp]));
		if (category == 2)
			d.andWith(manager.ithVarStack(sp + 1, 0));
		return new PoolSemiring(manager, d);
	}
	
	/**
	 * Returns <code>true</code> if A.aux is of type InvokeCondition, and
	 * the given condition fulfills. The condition contains a variable
	 * and a comparison type. The condition is fulfilled iff the current
	 * value of the variable in this bdd satisfies the comparison.
	 * 
	 * @param A
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private BDD fulfillsCondition(ExprSemiring A, int id) {
		
		if (A.aux == null) {
			log("\t\tno condition%n");
			return bdd.id();
		}
		
		Condition cond = (Condition) A.aux;
		int type = cond.getType();
		if (type == Condition.CONTAINS 
				|| type == Condition.NOTCONTAINS) {
			
			Set<Integer> set = cond.getSetValue();
			
			// Gets the stack pointer
			int sp = manager.sptr(bdd);
			
			// Gets the stack element where the instance is stored
			int[] sdom = manager.istack[sp - id];
			
			// Loops for all possible instances
			BDDIterator sitr = manager.iterator(bdd, sdom);
			BDD d = bdd.getFactory().zero();
			while (sitr.hasNext()) {
				
				// Gets an instance
				BDD e = sitr.nextBDD();
				int s = (int) BDDManager.scanVar(e, sdom);
				e.free();
				
				// Gets all possible ids for this instance
				int[] hdom = manager.iheap[s];
				e = bdd.id().andWith(manager.ithVar(s, sdom));
				BDDIterator hitr = manager.iterator(e, hdom);
				while (hitr.hasNext()) {
					
					// Gets an id
					BDD f = hitr.nextBDD();
					int h = (int) BDDManager.scanVar(f, hdom);
					f.free();
					
					// Bypasses if the id is not contained in the condition value
					if (type == Condition.CONTAINS && !set.contains(h)) {
						log("\t\tbypassing id %d%n", h);
						continue;
					}
					if (type == Condition.NOTCONTAINS && set.contains(h)) {
						log("\t\tbypassing id %d%n", h);
						continue;
					}
					
					// Prunes the bdd for this id
					d.orWith(bdd.id().andWith(manager.ithVar(s, sdom))
							.andWith(manager.ithVar(h, hdom)));
				}
				e.free();
			}
			
			return d;
		}
		
		// type is either ZERO or ONE
		int[] gdom = manager.iglobal(cond.getStringValue());
		int g = (int) BDDManager.scanVar(bdd, gdom);
		switch (type) {
		case Condition.ZERO:
			if (g == 0) return bdd.id();
			break;
		case Condition.ONE:
			if (g == 1) return bdd.id();
			break;
		}
		
		return bdd.getFactory().zero();
	}
	
	private BDD fulfillsCondition(ExprSemiring A) {
		
		int id = 0;
		switch (A.type) {
		case ExprType.DYNAMIC:
		case ExprType.INVOKE:
			id = ((Invoke) A.value).nargs;
			break;
		case ExprType.FIELDLOAD:
		case ExprType.JUMP:
			id = 1;
			break;
		case ExprType.FIELDSTORE:
			id = ((Field) A.value).getCategory().two() ? 3 : 2;
			break;
		}
		
		return fulfillsCondition(A, id);
	}
	
	/**
	 * Returns the BDD with variables specified by <code>dom</code>
	 * representing <code>value</code>.
	 * 
	 * @param value the value.
	 * @param dom the BDD domain.
	 * @return the BDD representing the value.
	 */
	public BDD bddOf(Value value, int[] ivar) {
		
		// All values
		if (value.all()) {
			return bdd.getFactory().one();
		} 
		
		// Deterministic values
		if (value.deterministic()) {
			long v;
			if (value.isInteger()) {
				v = PoolManager.encode(value.intValue(), ivar);
			} else if (value.isReal()) {
				v = manager.encode(value.floatValue(), ivar);
			} else {	// value.isString();
				v = manager.encode(value.stringValue(), ivar);
			}
			return manager.ithVar(v, ivar);
		}
		
		// Nondeterministic, but not all
		if (value.isReal())
			return manager.bddRange(ivar, value.floatValue(), value.next, 
					value.to.floatValue());
			
		if (Sat.all())
			log("\t\tvalue.intValue(): %d, value.to.intValue(): %d%n",
					value.intValue(), value.to.intValue());
		return manager.bddRange(ivar, value.intValue(), value.to.intValue());
	}
	
	private void log() {
//		if (manager.iglobal != null) {
//			for (Variable v : manager.bddmanager.globals.values()) {
//				log("\t\t%s: %d%n", v.getName(), PoolManager.scanVar(bdd, manager.iglobal[v.getIndex()]));
//			}
//		}
//		if (manager.iheap != null) {
//			log("\t\t[ ");
//			
//		}
		log("\t\t%s%n", bdd.toString());
	}
	
	public static void log(String msg, Object... args) {
		Sat.logger.fine(String.format(msg, args));
	}

	public Semiring diff(Semiring arg0) {
		// TODO Auto-generated method stub
		return null;
	}
}
