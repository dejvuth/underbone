package de.tum.in.jmoped.underbone;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDPairing;
import net.sf.javabdd.BDDVarSet;
import net.sf.javabdd.BDD.BDDIterator;
import de.tum.in.jmoped.underbone.ExprSemiring.ArithType;
import de.tum.in.jmoped.underbone.ExprSemiring.Condition;
import de.tum.in.jmoped.underbone.ExprSemiring.DupType;
import de.tum.in.jmoped.underbone.ExprSemiring.Condition.ConditionType;
import de.tum.in.wpds.CancelMonitor;
import de.tum.in.wpds.DpnSat;
import de.tum.in.wpds.Sat;
import de.tum.in.wpds.Semiring;

/**
 * BDD implementation of the <code>Semiring</code> interface.
 * 
 * @author suwimont
 *
 */
public class BDDSemiring implements Semiring {
	
	/**
	 * The variable manager.
	 */
	VarManager manager;
	
	/**
	 * The BDD.
	 */
	public BDD bdd;
	
	/**
	 * The constructor.
	 * 
	 * @param manager the variable manager.
	 * @param bdd the BDD.
	 */
	public BDDSemiring(VarManager manager, BDD bdd) {
		
		this.manager = manager;
		this.bdd = bdd;
		manager.updateMaxNodeNum();
	}
	
	/**
	 * Disjuncts this BDD with the BDD of <code>a</code>.
	 * 
	 * @param a the semiring.
	 * @return the disjuncted semiring.
	 * 
	 */
	public Semiring combine(Semiring a) {
		
		return new BDDSemiring(manager, bdd.or(((BDDSemiring) a).bdd));
	}
	
	/**
	 * Loads the values of the variable specified by vdom into the stack.
	 * 
	 * @param vdom the domain of the variable
	 * @return
	 */
	private BDD load(BDD bdd, BDDDomain vdom) {
		
		// Gets the current value of stack pointer (sp)
		BDDDomain spDom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spDom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp);
		
		// Abstracts the sp and the stack element at sp
		BDD cbdd = abstractVars(bdd, spDom, s0dom);
		
		// Updates the sp and the stack element at sp
		cbdd.andWith(spDom.ithVar(sp+1));
		cbdd.andWith(manager.bddEquals(s0dom, vdom));
		return cbdd;
	}
	
	/**
	 * Stores the values at the top of the stack to the variable specified by vdom.
	 * 
	 * @param vdom
	 * @return
	 */
	private BDD store(BDD bdd, BDDDomain vdom) {
		
		// Gets the current value of stack pointer (sp) minus 1
		BDDDomain spDom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spDom).intValue() -1;
		
		// Gets the top-of-stack domain
		BDDDomain s0dom = manager.getStackDomain(sp);
		
		// Abstracts the sp and the local variable
		BDD cbdd = abstractVars(bdd, spDom, vdom);
		
		// Updates the sp and the stack element at sp
		cbdd.andWith(spDom.ithVar(sp));
		cbdd.andWith(manager.bddEquals(s0dom, vdom));
		return cbdd;
	}
	
	private void log(BDD bdd) {
		if (Sat.DEBUG)
			log("%n\t\t%s%n%n", manager.toString(bdd, "\n\t\t"));
	}
	
	private void logRaw(BDD bdd) {
		if (Sat.DEBUG)
			log("%n\t\t%s%n%n", bdd.toStringWithDomains());
	}

	public Semiring extend(Semiring a, CancelMonitor monitor) {
		
		BDDFactory factory = bdd.getFactory();
		if (bdd.isZero()) return new BDDSemiring(manager, factory.zero());
		
		ExprSemiring A = (ExprSemiring) a;
		BDDDomain spDom = manager.getStackPointerDomain();
		
		log(bdd);
		logRaw(bdd);
		
		try {
		switch (A.type) {
		
		case ARITH:
			return arith(A);
		
		case ARRAYLENGTH:
			return arraylength(A);
		
		// Pushes from heap: s0 = heap[s1+s0+1], sp=sp-1;
		case ARRAYLOAD:
			return arrayload(A);
		
		// Pops to heap: heap[s2+s1+1]=s0, sp=sp-3;
		case ARRAYSTORE:
			return arraystore(A);
		
		case CONSTLOAD:
			return constload(A);
			
		case CONSTSTORE:
			return conststore(A);
		
		case DUP:
			return dup(A);
		
		case DYNAMIC:
			return dynamic(A);
			
		// Identity
		case ERROR:
			return error(A);
		
		case FIELDLOAD:
			return fieldload(A);
		
		case FIELDSTORE:
			return fieldstore(A);
		
		// Pushes ret value into the stack
		case GETRETURN: {
			BDDDomain rdom = manager.getRetVarDomain();
			BDD d = load(bdd, rdom);
			BDD c = abstractVars(d, rdom);
			d.free();
			return new BDDSemiring(manager, c);
		}
		
		// Pushes from global variable
		case GLOBALLOAD:
			return globalload(A);
		
		// Stores a constant to global variable
		case GLOBALPUSH: {
			BDDDomain gdom = manager.getGlobalVarDomain((String) A.value);
			BDD c = abstractVars(bdd, gdom);
			c.andWith(gdom.ithVar((Integer) A.aux));
			return new BDDSemiring(manager, c);
		}
		
		// Pops to global variable
		case GLOBALSTORE:
			return globalstore(A);
		
		case HEAPLOAD:
			return heapload(A);
			
		case HEAPOVERFLOW:
			return heapoverflow(A);
			
		// Pops and compares
		case IF:
			return ifExpr(A);
		
		// Pops twice and compares s1 with s0
		case IFCMP: {
			// Gets the current value of stack pointer (sp) minus 1
			int sp = bdd.scanVar(spDom).intValue() - 1;
			
			// Gets the stack domains
			BDDDomain s0dom = manager.getStackDomain(sp);
			BDDDomain s1dom = manager.getStackDomain(sp-1);
			
			ExprSemiring.CompType type = (ExprSemiring.CompType) A.value;
			BDD d;
			if (type == ExprSemiring.CompType.EQ)
//				d = s1dom.buildEquals(s0dom);
				d = manager.bddEquals(s1dom, s0dom);
			else if (type == ExprSemiring.CompType.NE)
				d = manager.bddNotEquals(s1dom, s0dom);
			else {
			
				// Gets all possible s1 values
				HashSet<Long> s1set = valuesOf(s1dom);
				
				d = factory.zero();
				for (Long s1 : s1set) {
					
					// Decodes s1
					int ds1 = VarManager.decode(s1, s1dom);
					
					// Gets all possible s0 values wrt. s1
					BDD e = bdd.id().andWith(s1dom.ithVar(s1));
					HashSet<Long> s0set = valuesOf(manager, e, s0dom);
					e.free();
					
					for (Long s0 : s0set) {
						
						// Decodes s0
						int ds0 = VarManager.decode(s0, s0dom);
						
						boolean valid = false;
						switch (type) {
						case LT:
							if (ds1 < ds0) valid = true;
							break;
						case GE:
							if (ds1 >= ds0) valid = true;
							break;
						case GT:
							if (ds1 > ds0) valid = true;
							break;
						case LE:
							if (ds1 <= ds0) valid = true;
							break;
						}
						
						if (valid) {
							d.orWith(s1dom.ithVar(s1).andWith(s0dom.ithVar(s0)));
//							System.out.printf("s1: %d(%d), s0: %d(%d)%n", s1, ds1, s0, ds0);
						}
					}
				}
			}
			
			d = bdd.id().andWith(d);
			if (d.isZero()) return new BDDSemiring(manager, d);
			BDD c = abstractVars(d, spDom, s0dom, s1dom);
			d.free();
			
			c.andWith(spDom.ithVar(sp-1));
			return new BDDSemiring(manager, c);
		}
		
		case INC:
			return inc(A);
		
		// Method invocation: (G0,L0,G1,L1) -> (G2,L2,L0,G1,L1)
		case INVOKE:
			return invoke(A);
			
		case IOOB:
			return ioob(A);
		
		// Pushes from local variable
		case LOAD: {
			
			BDD c = load(bdd, manager.getLocalVarDomain(((Integer) A.value)));
			return new BDDSemiring(manager, c);
		}
		
		case MONITORENTER:
			return monitorenter(A);
			
		case MONITOREXIT:
			return monitorexit(A);
		
		case NEW:
			return newExpr(A);
		
		case NEWARRAY:
			return newarray(A);
			
		case NOTIFY:
			return notify(A);
			
		case NPE:
			return npe(A);
		
		// Identity
		case ONE: {
			BDD c = fulfillsCondition(A);
			return new BDDSemiring(manager, c);
		}
		
		case POPPUSH:
			return poppush(A);
		
		case PRINT:
			return print(A);
		
		// Pushes constant
		case PUSH:
			return push(A);
		
		case RETURN: {
			
			BDD c;
			if (((Integer) A.value) > 0) {
				// Gets the current value of stack pointer (sp) minus 1
				int sp = bdd.scanVar(spDom).intValue() - 1;
				
				// Prepares the pair: seDom -> retDom
				BDDDomain seDom = manager.getStackDomain(sp);
				BDDPairing pair = factory.makePair(seDom, manager.getRetVarDomain());
				
				// Updates the return variable
				BDD d = bdd.id().replaceWith(pair);
				c = manager.abstractLocals(d);
				d.free();
			} else {
				c = manager.abstractLocals(bdd);
			}
//			c = manager.replaceG1L1withG2L2(c);
			c.replaceWith(manager.getG1L1pairG2L2());
			
			// Debug: prints ret values
//			log("\t\tret:");
//			BDDIterator itr = manager.iterator(c, manager.getRetVarDomain());
//			while (itr.hasNext()) {
//				BDD d = itr.nextBDD();
//				log(" %d", d.scanVar(manager.getRetVarDomain()));
//				d.free();
//			}
//			log("%n");
			
//			Sat.logger.fine(String.format("bdd: %s%n", bdd.toStringWithDomains()));
//			Sat.logger.fine(String.format("c: %s%n", c.toStringWithDomains()));
			return new BDDSemiring(manager, c);
		}
		
		// Pops to local variable
		case STORE: {
			BDD c = store(bdd, manager.getLocalVarDomain(((Integer) A.value)));
			return new BDDSemiring(manager, c);
		}
		
		case UNARYOP:
			return unaryop(A);
		
		case WAITINVOKE:
			return waitinvoke(A);
			
		case WAITRETURN:
			return waitreturn(A);
		}
		} catch (Exception e) {
			e.printStackTrace();
			System.out.println(manager.toString(bdd));
			System.out.println(A);
		}
		
		return null;
	}
	
	/**
	 * Performs arithmetic function: s0 = s1 op s0;
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring arith(ExprSemiring A) {
		
		// Gets the current value of stack pointer (sp) minus 1
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue() - 1;
		
		// Gets the stack domains
		BDDDomain s0dom = manager.getStackDomain(sp);
		BDDDomain s1dom = manager.getStackDomain(sp-1);
		BDDDomain tdom = manager.getTempVarDomain();
		
		// Gets all possible s1 values
		BDDIterator s1itr = manager.iterator(bdd, s1dom);
		
		BDDFactory factory = bdd.getFactory();
		BDD d = factory.zero();
		while (s1itr.hasNext()) {
			
			BDD e = s1itr.nextBDD();
			long s1 = e.scanVar(s1dom).longValue();
			e.free();
			
			// Gets all possible s0 values wrt. s1
			e = bdd.id().andWith(s1dom.ithVar(s1));
			BDDIterator s0itr = manager.iterator(e, s0dom);
			
			// Performs arithmetic function with s1 and s0
			BDD f = factory.zero();
			while (s0itr.hasNext()) {
				
				// Gets a s0 value
				BDD g = s0itr.nextBDD();
				long s0 = g.scanVar(s0dom).longValue();
				g.free();
				
				long r = manager.arith((ArithType) A.value, tdom, s1, s1dom, s0, s0dom);
				f.orWith(s0dom.ithVar(s0).andWith(tdom.ithVar(r)));
			}
			d.orWith(s1dom.ithVar(s1).andWith(f));
			e.free();
		}
		
		d = bdd.id().andWith(d);
		BDD c = abstractVars(d, spdom, s0dom, s1dom);
		d.free();
		
		c.andWith(spdom.ithVar(sp));
		c.replaceWith(factory.makePair(tdom, s1dom));
		
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring arraylength(ExprSemiring A) {
		
		// Gets the current value of stack pointer (sp) minus 1
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue() - 1;
		
		// Gets all possible s0 values
		BDDDomain tdom = manager.getTempVarDomain();
		BDDDomain s0dom = manager.getStackDomain(sp);
		BDDIterator s0itr = manager.iterator(bdd, s0dom);
		
		BDDFactory factory = bdd.getFactory();
		BDD c = factory.zero();
		while (s0itr.hasNext()) {
			
			// Gets a s0 value
			BDD d = s0itr.nextBDD();
			long s0 = d.scanVar(s0dom).longValue();
			d.free();
			log("\t\ts0: %d%n", s0);
			
			// Prunes the original bdd with s0 and copies the length values to temp
			BDDDomain ldom = manager.getArrayLengthDomain(s0);
			c.orWith(bdd.id().andWith(s0dom.ithVar(s0)).andWith(manager.bddEquals(ldom, tdom)));
		}
		
		// s0 gets the temp
		BDD d = abstractVars(c, s0dom);
		c.free();
		d.replaceWith(factory.makePair(tdom, s0dom));
		
		return new BDDSemiring(manager, d);
	}
	
	/**
	 * Pushes from heap: s0 = heap[s1+s0+1], sp=sp-1;
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring arrayload(ExprSemiring A) {
		
		// Gets the current value of stack pointer (sp)
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		// Gets the stack domains
		BDDDomain s0dom = manager.getStackDomain(sp - 1);	// index
		BDDDomain s1dom = manager.getStackDomain(sp - 2);	// arrayref
		BDDDomain tdom = manager.getTempVarDomain();
		
		// Gets all possible s1 values
		BDDIterator s1itr = manager.iterator(bdd, s1dom);
		
		BDDFactory factory = bdd.getFactory();
		BDD d = factory.zero();
		while (s1itr.hasNext()) {
			
			// Gets a s1 value
			BDD e = s1itr.nextBDD();
			long s1 = e.scanVar(s1dom).longValue();
			e.free();
			
			// Gets all possible s0 values wrt. s1
			e = bdd.id().andWith(s1dom.ithVar(s1));
			BDDIterator s0itr = manager.iterator(e, s0dom);
			
			nexts0: while (s0itr.hasNext()) {
			
				// Gets a s0 value
				BDD f = s0itr.nextBDD();
				int s0 = VarManager.decode(f.scanVar(s0dom).longValue(), s0dom);
				f.free();
				log("\t\ts1: %d, s0: %d%n", s1, s0);
				if (s0 < 0) {
					log("\t\tArray bound violation: index %d%n", s0);
					System.err.printf("Array bound violation: index %d%n", s0);
					continue nexts0;
				}
				
				// Check array bound
				f = e.id().andWith(s0dom.ithVar(s0));
				BDDDomain ldom = manager.getArrayLengthDomain(s1);
				BDDIterator lptr = manager.iterator(f, ldom);
				while (lptr.hasNext()) {
					BDD g = lptr.nextBDD();
					long l = g.scanVar(ldom).longValue();
					g.free();
					if (s0 >= l) {
						log("\t\tArray bound violation: length %d, index %d%n", l, s0);
						System.err.printf("Array bound violation: length %d, index %d%n", l, s0);
						continue nexts0;
					}
				}
				
				// Gets all possible heap[s1+s0+1] wrt. s1 and s0
				BDDDomain hdom = manager.getArrayElementDomain(s1, s0);
				BDDIterator hitr = manager.iterator(f, hdom);
				while (hitr.hasNext()) {
					
					// Gets a h value
					BDD g = hitr.nextBDD();
					long h = g.scanVar(hdom).longValue();
					g.free();
					
					d.orWith(tdom.ithVar(h)
							.andWith(hdom.ithVar(h))
							.andWith(s1dom.ithVar(s1))
							.andWith(s0dom.ithVar(s0)));
				}
				f.free();
			}
			e.free();
		}
		
		BDD c = bdd.id().andWith(d);
		d = abstractVars(c, spdom, s0dom, s1dom);
		c.free();
		d.andWith(spdom.ithVar(sp - 1));
		d.replaceWith(factory.makePair(tdom, s1dom));
		
		return new BDDSemiring(manager, d);
	}
	
	/**
	 * Pops to heap: heap[s2+s1+1]=s0, sp=sp-3;
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring arraystore(ExprSemiring A) {

		// Gets the current value of stack pointer (sp) minus 1
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue() - 1;
		
		// Gets the stack domains
		BDDDomain s0dom = manager.getStackDomain(sp);
		BDDDomain s1dom = manager.getStackDomain(sp-1);
		BDDDomain s2dom = manager.getStackDomain(sp-2);
		
		// Gets all possible s2 values
		BDDIterator s2itr = manager.iterator(bdd, s2dom);
		
		BDD c = bdd.getFactory().zero();
		while (s2itr.hasNext()) {
			
			// Gets a s2 value
			BDD d = s2itr.nextBDD();
			long s2 = d.scanVar(s2dom).longValue();
			d.free();
			
			// Gets all possible s1 wrt. s2
			d = bdd.id().andWith(s2dom.ithVar(s2));
			BDDIterator s1itr = manager.iterator(d, s1dom);
			
			nexts1: while (s1itr.hasNext()) {
				
				// Gets a s1 value
				BDD e = s1itr.nextBDD();
				int s1 = VarManager.decode(e.scanVar(s1dom).longValue(), s1dom);
				e.free();
				log("\t\ts2: %d, s1: %d%n", s2, s1);
				
				// Check array bound
				e = d.id().andWith(s1dom.ithVar(s1));
				BDDDomain ldom = manager.getArrayLengthDomain(s2);
				BDDIterator lptr = manager.iterator(e, ldom);
				while (lptr.hasNext()) {
					BDD f = lptr.nextBDD();
					long l = f.scanVar(ldom).longValue();
					f.free();
					if (s1 < 0 || s1 >= l) {
						log("\t\tArray bound violation: length %d, index %d%n", l, s1);
						System.err.printf("Array bound violation: length %d, index %d%n", l, s1);
						continue nexts1;
					}
				}
				
				// Gets the heap domain at s2+s1+1
				BDDDomain hdom = manager.getArrayElementDomain(s2, s1);
				
				// Gets all possible s0 wrt. s2 and s1
				BDDIterator s0itr = manager.iterator(e, s0dom);
				
				while (s0itr.hasNext()) {
					
					// Gets a s0 value
					BDD f = s0itr.nextBDD();
					long s0 = f.scanVar(s0dom).longValue();
					f.free();
					
					// Prunes the bdd to only for s0, s1, and s2
					f = bdd.id().andWith(s0dom.ithVar(s0)
							.andWith(s1dom.ithVar(s1))
							.andWith(s2dom.ithVar(s2)));
					
					// Updates the heap at the pruned bdd
					c.orWith(abstractVars(f, hdom).andWith(hdom.ithVar(s0)));
					f.free();
				}
				e.free();
			}
			d.free();
		}
		
		// Updates stack
		BDD d = abstractVars(c, spdom, s2dom, s1dom, s0dom);
		c.free();
		d.andWith(spdom.ithVar(sp-2));
		return new BDDSemiring(manager, d);
	}
	
	/**
	 * Pushes the constant specified by <code>A.value</code>.
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring constload(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		
		// Gets the stack pointer domain and the stack domain at the pointer
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain sdom = manager.getStackDomain(sp);
		
		// Gets the constant value
		int raw = manager.getConstant((String) A.value);
		
		// Updates the stack pointer and the stack
		BDD d = abstractVars(c, spdom, sdom);
		c.free();
		d.andWith(spdom.ithVar(sp + 1));
		d.andWith(sdom.ithVar(VarManager.encode(raw, sdom)));
		
		return new BDDSemiring(manager, d);
	}
	
	/**
	 * Stores the constant specified by <code>A.value</code>.
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring conststore(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		
		// Gets the stack pointer domain and the stack domain at the pointer - 1
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue() - 1;
		BDDDomain sdom = manager.getStackDomain(sp);
		
		// Stores the constant value
		long s = bdd.scanVar(sdom).longValue();
		manager.putConstant((String) A.value, VarManager.decode(s, sdom));
		
		// Updates the stack pointer and the stack
		BDD d = abstractVars(c, spdom, sdom);
		c.free();
		d.andWith(spdom.ithVar(sp));
		
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring dynamic(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		
		// Gets the stack pointer domain and the stack domain at the pointer - 1
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue() - 1;
		BDDDomain s0dom = manager.getStackDomain(sp);
		
		// Abstracts stack pointer and s0
		BDD d = abstractVars(c, spdom, s0dom);
		c.free();
		
		// Updates the stack pointer
		d.andWith(spdom.ithVar(sp));
		
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring dup(ExprSemiring A) {
		
		DupType type = (DupType) A.value;
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDD c = null;
		switch (type) {
		
		// ..., value ->  ..., value, value
		case DUP:
			c = load(bdd, manager.getStackDomain(sp - 1));
			break;
		
		// ..., value2, value1 -> ..., value1, value2, value1
		case DUP_X1: {
			BDDFactory factory = bdd.getFactory();
			c = bdd.id()
				.replaceWith(factory.makePair(
					manager.getStackDomain(sp - 1), manager.getStackDomain(sp)))
				.replaceWith(factory.makePair(
					manager.getStackDomain(sp - 2), manager.getStackDomain(sp - 1)))
				.andWith(manager.bddEquals(
						manager.getStackDomain(sp - 2), manager.getStackDomain(sp)));
			BDD tmp = abstractVars(c, spdom).andWith(spdom.ithVar(sp + 1));
			c.free();
			c = tmp;
			break;
		}
		}
		
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring error(ExprSemiring A) {
		return new BDDSemiring(manager, bdd.id());
	}
	
	/**
	 * Pushes the field of the instance s0.
	 * <code>A.value</code> specifies the field id.
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring fieldload(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		c.free();
		
		// The field id
		int id = (Integer) A.value;
		
		// Gets stack domains
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - 1);
		
		// Gets temp domain
		BDDDomain tdom = manager.getTempVarDomain();
		
		// Gets all possible s0
		BDDIterator s0itr = manager.iterator(bdd, s0dom);
		c = bdd.getFactory().zero();
		while (s0itr.hasNext()) {
			
			// Gets the heap domain at s0 + i
			BDD e = s0itr.nextBDD();
			long s0 = e.scanVar(s0dom).longValue();
			e.free();
			
			// NPE
			if (s0 == 0) {
				log("\t\tNullPointerException%n");
				continue;
			}
			
			// Gets all possible heap value wrt. to s0
			BDD d = bdd.id().andWith(s0dom.ithVar(s0));
			BDDDomain hdom = manager.getHeapDomain(s0 + id);
			log("\t\thdom: %d%n", hdom.getIndex());
			BDDIterator hitr = manager.iterator(d, hdom);
			while (hitr.hasNext()) {
				
				// Saves field value to temp and conjuncts with s0 and h
				e = hitr.nextBDD();
				long h = e.scanVar(hdom).longValue();
				e.free();
				c.orWith(//s0dom.ithVar(s0)
						d.id()
						.andWith(hdom.ithVar(h))
						.andWith(tdom.ithVar(h)));
				log("\t\tPush %d%n", h);
			}
			d.free();
		}
		
		// NPE
		if (c.isZero()) return new BDDSemiring(manager, c);
		
		// Abstracts s0
		BDD d = abstractVars(c, s0dom);
		c.free();
		
		// Replace temp with s0
		d.replaceWith(bdd.getFactory().makePair(tdom, s0dom));
		
		return new BDDSemiring(manager, d);
	}
	
	/**
	 * Stores s0 into the field of the instance s1.
	 * <code>A.value</code> specifies the field id.
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring fieldstore(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		c.free();
		
		// The field id
		int id = (Integer) A.value;
		
		// Gets stack domains
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - 1);
		BDDDomain s1dom = manager.getStackDomain(sp - 2);
		
		// Gets all possible s0
		BDDIterator s0itr = manager.iterator(bdd, s0dom);
		c = bdd.getFactory().zero();
		while (s0itr.hasNext()) {
			
			// Gets all possible s1 wrt. s0
			BDD e = s0itr.nextBDD();
			long s0 = e.scanVar(s0dom).longValue();
			e.free();
			
			BDD d = bdd.id().andWith(s0dom.ithVar(s0));
			BDDIterator s1itr = manager.iterator(d, s1dom);
			while (s1itr.hasNext()) {
				
				// Gets the heap domain at s1 + id
				e = s1itr.nextBDD();
				long s1 = e.scanVar(s1dom).longValue();
				log("\t\ts1: %d%n", s1);
				e.free();
				BDDDomain hdom = manager.getHeapDomain(s1 + id);
				
				// Prunes the bdd to only for s0 and s1
				e = bdd.id().andWith(s0dom.ithVar(s0)).andWith(s1dom.ithVar(s1));
				
				// Abstracts the heap domain of the pruned bdd and updates to s0
				c.orWith(abstractVars(e, hdom).andWith(hdom.ithVar(s0)));
				e.free();
			}
			d.free();
		}
		
		// Abstracts the stack pointer, s0, and s1
		BDD d = abstractVars(c, spdom, s0dom, s1dom);
		c.free();
		
		// Updates the stack pointer
		d.andWith(spdom.ithVar(sp - 2));
		
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring globalload(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		BDD d = load(c, manager.getGlobalVarDomain((String) A.value));
		c.free();
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring globalstore(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero())
			return new BDDSemiring(manager, c);
		BDD d = store(c, manager.getGlobalVarDomain((String) A.value));
		c.free();
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring heapload(ExprSemiring A) {
		
		// Gets the current value of stack pointer (sp) minus 1
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue() - 1;
		
		// Gets all possible s0 values
		BDDDomain tdom = manager.getTempVarDomain();
		BDDDomain s0dom = manager.getStackDomain(sp);
		BDDIterator s0itr = manager.iterator(bdd, s0dom);
		
		BDDFactory factory = bdd.getFactory();
		BDD c = factory.zero();
		while (s0itr.hasNext()) {
			
			// Gets a s0 value
			BDD d = s0itr.nextBDD();
			long s0 = d.scanVar(s0dom).longValue();
			d.free();
			
			// Prunes the original bdd with s0 and copies the length values to temp
			BDDDomain hdom = manager.getHeapDomain(s0);
			c.orWith(bdd.id().andWith(s0dom.ithVar(s0)).andWith(manager.bddEquals(hdom, tdom)));
		}
		
		// s0 gets the temp
		BDD d = abstractVars(c, s0dom);
		c.free();
		d.replaceWith(factory.makePair(tdom, s0dom));
		
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring heapoverflow(ExprSemiring A) {
		ExprType type = (ExprType) A.value;
		if (type == ExprType.NEW) {
			
			ExprSemiring.New n = (ExprSemiring.New) A.aux;
			
			// Gets all possible heap pointer values
			BDDDomain hpdom = manager.getHeapPointerDomain();
			BDDIterator hpitr = manager.iterator(bdd, hpdom);
			
			BDD c = bdd.getFactory().zero();
			while (hpitr.hasNext()) {
				
				// Gets a heap pointer value
				BDD d = hpitr.nextBDD();
				long hp = d.scanVar(hpdom).longValue();
				d.free();
				
				// Collects the heap pointer that will exceeds the heap size
				if (hp + n.size + 1 > manager.getHeapSize()) {
					c.orWith(hpdom.ithVar(hp));
					continue;
				}
			}
			
			return new BDDSemiring(manager, bdd.id().andWith(c));
		}
		
		// type == ExprType.NEWARRAY
		
		// Prepares BDD domains
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		ExprSemiring.Newarray newarray = (ExprSemiring.Newarray) A.aux;
		
		// doms[i] is domain of s_i, doms[newarray.dim] is domain of hp
		BDDDomain[] doms = new BDDDomain[newarray.dim + 1];
		for (int i = 0; i < newarray.dim; i++)
			doms[i] = manager.getStackDomain(sp - i - 1);
		doms[newarray.dim] = manager.getHeapPointerDomain();
		
		BDDIterator itr = manager.iterator(bdd, doms);
		BDD c = bdd.getFactory().zero();
		while (itr.hasNext()) {
			
			// Computes heap requirement
			BDD d = itr.nextBDD();
			int require = 0;
			int acc = 1;
			for (int i = newarray.dim - 1; i >= 0; i--) {
				int length_i = d.scanVar(doms[i]).intValue();
				log("\t\tlength_i: %d%n", length_i);
				require += acc * (length_i + manager.getArrayAuxSize());
				acc *= length_i;
			}
			log("\t\trequire: %d%n", require);
			
			// Heap requirement exceeds the heap size?
			int hp = d.scanVar(doms[newarray.dim]).intValue();
			if (hp + require >= manager.getHeapSize()) {
				c.orWith(d);
			} else {
				d.free();
			}
		}
		
		return new BDDSemiring(manager, bdd.id().andWith(c));
	}
	
	private BDDSemiring ifExpr(ExprSemiring A) {
		
		// Gets the current value of stack pointer (sp) minus 1
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue() - 1;
		BDDDomain sdom = manager.getStackDomain(sp);
		
		// Trims the bdd
		BDD c = bdd.id().andWith(manager.ifBDD((ExprSemiring.If) A.value, sdom));
		
		// Returns if the trimmed BDD is zero
		if (c.isZero())
			return new BDDSemiring(manager, c);
		
		// Updates stack
		BDD d = abstractVars(c, spdom, sdom).andWith(spdom.ithVar(sp));
		c.free();
		
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring inc(ExprSemiring A) {
		
		// Gets lv domain at index
		ExprSemiring.Inc inc = (ExprSemiring.Inc) A.value;
		BDDDomain lvdom = manager.getLocalVarDomain(inc.index);
		BDDDomain tdom = manager.getTempVarDomain();
		
		// Gets all lv values
		BDDFactory factory = bdd.getFactory();
		BDD c = factory.zero();
		BDDIterator lvitr = manager.iterator(bdd, lvdom);
		while (lvitr.hasNext()) {
			
			// Gets a lv value
			BDD d = lvitr.nextBDD();
			long lv = d.scanVar(lvdom).longValue();
			d.free();
			
			// Increments and stores it to temp
			long t = VarManager.encode(VarManager.decode(lv, lvdom) + inc.value, tdom);
			c.orWith(lvdom.ithVar(lv).andWith(tdom.ithVar(t)));
		}
		
		// Conjuncts
		BDD d = bdd.id().andWith(c);
		
		// Changes temp -> lv
		c = abstractVars(d, lvdom).replaceWith(factory.makePair(tdom, lvdom));
		d.free();
		return new BDDSemiring(manager, c);
	}
	
	/**
	 * Method invocation: (G0,L0,G1,L1) -> (G2,L2,L0,G1,L1)
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring invoke(ExprSemiring A) {
		
		boolean[] params = ((ExprSemiring.Invoke) A.value).params;
		int nargs = params.length;
		BDD c = fulfillsCondition(A);
		if (c.isZero()) {
			log("\t\tNOT fulfillsCondition%n");
			return new BDDSemiring(manager, c);
		}
		
//		// Abstracts all Gtids
//		BDD d;
//		if (manager.multithreading() && manager.symbolic()) {
//			d = c.exist(manager.getG3VarSet());
//			c.free();
//			c = d;
//		}
		
		// G0 becomes G2
		c.replaceWith(manager.getG0pairG2());
		if (nargs == 0) return new BDDSemiring(manager, c);
			
		// Gets the current value of stack pointer (sp)
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		c.andWith(manager.bddL0equalsL2params(sp-nargs, params));
		
		// Collects the domains to abstract: stack and stack pointer
		BDDDomain[] sdoms = new BDDDomain[nargs + 1];
		for (int i = 0; i < nargs; i++)
			sdoms[i] = manager.getStackDomain(sp-i-1);
		sdoms[nargs] = spdom;
		
		// Abstracts the stack
		BDD d = abstractVars(c, sdoms);
		c.free();
		
		// Updates the sp
		d.andWith(spdom.ithVar(sp - nargs));
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring ioob(ExprSemiring A) {
		
		// Gets the current value of stack pointer (sp)
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		// Gets the stack domains
		ExprSemiring.Npe ioob = (ExprSemiring.Npe) A.value;
		BDDDomain idom = manager.getStackDomain(sp - ioob.depth);		// index
		BDDDomain adom = manager.getStackDomain(sp - ioob.depth - 1);	// arrayref
		
		// Gets all possible arrayref values
		BDDIterator aitr = manager.iterator(bdd, adom);
		
		BDDFactory factory = bdd.getFactory();
		BDD c = factory.zero();
		while (aitr.hasNext()) {
			
			// Gets an arrayref
			BDD e = aitr.nextBDD();
			long a = e.scanVar(adom).longValue();
			e.free();
			
			// Gets all possible index values wrt. arrayref
			e = bdd.id().andWith(adom.ithVar(a));
			BDDIterator iitr = manager.iterator(e, idom);
			while (iitr.hasNext()) {
			
				// Gets an index
				BDD f = iitr.nextBDD();
				long i = f.scanVar(idom).longValue();
				int di = VarManager.decode(i, idom);
				f.free();
				
				// Gets all possible array length wrt. arrayref and index
				f = e.id().andWith(idom.ithVar(i));
				BDDDomain ldom = manager.getArrayLengthDomain(a);
				BDDIterator lptr = manager.iterator(f, ldom);
				while (lptr.hasNext()) {
					
					// Gets a length
					BDD g = lptr.nextBDD();
					long l = g.scanVar(ldom).longValue();
					g.free();
					
					// Checks NPE
					if (di < 0 || di >= l) {
						c.orWith(f.id().andWith(ldom.ithVar(l)));
					}
				}
				f.free();
			}
			e.free();
		}
		return new BDDSemiring(manager, c);
	}
	
	private BDD monitorenter(BDD d, BDDDomain thdom, BDDDomain cntdom) {
		
		// Gets all possible thread values
		BDD c = bdd.getFactory().zero();
		BDDIterator thitr = manager.iterator(d, thdom);
		while (thitr.hasNext()) {
			
			// Gets a thread value
			BDD e = thitr.nextBDD();
			int th = e.scanVar(thdom).intValue();
			e.free();
			
			// Continues the object is locked by another thread
			if (th != 0 && th != DpnSat.getCurrentThreadId()) {
				log("\t\tThread %d cannot lock, already locked by %d%n",
						DpnSat.getCurrentThreadId(), th);
				continue;
			}
			
			// Gets all possible counter values wrt. s0 and thread id
			e = d.id().andWith(thdom.ithVar(th));
			BDDIterator cntitr = manager.iterator(e, cntdom);
			while (cntitr.hasNext()) {
				
				// Gets a counter
				BDD f = cntitr.nextBDD();
				int cnt = f.scanVar(cntdom).intValue();
				f.free();
				log("\t\tth: %d, cnt: %d%n", th, cnt);
				
				// Updates the thread id and counter
				f = e.id().andWith(cntdom.ithVar(cnt));
				if (th == 0) {
					c.orWith(abstractVars(f, thdom, cntdom)
							.andWith(thdom.ithVar(DpnSat.getCurrentThreadId()))
							.andWith(cntdom.ithVar(1)));
				} else {
					if (cnt + 1 >= manager.size()) {
						error("Monitor is entered too many times, ignoring the rest");
						f.free();
						continue;
					}
					c.orWith(abstractVars(f, cntdom)
							.andWith(cntdom.ithVar(cnt + 1)));
				}
				f.free();
			}
			e.free();
		}
		
		return c;
	}
	
	private BDDSemiring monitorenter(ExprSemiring A) {
		
		ExprSemiring.Monitorenter expr = (ExprSemiring.Monitorenter) A.value;
		if (expr.type == ExprSemiring.Monitorenter.Type.POP 
				|| expr.type == ExprSemiring.Monitorenter.Type.TOUCH) {
		
			// Gets stack domains
			BDDDomain spdom = manager.getStackPointerDomain();
			int sp = bdd.scanVar(spdom).intValue() - expr.intValue();
			BDDDomain sdom = manager.getStackDomain(sp);
			
			// Gets all possible s
			BDDIterator sitr = manager.iterator(bdd, sdom);
			BDD c = bdd.getFactory().zero();
			while (sitr.hasNext()) {
				
				// Gets a s0 value
				BDD d = sitr.nextBDD();
				long s = d.scanVar(sdom).longValue();
				d.free();
				
				// Gets all possible thread ids wrt. s0
				BDDDomain thdom = manager.getHeapDomain(s + 1);
				BDDDomain cntdom = manager.getHeapDomain(s + 2);
				log("\t\ts: %d, thdom: %d, cntdom: %d%n", 
						s, thdom.getIndex(), cntdom.getIndex());
				d = bdd.id().andWith(sdom.ithVar(s));
				
				c.orWith(monitorenter(d, thdom, cntdom));
				
				d.free();
			}
			
			if (c.isZero())
				return new BDDSemiring(manager, c);
			
			// Updates the stack
			if (expr.type == ExprSemiring.Monitorenter.Type.POP) {
				BDD d = abstractVars(c, spdom, sdom);
				c.free();
				c = d;
				c.andWith(spdom.ithVar(sp));
			}
			return new BDDSemiring(manager, c);
		}
		
		return null;//TODO
	}
	
	private BDDSemiring monitorexit(ExprSemiring A) {
		
		// Gets stack domains
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue() - 1;
		BDDDomain s0dom = manager.getStackDomain(sp);
		
		// Gets all possible s0
		BDDIterator s0itr = manager.iterator(bdd, s0dom);
		BDD c = bdd.getFactory().zero();
		while (s0itr.hasNext()) {
			
			// Gets a s0 value
			BDD d = s0itr.nextBDD();
			long s0 = d.scanVar(s0dom).longValue();
			d.free();
			
			// Gets all possible thread ids wrt. to s0
			BDDDomain thdom = manager.getHeapDomain(s0 + 1);
			BDDDomain cntdom = manager.getHeapDomain(s0 + 2);
			d = bdd.id().andWith(s0dom.ithVar(s0));
			BDDIterator thitr = manager.iterator(d, thdom);
			while (thitr.hasNext()) {
				
				// Gets a heap value
				BDD e = thitr.nextBDD();
				int th = e.scanVar(thdom).intValue();
				e.free();
				
				// Continues if the object is locked by another thread
				if (th != 0 && th != DpnSat.getCurrentThreadId()) {
					continue;
				}
				
				// Gets all possible counter values wrt. to s0 and thread id
				e = d.id().andWith(thdom.ithVar(th));
				BDDIterator cntitr = manager.iterator(e, cntdom);
				while (cntitr.hasNext()) {
					
					// Gets a counter
					BDD f = cntitr.nextBDD();
					int cnt = f.scanVar(cntdom).intValue();
					f.free();
					log("\t\ts0: %d, th: %d, cnt: %d%n", s0, th, cnt);
					
					/*
					 * Continues if the monitor was not entered.
					 * This can happen when e.g. the same synchronized method 
					 * is called from different objects. The BDD has two
					 * different possibilities, one for each lock. We need to
					 * prune this BDD for the lock corresponds to the right
					 * object.
					 */
					if (cnt == 0) {
						log("\t\tcnt is zero, skipping%n");
						continue;
					}
					
					// Updates the thread id and counter
					f = e.id().andWith(cntdom.ithVar(cnt));
					if (cnt == 1) {
						c.orWith(abstractVars(f, thdom, cntdom)
								.andWith(thdom.ithVar(0))
								.andWith(cntdom.ithVar(0)));
					} else {
						c.orWith(abstractVars(f, cntdom)
								.andWith(cntdom.ithVar(cnt - 1)));
					}
					f.free();
				}
				e.free();
			}
			d.free();
		}
		
		if (c.isZero())
			return new BDDSemiring(manager, c);
		
		// Updates the stack
		BDD d = abstractVars(c, spdom, s0dom);
		c.free();
		d.andWith(spdom.ithVar(sp));
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring newExpr(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero()) {
			log("\t\tNOT fulfillsCondition%n");
			return new BDDSemiring(manager, c);
		}
		c.free();
		
		// Gets the current value of stack pointer (sp)
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp);
		
		// Gets all possible heap pointer values
		BDDDomain hpdom = manager.getHeapPointerDomain();
		BDDIterator hpitr = manager.iterator(bdd, hpdom);
		
		// Prepares temp domain
		BDDDomain tdom = manager.getTempVarDomain();
		
		// New info
		ExprSemiring.New n = (ExprSemiring.New) A.value;
		if (n.id >= manager.size()) {
			String msg = String.format("Not enough bits.%n%n" +
					"Reason: found class id %d.", n.id);
			throw new RemoplaError(msg);
		}
		
		c = bdd.getFactory().zero();
		while (hpitr.hasNext()) {
			
			// Gets a heap pointer value
			BDD d = hpitr.nextBDD();
			long hp = d.scanVar(hpdom).longValue();
			d.free();
			
			// Bypasses if the required memory is greater than the heap size
			if (hp + n.size + 1 > manager.getHeapSize()) {
				error("Not enough heap");
				continue;
			}
			log("\t\tNew object at heap index: %d (BDD index: %d)%n", 
					hp, manager.getHeapDomainIndex(hp));
			
//			// Monitor is a shared var
//			if (manager.multithreading()) {
//				manager.addSharedDom(manager.getHeapDomainIndex(hp + 1));
//				manager.addSharedDom(manager.getHeapDomainIndex(hp + 2));
//			}
			
			/*
			 * Stores class id to where the heap pointer points to, 
			 * pushes heap pointer, and
			 * temp gets the updated value of heap pointer
			 */
			BDDDomain hdom = manager.getHeapDomain(hp);
			d = bdd.id().andWith(hpdom.ithVar(hp));
			c.orWith(abstractVars(d, hdom, s0dom)
					.andWith(hdom.ithVar(n.id))
					.andWith(s0dom.ithVar(hp))
					.andWith(tdom.ithVar(hp + n.size + 1)));
			d.free();
		}
		
		// If the heap was full
		if (c.isZero())
			return new BDDSemiring(manager, c);
		
		// Abstracts stack pointer and heap pointer
		BDD d = abstractVars(c, spdom, hpdom);
		c.free();
		
		// Updates stack pointer, and renames temp to heap pointer
		d.andWith(spdom.ithVar(sp + 1));
		d.replaceWith(bdd.getFactory().makePair(tdom, hpdom));
		
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring newarray(ExprSemiring A) {
		
		// Prepares BDD domains
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		ExprSemiring.Newarray newarray = (ExprSemiring.Newarray) A.value;
		
		// doms[i] is domain of s_i, doms[newarray.dim] is domain of hp
		BDDDomain[] doms = new BDDDomain[newarray.dim + 1];
		for (int i = 0; i < newarray.dim; i++)
			doms[i] = manager.getStackDomain(sp - i - 1);
		doms[newarray.dim] = manager.getHeapPointerDomain();
		
		BDDIterator itr = manager.iterator(bdd, doms);
		BDD c = bdd.getFactory().zero();
		while (itr.hasNext()) {
			
			// Computes heap requirement
			BDD d = itr.nextBDD();
			int require = 0;
			int acc = 1;
			for (int i = newarray.dim - 1; i >= 0; i--) {
				int length_i = d.scanVar(doms[i]).intValue();
				log("\t\tlength_i: %d%n", length_i);
				require += acc * (length_i + manager.getArrayAuxSize());
				acc *= length_i;
			}
			log("\t\trequire: %d%n", require);
			
			int hp = d.scanVar(doms[newarray.dim]).intValue();
			if (hp + require >= manager.getHeapSize()) {
				log("\t\tNot enough heap. hp: %d, require: %d%n", hp, require);
				continue;
			}
			
			// Abstracts heap: heap[hp], ..., heap[hp + require - 1]
			BDDDomain[] abs = new BDDDomain[require];
			for (int i = 0; i < require; i++) {
				abs[i] = manager.getHeapDomain(hp + i);
			}
			BDD f = bdd.and(d);
			BDD e = abstractVars(f, abs);
			f.free();
			
			int ptr = hp;
			Queue<Integer> indices = new LinkedList<Integer>();
			for (int i = 1; i <= newarray.dim; i++) {
				
				// Computes number of blocks
				int blocknum = 1;
				for (int j = i; j < newarray.dim; j++) {
					blocknum *= d.scanVar(doms[j]).intValue();
				}
				
				// Fills blocks
				int blocksize = d.scanVar(doms[i - 1]).intValue();
				log("\t\tblocknum: %d, blocksize: %d%n", blocknum, blocksize);
				for (int j = 0; j < blocknum; j++) {
					
					// Remember the index
					indices.offer(ptr);
					
					// Fills the array type
					if (newarray.types[newarray.dim-i] >= manager.size())
						throw new RemoplaError("Not enough bits. " +
								"There are at least %d object types.", 
								newarray.types[newarray.dim-i]);
					e.andWith(manager.getHeapDomain(ptr++).ithVar(newarray.types[newarray.dim-i]));
					log("\t\tptr: %d%n", ptr);
					
					// Updtes ptr wrt. owner & counter
					for (int k = 2; k < manager.getArrayAuxSize(); k++)
						e.andWith(manager.getHeapDomain(ptr++).ithVar(0));
					
					// Fills the array length
					e.andWith(manager.getHeapDomain(ptr++).ithVar(blocksize));
					
					// Fills the array elements
					for (int k = 0; k < blocksize; k++) {
						
						// Initializes the array values
						BDDDomain hdom = manager.getHeapDomain(ptr++);
						BDD value;
						if (i == 1) {
							value = bddOf(newarray.init, hdom);
						} 
						
						// Initializes the array indices
						else {
							value = hdom.ithVar(indices.remove());
						}
						e.andWith(value);
					}
				}
			}
			
			// Updates the stack and the hp
			c.orWith(abstractVars(e, doms)
					.andWith(doms[newarray.dim - 1].ithVar(indices.remove()))
					.andWith(doms[newarray.dim].ithVar(hp + require)));
			e.free();
			d.free();
		}
		
		// Updates stack pointer
		BDD d = abstractVars(c, spdom).andWith(spdom.ithVar(sp - newarray.dim  + 1));
		c.free();
		return new BDDSemiring(manager, d);
	}
	
	private BDD bddOf(ExprSemiring.Value value, BDDDomain dom) {
		
		// All values
		if (value.all()) {
			return bdd.getFactory().one();
		} 
		
		// Deterministic values
		if (value.deterministic()) {
			if (value.isInteger()) {
				return dom.ithVar(VarManager.encode(value.intValue(), dom));
			} else if (value.isReal()) {
				return dom.ithVar(manager.encode(value.floatValue(), dom));
			} else {	// value.isString();
				return dom.ithVar(manager.encode(value.stringValue(), dom));
			}
		} 
		
		// Nondeterministic, but not all
		return manager.bddRange(dom, value.intValue(), value.to.intValue());
	}
	
	private BDDSemiring newarrayx(ExprSemiring A) {
		
		// Prepares BDD domains
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - 1);
		BDDDomain hpdom = manager.getHeapPointerDomain();
		
		// For all s0 values
		BDDIterator s0itr = manager.iterator(bdd, s0dom);
		BDD c = bdd.getFactory().zero();
		while (s0itr.hasNext()) {
			
			// Gets a s0 value
			BDD d = s0itr.nextBDD();
			int s0 = VarManager.decode(d.scanVar(s0dom).longValue(), s0dom);
			d.free();
			
			if (s0 < 0) {
				log("\t\tNegativeArraySizeException (length=%d)%n", s0);
				continue;
			}
			
			// For all hp values
			d = bdd.id().andWith(s0dom.ithVar(s0));
			BDDIterator hpitr = manager.iterator(d, hpdom);
			while (hpitr.hasNext()) {
				
				// Gets a hp value
				BDD e = hpitr.nextBDD();
				long hp = e.scanVar(hpdom).longValue();
				e.free();
				
				// Bypasses if the required memory is greater than the heap size
				if (hp + s0 + 1 > manager.getHeapSize()) {
					System.err.println("Not enough heap");
					log("\t\tNot enough heap%n");
					continue;
				}
				log("\t\tNew array at heap index: %d (BDD index: %d)%n", 
						hp, manager.getHeapDomainIndex(hp));
				
				/*
				 *  Prepares BDD domains to abstract: 
				 *  s0, hp, heap[hp], ..., heap[hp+s0]
				 */
				BDDDomain hdom = manager.getHeapDomain(hp);
				BDDDomain[] doms = new BDDDomain[s0 + 3];
				doms[0] = s0dom;
				doms[1] = hpdom;
				doms[2] = hdom;
				for (int i = 0; i < s0; i++)
					doms[i + 3] = manager.getHeapDomain(hp + i + 1);
				
				// Prunes the bdd to only for s0 and hp
				e = d.id().andWith(hpdom.ithVar(hp));
				
				// Updates s0, hp, and h (array length)
				BDD f = abstractVars(e, doms)
						.andWith(s0dom.ithVar(hp))
						.andWith(hpdom.ithVar(hp + s0 + 1)
						.andWith(hdom.ithVar(s0)));
				e.free();
				
				// Sets the array elements
				if (A.value != null) {
					for (int i = 0; i < s0; i++) {
						BDDDomain hd = manager.getHeapDomain(hp + i + 1);
						if (A.aux != null)
							f.andWith(manager.bddRange(hd, (Integer) A.aux, (Integer) A.value));
						else
							f.andWith(hd.ithVar((Integer) A.value));
					}
				}
				c.orWith(f);
			}
			d.free();
		}
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring notify(ExprSemiring A) {
		
		// Gets stack pointer
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		// Prepares domains: s0, waitfor, waitflag for each thread
		BDDDomain[] doms = new BDDDomain[2*manager.getThreadBound() + 1];
		doms[0] = manager.getStackDomain(sp - 1);
		for (int i = 1; i <= manager.getThreadBound(); i++) {
			doms[2*i - 1] = manager.getGlobalVarDomain(
					LabelUtils.formatWaitFor(i));
			doms[2*i] = manager.getGlobalVarDomain(
					LabelUtils.formatWaitFlag(i));
		}
		BDDIterator itr = manager.iterator(bdd, doms);
		
		ExprSemiring.NotifyType type = (ExprSemiring.NotifyType) A.value;
		BDD c = bdd.getFactory().zero();
		while (itr.hasNext()) {
			
			// Gets an s0 value
			BDD d = itr.nextBDD();
			long s0 = d.scanVar(doms[0]).longValue();
			
			BDD e = bdd.and(d);
			ArrayList<BDDDomain> waitingdoms = null;
			for (int i = 1; i <= manager.getThreadBound(); i++) {
				
				// Gets waitflag and waitfor value
				int waitflag = d.scanVar(doms[2*i]).intValue();
				if (waitflag == 0) {
					log("\t\tthread %d is not waiting%n", i);
					continue;
				}
				long waitfor = d.scanVar(doms[2*i - 1]).longValue();
				if (waitfor != s0) {
					log("\t\tthread %d is waiting for another object (%d)%n", 
							i, waitfor);
					continue;
				}
				
				if (type == ExprSemiring.NotifyType.NOTIFY) {
					BDD f = abstractVars(e, doms[2*i], doms[2*i - 1]);
					f.andWith(doms[2*i].ithVar(0)).andWith(doms[2*i - 1].ithVar(0));
					c.orWith(f);
				} else {	// NOTIFYALL
					if (waitingdoms == null)
						waitingdoms = new ArrayList<BDDDomain>();
					waitingdoms.add(doms[2*i]);
					waitingdoms.add(doms[2*i - 1]);
				}
			}
			
			if (type == ExprSemiring.NotifyType.NOTIFYALL) {
				BDD f;
				if (waitingdoms == null) {
					f = e.id();
				} else {
					f = abstractVars(e, waitingdoms.toArray(new BDDDomain[0]));
					for (BDDDomain dom : waitingdoms) {
						f.andWith(dom.ithVar(0));
					}
				}
				c.orWith(f);
			}
			
			e.free();
			d.free();
		}
		
		// In case no thread is waiting
		if (c.isZero()) c = bdd.id();
		
		// Updates stack
		BDD d = abstractVars(c, spdom, doms[0]).andWith(doms[0].ithVar(sp - 1));
		c.free();
		
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring npe(ExprSemiring A) {
		
		ExprSemiring.Npe npe = (ExprSemiring.Npe) A.value;
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - npe.depth - 1);
		
		return new BDDSemiring(manager, bdd.id().andWith(s0dom.ithVar(0)));
	}
	
	private BDDSemiring poppush(ExprSemiring A) {
		
		BDDDomain spdom = manager.getStackPointerDomain();
		
		// Changes nothing, if neither pop nor push
		int pop = (Integer) A.value;
		boolean push = (Boolean) A.aux;
		if (pop == 0 && !push)
			return new BDDSemiring(manager, bdd.id());
		
		// Gets the current value of stack pointer (sp)
		int sp = bdd.scanVar(spdom).intValue();
		
		// Abstracts stack pointer and stack elements
		BDDDomain[] d = new BDDDomain[pop + 1];
		d[0] = spdom;
		for (int i = 1; i <= pop; i++)
			d[i] = manager.getStackDomain(sp - i);
		BDD c = abstractVars(bdd, d);
		
		// Updates the stack pointer
		sp -= pop;
		if (push) sp++;
		c.andWith(spdom.ithVar(sp));
		
		// FIXME prohibits non-determinism
		if (push && manager.multithreading() /*&& !manager.symbolic()*/) {
			c.andWith(manager.getStackDomain(sp - 1).ithVar(0));
		}
		
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring print(ExprSemiring A) {
		
		// Gets iterator for s0
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - 1);
		BDDIterator s0itr = manager.iterator(bdd, s0dom);
		
		ExprSemiring.Print print = (ExprSemiring.Print) A.value;
		StringBuilder out = new StringBuilder();
		while (s0itr.hasNext()) {
			
			// Gets a s0 value
			BDD c = s0itr.nextBDD();
			long s0 = c.scanVar(s0dom).longValue();
			c.free();
			
			// Appends s0 to out
			Object decoded = null;;
			switch (print.type) {
			case INTEGER: decoded = s0; break;
			case FLOAT: decoded = manager.decodeFloat(s0); break;
			case CHARACTER: decoded = (char) s0; break;
			case STRING: decoded = manager.decodeString(s0); break;
			}
			out.append(decoded);
			if (s0itr.hasNext())
				out.append(" ");
		}
		
		// Prints out
		System.out.print(out);
		if (print.newline) System.out.println();
		
		// Updates stack
		BDD c = abstractVars(bdd, spdom, s0dom);
		c.andWith(spdom.ithVar(sp - 1));
		
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring push(ExprSemiring A) {
		
		// Gets the current value of stack pointer (sp)
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp);
		
		// Abstracts the sp and the stack element at sp
		BDD c = abstractVars(bdd, spdom, s0dom);
		
		// Updates the sp and the stack element at sp
		ExprSemiring.Value push = (ExprSemiring.Value) A.value;
		c.andWith(spdom.ithVar(sp+1));
		c.andWith(bddOf(push, s0dom));
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring unaryop(ExprSemiring A) {
		
		// Gets the current value of stack pointer (sp) minus 1
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue() - 1;
		
		// Gets the stack domains
		BDDDomain s0dom = manager.getStackDomain(sp);
		BDDDomain tdom = manager.getTempVarDomain();
		
		// Gets all possible s0 values
		BDDFactory factory = bdd.getFactory();
		BDD c = factory.zero();
		BDDIterator s0itr = manager.iterator(bdd, s0dom);
		
		ExprSemiring.UnaryOpType type = (ExprSemiring.UnaryOpType) A.value;
		while (s0itr.hasNext()) {
			
			// Gets a s0 value
			BDD d = s0itr.nextBDD();
			long s0 = d.scanVar(s0dom).longValue();
			d.free();
			
			long t = -1;
			switch (type) {
			case NEG:
				t = manager.neg(s0);
				break;
			case FNEG:
				t = manager.fneg(s0, s0dom);
				break;
			case F2I:
				t = VarManager.encode((int) manager.decodeFloat(s0), s0dom);
				break;
			case I2F:
				t = manager.encode((float) s0, s0dom);
				break;
			}
			c.orWith(tdom.ithVar(t).andWith(s0dom.ithVar(s0)));
		}
		
		c = bdd.id().andWith(c);
		BDD d = abstractVars(c, s0dom);
		c.free();
		
		d.replaceWith(factory.makePair(tdom, s0dom));
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring waitinvoke(ExprSemiring A) {
		
		// Gets domains for save,, waitfor
		int tid = DpnSat.getCurrentThreadId();
		BDDDomain savedom = manager.getGlobalVarDomain(
				LabelUtils.formatSave(tid));
		BDDDomain waitflagdom = manager.getGlobalVarDomain(
				LabelUtils.formatWaitFlag(tid));
		BDDDomain waitfordom = manager.getGlobalVarDomain(
				LabelUtils.formatWaitFor(tid));
		
		// Gets all possible s0 values
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - 1);
		BDDIterator s0itr = manager.iterator(bdd, s0dom);
		
		// Abstracts save & waitfor domain of this thread
		BDD b = abstractVars(bdd, savedom, waitflagdom, waitfordom);
		
		BDDFactory factory = bdd.getFactory();
		BDD c = factory.zero();
		while (s0itr.hasNext()) {
			
			// Gets a s0 value
			BDD d = s0itr.nextBDD();
			long s0 = d.scanVar(s0dom).longValue();
			d.free();
			
			// Gets domains: thread owner, count
			BDDDomain ownerdom = manager.getOwnerThreadDomain(s0);
			BDDDomain cntdom = manager.getOwnerCounterDomain(s0);
			
			d = b.id().andWith(s0dom.ithVar(s0));
			BDD e = abstractVars(d, ownerdom);
			d.free();
			
			// Updates save, waitfor, owner, cnt
			c.orWith(e.replaceWith(factory.makePair(cntdom, savedom))
					.andWith(waitflagdom.ithVar(1))
					.andWith(waitfordom.ithVar(s0))
					.andWith(ownerdom.ithVar(0))
					.andWith(cntdom.ithVar(0)));
		}
		
		b = abstractVars(c, spdom, s0dom).andWith(spdom.ithVar(sp - 1));
		return new BDDSemiring(manager, b);
	}
	
	private BDDSemiring waitreturn(ExprSemiring A) {
		
		int tid = DpnSat.getCurrentThreadId();
		BDDDomain savedom = manager.getGlobalVarDomain(
				LabelUtils.formatSave(tid));
		BDDDomain waitflagdom = manager.getGlobalVarDomain(
				LabelUtils.formatWaitFlag(tid));
		BDDDomain waitfordom = manager.getGlobalVarDomain(
				LabelUtils.formatWaitFor(tid));
		BDDIterator itr = manager.iterator(bdd, 
				new BDDDomain[] { savedom, waitflagdom, waitfordom });
		
		BDDFactory factory = bdd.getFactory();
		BDD c = factory.zero();
		while (itr.hasNext()) {
			
			BDD d = itr.nextBDD();
			int waitflag = d.scanVar(waitflagdom).intValue();
			
			// Skips if wait flag is set
			if (waitflag != 0) {
				log("\t\twaiting%n");
				continue;
			}
			
			// Gets all owners
			long save = d.scanVar(savedom).longValue();
			long waitfor = d.scanVar(waitfordom).intValue();
			d = bdd.id().andWith(d);
			BDDDomain ownerdom = manager.getOwnerThreadDomain(waitfor);
			BDDDomain cntdom = manager.getOwnerCounterDomain(waitfor);
			BDDIterator itr2 = manager.iterator(d, new BDDDomain[] { ownerdom, cntdom });
			
			while (itr2.hasNext()) {
				
				// Gets an owner
				BDD e = itr2.nextBDD();
				long owner = e.scanVar(ownerdom).longValue();
				
				if (owner != 0) {
					log("\t\tmonitor not free");
					continue;
				}
				
				e = d.id().andWith(e);
				c.orWith(abstractVars(e, savedom, waitflagdom, waitfordom, ownerdom, cntdom)
						.andWith(savedom.ithVar(0))
						.andWith(waitflagdom.ithVar(0))
						.andWith(waitfordom.ithVar(0))
						.andWith(ownerdom.ithVar(tid))
						.andWith(cntdom.ithVar(save)));
				e.free();
			}
			d.free();
		}
		
		return new BDDSemiring(manager, c);
	}
	
	/**
	 * Gets all possible integer values of this bdd at domain dom.
	 * 
	 * @param dom the domain
	 * @return the set of all possible integers
	 */
	public HashSet<Long> valuesOf(BDDDomain dom) {
		
		return valuesOf(manager, bdd, dom);
	}
	
	public static HashSet<Long> valuesOf(VarManager manager, BDD bdd, BDDDomain dom) {
		
		BDDVarSet varset = dom.set();
		BDDIterator itr = bdd.exist(manager.getVarSetWithout(dom.getIndex()))
				.iterator(varset);
		HashSet<Long> set = new HashSet<Long>();
		while (itr.hasNext())
			set.add(((BDD) itr.next()).scanVar(dom).longValue());
		varset.free();
		
		return set;
	}
	
	/**
	 * Abstract the variables specified by doms from bdd.
	 * 
	 * @param bdd
	 * @param doms
	 * @return
	 */
	public static BDD abstractVars(BDD bdd, BDDDomain... doms) {
		
		if (doms.length == 0) return bdd.id();
		
		BDDVarSet abs = doms[0].set();
		for (int i = 1; i < doms.length; i++) {
			abs.unionWith(doms[i].set());
		}
		BDD out = bdd.exist(abs);
		abs.free();
		
		return out;
	}
	
	/**
	 * (G0,G2,L2) + (G2,L2,L0,G1,L1) -> (G0,L0,G1,L1)
	 * 
	 */
	public Semiring extendPop(Semiring a, CancelMonitor monitor) {
		
//		log("%nepsilon: %s%n", bdd.toStringWithDomains());
//		log("%npopped: %s%n", ((BDDSemiring) a).bdd.toStringWithDomains());
		
		BDD d = bdd.and(((BDDSemiring) a).bdd);
		BDD c = d.exist(manager.getG2L2VarSet());
		d.free();
		
//		log("%nconjuncted: %s%n", c.toStringWithDomains());
		
		// Debug: prints ret values
//		BDDDomain retdom = manager.getRetVarDomain();
//		log("\t\tret (%d):", retdom.getIndex());
//		BDDIterator itr = manager.iterator(c, retdom);
//		while (itr.hasNext()) {
//			d = itr.nextBDD();
//			log(" %d", d.scanVar(retdom));
//			d.free();
//		}
//		log("%n");
		
		return new BDDSemiring(manager, c);
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
		if (cond.type == ConditionType.CONTAINS) {
			
			Set<Integer> set = (Set<Integer>) cond.value;
			
			// Gets the stack pointer
			BDDDomain spdom = manager.getStackPointerDomain();
			int sp = bdd.scanVar(spdom).intValue();
			
			// Gets the stack element where the instance is stored
			BDDDomain sdom = manager.getStackDomain(sp - id);
			
			// Loops for all possible instances
			BDDIterator sitr = manager.iterator(bdd, sdom);
			BDD d = bdd.getFactory().zero();
			while (sitr.hasNext()) {
				
				// Gets an instance
				BDD e = sitr.nextBDD();
				long s = e.scanVar(sdom).longValue();
				e.free();
				
				// Gets all possible ids for this instance
				BDDDomain hdom = manager.getHeapDomain(s);
				e = bdd.id().andWith(sdom.ithVar(s));
				BDDIterator hitr = manager.iterator(e, hdom);
				while (hitr.hasNext()) {
					
					// Gets an id
					BDD f = hitr.nextBDD();
					int h = f.scanVar(hdom).intValue();
					f.free();
					
					// Bypasses if the id is not contained in the condition value
					if (!set.contains(h)) {
						log("\t\tbypassing id %d%n", h);
						continue;
					}
					
					// Prunes the bdd for this id
					d.orWith(bdd.id().andWith(sdom.ithVar(s)).andWith(hdom.ithVar(h)));
				}
				e.free();
			}
			
			return d;
		}
		
		// type is either ZERO or ONE
		BDDDomain gdom = manager.getGlobalVarDomain((String) cond.value);
		int g = bdd.scanVar(gdom).intValue();
		switch (cond.type) {
		case ZERO:
			if (g == 0) return bdd.id();
			break;
		case ONE:
			if (g == 1) return bdd.id();
			break;
		}
		
		return bdd.getFactory().zero();
	}
	
	private BDD fulfillsCondition(ExprSemiring A) {
		
		int id = 0;
		switch (A.type) {
		case DYNAMIC:
		case INVOKE:
			id = ((ExprSemiring.Invoke) A.value).params.length;
			break;
		case FIELDLOAD:
		case ONE:
			id = 1;
			break;
		case FIELDSTORE:
			id = 2;
			break;
		}
		
		return fulfillsCondition(A, id);
	}
	
	/**
	 * <pre>
	 * (G0,L0,G1,L1) -> (G0,L0) -> (G0,L0,G1,L1)
	 * </pre>
	 * 
	 * where new G1,L1 are copies of G0,L0. 
	 */
	public Semiring extendPush(Semiring a, CancelMonitor monitor) {
		
		BDDFactory factory = bdd.getFactory();
		ExprSemiring A = (ExprSemiring) a;
		
		BDD d = bdd.exist(manager.getG1L1VarSet());
		BDD c = manager.abstractLocalVarsAndStackPointer(d);
		d.free();
		BDDDomain spDom = manager.getStackPointerDomain();
		if (spDom != null) {
			c.andWith(spDom.ithVar(0));
		}
		
		boolean[] params = ((ExprSemiring.Invoke) A.value).params;
		int nargs = params.length;
		
		if (nargs == 0) {
			for (int i = 0; i < manager.getMaxLocalVars(); i++)
				c.andWith(manager.getLocalVarDomain(i).ithVar(0));
			d = manager.abstractStack(c);
			c.free();
			d.andWith(manager.buildG0L0equalsG1L1().id());
			return new BDDSemiring(manager, d);
		}
		
		// Gets the current value of stack pointer (sp)
		int sp = bdd.scanVar(spDom).intValue();
		
		int j = 0;
		for (int i = 0; i < nargs; i++, j++) {
			
			// Updates the local variable: sdom -> lvdom
			BDDDomain lvdom = manager.getLocalVarDomain(j);
			BDDDomain sdom = manager.getStackDomain(sp - nargs + i);
			BDDPairing pair = factory.makePair(sdom, lvdom);
			c.replaceWith(pair);
			
			if (params[i]) {
				j++;
				c.andWith(manager.getLocalVarDomain(j).ithVar(0));
			}
		}
		
		for (; j < manager.getMaxLocalVars(); j++)
			c.andWith(manager.getLocalVarDomain(j).ithVar(0));
		
		d = manager.abstractStack(c);
		c.free();
		
		d.andWith(manager.buildG0L0equalsG1L1().id());
		
		// Turns me on if using manager.getRawArguments() is desired
//		if (((ExprSemiring.Invoke) A.value).init) {
//			
//			// Gets the maximum heap pointer value
//			BDDDomain hpdom = manager.getHeapPointerDomain();
//			BDDIterator hpitr = manager.iterator(d, hpdom);
//			int maxhp = 1;
//			while (hpitr.hasNext()) {
//				c = hpitr.nextBDD();
//				int hp = c.scanVar(hpdom).intValue();
//				c.free();
//				
//				if (hp > maxhp) maxhp = hp;
//			}
//			d.andWith(manager.saveArgs(maxhp, nargs));
//		}
		
		return new BDDSemiring(manager, d);
	}
	
	public static void log(String msg, Object... args) {
		Sat.logger.fine(String.format(msg, args));
	}
	
	public static void error(String msg) {
		System.err.println(msg);
		log("\t\t" + msg + "%n");
	}
	
	public Semiring id() {
		
		return new BDDSemiring(manager, bdd.id());
	}
	
	public void free() {
		
		if (bdd != null) bdd.free();
	}
	
	public boolean equals(Object o) {
		
		if (!(o instanceof BDDSemiring))
			return false;
		
		return ((BDDSemiring) o).bdd.equals(bdd);
		
	}
	
	public String toRawString() {
		return bdd.toStringWithDomains();
	}
	
	public String toString() {
		return manager.toString(bdd, "\n\t\t");
	}

	/**
	 * Symbolic:
	 * <pre>
	 * (G0,G3,G1,L1) -> (G3,L0)
	 * </pre>
	 * 
	 * Explicit:
	 * <pre>
	 * (G0,L0,G1,L1) -> (L0)
	 * </pre>
	 * 
	 */
	public Semiring extendDynamic(Semiring a, CancelMonitor monitor) {
		
		BDDFactory factory = bdd.getFactory();
		
		// Abstracts G1,L1
		BDD d = bdd.exist(manager.getG1L1VarSet());
		BDD c = manager.abstractLocalVarsAndStackPointer(d);
		d.free();
		
		// Initializes the stack pointer
		BDDDomain spdom = manager.getStackPointerDomain();
		if (spdom != null) { //TODO the rest of the method also needs this check
			c.andWith(spdom.ithVar(0));
		}
		
		// lv0 gets the top-of-stack value (the thread's object instance)
		int sp = bdd.scanVar(spdom).intValue() - 1;
		BDDDomain lvDom = manager.getLocalVarDomain(0);
		BDDDomain seDom = manager.getStackDomain(sp);
		BDDPairing pair = factory.makePair(seDom, lvDom);
		c.replaceWith(pair);
		
		// Updates the other local variables
		for (int i = 1; i < manager.getMaxLocalVars(); i++)
			c.andWith(manager.getLocalVarDomain(i).ithVar(0));
		
		// Abstracts stack
		d = manager.abstractStack(c);
		c.free();
		
		// Abstracts shared vars
		c = d.exist(manager.getSharedVarSet());
		d.free();
		
		return new BDDSemiring(manager, c);
	}
	
	/**
	 * [Eager] Returns the set of all different global values from this BDD.
	 * 
	 * @return the set of all global values.
	 */
	public Set<Semiring> getGlobals() {
		Set<Semiring> set = new HashSet<Semiring>();
		BDD shared = manager.abstractNonShared(bdd);
		BDDIterator itr = shared.iterator(manager.getSharedVarSet());
		while (itr.hasNext()) {
			set.add(new BDDSemiring(manager, itr.nextBDD()));
		}
		return set;
	}

	/**
	 * [Eager & Lazy] Lifts this BDD.
	 */
	public Semiring lift(Semiring a) {
		
		// For symbolic case
		if (manager.symbolic()) return lift2(); 
		
		return new BDDSemiring(manager, bdd.and(((BDDSemiring) a).bdd));
	}
	
	/**
	 * [Lazy] Copies G3 to G0.
	 * 
	 * @return
	 */
	private Semiring lift2() {
		// Copies the values of G3 to G0
		return new BDDSemiring(manager, bdd.and(manager.buildG0equalsG3()));
	}

	/**
	 * [Eager] Conjuncts this BDD and the BDD of <code>a</code>, and
	 * and abstracts all shared variables away.
	 * 
	 * The BDD <code>a</code> remains unchanged.
	 * 
	 * @return the restricted bdd.
	 */
	public Semiring restrict(Semiring a) {
		
		BDD c = bdd.and(((BDDSemiring) a).bdd);
		BDD d = c.exist(manager.getSharedVarSet());
		c.free();
		
		return new BDDSemiring(manager, d);
	}

	public Semiring andWith(Semiring a) {
		bdd.andWith(((BDDSemiring) a).bdd);
		return this;
	}

	/**
	 * [Lazy] Gets an equivalence class.
	 * 
	 * This BDD: (G3,G4)
	 * 
	 * @return an equivalence class (G3).
	 */
	public Semiring getEqClass(int approach) {
		
		// Gets a g4
		BDDIterator itr = bdd.exist(manager.getG3VarSet()).iterator(manager.getG4VarSet());
		BDD g4 = itr.nextBDD();
		
		// Gets G3 corresponding to g4
		BDD G3g4 = bdd.id().andWith(g4);
		BDD G3 = G3g4.exist(manager.getG4VarSet());
		G3g4.free();
		
		if (approach == 2) {
			while (true) {
				// G3 & (G3->G4) & not(this) & ordering
//				BDD G3G4 = G3.id().andWith(manager.replaceG3withG4(G3.id()));
				BDD G3G4 = G3.id().andWith(G3.id().replaceWith(manager.getG3pairG4()));
				G3G4.andWith(bdd.not()).andWith(manager.getG3G4ordering().id());
				if (G3G4.isZero()) break;
				
				// Gets the difference and subtracts from G3
				BDD diff = G3G4.exist(manager.getG4VarSet());
				G3G4.free();
				G3.andWith(diff.not());
				diff.free();
			}
		}
		
		return new BDDSemiring(manager, G3);
	}
	
	/**
	 * [Lazy] Gets equivalence relations. Approach 2.
	 * 
	 * This BDD: (G0,G3)
	 * 
	 * (\exists G0: (G0,G3) & (G0,G3->G4)) --> (G3=G4)
	 * 
	 * @return (G3,G4)
	 */
	private Semiring getEqRel2() {
//		BDD G0G4 = manager.replaceG3withG4(bdd.id());
		BDD G0G4 = bdd.id().replaceWith(manager.getG3pairG4());
		BDD G0G3G4 = bdd.id().andWith(G0G4);
		BDD G3G4 = G0G3G4.exist(manager.getG0VarSet());
		G0G3G4.free();
		
		BDD notG3G4 = G3G4.not();
		G3G4.free();
		
		return new BDDSemiring(manager, 
				notG3G4.orWith(manager.buildG3equalsG4().id()));
	}

	/**
	 * [Lazy] Gets equivalence relations.
	 * 
	 * This BDD: (G0,G3,L0,G1,L1) or (G3,L0,G1,L1)
	 * 
	 * @return (G3,G4)
	 */
	public Semiring getEqRel(int approach) {
		
		if (approach == 2) return getEqRel2();
		
//		BDD copy = manager.replaceG3withG4(bdd.id());
		BDD copy = bdd.id().replaceWith(manager.getG3pairG4());
		BDD biimp = bdd.biimp(copy);
		copy.free();
		
		BDD forall;
		forall = biimp.forAll(manager.getL0G1L1VarSet());
		biimp.free();
		return new BDDSemiring(manager, forall);
	}

	/**
	 * [Lazy] Abstracts L0,G1,L1 from this BDD.
	 * 
	 * This BDD: 
	 * - (G0,G3,L0,G1,L1) or 
	 * - (G0,G3,G2,L2) in case of epsilon transition.
	 * 
	 * @return (G0,G3)
	 */
	public Semiring getGlobal() {
		return new BDDSemiring(manager, bdd.exist(manager.getL0G1L1G2L2VarSet()));
	}
	
	/**
	 * [Lazy] Updates globals of this BDD with <code>a</code>.
	 * 
	 * This BDD: (G3,L0,G1,L1) or (G0,G3,L0,G1,L1)
	 * a: (G0,G3)
	 * 
	 * Conjoins this bdd with a; abstracts G3; and renames G0 to G3.
	 * 
	 * @return (G3,L0,G1,L1)
	 */
	public void updateGlobal(Semiring a) {
		BDD G0G3L0G1L1 = bdd.andWith(((BDDSemiring) a).bdd.id());
		BDD G0L0G1L1 = G0G3L0G1L1.exist(manager.getG3VarSet());
		G0G3L0G1L1.free();
		
//		bdd = manager.replaceG0withG3(G0L0G1L1);
		bdd = G0L0G1L1.replaceWith(manager.getG0pairG3());
	}
	
	/**
	 * [Lazy] Slices this equivalence relation with <code>eqclass</code>.
	 * Appraoch 2.
	 * 
	 * @param eqclass an equivalence class.
	 */
	private void sliceWith2(Semiring eqclass) {
		BDD G3 = ((BDDSemiring) eqclass).bdd;
//		BDD G4 = manager.replaceG3withG4(G3.id());
		BDD G4 = G3.id().replaceWith(manager.getG3pairG4());
		bdd.andWith(G3.not()).andWith(G4.not());
		G3.free();
		G4.free();
	}
	
	/**
	 * [Lazy] Slices this equivalence relation with <code>eqclass</code>.
	 * 
	 * @param eqclass an equivalence class.
	 * @param approach one or two.
	 */
	public void sliceWith(Semiring eqclass, int approach) {
		if (approach == 2) {
			sliceWith2(eqclass);
			return;
		}
		
		BDD G3 = ((BDDSemiring) eqclass).bdd;
		bdd.andWith(G3.not());
		G3.free();
	}
	
	public boolean isZero() {
		return bdd.isZero();
	}

	public Semiring orWith(Semiring a) {
		bdd.orWith(((BDDSemiring) a).bdd);
		return this;
	}
}
