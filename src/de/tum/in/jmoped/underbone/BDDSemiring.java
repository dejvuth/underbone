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
import de.tum.in.jmoped.underbone.expr.Arith;
import de.tum.in.jmoped.underbone.expr.Category;
import de.tum.in.jmoped.underbone.expr.Comp;
import de.tum.in.jmoped.underbone.expr.Condition;
import de.tum.in.jmoped.underbone.expr.Dup;
import de.tum.in.jmoped.underbone.expr.Field;
import de.tum.in.jmoped.underbone.expr.If;
import de.tum.in.jmoped.underbone.expr.Inc;
import de.tum.in.jmoped.underbone.expr.Invoke;
import de.tum.in.jmoped.underbone.expr.Jump;
import de.tum.in.jmoped.underbone.expr.Local;
import de.tum.in.jmoped.underbone.expr.Monitorenter;
import de.tum.in.jmoped.underbone.expr.New;
import de.tum.in.jmoped.underbone.expr.Newarray;
import de.tum.in.jmoped.underbone.expr.NotifyType;
import de.tum.in.jmoped.underbone.expr.Npe;
import de.tum.in.jmoped.underbone.expr.Poppush;
import de.tum.in.jmoped.underbone.expr.Print;
import de.tum.in.jmoped.underbone.expr.Return;
import de.tum.in.jmoped.underbone.expr.Unaryop;
import de.tum.in.jmoped.underbone.expr.Value;
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
		BDD b = bdd.or(((BDDSemiring) a).bdd);
		return new BDDSemiring(manager, b);
	}
	
//	/**
//	 * Loads the variables specified by <code>vdoms</code> onto the stack
//	 * of <code>bdd</code>. The first variable from <code>vdoms</code> will
//	 * be the depth-most element.
//	 * 
//	 * @param vdoms the variable domains.
//	 * @return new BDD where the variables are pushed.
//	 */
//	private BDD load(BDD bdd, BDDDomain... vdoms) {
//		
////		log("bdd: %s%n", bdd);
//		/* 
//		 * Prepares stack domains:
//		 * index 0 is stack pointer, last index is top of stack
//		 */ 
//		BDDDomain[] sdoms = new BDDDomain[vdoms.length + 1];
//		sdoms[0] = manager.getStackPointerDomain();
//		int sp = bdd.scanVar(sdoms[0]).intValue();
//		for (int i = 0; i < vdoms.length; i++)
//			sdoms[i + 1] = manager.getStackDomain(sp + i);
//		
//		// Abstracts stack pointer and stack
//		BDD c = abstractVars(bdd, sdoms);
//		
//		/*
//		 *  Updates stack pointer and stack:
//		 *  the depth-most element gets the first variable
//		 */
//		c.andWith(sdoms[0].ithVar(sp + vdoms.length));
//		for (int i = 0; i < vdoms.length; i++) {
//			if (vdoms[i] == null)	// Pushes dummy zero in case of null
//				c.andWith(sdoms[i+1].ithVar(0));
//			else {
//				BDD eq = manager.bddEquals(sdoms[i + 1], vdoms[i]);
////				log("eq: %s%n", eq);
//				c.andWith(eq);
//			}
//		}
//		
////		log("c: %s%n", c);
//		return c;
//	}
	
//	private BDD load(BDD bdd, BDDDomain vdom) {
//		// Gets domains: sp and s[sp]
//		BDDDomain spdom = manager.getStackPointerDomain();
//		int sp = bdd.scanVar(spdom).intValue();
//		BDDDomain s0dom = manager.getStackDomain(sp);
//		
//		// Abstracts sp and s[sp]
//		BDDVarSet abs = spdom.set().unionWith(s0dom.set());
//		BDD c = bdd.exist(abs);
//		abs.free();
//		
//		// Updates stack pointer and stack
//		c.andWith(spdom.ithVar(sp + 1));
//		c.andWith(s0dom.buildEquals(vdom));
//		return c;
//	}
	
	private BDD load(int cat, BDD bdd, BDDDomain vdom1, BDDDomain vdom2) {
		// Gets domains: sp, s[sp], and s[sp+1]
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp);
		BDDDomain s1dom = null;
		if (cat == 2)
			s1dom = manager.getStackDomain(sp + 1);
		
		// Abstracts sp, s[sp], and s[sp+1]
		BDDVarSet abs = spdom.set().unionWith(s0dom.set());
		if (cat == 2)
			abs.unionWith(s1dom.set());
		BDD c = bdd.exist(abs);
		abs.free();
		
		// Updates stack pointer and stack: vdom1 goes to s[sp]
		c.andWith(spdom.ithVar(sp + cat));
		c.andWith(s0dom.buildEquals(vdom1));
		if (cat == 2)
			c.andWith((vdom2 == null) ? s1dom.ithVar(0) : s1dom.buildEquals(vdom2));
		return c;
	}
	
//	/**
//	 * Stores the values at the top of the stack of <code>bdd</code>
//	 * to the variables specified by <code>doms</code>.
//	 * The first variable from <code>doms</code> gets the depth-most element.
//	 * 
//	 * @param doms the vairable domains.
//	 * @return new BDD where the variables get the stack values.
//	 */
//	private BDD store(BDD bdd, BDDDomain... vdoms) {
//		
//		/* 
//		 * Prepares stack domains:
//		 * index 0 is stack pointer, last index is top of stack
//		 */ 
//		BDDDomain[] sdoms = new BDDDomain[vdoms.length + 1];
//		sdoms[0] = manager.getStackPointerDomain();
//		int sp = bdd.scanVar(sdoms[0]).intValue();
//		for (int i = 0; i < vdoms.length; i++)
//			sdoms[i + 1] = manager.getStackDomain(sp - vdoms.length + i);
//		
//		// Abstracts local variables
//		BDD c = abstractVars(bdd, vdoms);
//		
//		/*
//		 *  Copies the stack to variables:
//		 *  the first variable gets the depth-most element
//		 */
//		for (int i = 0; i < vdoms.length; i++) {
//			// Ignores null domain
//			if (vdoms[i] == null)
//				continue;
//			
//			c.andWith(manager.bddEquals(sdoms[i + 1], vdoms[i]));
//		}
//		
//		// Abstracts the stack and updates the stack pointer
//		BDD d = abstractVars(c, sdoms);
//		c.free();
//		d.andWith(sdoms[0].ithVar(sp - vdoms.length));
//		
//		return d;
//	}
	
	private BDD store(int cat, BDD bdd, BDDDomain vdom1, BDDDomain vdom2) {
		// Gets domains: sp, s[sp-1], and s[sp-2]
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - 1);
		BDDDomain s1dom = null;
		if (cat == 2)
			s1dom = manager.getStackDomain(sp - 2);
		
		// Abstracts vdom1 and vdom2
		BDDVarSet abs = vdom1.set();
		if (cat == 2 && vdom2 != null)
			abs.unionWith(vdom2.set());
		BDD c = bdd.exist(abs);
		abs.free();
		
		// Updates the local vars
		if (cat == 1) {
			c.andWith(s0dom.buildEquals(vdom1));
		} else {	// cat == 2
			c.andWith(s1dom.buildEquals(vdom1));
			if (vdom2 != null)
				c.andWith(s0dom.buildEquals(vdom2));
		}
		
		// Abstracts sp, s[sp-1], and s[sp-2]
		abs = spdom.set().unionWith(s0dom.set());
		if (cat == 2)
			abs.unionWith(s1dom.set());
		BDD d = c.exist(abs);
		abs.free();
		c.free();
		
		// Updates sp
		d.andWith(spdom.ithVar(sp - cat));
		return d;
	}
	
	private void log(BDD bdd) {
		if (Sat.debug())
			log("%n\t\t%s%n%n", manager.toString(bdd, "\n\t\t"));
	}
	
	private void logRaw(BDD bdd) {
		if (Sat.all())
			log("%n\t\t%s%n%n", bdd.toStringWithDomains());
	}

	public Semiring extend(Semiring a, CancelMonitor monitor) {
		
		BDDFactory factory = bdd.getFactory();
		if (bdd.isZero()) return new BDDSemiring(manager, factory.zero());
		
		ExprSemiring A = (ExprSemiring) a;
		
		log(bdd);
		logRaw(bdd);
		
		BDDSemiring b = null;
		
		try {
		switch (A.type) {
		
		case ExprType.ARITH:
			b = arith(A); break;
		
		case ExprType.ARRAYLENGTH:
			b = arraylength(A); break;
		
		// Pushes from heap: s0 = heap[s1+s0+1], sp=sp-1;
		case ExprType.ARRAYLOAD:
			b = arrayload(A); break;
		
		// Pops to heap: heap[s2+s1+1]=s0, sp=sp-3;
		case ExprType.ARRAYSTORE:
			b = arraystore(A); break;
		
		case ExprType.CONSTLOAD:
			b = constload(A); break;
			
		case ExprType.CONSTSTORE:
			b = conststore(A); break;
		
		case ExprType.DUP:
			b = dup(A); break;
		
		case ExprType.DYNAMIC:
			b = dynamic(A); break;
			
		// Identity
		case ExprType.ERROR:
			b = error(A); break;
		
		case ExprType.FIELDLOAD:
			b = fieldload(A); break;
		
		case ExprType.FIELDSTORE:
			b = fieldstore(A); break;
		
		// Pushes ret value into the stack
		case ExprType.GETRETURN:
			b = getreturn(A); break;
		
		// Pushes from global variable
		case ExprType.GLOBALLOAD:
			b = globalload(A); break;
		
		// Stores a constant to global variable
		case ExprType.GLOBALPUSH: {
			BDDDomain gdom = manager.getGlobalVarDomain((String) A.value);
			BDD c = abstractVars(bdd, gdom);
			c.andWith(gdom.ithVar((Integer) A.aux));
			b = new BDDSemiring(manager, c);
			break;
		}
		
		// Pops to global variable
		case ExprType.GLOBALSTORE:
			b = globalstore(A); break;
		
		case ExprType.HEAPLOAD:
			b = heapload(A); break;
			
		case ExprType.HEAPOVERFLOW:
			b = heapoverflow(A); break;
			
		// Pops and compares
		case ExprType.IF:
			b = ifExpr(A); break;
		
		// Pops twice and compares s1 with s0
		case ExprType.IFCMP:
			b = ifcmp(A); break;
		
		case ExprType.INC:
			b = inc(A); break;
		
		// Method invocation: (G0,L0,G1,L1) -> (G2,L2,L0,G1,L1)
		case ExprType.INVOKE:
			b = invoke(A); break;
			
		case ExprType.IOOB:
			b = ioob(A); break;
			
		case ExprType.JUMP:
			b = jump(A); break;
		
		// Pushes from local variable
		case ExprType.LOAD:
			b = load(A); break;
		
		case ExprType.MONITORENTER:
			b = monitorenter(A); break;
			
		case ExprType.MONITOREXIT:
			b = monitorexit(A); break;
		
		case ExprType.NEW:
			b = newExpr(A); break;
		
		case ExprType.NEWARRAY:
			b = newarray(A); break;
			
		case ExprType.NOTIFY:
			b = notify(A); break;
			
		case ExprType.NPE:
			b = npe(A); break;
		
		case ExprType.POPPUSH:
			b = poppush(A); break;
		
		case ExprType.PRINT:
			b = print(A); break;
		
		// Pushes constant
		case ExprType.PUSH:
			b = push(A); break;
		
		case ExprType.RETURN:
			b = returnExpr(A); break;
		
		// Pops to local variable
		case ExprType.STORE:
			b = store(A); break;
		
		case ExprType.SWAP:
			b = swap(A); break;
		
		case ExprType.UNARYOP:
			b = unaryop(A); break;
		
		case ExprType.WAITINVOKE:
			b = waitinvoke(A); break;
			
		case ExprType.WAITRETURN:
			b = waitreturn(A); break;
		}
		} catch (Exception e) {
			e.printStackTrace();
			System.out.println(manager.toString(bdd));
			System.out.println(A);
		}
		
//		if (b != null && A.type != ExprType.INVOKE) 
//			manager.store(b.bdd);
		return b;
	}
	
	/**
	 * Performs arithmetic function: s0 = s1 op s0;
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring arith(ExprSemiring A) {
		
		// Gets the current value of stack pointer
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		// Gets the stack domains
		Arith arith = (Arith) A.value;
		Category cat = arith.getCategory();
		BDDDomain v1dom = manager.getStackDomain(sp - cat.intValue()*2);
		BDDDomain v2dom = manager.getStackDomain(sp - cat.intValue()*1);
		BDDDomain tdom = manager.getTempVarDomain();
		
		// Gets all possible value 1
		BDDIterator v1itr = manager.iterator(bdd, v1dom);
		
		BDDFactory factory = bdd.getFactory();
		BDD d = factory.zero();
		while (v1itr.hasNext()) {
			
			BDD e = v1itr.nextBDD();
			long v1 = e.scanVar(v1dom).longValue();
			e.free();
			
			// Gets all possible value 2 values wrt. value 1
			e = bdd.id().andWith(v1dom.ithVar(v1));
			BDDIterator v2itr = manager.iterator(e, v2dom);
			
			// Performs arithmetic function with v1 and v2
			BDD f = factory.zero();
			while (v2itr.hasNext()) {
				
				// Gets a s0 value
				BDD g = v2itr.nextBDD();
				long v2 = g.scanVar(v2dom).longValue();
				g.free();
				
				BDD h = manager.arith(arith.getType(), tdom, v1, v1dom, v2, v2dom);
				f.orWith(v2dom.ithVar(v2).andWith(h));
			}
			d.orWith(v1dom.ithVar(v1).andWith(f));
			e.free();
		}
		d = bdd.id().andWith(d);
		
		// Abstracts stack
		BDDDomain[] sdoms = new BDDDomain[1 + 2*cat.intValue()];
		sdoms[0] = spdom;
		sdoms[1] = v1dom;
		sdoms[2] = v2dom;
		if (cat == Category.TWO) {
			sdoms[3] = manager.getStackDomain(sp - 3);
			sdoms[4] = manager.getStackDomain(sp - 1);
		}
		BDD c = abstractVars(d, sdoms);
		d.free();
		
		// Updates stack
		boolean two = (cat == Category.TWO) && arith.getType() != Arith.CMP;
		c.andWith(spdom.ithVar(sp - 2*cat.intValue() + ((two) ? 2 : 1)));
		c.replaceWith(factory.makePair(tdom, v1dom));
		if (two)
			c.andWith(sdoms[3].ithVar(0));
		
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
			BDD eq = manager.bddEquals(ldom, tdom);
//			log("\t\tldom: %s%n", Arrays.toString(ldom.uvars()));
//			log("\t\ttdom: %s%n", Arrays.toString(tdom.uvars()));
//			log("\t\tbefore: %s%n", c);
//			log("\t\teq: %s%n", eq);
			c.orWith(bdd.id().andWith(s0dom.ithVar(s0)).andWith(eq));
//			log("\t\tafter: %s%n", c);
//			System.out.println(c);
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
			
			while (s0itr.hasNext()) {
			
				// Gets a s0 value
				BDD f = s0itr.nextBDD();
				int s0 = VarManager.decode(f.scanVar(s0dom).longValue(), s0dom);
				f.free();
				log("\t\ts1: %d, s0: %d%n", s1, s0);
				if (s0 < 0) {
					log("\t\tArray bound violation: index %d%n", s0);
					System.err.printf("Array bound violation: index %d%n", s0);
					continue;
				}
				
				// Gets all length values wrt. to s0 and s1
				f = e.id().andWith(s0dom.ithVar(s0));
				BDDDomain ldom = manager.getArrayLengthDomain(s1);
				BDDIterator lptr = manager.iterator(f, ldom);
				while (lptr.hasNext()) {
					BDD g = lptr.nextBDD();
					long l = g.scanVar(ldom).longValue();
					g.free();
					
					// Check array bound
					if (s0 >= l) {
						log("\t\tArray bound violation: length %d, index %d%n", l, s0);
						System.err.printf("Array bound violation: length %d, index %d%n", l, s0);
						continue;
					}
					
					// Gets all possible heap[s1+s0+1] wrt. length, s1, and s0
					g = f.id().andWith(ldom.ithVar(l));
					BDDDomain hdom = manager.getArrayElementDomain(s1, s0);
					BDDIterator hitr = manager.iterator(g, hdom);
					while (hitr.hasNext()) {
						
						// Gets a h value
						BDD x = hitr.nextBDD();
						long h = x.scanVar(hdom).longValue();
						x.free();
						
						d.orWith(tdom.ithVar(h)
								.andWith(hdom.ithVar(h))
								.andWith(ldom.ithVar(l))
								.andWith(s1dom.ithVar(s1))
								.andWith(s0dom.ithVar(s0)));
					}
					g.free();
				}
				f.free();
			}
			e.free();
		}
		BDD c = bdd.id().andWith(d);
		
		// Abstract stack
		Category category = (Category) A.value;
		if (category.one())
			d = abstractVars(c, spdom, s0dom, s1dom);
		else
			d = abstractVars(c, s0dom, s1dom);
		c.free();
		
		// Update stack
		d.replaceWith(factory.makePair(tdom, s1dom));
		if (category.one())
			d.andWith(spdom.ithVar(sp - 1));
		else // category 2
			d.andWith(s0dom.ithVar(0));
		
		return new BDDSemiring(manager, d);
	}
	
	/**
	 * Pops to heap: heap[s2+s1+1]=s0, sp=sp-3;
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring arraystore(ExprSemiring A) {

		// Gets the current value of stack pointer (sp)
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();	
		
		// Gets the stack domains
		int category = ((Category) A.value).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - category);
		BDDDomain s1dom = manager.getStackDomain(sp - category - 1);
		BDDDomain s2dom = manager.getStackDomain(sp - category - 2);
		
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
			
			while (s1itr.hasNext()) {
				
				// Gets a s1 value
				BDD e = s1itr.nextBDD();
				int s1 = VarManager.decode(e.scanVar(s1dom).longValue(), s1dom);
				e.free();
				log("\t\ts2: %d, s1: %d%n", s2, s1);
				
				// Gets all possible length values wrt. s1 and s2
				e = d.id().andWith(s1dom.ithVar(s1));
				BDDDomain ldom = manager.getArrayLengthDomain(s2);
				BDDIterator lptr = manager.iterator(e, ldom);
				while (lptr.hasNext()) {
					
					// Gets a length value
					BDD f = lptr.nextBDD();
					int l = f.scanVar(ldom).intValue();
					f.free();
					
					// Check array bound
					if (s1 < 0 || s1 >= l) {
						log("\t\tArray bound violation: length %d, index %d%n", l, s1);
						System.err.printf("Array bound violation: length %d, index %d%n", l, s1);
						continue;
					}
					
					// Gets all possible s0 wrt. length, s1, and s2
					f = e.id().andWith(ldom.ithVar(l));
					BDDDomain hdom = manager.getArrayElementDomain(s2, s1);
					
					BDDIterator s0itr = manager.iterator(f, s0dom);
					while (s0itr.hasNext()) {
						
						// Gets a s0 value
						BDD g = s0itr.nextBDD();
						long s0 = g.scanVar(s0dom).longValue();
						g.free();
						log("\t\ts0: %d%n", s0);
						
						// Prunes the bdd to only for s0, length, s1, and s2
						g = f.id().andWith(s0dom.ithVar(s0));
						
						// Updates the heap at the pruned bdd
						BDD x = g.exist(hdom.set());
						c.orWith(x.andWith(hdom.ithVar(s0)));
						g.free();
					}
					f.free();
				}
				e.free();
			}
			d.free();
		}
		
		// Abstracts stack
		log("\t\tAbstracting stack%n");
		BDDDomain[] sdoms = new BDDDomain[category + 3];
		sdoms[0] = spdom;
		sdoms[1] = s2dom;
		sdoms[2] = s1dom;
		sdoms[3] = s0dom;
		if (category == 2)
			sdoms[4] = manager.getStackDomain(sp - 1);
		BDD d = abstractVars(c, sdoms);
		c.free();
		
		// Updates stack
		d.andWith(spdom.ithVar(sp - category - 2));
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
		Field field = (Field) A.value;
		int raw = manager.getConstant(field.getName());
		
		// Abstracts the stack
		int category = field.getCategory().intValue();
		BDDDomain[] sdoms = new BDDDomain[category + 1];
		sdoms[0] = spdom;
		sdoms[1] = sdom;
		if (field.categoryTwo()) 
			sdoms[2] = manager.getStackDomain(sp + 1);
		BDD d = abstractVars(c, sdoms);
		c.free();
		
		// Updates the stack pointer and the stack
		d.andWith(spdom.ithVar(sp + category));
		d.andWith(sdom.ithVar(VarManager.encode(raw, sdom)));
		if (field.categoryTwo())
			d.andWith(sdoms[2].ithVar(0));
		
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
		
		// Gets the stack pointer domain and the stack domain
		Field field = (Field) A.value;
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		int category = field.getCategory().intValue();
		BDDDomain sdom = manager.getStackDomain(sp - category);
		
		// Stores the constant value
		long s = bdd.scanVar(sdom).longValue();
		manager.putConstant(field.getName(), VarManager.decode(s, sdom));
		
		// Updates the stack
		BDDDomain[] sdoms = new BDDDomain[category + 1];
		sdoms[0] = spdom;
		sdoms[1] = sdom;
		if (field.categoryTwo()) 
			sdoms[2] = manager.getStackDomain(sp - 1);
		BDD d = abstractVars(c, sdoms);
		c.free();
		
		// Updates the stack pointer
		d.andWith(spdom.ithVar(sp - category));
		
		return new BDDSemiring(manager, d);
	}
	
	/**
	 * sp = sp - 1;
	 * 
	 * @param A
	 * @return
	 */
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
		
		// Gets the stack pointer
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		// Duplicates
		Dup dup = (Dup) A.value;
		BDDFactory factory = bdd.getFactory();
		BDD c = bdd.id();
		for (int i = 0; i < dup.down; i++)
			c.replaceWith(factory.makePair(
				manager.getStackDomain(sp - i - 1), 
				manager.getStackDomain(sp + dup.push - i - 1)));
		for (int i = 0; i < dup.push; i++)
			c.andWith(manager.bddEquals(
					manager.getStackDomain(sp - dup.down + i), 
					manager.getStackDomain(sp + i)));
		BDD tmp = abstractVars(c, spdom).andWith(spdom.ithVar(sp + dup.push));
		c.free();
		c = tmp;
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring error(ExprSemiring A) {
		return new BDDSemiring(manager, bdd.id());
	}
	
	/**
	 * Pushes the field of the instance s0.
	 * <code>A.value</code> specifies the field.
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring fieldload(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		c.free();
		
		// The field
		Field field = (Field) A.value;
		
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
			BDDDomain hdom = manager.getHeapDomain(s0 + field.getId());
//			log("\t\thdom: %s%n", Arrays.toString(hdom.vars()));
			BDDIterator hitr = manager.iterator(d, hdom);
			while (hitr.hasNext()) {
				
				// Saves field value to temp and conjuncts with s0 and h
				e = hitr.nextBDD();
				long h = e.scanVar(hdom).longValue();
				e.free();
				
//				log("\t\td: %s%n", d);
				BDD x = hdom.ithVar(h);
//				log("\t\tx: %s%n", x);
				BDD y = tdom.ithVar(h);
//				log("\t\ty: %s%n", y);
				
				BDD z = d.id().andWith(x);
//				log("\t\tz: %s%n", z);
				
				z.andWith(y);
//				log("\t\tz: %s%n", z);
				
				c.orWith(z);
//				log("\t\tPush %d%n", h);
			}
			d.free();
		}
		
		// NPE
		if (c.isZero()) {
			log("\t\tZero BDD%n");
			return new BDDSemiring(manager, c);
		}
		
		// Abstracts s0
		BDD d = abstractVars(c, s0dom);
		c.free();
		
		// Replace temp with s0
		d.replaceWith(bdd.getFactory().makePair(tdom, s0dom));
		
		// Pushes one more if the field is of category 2
		if (field.categoryTwo()) {
			s0dom = manager.getStackDomain(sp);
			c = abstractVars(d, spdom, s0dom);
			d.free();
			c.andWith(spdom.ithVar(sp + 1)).andWith(s0dom.ithVar(0));
			d = c;
		}
		
		return new BDDSemiring(manager, d);
	}
	
	/**
	 * Stores s0 into the field of the instance s1.
	 * <code>A.value</code> specifies the field.
	 * 
	 * @param A
	 * @return
	 */
	private BDDSemiring fieldstore(ExprSemiring A) {
		
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		c.free();
		
		// The field
		Field field = (Field) A.value;
		
		// Gets stack domains
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain vdom = manager.getStackDomain(field.categoryTwo() ? sp - 2 : sp - 1);
		BDDDomain rdom = manager.getStackDomain(field.categoryTwo() ? sp - 3 : sp - 2);
		
		// Gets all possible references
		BDDIterator ritr = manager.iterator(bdd, rdom);
		c = bdd.getFactory().zero();
		while (ritr.hasNext()) {
			
			// Gets a reference
			BDD e = ritr.nextBDD();
			long r = e.scanVar(rdom).longValue();
			e.free();
			
			// Gets the heap domain at referece + id
			BDD d = bdd.id().andWith(rdom.ithVar(r));
			BDDDomain hdom = manager.getHeapDomain(r + field.getId());
			
			// Gets all possible values wrt. the references
			BDDIterator vitr = manager.iterator(d, vdom);
			while (vitr.hasNext()) {
				
				// Gets a value
				e = vitr.nextBDD();
				long v = e.scanVar(vdom).longValue();
				log("\t\tref: %d, value:%d%n", r, v);
				e.free();
				
				// Prunes the bdd to only for s0 and s1
				e = d.id().andWith(vdom.ithVar(v));
				
				// Abstracts the heap domain of the pruned bdd and updates to s0
				c.orWith(e.exist(hdom.set())
						.andWith(hdom.ithVar(v)));
				e.free();
			}
			d.free();
		}
		
		// Abstracts stack
		int category = field.getCategory().intValue();
		BDDDomain[] adoms = new BDDDomain[category + 2];
		adoms[0] = spdom;
		adoms[1] = vdom;
		adoms[2] = rdom;
		if (field.categoryTwo()) adoms[3] = manager.getStackDomain(sp - 1);
		BDD d = abstractVars(c, adoms);
		c.free();
		
		// Updates the stack pointer
		d.andWith(spdom.ithVar(sp - category - 1));
		
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring getreturn(ExprSemiring A) {
		int cat = ((Category) A.value).intValue();
		
		BDDDomain rdom = manager.getRetVarDomain();
		BDD d = load(cat, bdd, rdom, null);
		BDD c = abstractVars(d, rdom);
		d.free();
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring globalload(ExprSemiring A) {
		// Checks condition
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		
		// Loads
		Field field = (Field) A.value;
		BDD d = load(field.getCategory().intValue(), c, 
				manager.getGlobalVarDomain(field.getName()), null);
		c.free();
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring globalstore(ExprSemiring A) {
		// Checks condition
		BDD c = fulfillsCondition(A);
		if (c.isZero())
			return new BDDSemiring(manager, c);
		
		Field field = (Field) A.value;
		BDDDomain gdom = manager.getGlobalVarDomain(field.getName());
		
		// Stores
		BDD d = store(field.getCategory().intValue(), c, gdom, null);
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
		Integer type = (Integer) A.value;
		if (type == ExprType.NEW) {
			
			New n = (New) A.aux;
			
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
		Newarray newarray = (Newarray) A.aux;
		
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
		BDD c = bdd.id().andWith(manager.ifBDD((If) A.value, sdom));
		
		// Returns if the trimmed BDD is zero
		if (c.isZero())
			return new BDDSemiring(manager, c);
		
		// Updates stack
		BDD d = abstractVars(c, spdom, sdom).andWith(spdom.ithVar(sp));
		c.free();
		
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring ifcmp(ExprSemiring A) {
		
		// Gets the current value of stack pointer
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		// Gets the stack domains
		BDDDomain s0dom = manager.getStackDomain(sp - 1);
		BDDDomain s1dom = manager.getStackDomain(sp - 2);
		
		Integer type = (Integer) A.value;
		BDD c;
		if (type == Comp.EQ)
			c = manager.bddEquals(s1dom, s0dom);
		else if (type == Comp.NE)
			c = manager.bddNotEquals(s1dom, s0dom);
		else {
			c = manager.getFactory().zero();
			
			// Gets all possible s1 values
			BDDIterator s1itr = manager.iterator(bdd, s1dom);
			while (s1itr.hasNext()) {
				
				// Gets an s1 value
				BDD d = s1itr.nextBDD();
				long s1 = d.scanVar(s1dom).longValue();
				d.free();
				
				// Gets all possible s0 values wrt. s1
				d = bdd.id().andWith(s1dom.ithVar(s1));
				BDDIterator s0itr = manager.iterator(d, s0dom);
				while (s0itr.hasNext()) {
					
					// Gets an s0 value
					BDD e = s0itr.nextBDD();
					long s0 = e.scanVar(s0dom).longValue();
					e.free();
					
					// Decodes
					long ds1 = VarManager.decode(s1, s1dom);
					long ds0 = VarManager.decode(s0, s0dom);
					
					boolean valid = false;
					switch (type) {
					case Comp.LT:
						if (ds1 < ds0) valid = true;
						break;
					case Comp.GE:
						if (ds1 >= ds0) valid = true;
						break;
					case Comp.GT:
						if (ds1 > ds0) valid = true;
						break;
					case Comp.LE:
						if (ds1 <= ds0) valid = true;
						break;
					}
					
					if (valid) {
						c.orWith(s1dom.ithVar(s1).andWith(s0dom.ithVar(s0)));
					}
				}
			}
		}
		c = bdd.id().andWith(c);
		if (c.isZero()) return new BDDSemiring(manager, c);
		
		// Abstracts stack
		BDD d = abstractVars(c, spdom, s1dom, s0dom);
		c.free();
		
		// Updates stack
		d.andWith(spdom.ithVar(sp - 2));
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring inc(ExprSemiring A) {
		
		// Gets lv domain at index
		Inc inc = (Inc) A.value;
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
		
		int nargs = ((Invoke) A.value).nargs;
		BDD c = fulfillsCondition(A);
		if (c.isZero()) {
			log("\t\tNOT fulfillsCondition%n");
			return new BDDSemiring(manager, c);
		}
		
//		// Abstracts G3
//		if (manager.multithreading() && manager.lazy()) {
//			BDD d = c.exist(manager.getG3VarSet());
//			c.free();
//			c = d;
//		}
		
		// G0 becomes G2
//		log("\t\tc: %s%n", c);
		c.replaceWith(manager.getG0pairG2());
//		log("\t\tpair: %s%n", manager.getG0pairG2());
//		log("\t\tc: %s%n", c);
		if (nargs == 0) return new BDDSemiring(manager, c);
			
		// Gets the current value of stack pointer (sp)
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		c.andWith(manager.bddL0equalsL2params(sp-nargs, nargs));
		
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
		Npe ioob = (Npe) A.value;
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
	
	private BDDSemiring jump(ExprSemiring A) {
		BDD c = fulfillsCondition(A);
		if (c.isZero())
			return new BDDSemiring(manager, c);
		
		Jump type = (Jump) A.value;
		if (type.equals(Jump.ONE))
			return new BDDSemiring(manager, c);
		else {	// Jump.THROW
			
			// Gets stack domains
			BDDDomain spdom = manager.getStackPointerDomain();
			int sp = bdd.scanVar(spdom).intValue() - 1;
			BDDDomain s0dom = manager.getStackDomain(sp);
			
			/*
			 *  Abstracts the error var, and if sp > 0 
			 *  also abstracts all stack elements below sp, and the stack pointer.
			 */
			BDDDomain[] doms = new BDDDomain[sp + ((sp > 0) ? 2 : 1)];
			for (int i = 0; i < sp; i++)
				doms[i] = manager.getStackDomain(i);
			doms[sp] = manager.getGlobalVarDomain(Remopla.e);
			if (sp > 0) doms[sp + 1] = spdom;
					
			BDD d;
			if (sp > 0) d = abstractVars(c, doms);
			else d = abstractVars(c, doms[sp]);
			
			// Replaces the bottom element with s0 and set the stack pointer to 1
			if (sp > 0) {
				d.replaceWith(bdd.getFactory().makePair(s0dom, doms[0]))
						.andWith(spdom.ithVar(1));
			}
			
			// Resets the error status
			d.andWith(doms[sp].ithVar(0));
			return new BDDSemiring(manager, d);
		}
	}
	
	private BDDSemiring load(ExprSemiring A) {
		Local local = (Local) A.value;
		
		BDD c = load(local.getCategory().intValue(), bdd,
				manager.getLocalVarDomain(local.index), 
				manager.getLocalVarDomain(local.index + 1));
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
			
			e = d.id().andWith(thdom.ithVar(th));
			
			long max = 0;
			BDDIterator cntitr = manager.iterator(e, cntdom);
			while (cntitr.hasNext()) {
				BDD f = cntitr.nextBDD();
				long cnt = f.scanVar(cntdom).longValue();
				f.free();
				if (cnt > max) max = cnt;
			}
			
			// Gets all possible counter values wrt. s0 and thread id
			cntitr = manager.iterator(e, cntdom);
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
		
		Monitorenter expr = (Monitorenter) A.value;
		if (expr.type == Monitorenter.Type.POP 
				|| expr.type == Monitorenter.Type.TOUCH) {
		
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
			if (expr.type == Monitorenter.Type.POP) {
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
		New n = (New) A.value;
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
		Newarray newarray = (Newarray) A.value;
		
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
				if (blocksize >= manager.size())
					throw new RemoplaError("Not enough bits. An array is of " +
							"size %d, in which %d bits are not enough.", 
							blocksize, manager.getBits());
				for (int j = 0; j < blocknum; j++) {
					
					// Remember the index
					indices.offer(ptr);
					
					// Fills the array type
					if (newarray.types[newarray.dim-i] >= manager.size())
						throw new RemoplaError("Not enough bits. " +
								"There are at least %d object types.", 
								newarray.types[newarray.dim-i]);
					BDDDomain hdom = manager.getHeapDomain(ptr++);
					e.andWith(hdom.ithVar(newarray.types[newarray.dim-i]));
					log("\t\tptr: %d%n", ptr);
					
					// Updtes ptr wrt. owner & counter
					for (int k = 2; k < manager.getArrayAuxSize(); k++)
						e.andWith(manager.getHeapDomain(ptr++).ithVar(0));
					
					// Fills the array length
					hdom = manager.getHeapDomain(ptr++);
					e.andWith(hdom.ithVar(blocksize));
					
					// Fills the array elements
					for (int k = 0; k < blocksize; k++) {
						// Initializes the array values
						hdom = manager.getHeapDomain(ptr++);
						BDD value;
						if (i == 1) {
							value = bddOf(newarray.init, hdom);
						} 
						
						// Initializes the array indices
						else {
							int index = indices.remove();
							value = hdom.ithVar(index);
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
		
		NotifyType type = (NotifyType) A.value;
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
				
				if (type == NotifyType.NOTIFY) {
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
			
			if (type == NotifyType.NOTIFYALL) {
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
		
		Npe npe = (Npe) A.value;
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - npe.depth - 1);
		
		return new BDDSemiring(manager, bdd.id().andWith(s0dom.ithVar(0)));
	}
	
	private BDDSemiring poppush(ExprSemiring A) {
		
		BDDDomain spdom = manager.getStackPointerDomain();
		
		// Changes nothing, if neither pop nor push
		Poppush poppush = (Poppush) A.value;
		if (poppush.nochange())
			return new BDDSemiring(manager, bdd.id());
		
		// Gets the current value of stack pointer (sp)
		int sp = bdd.scanVar(spdom).intValue();
		
		// Abstracts stack pointer and stack elements
		BDDDomain[] d = new BDDDomain[poppush.pop + 1];
		d[0] = spdom;
		for (int i = 1; i <= poppush.pop; i++)
			d[i] = manager.getStackDomain(sp - i);
		BDD c = abstractVars(bdd, d);
		
		// Updates the stack pointer
		sp = sp - poppush.pop + poppush.push;
		c.andWith(spdom.ithVar(sp));
		
		for (int i = 1; i <= poppush.push; i++)
			c.andWith(manager.getStackDomain(sp - i).ithVar(0));
		
		// FIXME prohibits non-determinism
//		if (push && manager.multithreading() /*&& !manager.symbolic()*/) {
//			c.andWith(manager.getStackDomain(sp - 1).ithVar(0));
//		}
		
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring print(ExprSemiring A) {
		
		// Gets iterator for s0
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp - 1);
		
		BDD c;
		Print print = (Print) A.value;
		StringBuilder out = new StringBuilder();
		if (print.type == Print.NOTHING) {
			// Updates stack
			c = abstractVars(bdd, spdom, s0dom);
			c.andWith(spdom.ithVar(sp - 1));
		} else {
			boolean nd = false;
			BDDIterator s0itr = manager.iterator(bdd, s0dom);
			while (s0itr.hasNext()) {
				
				// Gets a s0 value
				c = s0itr.nextBDD();
				long s0 = c.scanVar(s0dom).longValue();
				c.free();
				
				// Appends s0 to out
				Object decoded = null;;
				switch (print.type) {
				case Print.INTEGER: decoded = VarManager.decode(s0, s0dom); break;
				case Print.FLOAT: decoded = manager.decodeFloat(s0); break;
				case Print.CHARACTER: decoded = (char) s0; break;
				case Print.STRING: decoded = manager.decodeString(s0); break;
				}
				out.append(decoded);
				if (s0itr.hasNext()) {
					nd = true;
					out.append(" ");
				}
			}
			if (nd) {
				out.insert(0, "[");
				out.append("]");
			}
			
			// Updates stack
			c = abstractVars(bdd, spdom, s0dom, manager.getStackDomain(sp - 2));
			c.andWith(spdom.ithVar(sp - 2));
		}
		
		// Prints out
		System.out.print(out);
		if (print.newline) System.out.println();
		
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring push(ExprSemiring A) {
		// Checks condition
		BDD c = fulfillsCondition(A);
		if (c.isZero()) 
			return new BDDSemiring(manager, c);
		
		// Gets the current value of stack pointer
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = c.scanVar(spdom).intValue();
		BDDDomain s0dom = manager.getStackDomain(sp);
		
		// Abstracts the stack
		Value value = (Value) A.value;
		int category = value.getCategory().intValue();
		BDDVarSet varset = spdom.set().unionWith(s0dom.set());
		if (category == 2)
			varset.unionWith(manager.getStackDomain(sp + 1).set());
		BDD d = c.exist(varset);
		c.free();
		
		// Updates the stack
		d.andWith(spdom.ithVar(sp + category));
		d.andWith(bddOf(value, s0dom));
		if (category == 2)
			d.andWith(manager.getStackDomain(sp + 1).ithVar(0));
		return new BDDSemiring(manager, d);
	}
	
	private BDDSemiring returnExpr(ExprSemiring A) {
		BDD c;
		Return ret = (Return) A.value;
		if (ret.type == Return.Type.VOID) {
			c = manager.abstractLocals(bdd);
		} else {	// if (ret.type == Return.Type.SOMETHING) {
			// Gets the pointer to the stack element
			BDDDomain spdom = manager.getStackPointerDomain();
			int sp = bdd.scanVar(spdom).intValue() - ret.getCategory().intValue();
			
			// Prepares the pair: seDom -> retDom
			BDDDomain seDom = manager.getStackDomain(sp);
			BDDPairing pair = bdd.getFactory().makePair(seDom, manager.getRetVarDomain());
			
			// Updates the return variable
			BDD d = bdd.id().replaceWith(pair);
			c = manager.abstractLocals(d);
			d.free();
		} 
//		else {	// Return.Type.THROW
//			Return.ThrowInfo t = ret.getThrowInfo();
//			
//			// Gets the stack pointer
//			BDDDomain spdom = manager.getStackPointerDomain();
//			int sp = bdd.scanVar(spdom).intValue();
//			
//			// Gets the stack element where the instance is stored
//			BDDDomain sdom = manager.getStackDomain(sp - 1);
//			
//			BDDDomain vdom = manager.getGlobalVarDomain(t.var);
//			BDD d = abstractVars(bdd, vdom);
//			
//			// Loops for all possible instances
//			BDDIterator sitr = manager.iterator(d, sdom);
//			c = bdd.getFactory().zero();
//			while (sitr.hasNext()) {
//				
//				// Gets an instance
//				BDD e = sitr.nextBDD();
//				long s = e.scanVar(sdom).longValue();
//				e.free();
//				
//				// Gets all possible ids for this instance
//				BDDDomain hdom = manager.getHeapDomain(s);
//				e = d.id().andWith(sdom.ithVar(s));
//				BDDIterator hitr = manager.iterator(e, hdom);
//				while (hitr.hasNext()) {
//					
//					// Gets an id
//					BDD f = hitr.nextBDD();
//					int h = f.scanVar(hdom).intValue();
//					f.free();
//					
//					// Bypasses if the id is not contained in the condition value
//					if (t.set.contains(h)) {
//						log("\t\tbypassing id %d%n", h);
//						continue;
//					}
//					
//					// Prunes the bdd for this id
//					c.orWith(d.id().andWith(sdom.ithVar(s))
//							.andWith(hdom.ithVar(h))
//							.andWith(vdom.ithVar(s)));
//				}
//				e.free();
//			}
//			if (c.isZero())
//				return new BDDSemiring(manager, c);
//			
//		}
//		log("g1l1_g2l2: %s%n", manager.getG1L1pairG2L2());
		c.replaceWith(manager.getG1L1pairG2L2());
		
		// Debug: prints ret values
//		log("\t\tret:");
//		BDDIterator itr = manager.iterator(c, manager.getRetVarDomain());
//		while (itr.hasNext()) {
//			BDD d = itr.nextBDD();
//			log(" %d", d.scanVar(manager.getRetVarDomain()));
//			d.free();
//		}
//		log("%n");
		
//		Sat.logger.fine(String.format("bdd: %s%n", bdd.toStringWithDomains()));
//		Sat.logger.fine(String.format("c: %s%n", c.toStringWithDomains()));
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring store(ExprSemiring A) {
		Local local = (Local) A.value;
		BDD c = store(local.getCategory().intValue(), bdd, 
				manager.getLocalVarDomain(local.index), 
				manager.getLocalVarDomain(local.index + 1));
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring swap(ExprSemiring A) {
		
		// Gets the current value of stack pointer (sp)
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		// Prepares domains
		BDDDomain s0dom = manager.getStackDomain(sp - 1);
		BDDDomain s1dom = manager.getStackDomain(sp - 2);
		BDDDomain tdom = manager.getTempVarDomain();
		
		// s0dom -> tdom
		BDDFactory factory = bdd.getFactory();
		BDD c = bdd.id().replaceWith(factory.makePair(s0dom, tdom));
		
		// s1dom -> s0dom
		c.replaceWith(factory.makePair(s1dom, s0dom));
		
		// tdom -> s1dom
		c.replaceWith(factory.makePair(tdom, s1dom));
		
		return new BDDSemiring(manager, c);
	}
	
	private BDDSemiring unaryop(ExprSemiring A) {
		
		// Narrows: D2F, L2I
		Unaryop unaryop = (Unaryop) A.value;
		if (unaryop.type == Unaryop.Type.D2F
				|| unaryop.type == Unaryop.Type.L2I)
			return poppush(new ExprSemiring(ExprType.POPPUSH, new Poppush(1, 0)));
		
		// Widens: F2D, I2L
		if (unaryop.type == Unaryop.Type.F2D
				|| unaryop.type == Unaryop.Type.I2L)
			return push(new ExprSemiring(ExprType.PUSH, 
					new Value(Category.ONE, 0)));
		
		// Gets the current value of stack pointer
		BDDDomain spdom = manager.getStackPointerDomain();
		int sp = bdd.scanVar(spdom).intValue();
		
		// Gets the stack domains
		
		BDDDomain vdom = manager.getStackDomain(sp - unaryop.type.pop.intValue());
		BDDDomain tdom = manager.getTempVarDomain();
		
		// Gets all possible s0 values
		BDDFactory factory = bdd.getFactory();
		BDD c = factory.zero();
		BDDIterator vitr = manager.iterator(bdd, vdom);
		
		while (vitr.hasNext()) {
			
			// Gets a s0 value
			BDD d = vitr.nextBDD();
			long v = d.scanVar(vdom).longValue();
			d.free();
			
			long t = -1;
			switch (unaryop.type) {
			case INEG:
			case LNEG:
				t = manager.neg(v);
				break;
			case DNEG:
			case FNEG:
				t = manager.fneg(v, vdom);
				break;
			case D2I:
			case D2L:
			case F2I:
			case F2L:
				t = VarManager.encode((int) manager.decodeFloat(v), vdom);
				break;
			case I2D:
			case I2F:
			case L2D:
			case L2F:
				t = manager.encode((float) v, vdom);
				break;
			case CONTAINS:
				t = (unaryop.set.contains((int) v)) ? 1 : 0;
				break;
			}
			c.orWith(tdom.ithVar(t).andWith(vdom.ithVar(v)));
		}
		c = bdd.id().andWith(c);
		
		// Abstracts stack
		ArrayList<BDDDomain> sdoms = new ArrayList<BDDDomain>();
		sdoms.add(vdom);
		if (unaryop.type.pop != unaryop.type.push) {
			sdoms.add(spdom);
			if (unaryop.type.pop.one())	// && unaryop.type.push == 2
				sdoms.add(manager.getStackDomain(sp));
			else	// unaryop.type.pop == 2 && unaryop.type.push == 1
				sdoms.add(manager.getStackDomain(sp - 1));
		}
		BDD d = abstractVars(c, sdoms.toArray(new BDDDomain[sdoms.size()]));
		c.free();
		
		// Updates stack
		d.replaceWith(factory.makePair(tdom, vdom));
		if (unaryop.type.pop != unaryop.type.push) {
			if (unaryop.type.pop.one()) {	// && unaryop.type.push == 2
				d.andWith(spdom.ithVar(sp + 1));
				d.andWith(manager.getStackDomain(sp).ithVar(0));
			} else {	// unaryop.type.pop == 2 && unaryop.type.push == 1
				d.andWith(spdom.ithVar(sp - 1));
			}
		}
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
	public Set<Long> valuesOf(BDDDomain dom) {
		
		return manager.valuesOf(bdd, dom);
	}
	
	/**
	 * Returns the BDD with variables specified by <code>dom</code>
	 * representing <code>value</code>.
	 * 
	 * @param value the value.
	 * @param dom the BDD domain.
	 * @return the BDD representing the value.
	 */
	public BDD bddOf(Value value, BDDDomain dom) {
		
		// All values
		if (value.all()) {
			return bdd.getFactory().one();
		} 
		
		// Deterministic values
		if (value.deterministic()) {
			long v;
			if (value.isInteger()) {
				v = VarManager.encode(value.intValue(), dom);
			} else if (value.isReal()) {
				v = manager.encode(value.floatValue(), dom);
			} else {	// value.isString();
				v = manager.encode(value.stringValue(), dom);
			}
			return dom.ithVar(v);
		}
		
		// Nondeterministic, but not all
		if (value.isReal())
			return manager.bddRange(dom, value.floatValue(), value.next, 
					value.to.floatValue());
			
		if (Sat.all())
			log("\t\tvalue.intValue(): %d, value.to.intValue(): %d%n",
					value.intValue(), value.to.intValue());
		return manager.bddRange(dom, value.intValue(), value.to.intValue());
	}
	
	/**
	 * Abstract the variables specified by doms from bdd.
	 * The method ignores null domains, 
	 * however the first domain must not be null.
	 * 
	 * @param bdd the BDD.
	 * @param doms the BDD domains.
	 * @return new abstracted BDD.
	 */
	public static BDD abstractVars(BDD bdd, BDDDomain... doms) {
		
		if (doms.length == 0) return bdd.id();
		
		BDDVarSet abs = doms[0].set();
		for (int i = 1; i < doms.length; i++) {
			if (doms[i] != null)
				abs.unionWith(doms[i].set());
		}
		BDD out = bdd.exist(abs);
		abs.free();
		
		return out;
	}
	
	/**
	 * (G0,G2,L2) + (G2,L2,L0,G1,L1) -> (G0,L0,G1,L1)
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
		
//		manager.store(c);
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
		int type = cond.getType();
		if (type == Condition.CONTAINS 
				|| type == Condition.NOTCONTAINS) {
			
			Set<Integer> set = cond.getSetValue();
			
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
					if (type == Condition.CONTAINS && !set.contains(h)) {
						log("\t\tbypassing id %d%n", h);
						continue;
					}
					if (type == Condition.NOTCONTAINS && set.contains(h)) {
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
		BDDDomain gdom = manager.getGlobalVarDomain(cond.getStringValue());
		int g = bdd.scanVar(gdom).intValue();
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
			id = ((Field) A.value).categoryTwo() ? 3 : 2;
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
		
		int nargs = ((Invoke) A.value).nargs;
		
		if (nargs == 0) {
			for (int i = 0; i < manager.getMaxLocalVars(); i++)
				c.andWith(manager.getLocalVarDomain(i).ithVar(0));
			d = manager.abstractStack(c);
			c.free();
			d.andWith(manager.buildG0L0equalsG1L1().id());
//			manager.store(d);
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
		
		// For lazy splitting
		if (manager.lazy()) return lift2(); 
		
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
