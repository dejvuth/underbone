package de.tum.in.jmoped.underbone;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.tum.in.jmoped.underbone.expr.Arith;
import de.tum.in.jmoped.underbone.expr.If;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDPairing;
import net.sf.javabdd.BDDVarSet;
import net.sf.javabdd.BDD.BDDIterator;

/**
 * The manager that works on the level of BDD domains for managing variables
 * during the analysis.
 * 
 * @author suwimont
 *
 */
public class DomainManager extends BDDManager {
	
	// Domains of all variables
	protected BDDDomain[] doms;
	
	// Stack pointer domain index
	protected int spDomIndex;
	
	// Stack domain index
	protected int sDomIndex;
	
	// Local variable domain index
	protected int lvDomIndex;
	
	// Return variable domain index
	private int retDomIndex;
	
	// Heap pointer domain index
	private int hpDomIndex;
	
	// Heap domain index
	private int hDomIndex;
	
	/**
	 * Number of globals: global vars + heap pointer + heap
	 */
	int gnum;
	
	/** 
	 * Maps a domain index of a variable to a variable set 
	 * of all variables without that variable.
	 * Use for abstracting other variables away. 
	 */
	private HashMap<Integer, BDDVarSet> varSetWithout;
	
	public static boolean cache = true;

	/**
	 * Constructs a variable manager.
	 * 
	 * @param bddpackage the BDD package: "cudd" or "java".
	 * @param nodenum the estimated number of BDD nodes.
	 * @param cachesize the cache size.
	 * @param bits the number of variable bits.
	 * @param heapSizes the heap sizes.
	 * @param g the global variables.
	 * @param smax the maximum stack depth.
	 * @param lvmax the maximum number of local variables.
	 * @param tbound the thread bound.
	 * @param lazy lazy splitting?
	 */
	public DomainManager(String bddpackage, int nodenum, int cachesize, 
			int bits, long[] heapSizes, Collection<Variable> g, 
			int smax, int lvmax, int tbound, boolean lazy) {
		// Calls super
		super(bddpackage, nodenum, cachesize, bits, g,
				(heapSizes == null) ? 0 : heapSizes.length, 
				smax, lvmax, tbound, lazy);
		
		if (debug())
			log("bits: %d, heapSizes: %s, g: %s, smax: %s, lvmax: %d, tbound %d%n",
					bits, Arrays.toString(heapSizes), g, smax, lvmax, tbound);
		long size = 1 << bits;
		
		// Prepares array for domains
		int s = smax + varcopy*lvmax;
		if (smax > 0) s++;	// for stack pointer
		
		if (heaplength > 1) s += globalcopy*(heaplength + 1);
		if (g != null && !g.isEmpty()) {
			s += globalcopy*g.size();
		}
		s++;	// ret var
		long[] domSize = new long[s];
		
		// Global variables
		int index = 0;
		if (g != null && !g.isEmpty()) {
			for (Variable v : g) {
				v.setIndex(index);
				if (debug()) log("%s (%d)%n", v.name, v.getIndex());
				long gsize = 1 << v.getBits(bits);
				for (int i = 0; i < globalcopy; i++)
					domSize[index++] = gsize;
				gnum++;
			}
		}
		
		// Heap
		if (heaplength > 1) {
			
			// Heap pointer
			hpDomIndex = index;
			if (debug()) log("heap pointer (%d)%n", index);
			for (int i = 0; i < globalcopy; i++)
				domSize[index++] = size;
			gnum++;
			
			// Heap: at zero
			hDomIndex = index;
			if (debug()) log("heap[0] (%d)%n", index);
			for (int j = 0; j < globalcopy; j++)
				domSize[index++] = 2;
			gnum++;
			
			// Heap: the rest
			for (int i = 1; i < heaplength; i++) {
				
				if (debug()) log("heap[%d] - index: %d, size: %d%n", i, index, heapSizes[i]);
				for (int j = 0; j < globalcopy; j++)
					domSize[index++] = heapSizes[i];
				gnum++;
			}
		} else {
			
			hpDomIndex = -1;
			hDomIndex = -1;
		}
		
		// Local vars
		l0 = index;
		if (lvmax > 0) {
			
			lvDomIndex = index;
			for (int i = 0; i < lvmax; i++) {
				if (debug()) log("lv%d (%d)%n", i, index);
				for (int j = 0; j < varcopy; j++)
					domSize[index++] = size;
			}
		} else {
			lvDomIndex = -1;
		}
		
		// Stack
		if (smax > 0) {
			
			// Stack pointer
			if (debug()) log("stack pointer (%d)%n", index);
			spDomIndex = index;
			domSize[index++] = smax + 1;
			
			// Stack element
			sDomIndex = index;
			for (int i = 0; i < smax; i++) {
				if (debug()) log("stack%d (%d)%n", i, index);
				domSize[index++] = size;//(cache) ? 32 : size;
			}
		} else {
			spDomIndex = -1;
			sDomIndex = -1;
		}
		
		// Return and temp variable
		retDomIndex = index;
		domSize[index++] = size;
		
		// Constructs domains
		doms = factory.extDomain(domSize);
		
		if (debug()) {
			log("%n");
			for (int i = 0; i < doms.length; i++)
				log("doms[%d]:%s%n", i, Arrays.toString(doms[i].vars()));
		}
	}
	
	/**
	 * Initializes variables.
	 */
	public BDD initVars() {
		
		// Initializes G3 (instead of G0) in case of lazy splitting
		int shifted = (multithreading() && lazy()) ? gindex[3] : 0;
		
		// Initializes global variables
		BDD a = factory.one();
		if (globals != null) {
			for (Variable var : globals.values()) {
				a.andWith(ithVar(doms[var.getIndex() + shifted], 0));
			}
		}
		
		// Initializes heap
		if (getHeapLength() > 1) {
			a.andWith(ithVar(doms[hpDomIndex + shifted], 1));
			for (int i = 0; i < getHeapLength(); i++) {
				a.andWith(ithVar(doms[getHeapDomainIndex(i) + shifted], 0));
			}
		}
		
		// Initializes stack
		if (smax > 0) {
			a.andWith(ithVar(getStackPointerDomain(), 0));
		}
		
		// Initializes local variables
		for (int i = 0; i < lvmax; i++)
			a.andWith(ithVar(getLocalVarDomain(i), 0));
		
		return a;
	}
	
	public BDD initSharedVars() {
		
		BDD a = factory.one();
		for (int i = 0; i < gnum; i++) {
			int index = g0 + globalcopy*i;
			if (index == hpDomIndex) a.andWith(ithVar(doms[index], 1));
			else a.andWith(ithVar(doms[index], 0));
		}
		return a;
	}
	
	/**
	 * Returns a BDD representing all variables having zero values.
	 * 
	 * @return A BDD representing all variables having zero values.
	 */
	public BDD allZero() {
		
		BDD a = factory.one();
		for (int i = 0; i < doms.length; i++) {
			a.andWith(ithVar(doms[i], 0));
		}
		return a;
	}
	
	public BDDDomain[] getDomains() {
		return doms;
	}
	
	public BDDDomain getDomain(int index) {
		return doms[index];
	}
		
	/**
	 * Abstracts local variables from BDD a.
	 * 
	 * @param a the BDD
	 * @return the abstracted BDD
	 */
	public BDD abstractLocals(BDD a) {
		
		BDDVarSet lvs = getLocalVarSet();
		return a.exist(lvs);
	}
	
	public BDD abstractNonShared(BDD a) {
		
		return a.exist(getNonSharedVarSet());
	}
	
	public BDD abstractLocalVarsAndStackPointer(BDD a) {
		
		BDDVarSet lvspvs = getLvSpVarSet();
		return a.exist(lvspvs);
	}
	
	public BDD abstractStack(BDD a) {
		
		return a.exist(getStackVarSet());
	}
	
	/*************************************************************************
	 * Methods for domains
	 *************************************************************************/
	
	/**
	 * Gets the BDD domain representing the stack pointer.
	 * 
	 * @return the BDD domain.
	 */
	public BDDDomain getStackPointerDomain() {
		if (spDomIndex == -1) return null;
		return doms[spDomIndex];
	}
	
	/**
	 * Gets the BDD domain representing the stack element at <code>index</code>.
	 * 
	 * @param index the stack element index.
	 * @return the BDD domain.
	 */
	public BDDDomain getStackDomain(int index) {
		if (sDomIndex == -1) return null;
		return doms[sDomIndex + index];
	}
	
	/**
	 * Returns the BDD domain representing the global variable 
	 * having the specified name.
	 * 
	 * @param name the name of the variable.
	 * @return the BDD domain.
	 */
	public BDDDomain getGlobalVarDomain(String name) {
		Variable var = getGlobalVar(name);
		if (var == null) return null;
		return doms[var.getIndex()];
	}
	
	public BDDDomain getRetVarDomain() {
		// This never happen because we always add ret var
		if (retDomIndex == -1) return null; 
		return doms[retDomIndex];
	}
	
	public BDDDomain getTempVarDomain() {
		
		return doms[retDomIndex];
	}
	
	public BDDDomain getHeapPointerDomain() {
		
		if (hpDomIndex == -1) return null;
		return doms[hpDomIndex];
	}
	
	private int getHeapDomainIndex(int index) {
		if (hDomIndex == -1) return -1;
		return hDomIndex + globalcopy*index;
	}
	
	/**
	 * Returns the BDD Domain representing the heap at <code>index</code>.
	 * 
	 * @return the BDD Domain.
	 */
	public BDDDomain getHeapDomain(int index) {
		return doms[getHeapDomainIndex(index)];
	}
	
	/**
	 * Returns the BDD Domain representing the heap at <code>index</code>.
	 * 
	 * @return the BDD Domain.
	 */
	public BDDDomain getHeapDomain(long index) {
		return getHeapDomain((int) index);
	}
	
	/**
	 * Returns the BDDDomain representing the array length.
	 * The array pointer is specified by <code>ptr</code>.
	 * 
	 * @return the BDDDomain representing the array length.
	 */
	BDDDomain getArrayLengthDomain(long ptr) {
		return getHeapDomain(decodeHeapIndex((int) ptr) + getArrayAuxSize() - 1);
	}
	
	/**
	 * Returns the BDDDomain representing the array element.
	 * The array pointer is specified by <code>ptr</code>.
	 * The array index is specified by <code>index</code>.
	 * 
	 * @return the BDDDomain representing the array element.
	 */
	BDDDomain getArrayElementDomain(long ptr, int index) {
		return getHeapDomain(decodeHeapIndex((int) ptr) + getArrayAuxSize() + index);
	}
	
	BDDDomain getOwnerThreadDomain(long ptr) {
		return getHeapDomain(decodeHeapIndex((int) ptr) + 1);
	}
	
	BDDDomain getOwnerCounterDomain(long ptr) {
		return getHeapDomain(decodeHeapIndex((int) ptr) + 2);
	}
	
	/**
	 * Gets the <code>BDDDomain</code> of the local variable at <code>index</code>.
	 * 
	 * @param index the local variable index.
	 * @return the <code>BDDDomain</code> of the local variable.
	 */
	public BDDDomain getLocalVarDomain(int index) {
		if (lvDomIndex == -1) return null;
		if (index >= lvmax) return null;
		return doms[lvDomIndex + varcopy*index];
	}
	
	public BDDVarSet getVarSetWithout(int index) {
		
		if (cache && varSetWithout == null) 
			varSetWithout = new HashMap<Integer, BDDVarSet>();
		
		// Uses cache
		if (cache && varSetWithout.containsKey(index))
			return varSetWithout.get(index);
		
		BDDDomain[] d = new BDDDomain[doms.length - 1];
		for (int i = 0, j = 0; i < doms.length; i++) {
			if (i != index) {
				d[j++] = doms[i];
			}
		}
		BDDVarSet varset = factory.makeSet(d);
		
		// Caches
		if (cache)
			varSetWithout.put(index, varset);
		
		return varset;
	}
	
	/**
	 * Gets all BDD variable set without those having indices 
	 * specified by <code>indices</code>.
	 * 
	 * @param indices the indices.
	 * @return the variable set.
	 */
//	public BDDVarSet getVarSetWithout(Set<Integer> indices) {
//		
//		BDDDomain[] d = new BDDDomain[doms.length - indices.size()];
//		for (int i = 0, j = 0; i < doms.length; i++) {
//			if (indices.contains(i)) continue;
//			d[j++] = doms[i];
//		}
//		BDDVarSet varset = factory.makeSet(d);
//		
//		return varset;
//	}
	
	/**
	 * Creates BDD for If expression.
	 * 
	 * @param expr
	 * @param sdom
	 * @return
	 */
	BDD ifBDD(If expr, BDDDomain sdom) {
		
		int bits = getBits();
		switch (expr.getType()) {
		
		case If.EQ:
			return ithVar(sdom, 0);
				
		case If.NE:
			return ithVar(sdom, 0).not();
			
		case If.LT:
			return factory.ithVar(sdom.vars()[bits-1]);
			
		case If.GE:
			return factory.nithVar(sdom.vars()[bits-1]);
			
		case If.GT:
			return factory.nithVar(sdom.vars()[bits-1])
					.andWith(ithVar(sdom, 0).not());
			
		case If.LE:
			return factory.ithVar(sdom.vars()[bits-1])
					.orWith(ithVar(sdom, 0));
			
		case If.ID:
			int index = findObjectIdIndex(expr.getValue());
			if (index < 0 || (index > 0 && omap[index] == 0))
				return factory.zero();
			else
				return ithVar(sdom, index);
			
		case If.IS:
			return ithVar(sdom, expr.getValue());
			
		case If.LG: {
			BDD a = factory.zero();
			for (int i = expr.getLowValue(); i <= expr.getHighValue(); i++) {
				a.orWith(ithVar(sdom, encode(i, sdom)));
			}
			BDD b = a.not();
			a.free();
			return b;
		}
		
		case If.NOT: {
			Set<Integer> set = expr.getNotSet();
			BDD a = factory.zero();
			for (int i : set) {
				a.orWith(ithVar(sdom, encode(i, sdom)));
			}
			BDD b = a.not();
			a.free();
			return b;
		}
		}
		
		throw new IllegalArgumentException("Invalid comparison type: " + expr.getType());
	}
	
	/**
	 * Returns the BDD representing the equality of two variables 
	 * specified by dom1 and dom2.
	 * 
	 * @param dom1 the BDD domain 1
	 * @param dom2 the BDD domain 2
	 * @return the equality BDD
	 */
	public BDD bddEquals(BDDDomain dom1, BDDDomain dom2/*, boolean signed*/) {
		
//		BigInteger size1 = dom1.usize();
//		BigInteger size2 = dom2.usize();
		
//		if (size1.compareTo(size2) < 0) {
//			if (log())
//				BDDSemiring.log("\t\t(dom1:%d size1:%s).extendCapacity(%d)%n", dom1.getIndex(), size1, size2);
//			dom1.extendCapacity(size2.divide(BigInteger.valueOf(2)).subtract(BigInteger.ONE));
//		} else if (size1.compareTo(size2) > 0) {
//			if (log())
//				BDDSemiring.log("\t\t(dom2:%d size2:%s).extendCapacity(%d)%n", dom2.getIndex(), size2, size1);
//			dom2.extendCapacity(size1.divide(BigInteger.valueOf(2)).subtract(BigInteger.ONE));
//		}
//		
//		return dom1.buildEquals(dom2);
		
		// Uses the library function if the domains have the same size
		int[] lessvars = dom1.vars();
		int[] morevars = dom2.vars();
		
		if (lessvars.length == morevars.length)
			return dom1.buildEquals(dom2);
		
		if (lessvars.length > morevars.length) {
			int[] tmp = lessvars;
			lessvars = morevars;
			morevars = tmp;
		}
//		int[] lessvars = less.vars();
//		int[] morevars = more.vars();
		
		
		if (lessvars.length == 1) {
			BDD e = factory.one();
			BDD a = factory.ithVar(lessvars[0]);
            BDD b = factory.ithVar(morevars[0]);
            a.biimpWith(b);
            e.andWith(a);
            
            for (int i = 1; i < morevars.length; i++)
            	e.andWith(factory.nithVar(morevars[i]));
			return e;
		}
		
		BDD a = factory.one();
		int i, j;
		for (i = 0; i < lessvars.length - 1; i++) {
			BDD b = factory.ithVar(lessvars[i]).andWith(factory.ithVar(morevars[i]));
			b.orWith(factory.nithVar(lessvars[i]).andWith(factory.nithVar(morevars[i])));
			a.andWith(b);
		}
		
//		if (signed) {
		
			// Sign-bit extension: zero
			BDD b = factory.ithVar(lessvars[i]);
			for (j = i; j < morevars.length; j++)
				b.andWith(factory.ithVar(morevars[j]));
	
			// Sign-bit extension: one
			BDD c = factory.nithVar(lessvars[i]);
			for (j = i; j < morevars.length; j++)
				c.andWith(factory.nithVar(morevars[j]));
		
//		for (i = lessvars.length - 1, j = morevars.length - 1; i >= 1; i--, j--) {
//			BDD b = factory.ithVar(lessvars[i]).andWith(factory.ithVar(morevars[j]));
//			b.orWith(factory.nithVar(lessvars[i]).andWith(factory.nithVar(morevars[j])));
//			a.andWith(b);
//		}
//		
//		// Sign-bit extension: zero
//		BDD b = factory.ithVar(lessvars[0]);
//		for (i = j; i >= 0; i--)
//			b.andWith(factory.ithVar(morevars[i]));
//
//		// Sign-bit extension: one
//		BDD c = factory.nithVar(lessvars[0]);
//		for (i = j; i >= 0; i--)
//			c.andWith(factory.nithVar(morevars[i]));
		
			a.andWith(b.orWith(c));	
//		} else {	// unsigned
//			// i = lessvars.length - 1
//			BDD b = factory.ithVar(lessvars[i]).andWith(factory.ithVar(morevars[i]));
//			b.orWith(factory.nithVar(lessvars[i]).andWith(factory.nithVar(morevars[i])));
//			a.andWith(b);
//			
//			for (j = i + 1; j < morevars.length; j++)
//				a.andWith(factory.nithVar(morevars[j]));
//		}
			
		DomainSemiring.log("a: %s%n", a);
		return a;
	}
	
	private static final int EQ_G0L0_G1L1 = 0;
	private static final int EQ_G0_G3 = 1;
	private static final int EQ_G3_G4 = 2;
	private static final int EQ_NUM = 3;
	
	private BDD[] equals;
	
	public BDD buildG0L0equalsG1L1() {
		if (equals == null) 
			equals = new BDD[EQ_NUM];
		
		if (equals[EQ_G0L0_G1L1] != null) 
			return equals[EQ_G0L0_G1L1];
		
		BDD G0L0equalsG1L1 = factory.one();
		for (int i = 0; i < gnum; i++) {
			int index = g0 + globalcopy*i;
			G0L0equalsG1L1.andWith(doms[index].buildEquals(doms[index + gindex[1]]));
		}
		for (int i = 0; i < lvmax; i++) {
			int index = lvDomIndex + varcopy*i;
			G0L0equalsG1L1.andWith(doms[index].buildEquals(doms[index + 1]));
		}
		
		equals[EQ_G0L0_G1L1] = G0L0equalsG1L1;
		return G0L0equalsG1L1;
	}
	
	public BDD buildG0equalsG3() {
		if (equals == null) equals = new BDD[EQ_NUM];
		
		if (equals[EQ_G0_G3] != null)
			return equals[EQ_G0_G3];
		
		BDD G0equalsG3 = factory.one();
		for (int i = 0; i < gnum; i++) {
			int index = g0 + globalcopy*i;
			G0equalsG3.andWith(doms[index].buildEquals(doms[index + gindex[3]]));
		}
		
		equals[EQ_G0_G3] = G0equalsG3;
		return G0equalsG3;
	}
	
	public BDD buildG3equalsG4() {
		if (equals == null) 
			equals = new BDD[EQ_NUM];
		
		if (equals[EQ_G3_G4] != null)
			return equals[EQ_G3_G4];
		
		BDD G3equalsG4 = factory.one();
		for (int i = 0; i < gnum; i++) {
			int index = g0 + globalcopy*i;
			G3equalsG4.andWith(doms[index + gindex[3]].buildEquals(doms[index + gindex[4]]));
		}
		
		equals[EQ_G3_G4] = G3equalsG4;
		return G3equalsG4;
	}
	
	/**
	 * Returns the bdd representing stack of l0 equals to local variables of l2.
	 * The parameter s points to the "deepest" stack element.
	 * The parameter nargs specifies the number of arguments, i.e.
	 * the number of equality pairs.
	 * For example, if s=2, nargs=3, the method returns the bdd for
	 * s[2]=lv2[0], s[3]=lv2[1], s[4]=lv2[2];
	 * 
	 * @param s
	 * @param nargs
	 * @return
	 */
	BDD bddL0equalsL2params(int s, int nargs) {
		
		BDD d = factory.one();
		for (int i = 0; i < nargs; i++) {
			d.andWith(getStackDomain(s + i).buildEquals(doms[l0 + varcopy*i + 2]));
		}
		
		return d;
	}
	
	/**
	 * Returns the bdd representing the inequality of two variables 
	 * specified by dom1 and dom2.
	 * 
	 * @param dom1
	 * @param dom2
	 * @return
	 */
	public BDD bddNotEquals(BDDDomain dom1, BDDDomain dom2) {
		
		BigInteger size1 = dom1.size();
		BigInteger size2 = dom2.size();
		
		// Uses the library function if the domains have the same size
		if (size1.equals(size2))
			return dom1.buildEquals(dom2).not();
		
		BDDDomain less, more;
		if (size1.compareTo(size2) < 0) {
			less = dom1;
			more = dom2;
		} else {
			less = dom2;
			more = dom1;
		}
		int[] lessvars = less.vars();
		int[] morevars = more.vars();
		BDD a = factory.zero();
		for (int i = 0; i < lessvars.length; i++) {
			a.orWith(factory.nithVar(lessvars[i]).andWith(factory.ithVar(morevars[i])));
			a.orWith(factory.ithVar(lessvars[i]).andWith(factory.nithVar(morevars[i])));
		}
		
		// Not equal, if the sign bits are different
		a.orWith(factory.nithVar(lessvars[lessvars.length-1])
				.andWith(factory.ithVar(morevars[morevars.length-1])));
		a.orWith(factory.ithVar(lessvars[lessvars.length-1])
				.andWith(factory.nithVar(morevars[morevars.length-1])));
		return a;
	}
	
	/**
	 * Returns the BDD with domain specified by <code>dom</code>
	 * representing values from <code>min</code> to <code>max</code>.
	 * 
	 * @param dom the domain of the BDD.
	 * @param min the minimum value.
	 * @param max the maximium value.
	 * @return the BDD with values from <code>min</code> to <code>max</code>.
	 */
	public BDD bddRange(BDDDomain dom, int min, int max) {
		
		if (min == max)
			return ithVar(dom, min);
		
		// Bug in JavaBDD; Handles manually
		
//		// Handles manually, because the library seems to be wrong in this case
//		if (min == 0 && max == 1)
//			return dom.ithVar(0).orWith(dom.ithVar(1));
//		
//		if (min >= 0) {
//			return dom.varRange(encode(min, dom), encode(max, dom));
//		}
		
		BDD a = factory.zero();
		for (int i = min; i <= max; i++) {
			long e = encode(i, dom);
			a.orWith(ithVar(dom, e));
		}
		
		return a;
	}
	
	/**
	 * TODO this is not compatible with the semantics of Java
	 * because max is inclusive.
	 * 
	 * @param dom
	 * @param min
	 * @param next
	 * @param max
	 * @return
	 */
	public BDD bddRange(BDDDomain dom, float min, Number next, float max) {
		
		float step = (next == null) ? (max - min)/(size() - 1) : next.floatValue();
		
		BDD a = factory.zero();
		for (float i = min; i <= max; i += step) {
			long v = encode(i, dom);
			a.orWith(ithVar(dom, v));
		}
		
		return a;
	}
	
	/**
	 * Gets the BDD iterator from the <code>bdd</code>.
	 * The iterator contains only the variables specified by <code>dom</code>. 
	 * 
	 * @param bdd the BDD.
	 * @param doms the BDD domain.
	 * @return the BDD iterator.
	 */
	public BDDIterator iterator(BDD bdd, BDDDomain dom) {
		
		BDDVarSet varset = dom.set();
		BDDIterator itr = bdd.exist(getVarSetWithout(dom.getIndex())).iterator(varset);
		varset.free();
		
		return itr;
	}
	
	private BDDVarSet getVarSetWithout(boolean[] without) {
		BDDVarSet varset = factory.emptySet();
		for (int i = 0; i < doms.length; i++) {
			if (without[i])
				continue;
			varset.unionWith(doms[i].set());
		}
		return varset;
	}
	
	/**
	 * Gets the BDD iterator from the <code>bdd</code>.
	 * The iterator contains only the variables specified by <code>doms</code>. 
	 * 
	 * @param bdd the BDD.
	 * @param doms the BDD domains.
	 * @return the BDD iterator.
	 */
	public BDDIterator iterator(BDD bdd, BDDDomain... doms) {
		
		// Collects var set and indices from doms
		BDDVarSet varset = factory.emptySet();
//		Set<Integer> indices = new HashSet<Integer>((int) (1.4*doms.length));
		boolean[] without = new boolean[this.doms.length];
		for (int i = 0; i < doms.length; i++) {
			varset.unionWith(doms[i].set());
//			indices.add(doms[i].getIndex());
			without[doms[i].getIndex()] = true;
		}
		
		// Abstracts and creates iterator
		BDDVarSet abs = getVarSetWithout(without);
		BDDIterator itr = bdd.exist(abs).iterator(varset);
		abs.free();
		varset.free();
		
		return itr;
	}
	
	/**
	 * Gets the set of values of the variables specified by <code>dom</code>
	 * inside <code>bdd</code>.
	 * 
	 * @param bdd the BDD.
	 * @param dom the BDD domain.
	 * @return thes set of values.
	 */
	public Set<Long> valuesOf(BDD bdd, BDDDomain dom) {
		
		BDDVarSet varset = dom.set();
		BDDIterator itr = bdd.exist(getVarSetWithout(dom.getIndex()))
				.iterator(varset);
		HashSet<Long> set = new HashSet<Long>();
		while (itr.hasNext())
			set.add(scanVar((BDD) itr.next(), dom));
		varset.free();
		
		return set;
	}
	
	public int countRawArguments(BDD a) {
		// Abstracts G0 and L0
		BDDVarSet abs = getG0VarSet().union(getLocalVarSet());
		BDD b = a.exist(abs);
		abs.free();
		
		// Gets iterator
		BDDIterator itr = b.iterator(getG1L1VarSet());
		
		// For each possible argument
		int count = 0;
		while (itr.hasNext()) {
			BDD c = itr.nextBDD();
			count++;
			c.free();
		}
		
		b.free();
		return count;
	}
	
	/**
	 * Signature of a: (G0,L0,G1,L1)
	 * 
	 * @param a
	 * @return
	 */
	public List<RawArgument> getRawArguments(BDD a) {
		
		if (debug()) log("a: %s%n", a.toStringWithDomains());
		
		// Abstracts G0 and L0
		BDDVarSet abs = getG0VarSet().union(getLocalVarSet());
		BDD b = a.exist(abs);
		abs.free();
		
		// Gets iterator
		BDDIterator itr = b.iterator(getG1L1VarSet());
		
		// For each possible argument
		List<RawArgument> args = new ArrayList<RawArgument>();
		while (itr.hasNext()) {
			BDD c = itr.nextBDD();
			RawArgument arg = new RawArgument(lvmax, getHeapLength() - 1);
			for (int i = 0; i < lvmax; i++) {
				BDDDomain dom = doms[l0 + varcopy*i + 1];
				arg.lv[i] = decode(DomainManager.scanVar(c, dom), dom);
			}
			for (int i = 0; i < getHeapLength() - 1; i++) {
				BDDDomain dom = doms[hDomIndex + globalcopy*(i+1) + 1];
				arg.heap[i] = decode(DomainManager.scanVar(c, dom), dom);
			}
			if (debug()) log("arg: %s%n", arg);
			args.add(arg);
			c.free();
		}
		
		b.free();
		return args;
	}
	
	/**
	 * Signature of a: (G0,L0,G1,L1).
	 * Signature of b: (G2,L2,L0,G1,L1).
	 * 
	 * The method (i) changes a to (G0,L0,G2,L2),
	 * (ii) abstracts L0 from b, 
	 * (iii) conjuncts a (G0,L0,G2,L2) and b (G2,L2,G1,L1), and
	 * (iv) abstracts G2 and L2.
	 * 
	 * The bdd a and b remain unchanged.
	 * 
	 * @param a
	 * @param b
	 * @return
	 */
	public BDD conjoin(BDD a, BDD b) {
		
		// (i) Changes a to (G0,L0,G2,L2)
//		BDD ap = replaceG1L1withG2L2(a.id());
		BDD ap = a.id().replaceWith(getG1L1pairG2L2());
		
		// (ii) Abstracts L0 from b
		BDD bp = b.exist(getLocalVarSet());
		
		// (iii) Conjuncts a and b
		ap.andWith(bp);
		
		// (iv) Abstracts G2 and L2
		bp = ap.exist(getG2L2VarSet());
		ap.free();
		
		return bp;
	}
	
	/**
	 * Encodes <code>raw</code> in two-complement format.
	 * 
	 * @param raw
	 * @return
	 */
	public static long encode(int raw, BDDDomain dom) {
		return encode(raw, dom.size().longValue());
	}
	
	public static int decode(long encoded, BDDDomain dom) {
		return decode(encoded, dom.size().longValue());
	}
	
	public long encode(float raw, BDDDomain dom) {
		return encode(raw, dom.size().intValue());
	}
	
	public long encode(String raw, BDDDomain dom) {
		return encode(raw, dom.size().intValue());
	}
	
	public static long neg(long encoded, BDDDomain dom) {
		return neg(encoded, dom.size().longValue());
	}
	
	public static boolean isNeg(long v, BDDDomain dom) {
		return v > dom.size().longValue()/2 - 1;
	}
	
	public static long scanVar(BDD bdd, BDDDomain dom) {
		return scanVar(bdd, dom.vars());
//		return bdd.scanVar(dom).longValue();
	}
	
	public BDD ithVar(BDDDomain dom, long value) {
		return ithVar(dom.vars(), value);
//		return dom.ithVar(value);
	}
	
	/**
	 * Performs arithmetic.
	 * 
	 * @param type the arithmetic type.
	 * @param rdom the result domain.
	 * @param v1 the value 1.
	 * @param dom1 the domain of value 1.
	 * @param v2 the value 2.
	 * @param dom2 the domain of value 2.
	 * @return the arithmetic result.
	 */
	public BDD arith(int type, BDDDomain rdom, 
			long v1, BDDDomain dom1, long v2, BDDDomain dom2) {
		
		switch (type) {
		case Arith.ADD:
			return ithVar(rdom, encode(decode(v1, dom1) + decode(v2, dom2), rdom));
		case Arith.AND:
			return ithVar(rdom, encode(decode(v1, dom1) & decode(v2, dom2), rdom));
		case Arith.CMP: {
			int de1 = decode(v1, dom1);
			int de2 = decode(v2, dom2);
			if (de1 > de2) return ithVar(rdom, encode(1, rdom));
			if (de1 == de2) return ithVar(rdom, encode(0, rdom));
			return ithVar(rdom, encode(-1, rdom));
		}
		case Arith.DIV:
			return ithVar(rdom, encode(decode(v1, dom1) / decode(v2, dom2), rdom));
		case Arith.MUL:
			return ithVar(rdom, encode(decode(v1, dom1) * decode(v2, dom2), rdom));
		case Arith.OR:
			return ithVar(rdom, encode(decode(v1, dom1) | decode(v2, dom2), rdom));
		case Arith.REM:
			return ithVar(rdom, encode(decode(v1, dom1) % decode(v2, dom2), rdom));
		case Arith.SHL:
			return ithVar(rdom, encode(decode(v1, dom1) << (decode(v2, dom2) & 31), rdom));
		case Arith.SHR:
			return ithVar(rdom, encode(decode(v1, dom1) >> (decode(v2, dom2) & 31), rdom));
		case Arith.SUB:
			return ithVar(rdom, encode(decode(v1, dom1) - decode(v2, dom2), rdom));
		case Arith.USHR:
			return ithVar(rdom, encode(decode(v1, dom1) >>> (decode(v2, dom2) & 31), rdom));
		case Arith.XOR:
			return ithVar(rdom, encode(decode(v1, dom1) ^ decode(v2, dom2), rdom));
		case Arith.FADD:
			return ithVar(rdom, encode(decodeFloat(v1) + decodeFloat(v2), rdom));
		case Arith.FCMPG: 
		case Arith.FCMPL: {
			float f1 = decodeFloat(v1);
			float f2 = decodeFloat(v2);
			if (f1 > f2) return ithVar(rdom, encode(1, rdom));
			else if (f1 == f2) return ithVar(rdom, encode(0, rdom));
			else if (f1 < f2) return ithVar(rdom, encode(-1, rdom));
			// At least one must be NaN
			else if (type == Arith.FCMPG) return ithVar(rdom, encode(1, rdom));
			else return ithVar(rdom, encode(-1, rdom));
		}
		case Arith.FDIV:
			return ithVar(rdom, encode(decodeFloat(v1) / decodeFloat(v2), rdom));
		case Arith.FMUL:
			return ithVar(rdom, encode(decodeFloat(v1) * decodeFloat(v2), rdom));
		case Arith.FREM:
			return ithVar(rdom, encode(decodeFloat(v1) % decodeFloat(v2), rdom));
		case Arith.FSUB:
			return ithVar(rdom, encode(decodeFloat(v1) - decodeFloat(v2), rdom));
		case Arith.NDT:
			return bddRange(rdom, decode(v1, dom1), decode(v2, dom2));
			
		default:
			throw new IllegalArgumentException("Invalid ArithType: " + type);
		}
	}
	
	public long fneg(long v, BDDDomain dom) {
		float f = decodeFloat(v);
		return encode(-f, dom);
	}
	
//	/**
//	 * Returns the negation of v in two-complement format.
//	 * For example, if bits = 3, then the following input/output pairs valid:
//	 * 0->0, 1->4, 2->5, 3->6, 4->1 5->2, 6->3, 7->3.
//	 * 
//	 * Note that an overflow occurs when negating the minimum (negative) value.
//	 * In the example, 7(-4) -> 4(-1).
//	 * 
//	 * @param v the value to be negated.
//	 * @return the negation of v.
//	 */
//	public long neg(long v) {
//		if (v == 0) return 0;
//		
//		int maxint = getMaxInt();
//		return (v <= maxint) ? v + maxint : v - maxint;
//	}
	
	private static final int TO_STRING_BOUND = 20;
	
	public String toString(BDD a, String separator, BDD restrictor) {
		
		// Abstracts G1, L1, G2, L2, unused stack elements, and return variable
		BDDVarSet abs = getG1L1VarSet().union(getG2L2VarSet());
		int sp = (int) scanVar(a, getStackPointerDomain());
		abs.unionWith(getStackPointerDomain().set());
		for (int i = sp; i < smax; i++) {
			abs.unionWith(getStackDomain(i).set());
		}
		abs.unionWith(getRetVarDomain().set());
		
//		if (multithreading() && symbolic())
//			abs.unionWith(getG3VarSet().id());
		BDD b = a.exist(abs);
		abs.free();
		
//		if (multithreading() && symbolic())
//			b.andWith(getRetVarDomain().ithVar(0));
		
		if (restrictor != null)
			b.andWith(restrictor);
		
		// Creates var set over globals, locals, and stacks
//		int nargs = (argDoms == null) ? 0 : argDoms.length;
		BDDDomain[] d = new BDDDomain[gnum + lvmax + sp/* + nargs*/];
		int j = 0;
		for (int i = 0; i < gnum; i++)
			d[j++] = doms[g0 + globalcopy*i];
		for (int i = 0; i < lvmax; i++)
			d[j++] = doms[l0 + varcopy*i];
		for (int i = 0; i < sp; i++)
			d[j++] = getStackDomain(i);
//		for (int i = 0; i < nargs; i++)
//			d[j++] = argDoms[i];
		BDDVarSet vs0 = factory.makeSet(d);
		
		// Creates iterator
		BDDIterator itr = b.iterator(vs0);
		b.free();
		vs0.free();
		
		int count = 0;
		ArrayList<String> all = new ArrayList<String>();
		while (itr.hasNext() && count++ < TO_STRING_BOUND) {
			
			ArrayList<String> state = new ArrayList<String>();
			b = (BDD) itr.next();
			
//			if (lvmax > 0 && b.scanVar(getLocalVarDomain(0)).intValue() == 1)
//				continue;
			
			// Global vars
			if (globals != null) {
				ArrayList<String> gv = new ArrayList<String>();
				for (String name : globals.keySet()) {
					gv.add(String.format("%s: %d", name, scanVar(b, getGlobalVarDomain(name))));
				}
				state.add(toCommaString(gv));
			}
			
			if (getHeapLength() > 1) {
				int ptr = (int) scanVar(b, getHeapPointerDomain());
				state.add(String.format("ptr: %d", ptr));
				
				ArrayList<Integer> heap = new ArrayList<Integer>((int) (1.4*getHeapLength()));
				for (int i = 0; i < ptr; i++) {
					heap.add((int) scanVar(b, getHeapDomain(i)));
				}
				state.add(String.format("heap: [%s]", toCommaString(heap)));
			}
			
			if (lvmax > 0) {
				ArrayList<Integer> lv = new ArrayList<Integer>((int) (1.4*lvmax));
				for (int i = 0; i < lvmax; i++) {
					lv.add((int) scanVar(b, getLocalVarDomain(i)));
				}
				state.add(String.format("lv: [%s]", toCommaString(lv)));
			}
			
			if (sp > 0) {
				ArrayList<Integer> s = new ArrayList<Integer>((int) (1.4*sp));
				for (int i = 0; i < sp; i++) {
					s.add((int) scanVar(b, getStackDomain(i)));
				}
				state.add(String.format("stack: [%s]", toCommaString(s)));
			}
			
//			if (nargs > 0) {
//				ArrayList<Integer> args = new ArrayList<Integer>((int) (1.4*nargs));
//				for (int i = 0; i < nargs; i++) {
//					args.add(b.scanVar(argDoms[i]).intValue());
//				}
//				state.add(String.format("args: [%s]", toCommaString(args)));
//			}
			
//			System.out.println(toCommaString(state));
			all.add(toCommaString(state));
			b.free();
		}
		
		if (count >= TO_STRING_BOUND) {
			all.add("toString() bound reached, skipping the rest");
		}
		
		return "hmap: " + Arrays.toString(hmap) + "\n\t\t"
				+ "omap: " + Arrays.toString(omap) + "\n\t\t"
				+ toString(all, separator);
	}
	
	public String toString(BDD a, BDD restrictor) {

		return toString(a, "\n", restrictor);
	}
	
	public String toString(BDD a, String separator) {
		
		return toString(a, separator, null);
	}
	
	public String toString(BDD a) {
		
		return toString(a, "\n");
	}
	
	public static String toString(ArrayList<? extends Object> list, String separator) {
		
		if (list == null) return null;
		if (list.isEmpty()) return "";
		
		StringBuilder out = new StringBuilder();
		Iterator<? extends Object> itr = list.iterator();
		out.append(itr.next());
		while (itr.hasNext()) {
			out.append(separator).append(itr.next());
		}
		
		return out.toString();
	}
	
	public static String toCommaString(ArrayList<? extends Object> list) {
		
		return toString(list, ", ");
	}
	
	/*************************************************************************
	 * Methods for computing BDDDomain[]
	 *************************************************************************/
	
	private static final int DOM_G0 = 0;
	private static final int DOM_G1 = 1;
	private static final int DOM_G2 = 2;
	private static final int DOM_G3 = 3;
	private static final int DOM_G4 = 4;
	private static final int DOM_G1L1 = 5;
	private static final int DOM_G2L2 = 6;
	private static final int DOM_NUM = 7;
	
	private BDDDomain[][] domains;
	
	private BDDDomain[] putGxDomain(int type, int x) {
		if (domains == null) 
			domains = new BDDDomain[DOM_NUM][];
		
		if (domains[type] != null)
			return domains[type];
		
		BDDDomain[] d = new BDDDomain[gnum];
		for (int i = 0; i < gnum; i++)
			d[i] = doms[g0 + globalcopy*i + gindex[x]];
		
		domains[type] = d;
		return d;
	}
	
	private BDDDomain[] getGxDomain(int x) {
		switch (x) {
		case 0: return putGxDomain(DOM_G0, 0);
		case 1: return putGxDomain(DOM_G1, 1);
		case 2: return putGxDomain(DOM_G2, 2);
		case 3: return putGxDomain(DOM_G3, 3);
		case 4: return putGxDomain(DOM_G4, 4);
		}
		
		throw new RemoplaError("Unexpected G%d domain", x);
	}
	
	private BDDDomain[] putGxLxDomain(int type, int x) {
		if (domains == null) 
			domains = new BDDDomain[DOM_NUM][];
		
		if (domains[type] != null)
			return domains[type];
		
		BDDDomain[] d = new BDDDomain[gnum + lvmax];
		int j = 0;
		for (int i = 0; i < gnum; i++)
			d[j++] = doms[g0 + globalcopy*i + gindex[x]];
		for (int i = 0; i < lvmax; i++)
			d[j++] = doms[l0 + varcopy*i + x];
		
		domains[type] = d;
		return d;
	}
	
	private BDDDomain[] getG1L1Domain() {
		return putGxLxDomain(DOM_G1L1, 1);
	}
	
	private BDDDomain[] getG2L2Domain() {
		return putGxLxDomain(DOM_G2L2, 2);
	}
	
	/*************************************************************************
	 * Methods for computing BDDVarSet
	 *************************************************************************/
	
	private static final int VARSET_L0G1L1 = 0;
	private static final int VARSET_L0G1L1G2L2 = 1;
	private static final int VARSET_G1L1 = 2;
	private static final int VARSET_G2L2 = 3;
	private static final int VARSET_G0 = 4;
	private static final int VARSET_G3 = 5;
	private static final int VARSET_G4 = 6;
	private static final int VARSET_L0 = 7;
	private static final int VARSET_LVSP = 8;
	private static final int VARSET_NSHARED = 9;
	private static final int VARSET_SHARED = 10;
	private static final int VARSET_STACK = 11;
	private static final int VARSET_NUM = 12;
	
	private BDDVarSet[] varsets;
	
	/**
	 * Stores the variable set specified by the domains <code>d</code>.
	 * 
	 * @param type the type of the variable set.
	 * @param d the domains.
	 * @return the variable set.
	 */
	private BDDVarSet putVarSet(int type, BDDDomain[] d) {
		if (varsets == null)
			varsets = new BDDVarSet[VARSET_NUM];
		
		BDDVarSet vs = factory.makeSet(d);
		varsets[type] = vs;
		return vs;
	}
	
	BDDVarSet getL0G1L1VarSet() {
		
		if (varsets != null && varsets[VARSET_L0G1L1] != null)
			return varsets[VARSET_L0G1L1];
		
		BDDDomain[] d = new BDDDomain[gnum + 2*lvmax + ((smax > 0) ? smax + 1 : 0)];
		int j = 0;
		for (int i = 0; i < gnum; i++)
			d[j++] = doms[g0 + globalcopy*i + gindex[1]];
		for (int i = 0; i < lvmax; i++) {
			d[j++] = doms[l0 + varcopy*i];
			d[j++] = doms[l0 + varcopy*i + 1];
		}
		if (smax > 0) {
			d[j++] = getStackPointerDomain();
			for (int i = 0; i < smax; i++)
				d[j++] = getStackDomain(i);
		}
		
		return putVarSet(VARSET_L0G1L1, d);
	}
	
	BDDVarSet getL0G1L1G2L2VarSet() {
		
		if (varsets != null && varsets[VARSET_L0G1L1G2L2] != null)
			return varsets[VARSET_L0G1L1G2L2];
		
		BDDDomain[] d = new BDDDomain[2*gnum + 3*lvmax + ((smax > 0) ? smax + 1 : 0)];
		int j = 0;
		for (int i = 0; i < gnum; i++){
			d[j++] = doms[g0 + globalcopy*i + gindex[1]];
			d[j++] = doms[g0 + globalcopy*i + gindex[2]];
		}
		for (int i = 0; i < lvmax; i++) {
			d[j++] = doms[l0 + varcopy*i];
			d[j++] = doms[l0 + varcopy*i + 1];
			d[j++] = doms[l0 + varcopy*i + 2];
		}
		if (smax > 0) {
			d[j++] = getStackPointerDomain();
			for (int i = 0; i < smax; i++)
				d[j++] = getStackDomain(i);
		}
		
		return putVarSet(VARSET_L0G1L1G2L2, d);
	}
	
	BDDVarSet getG1L1VarSet() {
		if (varsets != null && varsets[VARSET_G1L1] != null)
			return varsets[VARSET_G1L1];
		
		return putVarSet(VARSET_G1L1, getG1L1Domain());
	}
	
	/**
	 * Gets the BDD variables representing G2 and L2.
	 * 
	 * @return the BDD variables representing G2 and L2.
	 */
	BDDVarSet getG2L2VarSet() {
		if (varsets != null && varsets[VARSET_G2L2] != null)
			return varsets[VARSET_G2L2];
		
		return putVarSet(VARSET_G2L2, getG2L2Domain());
	}
	
	private BDDVarSet getGxVarSet(int type, int x) {
		if (varsets != null && varsets[type] != null)
			return varsets[type];
		
		return putVarSet(type, getGxDomain(x));
	}
	
	BDDVarSet getG0VarSet() {
		return getGxVarSet(VARSET_G0, 0);
	}
	
	BDDVarSet getG3VarSet() {
		return getGxVarSet(VARSET_G3, 3);
	}
	
	BDDVarSet getG4VarSet() {
		return getGxVarSet(VARSET_G4, 4);
	}
	
	BDDVarSet getLocalVarSet() {
		
		if (varsets != null && varsets[VARSET_L0] != null) 
			return varsets[VARSET_L0];
		
		int i = 0;
		BDDDomain[] d = new BDDDomain[(smax > 0) ? smax + 1 + lvmax : lvmax];
		if (smax > 0) {
			
			d[i++] = getStackPointerDomain();
			for (int j = 0; j < smax; j++)
				d[i++] = getStackDomain(j);
		}
		for (int j = 0; j < lvmax; j++) {
			d[i++] = getLocalVarDomain(j);
		}
		
		return putVarSet(VARSET_L0, d);
	}
	
	/**
	 * Gets the BDD variables representing the local variables 
	 * and the stack pointer.
	 */
	private BDDVarSet getLvSpVarSet() {
		
		if (varsets != null && varsets[VARSET_LVSP] != null) 
			return varsets[VARSET_LVSP];
		
		int i = 0;
		BDDDomain[] d = new BDDDomain[(smax > 0) ? lvmax + 1 : lvmax];
		if (smax > 0) {
			d[i++] = getStackPointerDomain();
		}
		for (int j = 0; j < lvmax; j++) {
			d[i++] = getLocalVarDomain(j);
		}
		
		return putVarSet(VARSET_LVSP, d);
	}
	
	private BDDVarSet getNonSharedVarSet() {
		
		if (varsets != null && varsets[VARSET_NSHARED] != null) 
			return varsets[VARSET_NSHARED];
		
		// Here we use the fact that g0 is always zero
		int max = globalcopy*gnum;
		BDDDomain[] d = new BDDDomain[doms.length - gnum];
		int count = 0;
		for (int i = 0; i < doms.length; i++) {
			if (i < max && i%globalcopy == 0)	// Shortcuts shared vars
				continue;
			d[count++] = doms[i];
		}
		
		return putVarSet(VARSET_NSHARED, d);
	}
	
	/**
	 * Gets the shared var set.
	 * 
	 * @return the shared var set.
	 */
	public BDDVarSet getSharedVarSet() {
		
		if (varsets != null && varsets[VARSET_SHARED] != null) 
			return varsets[VARSET_SHARED];
		
		BDDDomain[] d = new BDDDomain[gnum];
		for (int i = 0; i < gnum; i++) {
			d[i] = doms[g0 + globalcopy*i];
		}
		
		return putVarSet(VARSET_SHARED, d);
	}
	
	/**
	 * Gets the BDD variables representing the stack.
	 * 
	 * @return the BDD variables representing the stack.
	 */
	private BDDVarSet getStackVarSet() {
		
		if (varsets != null && varsets[VARSET_STACK] != null) 
			return varsets[VARSET_STACK];
		
		BDDDomain[] d = new BDDDomain[smax];
		for (int i = 0; i < smax; i++) {
			d[i] = getStackDomain(i);
		}
		
		return putVarSet(VARSET_STACK, d);
	}
	
	/*************************************************************************
	 * Methods for renaming BDD variables
	 *************************************************************************/
	
	private static final int PAIR_G1L1_G2L2 = 0;
	private static final int PAIR_G0_G2 = 1;
	private static final int PAIR_G0_G3 = 2;
	private static final int PAIR_G3_G4 = 3;
	private static final int PAIR_NUM = 4;
	
	private BDDPairing[] pairings;
	
	private BDDPairing putPairing(int type, BDDDomain[] d1, BDDDomain[] d2) {
		if (pairings == null)
			pairings = new BDDPairing[PAIR_NUM];
		
		BDDPairing p = factory.makePair();
		p.set(d1, d2);
		pairings[type] = p;
		return p;
	}
	
	BDDPairing getG1L1pairG2L2() {
		if (pairings != null && pairings[PAIR_G1L1_G2L2] != null)
			return pairings[PAIR_G1L1_G2L2];
		
		return putPairing(PAIR_G1L1_G2L2, getG1L1Domain(), getG2L2Domain());
	}
	
	private BDDPairing getGxpairGy(int type, int x, int y) {
		if (pairings != null && pairings[type] != null)
			return pairings[type];
		
		return putPairing(type, getGxDomain(x), getGxDomain(y));
	}
	
	BDDPairing getG0pairG2() {
		return getGxpairGy(PAIR_G0_G2, 0, 2);
	}
	
	BDDPairing getG0pairG3() {
		return getGxpairGy(PAIR_G0_G3, 0, 3);
	}
	
	BDDPairing getG3pairG4() {
		return getGxpairGy(PAIR_G3_G4, 3, 4);
	}
	
	private BDD g3g4ordering;
	
	public BDD getG3G4ordering() {
		
		if (g3g4ordering != null) return g3g4ordering;
		
		g3g4ordering = factory.zero();
		for (int i = 0; i < gnum; i++) {
			int index = g0 + globalcopy*i;
			int[] vars3 = doms[index + gindex[3]].vars();
			int[] vars4 = doms[index + gindex[4]].vars();
			for (int j = 0; j < vars3.length; j++)
				g3g4ordering = factory.nithVar(vars3[j]).andWith(factory.ithVar(vars4[j]))
						.orWith(factory.ithVar(vars3[j]).biimpWith(factory.ithVar(vars4[j]))
								.andWith(g3g4ordering));
		}
		
		return g3g4ordering;
	}
	
	public String toString() {
		
		StringBuilder out = new StringBuilder();
		out.append(String.format("Bits: %d, Heap Size: %d%n", bits, getHeapLength(), g0));
		out.append(String.format("g0: %d, gnum: %d, hpDomIndex: %d, hDomIndex: %d%n", g0, gnum, hpDomIndex, hDomIndex));
		out.append(String.format("l0: %d, lvmax: %d, lvDomIndex: %d%n", l0, lvmax, lvDomIndex));
		out.append(String.format("smax: %d, spDomIndex, sDomIndex: %d%n", smax, spDomIndex, sDomIndex));
		
		return out.toString();
	}
	
	public void free() {
		if (varSetWithout != null) {
			for (BDDVarSet a : varSetWithout.values())
				a.free();
		}
		
		if (equals != null) {
			for (int i = 0; i < equals.length; i++) {
				if (equals[i] != null)
					equals[i].free();
			}
		}
		
		if (varsets != null) {
			for (int i = 0; i < varsets.length; i++) {
				if (varsets[i] != null)
					varsets[i].free();
			}
		}
		
		if (g3g4ordering != null) g3g4ordering.free();
		
		factory.done();
		
	}
}
