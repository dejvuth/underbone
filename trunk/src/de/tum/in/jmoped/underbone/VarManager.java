package de.tum.in.jmoped.underbone;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;

import de.tum.in.jmoped.underbone.ExprSemiring.ArithType;
import de.tum.in.wpds.Utils;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDPairing;
import net.sf.javabdd.BDDVarSet;
import net.sf.javabdd.BDD.BDDIterator;

/**
 * The <code>VarManager</code> manages variables during the analysis.
 * 
 * @author suwimont
 *
 */
public class VarManager {

	// Integer bits
	private int bits;
	
	// 2^bits
	private long size;
	
	// 2^(bits-1) - 1
	private int maxint;
	
	// Heap size
	private long[] heapSizes;
	
	int smax;
	
	int lvmax;
	
	private int tbound;
	
	private boolean symbolic;
	
	static int varcopy = 3;
	
	int globalcopy;
	
	/**
	 * Maps names to global variables
	 */
	private HashMap<String, Variable> globals;
	
	private HashSet<Integer> sharedDomIndex;
	
	// Domains of all variables
	BDDDomain[] doms;
	
	// Return variable domain index
	private int retDomIndex;
	
	// Heap pointer domain index
	private int hpDomIndex;
	
	// Heap domain index
	private int hDomIndex;
	
	// Stack pointer domain index
	private int spDomIndex;
	
	// Stack domain index
	private int sDomIndex;
	
	// Local variable domain index
	private int lvDomIndex;
	
	/**
	 * Number of globals: global vars + heap pointer + heap
	 */
	int gnum;
	
	// Starting domain index of globals
	int g0;
	
	// Starting domain index of locals
	int l0;
	
	// BDDFactory
	BDDFactory factory;
	
	private int[] gindex;
	
	/* 
	 * Maps a domain index of a variable to a variable set 
	 * of all variables without that variable.
	 * Use for abstracting other variables away. 
	 */
	private HashMap<Integer, BDDVarSet> varSetWithout;
	
	/**
	 * Maps names of constants to their values.
	 */
	private HashMap<String, Integer> constants = new HashMap<String, Integer>();
	
	/**
	 * Verbosity level.
	 */
	private static int verbosity = 0;
	
	/**
	 * The logger.
	 */
	static Logger logger = Utils.getLogger(VarManager.class);
	
	/**
	 * Records the maximum number of BDD nodes. For statistics purpose.
	 */
	private static int maxNodeNum;
	
	/**
	 * Constructs a variable manager.
	 * 
	 * @param bddpackage
	 * @param nodenum
	 * @param cachesize
	 * @param bits
	 * @param heapSizes
	 * @param g
	 * @param smax
	 * @param lvmax
	 * @param tbound
	 * @param symbolic
	 */
	public VarManager(String bddpackage, int nodenum, int cachesize, 
			int bits, long[] heapSizes, Collection<Variable> g, 
			int smax, int lvmax, int tbound, boolean symbolic) {
		
		maxNodeNum = 0;
		log("bits: %d, heapSizes: %s, g: %s, smax: %s, lvmax: %d, tbound %d%n",
				bits, Arrays.toString(heapSizes), g, smax, lvmax, tbound);
		this.bits = bits;
		this.size = (long) Math.pow(2, bits);
		this.maxint = (int) size/2 - 1;
		this.heapSizes = heapSizes;
		this.smax = smax;
		this.lvmax = lvmax;
		this.tbound = tbound;
		this.symbolic = symbolic;
		this.globalcopy = (!multithreading() || !symbolic()) ? varcopy : varcopy + 2;
		
		if (multithreading() && symbolic()) {
			gindex = new int[] { 0, 3, 4, 1, 2 };
		} else {
			gindex = new int[] { 0, 1, 2, 3, 4 };
		}
		
		// Prepares array for domains
		int heapLength = heapSizes.length;
		int s = smax + varcopy*lvmax;
		if (smax > 0) s++;	// for stack pointer
		if (heapLength > 1) s += globalcopy*(heapLength + 1);
		if (g != null && !g.isEmpty()) {
			s += globalcopy*g.size();
		}
//		s += (multithreading() && symbolic()) ? globalcopy : 1;	// ret var
		s++;
		long[] domSize = new long[s];
		
		if (multithreading())
			sharedDomIndex = new HashSet<Integer>((int) (1.5*tbound*heapLength));
		
		// Global variables
		int index = 0;
		g0 = index;
		if (g != null && !g.isEmpty()) {
			
			globals = new HashMap<String, Variable>((int) (1.4 * g.size()));
			for (Variable v : g) {
				
				v.setIndex(index);
				log("%s (%d)%n", v.name, v.getIndex());
				if (multithreading() && v.isShared()) {
					sharedDomIndex.add(index);
				}
				long gsize = (long) Math.pow(2, v.getBits(bits));
				for (int i = 0; i < globalcopy; i++)
					domSize[index++] = gsize;
				globals.put(v.name, v);
				gnum++;
			}
		}
		
		// Heap
		if (heapLength > 1) {
			
			// Heap pointer
			hpDomIndex = index;
			log("heap pointer (%d)%n", index);
			if (multithreading()) {
				sharedDomIndex.add(index);
			}
			for (int i = 0; i < globalcopy; i++)
				domSize[index++] = size;
			gnum++;
			
			// Heap: at zero
			hDomIndex = index;
			log("heap[0] (%d)%n", index);
			if (multithreading()) {
				sharedDomIndex.add(index);
			}
			for (int j = 0; j < globalcopy; j++)
				domSize[index++] = 2;
			gnum++;
			
			// Heap: the rest
			for (int i = 1; i < heapLength; i++) {
				
				log("heap[%d] - index: %d, size: %d%n", i, index, heapSizes[i]);
				if (multithreading()) {
					sharedDomIndex.add(index);
				}
				for (int j = 0; j < globalcopy; j++)
					domSize[index++] = heapSizes[i];
				gnum++;
			}
		} else {
			
			hpDomIndex = -1;
			hDomIndex = -1;
		}
		
//		if (multithreading() && symbolic()) {
//			log("ret (%d)%n", index);
//			retDomIndex = index;
//			sharedDomIndex.add(index);
//			for (int j = 0; j < globalcopy; j++)
//				domSize[index++] = size;
//			gnum++;
//		}
		
		// Local vars
		l0 = index;
		if (lvmax > 0) {
			
			lvDomIndex = index;
			for (int i = 0; i < lvmax; i++) {
				log("lv%d (%d)%n", i, index);
				for (int j = 0; j < varcopy; j++)
					domSize[index++] = size;
			}
		} else {
			lvDomIndex = -1;
		}
		
		// Stack
		if (smax > 0) {
			
			// Stack pointer
			log("stack pointer (%d)%n", index);
			spDomIndex = index;
			domSize[index++] = smax + 1;
			
			// Stack element
			sDomIndex = index;
			for (int i = 0; i < smax; i++) {
				log("stack%d (%d)%n", i, index);
				domSize[index++] = size;
			}
		} else {
			spDomIndex = -1;
			sDomIndex = -1;
		}
		
//		if (!multithreading() || !symbolic()) {
			retDomIndex = index;
			domSize[index++] = size;
//		}
		
		factory = BDDFactory.init(bddpackage, nodenum, cachesize);
		doms = factory.extDomain(domSize);
		
		info("BDD package: %s%n", factory.getClass().getName());
	}
	
	public int getHeapSize() {
		return heapSizes.length;
	}
	
	public int getMaxLocalVars() {
		
		return lvmax;
	}
	
	public boolean multithreading() {
		return tbound > 1;
	}
	
	public int getThreadBound() {
		return tbound;
	}
	
	public boolean symbolic() {
		return symbolic;
	}
	
	void updateMaxNodeNum() {
		int num = factory.getNodeNum();
		if (num > maxNodeNum) maxNodeNum = num;
	}
	
	public static int getMaxNodeNum() {
		return maxNodeNum;
	}
	
//	private static int[] gindex = new int[] { 0, 1, 2, 3, 4 };
	
	public BDD initVars() {
		
		// Initializes G3 in case of lazy splitting
		int shifted = (multithreading() && symbolic()) ? gindex[3] : 0;
		
		// Initializes global variables
		BDD a = factory.one();
		if (globals != null) {
			for (Variable var : globals.values()) {
				a.andWith(doms[var.getIndex() + shifted].ithVar(0));
			}
		}
		
		// Initializes heap
		if (getHeapSize() > 1) {
			a.andWith(doms[hpDomIndex + shifted].ithVar(1));
			for (int i = 0; i < getHeapSize(); i++) {
				a.andWith(doms[getHeapDomainIndex(i) + shifted].ithVar(0));
			}

		}
		
		// Initializes stack
		if (smax > 0) {
			a.andWith(getStackPointerDomain().ithVar(0));
		}
		
		// Initializes local variables
		for (int i = 0; i < lvmax; i++)
			a.andWith(getLocalVarDomain(i).ithVar(0));
		
		return a;
	}
	
	public BDD initSharedVars() {
		
		BDD a = factory.one();
//		for (int i = 0; i < gnum; i++) {
//			a.andWith(doms[g0 + globalcopy*i].ithVar(0));
//		}
		for (Integer i : sharedDomIndex) {
			if (i == hpDomIndex) a.andWith(doms[i].ithVar(1));
			else a.andWith(doms[i].ithVar(0));
		}
		
		return a;
	}
	
	public Integer getConstant(String name) {
		return constants.get(name);
	}
	
	public void putConstant(String name, Integer value) {
		constants.put(name, value);
	}
	
	/**
	 * Returns a BDD representing all variables having zero values.
	 * 
	 * @return A BDD representing all variables having zero values.
	 */
	public BDD allZero() {
		
		BDD a = factory.one();
		for (int i = 0; i < doms.length; i++) {
			a.andWith(doms[i].ithVar(0));
		}
		return a;
	}
	
	private BDDVarSet globalVarSet = null;
	
	/**
	 * Gets BDDVarSet of G0.
	 * 
	 * @return
	 */
	private BDDVarSet getGlobalVarSet() {
		
		if (globalVarSet != null) return globalVarSet;
		
		int i = 0;
		BDDDomain[] d = new BDDDomain[gnum];
		if (globals != null) {
			for (Variable var : globals.values())
				d[i++] = doms[var.getIndex()];
		}
		
		if (getHeapSize() > 1) {
			
			d[i++] = getHeapPointerDomain();
			for (int j = 0; j < getHeapSize(); j++)
				d[i++] = getHeapDomain(j);
		}
		
		globalVarSet = factory.makeSet(d);
		return globalVarSet;
	}
	
	/**
	 * Abstracts global variables (G0) from BDD a.
	 * 
	 * @param a the BDD
	 * @return the abstracted BDD
	 */
	public BDD abstractGlobals(BDD a) {
		
		BDDVarSet gvs = getGlobalVarSet();
		return a.exist(gvs);
	}
	
	private BDDVarSet localVarSet = null;
	
	private BDDVarSet getLocalVarSet() {
		
		if (localVarSet != null) return localVarSet;
		
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
		
		localVarSet = factory.makeSet(d);
		return localVarSet;
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
	
	private BDDVarSet sharedVarSet = null;
	private BDDVarSet nonSharedVarSet = null;
	
	private BDDVarSet getNonSharedVarSet() {
		
		if (nonSharedVarSet != null) return nonSharedVarSet;
		
		BDDDomain[] d = new BDDDomain[doms.length - sharedDomIndex.size()];
		int count = 0;
		for (int i = 0; i < doms.length; i++) {
			if (!sharedDomIndex.contains(i))
				d[count++] = doms[i];
		}
		nonSharedVarSet = factory.makeSet(d);
		return nonSharedVarSet;
	}
	
	public BDD abstractNonShared(BDD a) {
		
		return a.exist(getNonSharedVarSet());
	}
	
	/**
	 * Gets the shared var set.
	 * 
	 * @return the shared var set.
	 */
	public BDDVarSet getSharedVarSet() {
		
		if (sharedVarSet != null) return sharedVarSet;
		
		BDDDomain[] d = new BDDDomain[sharedDomIndex.size()];
		int count = 0;
		for (Integer i : sharedDomIndex) {
			d[count++] = doms[i];
		}
		sharedVarSet = factory.makeSet(d);
		return sharedVarSet;
	}
	
//	private BDDVarSet[] gtidVarSet;
//	
//	/**
//	 * TODO copied from getGtidVarSetWithout
//	 * 
//	 * @param tid
//	 * @return
//	 */
//	BDDVarSet getGtidVarSet(int tid) {
//		
//		if (gtidVarSet == null)
//			gtidVarSet = new BDDVarSet[tbound];
//		
//		// Returns cached
//		if (gtidVarSet[tid - 1] != null)
//			return gtidVarSet[tid - 1];
//		
//		// Global vars
//		int offset = varcopy + tid - 1;
//		int i = 0;
//		BDDDomain[] d = new BDDDomain[gnum];
//		if (globals != null) {
//			for (Variable var : globals.values())
//				d[i++] = doms[var.getIndex() + offset];
//		}
//		
//		// Heap
//		if (getHeapSize() > 1) {
//			d[i++] = doms[hpDomIndex + offset];
//			for (int j = 0; j < getHeapSize(); j++)
//				d[i++] = doms[hDomIndex + globalcopy*j + offset];
//		}
//		
//		gtidVarSet[tid - 1] = factory.makeSet(d);
//		return gtidVarSet[tid - 1];
//	}
	
//	private BDDVarSet[] gtidVarSetWithout;
//	
//	BDDVarSet getGtidVarSetWithout(int tid) {
//		
//		if (gtidVarSetWithout == null)
//			gtidVarSetWithout = new BDDVarSet[tbound];
//		
//		// Returns cached
//		if (gtidVarSetWithout[tid - 1] != null)
//			return gtidVarSetWithout[tid - 1];
//		
//		// Global vars
//		BDDDomain[] d = new BDDDomain[(tbound - 1)*gnum];
//		int index = 0;
//		if (globals != null) {
//			for (Variable var : globals.values()) {
//				for (int i = 1; i <= tbound; i++) {
//					if (i == tid) continue;
//					d[index++] = doms[var.getIndex() + varcopy + i - 1];
//				}
//			}
//		}
//		
//		// Heap
//		if (getHeapSize() > 1) {
//			for (int i = 1; i <= tbound; i++) {
//				if (i == tid) continue;
//				d[index++] = doms[hpDomIndex + varcopy + i - 1];
//			}
//			for (int j = 0; j < getHeapSize(); j++) {
//				for (int i = 1; i <= tbound; i++) {
//					if (i == tid) continue;
//					d[index++] = doms[hDomIndex + globalcopy*j + varcopy + i - 1];
//				}
//			}
//		}
//		
//		gtidVarSetWithout[tid - 1] = factory.makeSet(d);
//		return gtidVarSetWithout[tid - 1];
//	}
	
	private BDDVarSet lvspVarSet = null;
	
	private BDDVarSet getLvSpVarSet() {
		
		if (lvspVarSet != null) return lvspVarSet;
		
		int i = 0;
		BDDDomain[] d = new BDDDomain[(smax > 0) ? lvmax + 1 : lvmax];
		if (smax > 0) {
			d[i++] = getStackPointerDomain();
		}
		for (int j = 0; j < lvmax; j++) {
			d[i++] = getLocalVarDomain(j);
		}
		
		lvspVarSet = factory.makeSet(d);
		return lvspVarSet;
	}
	
	public BDD abstractLocalVarsAndStackPointer(BDD a) {
		
		BDDVarSet lvspvs = getLvSpVarSet();
		return a.exist(lvspvs);
	}
	
	private BDDVarSet sVarSet = null;
	
	private BDDVarSet getStackVarSet() {
		
		if (sVarSet != null) return sVarSet;
		
		BDDDomain[] d = new BDDDomain[smax];
		for (int i = 0; i < smax; i++) {
			d[i] = getStackDomain(i);
		}
		
		sVarSet = factory.makeSet(d);
		return sVarSet;
	}
	
	public BDD abstractStack(BDD a) {
		
		return a.exist(getStackVarSet());
	}
	
	/**
	 * Returns the default integer bits.
	 * 
	 * @return the default integer bits.
	 */
	public int getBits() {
		return bits;
	}
	
	public int getMaxInt() {
		return maxint;
	}
	
	/**
	 * Returns 2^bits.
	 * 
	 * @return 2^bits.
	 */
	public long size() {
		
		return size;
	}
	
	public BDDDomain[] getDomains() {
		
		return doms;
	}
	
	public BDDDomain getDomain(int index) {
		
		return doms[index];
	}
	
	public BDDFactory getFactory() {
		
		return factory;
	}
	
	public BDDVarSet getVarSetWithout(int index) {
		
		if (varSetWithout == null) 
			varSetWithout = new HashMap<Integer, BDDVarSet>();
		
		BDDVarSet varset = varSetWithout.get(index);
		if (varset != null) return varset;
		
		BDDDomain[] d = new BDDDomain[factory.numberOfDomains() - 1];
		for (int i = 0, j = 0; i < factory.numberOfDomains(); i++) {
			if (i != index) {
				d[j++] = factory.getDomain(i);
			}
				
		}
		varset = factory.makeSet(d);
		varSetWithout.put(index, varset);
		
		return varset;
	}
	
	public BDDVarSet getVarSetWithout(Set<Integer> indices) {
		
		BDDDomain[] d = new BDDDomain[factory.numberOfDomains() - indices.size()];
		for (int i = 0, j = 0; i < factory.numberOfDomains(); i++) {
			if (indices.contains(i)) continue;
			d[j++] = factory.getDomain(i);
		}
		return factory.makeSet(d);
	}
	
	/**
	 * Returns the variable having the specified name.
	 * 
	 * @param name the name of the variable
	 * @return the variable
	 */
	public Variable getGlobalVar(String name) {
		
		if (globals == null) return null;
		return globals.get(name);
	}
	
	public BDDDomain getGlobalVarDomain(String name) {
		
		Variable var = getGlobalVar(name);
		if (var == null) return null;
		return doms[var.getIndex()];
	}
	
	public BDDDomain getRetVarDomain() {
		
		if (retDomIndex == -1) return null;	// TODO this never happen because we always add ret var
		return doms[retDomIndex];
	}
	
	public BDDDomain getTempVarDomain() {
		
		return doms[retDomIndex];
	}
	
	public BDDDomain getHeapPointerDomain() {
		
		if (hpDomIndex == -1) return null;
		return doms[hpDomIndex];
	}
	
	public int getHeapDomainIndex(int index) {
		
		if (hDomIndex == -1) return -1;
		return hDomIndex + globalcopy*index;
	}
	
	public int getHeapDomainIndex(long index) {
		
		return getHeapDomainIndex((int) index);
	}
	
	/**
	 * Returns the BDDDomain of the heap at <code>ptr</code>.
	 * 
	 * @return the BDDDomain of the heap at <code>ptr</code>.
	 */
	public BDDDomain getHeapDomain(int index) {
		return doms[getHeapDomainIndex(index)];
	}
	
	public BDDDomain getHeapDomain(long index) {
		
		return getHeapDomain((int) index);
	}
	
	BDDDomain getObjectTypeDomain(long ptr) {
		return getHeapDomain(ptr);
	}
	
	/**
	 * Returns the number of blocks required for storing
	 * auxiliary information of an array.
	 * 
	 * @return two in normal case; or four in case of lazy splitting.
	 */
	int getArrayAuxSize() {
		return (multithreading() && symbolic()) ? 4 : 2;
	}
	
	/**
	 * Returns the BDDDomain representing the array length 
	 * from the heap at <code>ptr</code>.
	 * 
	 * @return the BDDDomain representing the array length 
	 * 			from the heap at <code>ptr</code>.
	 */
	BDDDomain getArrayLengthDomain(long ptr) {
		return getHeapDomain(ptr + getArrayAuxSize() - 1);
	}
	
	BDDDomain getArrayElementDomain(long ptr, int index) {
		return getHeapDomain(ptr + getArrayAuxSize() + index);
	}
	
	BDDDomain getOwnerThreadDomain(long ptr) {
		return getHeapDomain(ptr + 1);
	}
	
	BDDDomain getOwnerCounterDomain(long ptr) {
		return getHeapDomain(ptr + 2);
	}
	
	public BDDDomain getStackPointerDomain() {
		
		if (spDomIndex == -1) return null;
		return doms[spDomIndex];
	}
	
	/**
	 * Gets the <code>BDDDomain</code> of the stack element at <code>index</code>.
	 * 
	 * @param index the stack element index.
	 * @return the <code>BDDDomain</code> of the stack element.
	 */
	public BDDDomain getStackDomain(int index) {
		if (sDomIndex == -1) return null;
		return doms[sDomIndex + index];
	}
	
	public BDDDomain getLocalVarDomain(int index) {
		
		if (lvDomIndex == -1) return null;
		return doms[lvDomIndex + varcopy*index];
	}
	
	/**
	 * Creates BDD for If expression.
	 * 
	 * @param expr
	 * @param sdom
	 * @return
	 */
	BDD ifBDD(ExprSemiring.If expr, BDDDomain sdom) {
		
		int bits = getBits();
		switch (expr.type) {
		
		case EQ:
			return sdom.ithVar(0);
				
		case NE:
			return sdom.ithVar(0).not();
			
		case LT:
			return factory.ithVar(sdom.vars()[bits-1]);
			
		case GE:
			return factory.nithVar(sdom.vars()[bits-1]);
			
		case GT:
			return factory.nithVar(sdom.vars()[bits-1])
					.andWith(sdom.ithVar(0).not());
			
		case LE:
			return factory.ithVar(sdom.vars()[bits-1])
					.orWith(sdom.ithVar(0));
			
		case IS:
			return sdom.ithVar(expr.getValue());
			
		case LG: {
			BDD a = factory.zero();
			for (int i = expr.getLowValue(); i <= expr.getHighValue(); i++) {
				a.orWith(sdom.ithVar(encode(i, sdom)));
			}
			BDD b = a.not();
			a.free();
			return b;
		}
		
		case NOT: {
			Set<Integer> set = expr.getNotSet();
			BDD a = factory.zero();
			for (int i : set) {
				a.orWith(sdom.ithVar(encode(i, sdom)));
			}
			BDD b = a.not();
			a.free();
			return b;
		}
		}
		
		throw new IllegalArgumentException("Invalid comparison type: " + expr.type);
	}
	
	/**
	 * Returns the bdd representing the equality of two variables 
	 * specified by dom1 and dom2.
	 * 
	 * @param dom1
	 * @param dom2
	 * @return
	 */
	public BDD bddEquals(BDDDomain dom1, BDDDomain dom2) {
		
		BigInteger size1 = dom1.size();
		BigInteger size2 = dom2.size();
		
		// Uses the library function if the domains have the same size
		if (size1.equals(size2))
			return dom1.buildEquals(dom2);
		
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
		
		BDD a = factory.one();
		int i;
		for (i = 0; i < lessvars.length - 1; i++) {
			BDD b = factory.ithVar(lessvars[i]).andWith(factory.ithVar(morevars[i]));
			b.orWith(factory.nithVar(lessvars[i]).andWith(factory.nithVar(morevars[i])));
			a.andWith(b);
		}
		
		// Sign-bit extension: zero
		BDD b = factory.ithVar(lessvars[i]);
		for (int j = i; j < morevars.length; j++)
			b.andWith(factory.ithVar(morevars[j]));

		// Sign-bit extension: one
		BDD c = factory.nithVar(lessvars[i]);
		for (int j = i; j < morevars.length; j++)
			c.andWith(factory.nithVar(morevars[j]));
		
		a.andWith(b.orWith(c));
		return a;
	}
	
	private BDD G0L0equalsG1L1 = null;
	
	public BDD buildG0L0equalsG1L1() {
		
		if (G0L0equalsG1L1 != null) return G0L0equalsG1L1;
		
		G0L0equalsG1L1 = factory.one();
		for (int i = 0; i < gnum; i++) {
			int index = g0 + globalcopy*i;
			G0L0equalsG1L1.andWith(doms[index].buildEquals(doms[index + gindex[1]]));
		}
		for (int i = 0; i < lvmax; i++) {
			int index = lvDomIndex + varcopy*i;
			G0L0equalsG1L1.andWith(doms[index].buildEquals(doms[index + 1]));
		}
		
		return G0L0equalsG1L1;
	}
	
//	private BDD[] G0equalsGtid;
//	
//	public BDD buildG0equalsGtid(int tid) {
//		
//		if (G0equalsGtid == null)
//			G0equalsGtid = new BDD[tbound];
//		
//		if (G0equalsGtid[tid - 1] != null)
//			return G0equalsGtid[tid - 1];
//		
//		int offset = varcopy + tid - 1;
//		BDD a = factory.one();
//		for (int i = 0; i < gnum; i++) {
//			int index = g0 + globalcopy*i;
//			a.andWith(doms[index].buildEquals(doms[index + offset]));
//		}
//		G0equalsGtid[tid - 1] = a;
//		return a;
//	}
	
	private BDD G0equalsG3;
	
	public BDD buildG0equalsG3() {
		
		if (G0equalsG3 != null)
			return G0equalsG3;
		
		G0equalsG3 = factory.one();
		for (int i = 0; i < gnum; i++) {
			int index = g0 + globalcopy*i;
			G0equalsG3.andWith(doms[index].buildEquals(doms[index + gindex[3]]));
		}
		
		return G0equalsG3;
	}
	
	private BDD G3equalsG4;
	
	public BDD buildG3equalsG4() {
		
		if (G3equalsG4 != null)
			return G3equalsG4;
		
		G3equalsG4 = factory.one();
		for (int i = 0; i < gnum; i++) {
			int index = g0 + globalcopy*i;
			G3equalsG4.andWith(doms[index + gindex[3]].buildEquals(doms[index + gindex[4]]));
		}
		
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
	BDD bddL0equalsL2params(int s, boolean[] params) {
		
		BDD d = factory.one();
		for (int i = 0, j = 0; i < params.length; i++, j++) {
			d.andWith(getStackDomain(s+i).buildEquals(doms[l0 + varcopy*j + 2]));
			
			// Skips one local variable is the argument is long or double
			if (params[i]) {
				j++;
			}
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
	
	public BDD bddRange(BDDDomain dom, int min, int max) {
		
		if (min == max)
			return dom.ithVar(min);
		
		// Handles manually, because the library seems to be wrong in this case
		if (min == 0 && max == 1)
			return dom.ithVar(0).orWith(dom.ithVar(1));
		
		if (min >= 0) 
			return dom.varRange(encode(min, dom), encode(max, dom));
		
		BDD a = factory.zero();
		for (int i = min; i <= max; i++) {
			a.orWith(dom.ithVar(encode(i, dom)));
		}
		
		return a;
	}
	
	public BDDIterator iterator(BDD bdd, BDDDomain dom) {
		
		BDDVarSet varset = dom.set();
		BDDIterator itr = bdd.exist(getVarSetWithout(dom.getIndex())).iterator(varset);
		varset.free();
		
		return itr;
	}
	
	public BDDIterator iterator(BDD bdd, BDDDomain[] doms) {
		
		// Collects var set and indices
		BDDVarSet varset = factory.emptySet();
		Set<Integer> indices = new HashSet<Integer>((int) (1.4*doms.length));
		for (int i = 0; i < doms.length; i++) {
			varset.unionWith(doms[i].set());
			indices.add(doms[i].getIndex());
		}
		
		// Abstracts and creates iterator
		BDDVarSet abs = getVarSetWithout(indices);
		BDDIterator itr = bdd.exist(abs).iterator(varset);
		abs.free();
		varset.free();
		
		return itr;
	}
	
	private int nargs;
	private BDDDomain[] argDoms;
	
	public BDD saveArgs(int hp, int nargs) {
	
		this.nargs = nargs;
		if (nargs <= 0) return factory.one();
		
		long[] domSize = new long[nargs + hp - 1];
		int j = 0;
		for (int i = 0; i < nargs; i++)
			domSize[j++] = size;
		for (int i = 1; i < hp; i++)
			domSize[j++] = heapSizes[i];
		argDoms = factory.extDomain(domSize);
		BDD bdd = factory.one();
		j = 0;
		for (int i = 0; i < nargs; i++)
			bdd.andWith(getLocalVarDomain(i).buildEquals(argDoms[j++]));
		for (int i = 1; i < hp; i++)
			bdd.andWith(getHeapDomain(i).buildEquals(argDoms[j++]));
		return bdd;
	}
	
	public List<RawArgument> getRawArguments(BDD a) {
		
		// Abstracts everything else
		BDDVarSet abs = factory.emptySet();
		for (int i = 0; i < doms.length; i++)
			abs.unionWith(doms[i].set());
		BDD b = a.exist(abs);
		
		// Gets iterator
		BDDVarSet vs = factory.emptySet();
		for (int i = 0; i < argDoms.length; i++)
			vs.unionWith(argDoms[i].set());
		BDDIterator itr = b.iterator(vs);
		
		// For each possible argument
		List<RawArgument> args = new ArrayList<RawArgument>();
		while (itr.hasNext()) {
			BDD c = itr.nextBDD();
			RawArgument arg = new RawArgument(nargs, argDoms.length - nargs);
			for (int i = 0; i < nargs; i++)
				arg.lv[i] = decode(c.scanVar(argDoms[i]).longValue(), argDoms[i]);
			for (int i = nargs; i < argDoms.length; i++)
				arg.heap[i - nargs] = decode(c.scanVar(argDoms[i]).longValue(), argDoms[i]);
			log("arg: %s%n", arg);
			args.add(arg);
			c.free();
		}
		
		vs.free();
		b.free();
		return args;
	}
	
	/**
	 * Signature of a: (G0,L0,G1,L1)
	 * 
	 * @param a
	 * @return
	 */
	public List<RawArgument> getRawArguments2(BDD a) {
		
		log("a: %s%n", a.toStringWithDomains());
		
		// Abstracts G0 and L0
		BDDVarSet abs = getGlobalVarSet().union(getLocalVarSet());
		BDD b = a.exist(abs);
		abs.free();
		
		// Gets iterator
		BDDIterator itr = b.iterator(getG1L1VarSet());
		
		// For each possible argument
		List<RawArgument> args = new ArrayList<RawArgument>();
		while (itr.hasNext()) {
			BDD c = itr.nextBDD();
			RawArgument arg = new RawArgument(lvmax, heapSizes.length - 1);
			for (int i = 0; i < lvmax; i++) {
				BDDDomain dom = doms[l0 + varcopy*i + 1];
				arg.lv[i] = decode(c.scanVar(dom).longValue(), dom);
			}
			for (int i = 0; i < heapSizes.length - 1; i++) {
				BDDDomain dom = doms[hDomIndex + globalcopy*(i+1) + 1];
				arg.heap[i] = decode(c.scanVar(dom).longValue(), dom);
			}
			log("arg: %s%n", arg);
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
	
	private ArrayList<String> strings = new ArrayList<String>();
	
	public List<String> getStrings() {
		return strings;
	}
	
	public long encode(String raw, BDDDomain dom) {
		
		// Adds a dummy string at index zero for preventing NPE
		if (strings.isEmpty())
			strings.add("");
		
		// Returns the index if the string already exists
		int index = strings.indexOf(raw);
		if (index != -1) return index;
		
		index = strings.size();
		if (index >= dom.size().intValue())
			System.err.println("Too many strings");
		strings.add(raw);
		return index;
	}
	
	public String decodeString(long encoded) {
		return strings.get((int) encoded);
	}
	
	private ArrayList<Float> floats = new ArrayList<Float>();
	
	public List<Float> getFloats() {
		return floats;
	}
	
	/**
	 * Encodes the float <code>raw</code>.
	 * 
	 * @param raw
	 * @param dom
	 * @return
	 */
	public long encode(float raw, BDDDomain dom) {
		int index = floats.indexOf(raw);
		if (index != -1) return index;
		
		index = floats.size();
		if (index >= dom.size().intValue())
			System.err.println("Too many floats");
		floats.add(raw);
		return index;
	}
	
	public float decodeFloat(long encoded) {
		return floats.get((int) encoded);
	}
	
	/**
	 * Encodes <code>raw</code> in two-complement format.
	 * 
	 * @param raw
	 * @return
	 */
	public static long encode(int raw, BDDDomain dom) {
		
//		long maxint = dom.size().longValue()/2 - 1;
//		if (raw >= 0) 
//			return ((long) raw) & maxint;
		
		if (raw == Integer.MAX_VALUE)
			return dom.size().longValue()/2 - 1;
		
		if (raw == Integer.MIN_VALUE)
			return dom.size().longValue()/2;
		
		long max = dom.size().longValue() - 1;
		if (raw >= 0)
			return ((long) raw) & max;
		
		long result = (long) raw;
		do
			result += dom.size().longValue();
		while (result < 0);
		return result;
	}
	
	public static int decode(long encoded, BDDDomain dom) {
		
		int maxint = (int) (dom.size().longValue()/2 - 1);
		if (maxint == 0 || encoded <= maxint) 
			return (int) encoded;
		
		return (int) (encoded - dom.size().longValue());
	}
	
	public static boolean isNeg(long v, BDDDomain dom) {
		
		return v > dom.size().longValue()/2 - 1;
	}
	
	public long arith(ArithType type, BDDDomain rdom, 
			long v1, BDDDomain dom1, long v2, BDDDomain dom2) {
		
		switch (type) {
		case ADD:
			return encode(decode(v1, dom1) + decode(v2, dom2), rdom);
		case AND:
			return encode(decode(v1, dom1) & decode(v2, dom2), rdom);
		case CMP: {
			int de1 = decode(v1, dom1);
			int de2 = decode(v2, dom2);
			if (de1 > de2) return encode(1, rdom);
			if (de1 == de2) return encode(0, rdom);
			return encode(-1, rdom);
		}
		case DIV:
			return encode(decode(v1, dom1) / decode(v2, dom2), rdom);
		case MUL:
			return encode(decode(v1, dom1) * decode(v2, dom2), rdom);
		case OR:
			return encode(decode(v1, dom1) | decode(v2, dom2), rdom);
		case REM:
			return encode(decode(v1, dom1) % decode(v2, dom2), rdom);
		case SHL:
			return encode(decode(v1, dom1) << (decode(v2, dom2) & 31), rdom);
		case SHR:
			return encode(decode(v1, dom1) >> (decode(v2, dom2) & 31), rdom);
		case SUB:
			return encode(decode(v1, dom1) - decode(v2, dom2), rdom);
		case USHR:
			return encode(decode(v1, dom1) >>> (decode(v2, dom2) & 31), rdom);
		case XOR:
			return encode(decode(v1, dom1) ^ decode(v2, dom2), rdom);
		case FADD:
			return encode(decodeFloat(v1) + decodeFloat(v2), rdom);
		case FCMPG: 
		case FCMPL: {
			float f1 = decodeFloat(v1);
			float f2 = decodeFloat(v2);
			if (f1 > f2) return encode(1, rdom);
			else if (f1 == f2) return encode(0, rdom);
			else if (f1 < f2) return encode(-1, rdom);
			// At least one must be NaN
			else if (type == ArithType.FCMPG) return encode(1, rdom);
			else return encode(-1, rdom);
		}
		case FDIV:
			return encode(decodeFloat(v1) / decodeFloat(v2), rdom);
		case FMUL:
			return encode(decodeFloat(v1) * decodeFloat(v2), rdom);
		case FREM:
			return encode(decodeFloat(v1) % decodeFloat(v2), rdom);
		case FSUB:
			return encode(decodeFloat(v1) - decodeFloat(v2), rdom);
			
		default:
			throw new IllegalArgumentException("Invalid ArithType: " + type);
		}
	}
	
	public long fneg(long v, BDDDomain dom) {
		float f = decodeFloat(v);
		return encode(-f, dom);
	}
	
	/**
	 * Returns the negation of v in two-complement format.
	 * For example, if bits = 3, then the following input/output pairs valid:
	 * 0->0, 1->4, 2->5, 3->6, 4->1 5->2, 6->3, 7->3.
	 * 
	 * Note that an overflow occurs when negating the minimum (negative) value.
	 * In the example, 7(-4) -> 4(-1).
	 * 
	 * @param v the value to be negated.
	 * @return the negation of v.
	 */
	public long neg(long v) {
		
		if (v == 0) return 0;
		
		return (v <= maxint) ? v + maxint : v - maxint;
	}
	
	private static final int TO_STRING_BOUND = 20;
	
	public String toString(BDD a, String separator, BDD restrictor) {
		
		// Abstracts G1, L1, G2, L2, unused stack elements, and return variable
		BDDVarSet abs = getG1L1VarSet().union(getG2L2VarSet());
		int sp = a.scanVar(getStackPointerDomain()).intValue();
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
		int nargs = (argDoms == null) ? 0 : argDoms.length;
		BDDDomain[] d = new BDDDomain[gnum + lvmax + sp + nargs];
		int j = 0;
		for (int i = 0; i < gnum; i++)
			d[j++] = doms[g0 + globalcopy*i];
		for (int i = 0; i < lvmax; i++)
			d[j++] = doms[l0 + varcopy*i];
		for (int i = 0; i < sp; i++)
			d[j++] = getStackDomain(i);
		for (int i = 0; i < nargs; i++)
			d[j++] = argDoms[i];
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
					gv.add(String.format("%s: %d", name, b.scanVar(getGlobalVarDomain(name))));
				}
				state.add(toCommaString(gv));
			}
			
			if (getHeapSize() > 1) {
				int ptr = b.scanVar(getHeapPointerDomain()).intValue();
				state.add(String.format("ptr: %d", ptr));
				
				ArrayList<Integer> heap = new ArrayList<Integer>((int) (1.4*getHeapSize()));
				for (int i = 0; i < ptr; i++) {
					heap.add(b.scanVar(getHeapDomain(i)).intValue());
				}
				state.add(String.format("heap: [%s]", toCommaString(heap)));
			}
			
			if (lvmax > 0) {
				ArrayList<Integer> lv = new ArrayList<Integer>((int) (1.4*lvmax));
				for (int i = 0; i < lvmax; i++) {
					lv.add(b.scanVar(getLocalVarDomain(i)).intValue());
				}
				state.add(String.format("lv: [%s]", toCommaString(lv)));
			}
			
			if (sp > 0) {
				ArrayList<Integer> s = new ArrayList<Integer>((int) (1.4*sp));
				for (int i = 0; i < sp; i++) {
					s.add(b.scanVar(getStackDomain(i)).intValue());
				}
				state.add(String.format("stack: [%s]", toCommaString(s)));
			}
			
			if (nargs > 0) {
				ArrayList<Integer> args = new ArrayList<Integer>((int) (1.4*nargs));
				for (int i = 0; i < nargs; i++) {
					args.add(b.scanVar(argDoms[i]).intValue());
				}
				state.add(String.format("args: [%s]", toCommaString(args)));
			}
			
//			System.out.println(toCommaString(state));
			all.add(toCommaString(state));
			b.free();
		}
		
		if (count >= TO_STRING_BOUND) {
			all.add("toString() bound reached, skipping the rest");
		}
		
		return toString(all, separator);
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
	
	private static enum DomainType {
		G0, G1, G2, G3, G4, G1L1, G2L2;
	}
	
	private EnumMap<DomainType, BDDDomain[]> domains 
			= new EnumMap<DomainType, BDDDomain[]>(DomainType.class);
	
	private BDDDomain[] putGxDomain(DomainType type, int x) {
		if (domains.containsKey(type))
			return domains.get(type);
		
		BDDDomain[] d = new BDDDomain[gnum];
		for (int i = 0; i < gnum; i++)
			d[i] = doms[g0 + globalcopy*i + gindex[x]];
		
		domains.put(type, d);
		return d;
	}
	
	private BDDDomain[] getGxDomain(int x) {
		switch (x) {
		case 0: return putGxDomain(DomainType.G0, 0);
		case 1: return putGxDomain(DomainType.G1, 1);
		case 2: return putGxDomain(DomainType.G2, 2);
		case 3: return putGxDomain(DomainType.G3, 3);
		case 4: return putGxDomain(DomainType.G4, 4);
		}
		
		throw new RemoplaError("Unexpected G%d domain", x);
	}
	
	private BDDDomain[] putGxLxDomain(DomainType type, int x) {
		if (domains.containsKey(type))
			return domains.get(type);
		
		BDDDomain[] d = new BDDDomain[gnum + lvmax];
		int j = 0;
		for (int i = 0; i < gnum; i++)
			d[j++] = doms[g0 + globalcopy*i + gindex[x]];
		for (int i = 0; i < lvmax; i++)
			d[j++] = doms[l0 + varcopy*i + x];
		
		domains.put(type, d);
		return d;
	}
	
	private BDDDomain[] getG1L1Domain() {
		return putGxLxDomain(DomainType.G1L1, 1);
	}
	
	private BDDDomain[] getG2L2Domain() {
		return putGxLxDomain(DomainType.G2L2, 2);
	}
	
	/*************************************************************************
	 * Methods for computing BDDVarSet
	 *************************************************************************/
	
	private static enum VarSetType {
		G0L0, G0G1G2L0L1L2, G0L0G1L1, L0G1L1, L0G1L1G2L2, G0G4, G1L1, G2L2, G0, G3, G4;
	}
	
	private EnumMap<VarSetType, BDDVarSet> varsets 
			= new EnumMap<VarSetType, BDDVarSet>(VarSetType.class);
	
	private BDDVarSet putVarSet(VarSetType type, BDDDomain[] d) {
		BDDVarSet vs = factory.makeSet(d);
		varsets.put(type, vs);
		return vs;
	}
	
	BDDVarSet getVarSet0() {
		
		if (varsets.containsKey(VarSetType.G0L0))
			return varsets.get(VarSetType.G0L0);
		
		int base = gnum + lvmax;
		BDDDomain[] d = new BDDDomain[base + ((smax > 0) ? smax + 1 : 0)];
		int j = 0;
		for (int i = 0; i < gnum; i++)
			d[j++] = doms[g0 + globalcopy*i];
		for (int i = 0; i < lvmax; i++)
			d[j++] = doms[l0 + VarManager.varcopy*i];
		if (smax > 0) {
			d[j++] = getStackPointerDomain();
			for (int i = 0; i < smax; i++)
				d[j++] = getStackDomain(i);
		}
		
		return putVarSet(VarSetType.G0L0, d);
	}
	
	BDDVarSet getG0G1G2L0L1L2VarSet() {
		
		if (varsets.containsKey(VarSetType.G0G1G2L0L1L2))
			return varsets.get(VarSetType.G0G1G2L0L1L2);
		
		BDDDomain[] d = new BDDDomain[3*gnum + 3*lvmax + ((smax > 0) ? smax + 1 : 0)];
		int j = 0;
		for (int i = 0; i < gnum; i++) {
			d[j++] = doms[g0 + globalcopy*i];
			d[j++] = doms[g0 + globalcopy*i + gindex[1]];
			d[j++] = doms[g0 + globalcopy*i + gindex[2]];
		}
		for (int i = 0; i < lvmax; i++) {
			d[j++] = doms[l0 + VarManager.varcopy*i];
			d[j++] = doms[l0 + VarManager.varcopy*i + 1];
			d[j++] = doms[l0 + VarManager.varcopy*i + 2];
		}
		if (smax > 0) {
			d[j++] = getStackPointerDomain();
			for (int i = 0; i < smax; i++)
				d[j++] = getStackDomain(i);
		}
		
		return putVarSet(VarSetType.G0G1G2L0L1L2, d);
	}
	
	BDDVarSet getG0L0G1L1VarSet() {
		
		if (varsets.containsKey(VarSetType.G0L0G1L1))
			return varsets.get(VarSetType.G0L0G1L1);
		
		BDDDomain[] d = new BDDDomain[2*gnum + 2*lvmax + ((smax > 0) ? smax + 1 : 0)];
		int j = 0;
		for (int i = 0; i < gnum; i++) {
			d[j++] = doms[g0 + globalcopy*i];
			d[j++] = doms[g0 + globalcopy*i + gindex[1]];
		}
		for (int i = 0; i < lvmax; i++) {
			d[j++] = doms[l0 + varcopy*i];
			d[j++] = doms[l0 + varcopy*i + 1];
		}
		if (smax > 0) {
			d[j++] = getStackPointerDomain();
			for (int i = 0; i < smax; i++)
				d[j++] = getStackDomain(i);
		}
		
		return putVarSet(VarSetType.G0L0G1L1, d);
	}
	
	BDDVarSet getL0G1L1VarSet() {
		
		if (varsets.containsKey(VarSetType.L0G1L1))
			return varsets.get(VarSetType.L0G1L1);
		
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
		
		return putVarSet(VarSetType.L0G1L1, d);
	}
	
	BDDVarSet getL0G1L1G2L2VarSet() {
		
		if (varsets.containsKey(VarSetType.L0G1L1G2L2))
			return varsets.get(VarSetType.L0G1L1G2L2);
		
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
		
		return putVarSet(VarSetType.L0G1L1G2L2, d);
	}
	
	BDDVarSet getG0G4VarSet() {
		
		if (varsets.containsKey(VarSetType.G0G4))
			return varsets.get(VarSetType.G0G4);
		
		BDDDomain[] d = new BDDDomain[2*gnum];
		int j = 0;
		for (int i = 0; i < gnum; i++) {
			d[j++] = doms[g0 + globalcopy*i];
			d[j++] = doms[g0 + globalcopy*i + gindex[4]];
		}
		
		return putVarSet(VarSetType.G0G4, d);
	}
	
	BDDVarSet getG1L1VarSet() {
		
		if (varsets.containsKey(VarSetType.G1L1))
			return varsets.get(VarSetType.G1L1);
		
//		BDDDomain[] d = new BDDDomain[gnum + lvmax];
//		int j = 0;
//		for (int i = 0; i < gnum; i++)
//			d[j++] = doms[g0 + globalcopy*i + gindex[1]];
//		for (int i = 0; i < lvmax; i++)
//			d[j++] = doms[l0 + varcopy*i + 1];
		
		return putVarSet(VarSetType.G1L1, getG1L1Domain());
	}
	
	BDDVarSet getG2L2VarSet() {
		
		if (varsets.containsKey(VarSetType.G2L2))
			return varsets.get(VarSetType.G2L2);
		
//		BDDDomain[] d = new BDDDomain[gnum + lvmax];
//		int j = 0;
//		for (int i = 0; i < gnum; i++)
//			d[j++] = doms[g0 + globalcopy*i + gindex[2]];
//		for (int i = 0; i < lvmax; i++)
//			d[j++] = doms[l0 + varcopy*i + 2];
		
		return putVarSet(VarSetType.G2L2, getG2L2Domain());
	}
	
	private BDDVarSet getGxVarSet(VarSetType type, int x) {
		if (varsets.containsKey(type))
			return varsets.get(type);
		
		return putVarSet(type, getGxDomain(x));
	}
	
	BDDVarSet getG0VarSet() {
		return getGxVarSet(VarSetType.G0, 0);
	}
	
	BDDVarSet getG3VarSet() {
		return getGxVarSet(VarSetType.G3, 3);
	}
	
	BDDVarSet getG4VarSet() {
		return getGxVarSet(VarSetType.G4, 4);
	}
	
	/*************************************************************************
	 * Methods for renaming BDD variables
	 *************************************************************************/
	
	private static enum PairingType {
		G1L1_G2L2, G0_G2, G0_G3, G3_G4;
	}
	
	private EnumMap<PairingType, BDDPairing> pairings 
			= new EnumMap<PairingType, BDDPairing>(PairingType.class);
	
	private BDDPairing putPairing(PairingType type, BDDDomain[] d1, BDDDomain[] d2) {
		BDDPairing p = factory.makePair();
		p.set(d1, d2);
		pairings.put(type, p);
		return p;
	}
	
//	/**
//	 * Changes the signature of a from (...,G1,L1,...) to (...,G2,L2,...).
//	 * The bdd a is mutated.
//	 * 
//	 * @param a
//	 * @return
//	 */
//	BDD replaceG1L1withG2L2(BDD a) {
//		
//		
//		
//		for (int i = 0; i < gnum; i++) {
//			int index = g0 + globalcopy*i;
//			replaceWith(a, index + gindex[1], index + gindex[2]);
//		}
//		for (int i = 0; i < lvmax; i++) {
//			int index = l0 + varcopy*i + 1;
//			replaceWith(a, index, index + 1);
//		}
//		
//		return a;
//	}
	
	BDDPairing getG1L1pairG2L2() {
		if (pairings.containsKey(PairingType.G1L1_G2L2))
			return pairings.get(PairingType.G1L1_G2L2);
		
		return putPairing(PairingType.G1L1_G2L2, getG1L1Domain(), getG2L2Domain());
	}
	
//	private BDD replaceG0withGx(BDD a, int x) {
//		for (int i = 0; i < gnum; i++) {
//			int index = g0 + globalcopy*i;
//			replaceWith(a, index, index + gindex[x]);
//		}
//		
//		return a;
//	}
	
//	BDD replaceG0withG2(BDD a) {
//		return replaceG0withGx(a, 2);
//	}
	
	private BDDPairing getGxpairGy(PairingType type, int x, int y) {
		if (pairings.containsKey(type))
			return pairings.get(type);
		
		return putPairing(type, getGxDomain(x), getGxDomain(y));
	}
	
	BDDPairing getG0pairG2() {
		return getGxpairGy(PairingType.G0_G2, 0, 2);
	}
	
	BDDPairing getG0pairG3() {
		return getGxpairGy(PairingType.G0_G3, 0, 3);
	}
	
//	BDD replaceG0withG3(BDD a) {
////		return replaceG0withGx(a, 3);
//		return a.replaceWith(getG0pairG3());
//	}
	
	BDDPairing getG3pairG4() {
		return getGxpairGy(PairingType.G3_G4, 3, 4);
	}
	
//	BDD replaceG3withG4(BDD a) {
//		for (int i = 0; i < gnum; i++) {
//			int index = g0 + globalcopy*i;
//			replaceWith(a, index + gindex[3], index + gindex[4]);
//		}
//		
//		return a;
//	}
	
//	BDD replaceG0withGtid(BDD a, int tid) {
//		
//		for (int i = 0; i < gnum; i++) {
//			int index = g0 + globalcopy*i;
//			replaceWith(a, index, index + varcopy + tid - 1);
//		}
//		
//		return a;
//	}
	
//	private BDD replaceWith(BDD a, int i1, int i2) {
//		return a.replaceWith(factory.makePair(doms[i1], doms[i2]));
//	}
	
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
	
	/**
	 * Sets the verbosity level.
	 * 
	 * @param level the verbosity level.
	 */
	public static void setVerbosity(int level) {
		verbosity = level;
	}
	
	/**
	 * Logs translator information.
	 * 
	 * @param msg
	 * @param args
	 */
	public static void log(String msg, Object... args) {
		log(2, msg, args);
	}
	
	/**
	 * Logs translator information.
	 * 
	 * @param msg
	 * @param args
	 */
	public static void info(String msg, Object... args) {
		log(1, msg, args);
	}
	
	private static void log(int threshold, String msg, Object... args) {
		if (verbosity >= threshold)
			logger.fine(String.format(msg, args));
	}
	
	public String toString() {
		
		StringBuilder out = new StringBuilder();
		out.append(String.format("Bits: %d, Heap Size: %d%n", bits, getHeapSize(), g0));
		out.append(String.format("g0: %d, gnum: %d, hpDomIndex: %d, hDomIndex: %d%n", g0, gnum, hpDomIndex, hDomIndex));
		out.append(String.format("l0: %d, lvmax: %d, lvDomIndex: %d%n", l0, lvmax, lvDomIndex));
		out.append(String.format("smax: %d, spDomIndex, sDomIndex: %d%n", smax, spDomIndex, sDomIndex));
		
		return out.toString();
	}
	
	public void free() {
		
		if (localVarSet != null) localVarSet.free();
		
		if (sharedVarSet != null) sharedVarSet.free();
		if (nonSharedVarSet != null) nonSharedVarSet.free();
		
		if (lvspVarSet != null) lvspVarSet.free();
		
		if (globalVarSet != null) globalVarSet.free();
		
//		if (gtidVarSet != null) {
//			for (int i = 0; i < tbound; i++)
//				if (gtidVarSet[i] != null)
//					gtidVarSet[i].free();
//		}
		
//		if (gtidVarSetWithout != null) {
//			for (int i = 0; i < tbound; i++)
//				if (gtidVarSetWithout[i] != null)
//					gtidVarSetWithout[i].free();
//		}
		
		if (varSetWithout != null) {
			for (BDDVarSet a : varSetWithout.values())
				a.free();
		}
		
		if (G0L0equalsG1L1 != null) G0L0equalsG1L1.free();
		
//		if (G0equalsGtid != null) {
//			for (int i = 0; i < G0equalsGtid.length; i++) {
//				if (G0equalsGtid[i] != null)
//					G0equalsGtid[i].free();
//			}
//		}
		
		if (G0equalsG3 != null) G0equalsG3.free();
		
		if (G3equalsG4 != null) G3equalsG4.free();
		
		for (BDDVarSet vs : varsets.values())
			vs.free();
		
//		if (VarSet0 != null) VarSet0.free();
//		
//		if (g0g1g2l0l1l2VarSet != null) g0g1g2l0l1l2VarSet.free();
//		
//		if (g0l0g1l1VarSet != null) g0l0g1l1VarSet.free();
//		
//		if (l0g1l1VarSet != null) l0g1l1VarSet.free();
//		
//		if (l0g1l1g2l2VarSet != null) l0g1l1g2l2VarSet.free();
//		
//		if (g0g4VarSet != null) g0g4VarSet.free();
//		
//		if (g1l1VarSet != null) g1l1VarSet.free();
//		
//		if (g2l2VarSet != null) g2l2VarSet.free();
//		
//		if (g0VarSet != null) g0VarSet.free();
//		
//		if (g3VarSet != null) g3VarSet.free();
//		
//		if (g4VarSet != null) g4VarSet.free();
		
		if (g3g4ordering != null) g3g4ordering.free();
		
		factory.done();
		
	}
}
