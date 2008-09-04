package de.tum.in.jmoped.underbone;

import java.util.Arrays;
import java.util.Collection;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDVarSet;
import net.sf.javabdd.BDD.BDDIterator;

public class PoolManager {

	BDDManager bddmanager;
	
	int index;
	int[][] iglobal;
	int[] iptr;
	int[][] iheap;
	int[][] ilv;
	int[] isptr;
	int[][] istack;
	
	public PoolManager(String bddpackage, int nodenum, int cachesize, 
			int bits, Collection<Variable> g, int heaplength,
			int smax, int lvmax, int tbound, boolean lazy) {
		bddmanager = new BDDManager(bddpackage, nodenum, cachesize, 
				bits, g, heaplength, smax, lvmax, tbound, lazy);
		
		int varnum = 0;
		index = 0;
		
		if (g != null && !g.isEmpty()) {
			int i = 0;
			iglobal = new int[g.size()][1];
			for (Variable v : g) {
				v.setIndex(i++);
				iglobal[i][0] = index;
				index += bddmanager.globalcopy;
			}
			varnum += g.size()*bits*bddmanager.globalcopy;
		}
		
		if (heaplength > 0) {
			// Heap pointer
			iptr = new int[bits];
			for (int i = 0; i < bits; i++) {
				iptr[i] = index;
				index += bddmanager.globalcopy;
			}
			
			iheap = new int[heaplength][1];
			for (int i = 0; i < heaplength; i++) {
				iheap[i][0] = index;
				index += bddmanager.globalcopy;
			}
			varnum += (heaplength + 1)*bits*bddmanager.globalcopy;
		}
		
		bddmanager.l0 = varnum;
		if (lvmax > 0) {
			ilv = new int[lvmax][bits];
			for (int j = 0; j < bits; j++) {
				for (int i = 0; i < lvmax; i++) {
					ilv[i][j] = index;
					index += BDDManager.varcopy;
				}
			}
			varnum += lvmax*bits*BDDManager.varcopy;
		}
		
		if (smax > 0) {
			// Stack pointer
			isptr = new int[bits];
			for (int i = 0; i < bits; i++)
				isptr[i] = index++;
			
			istack = new int[smax][bits];
			for (int j = 0; j < bits; j++) {
				for (int i = 0; i < smax; i++) {
					istack[i][j] = index++;
				}
			}
			varnum += (smax + 1)*bits;
		}
		
		bddmanager.factory.extVarNum(varnum);
		if (BDDManager.log()) BDDManager.log(toString());
	}
	
	private PoolManager(BDDManager bddmanager) {
		this.bddmanager = bddmanager;
	}
	
	public PoolSemiring init() {
		BDD bdd = bddmanager.factory.one();
		if (iglobal != null) {
			for (int i = 0; i < iglobal.length; i++)
				bdd.andWith(ithVar(0, iglobal[i]));
		}
		if (iptr != null) {
			bdd.andWith(ithVar(0, iptr));
			for (int i = 0; i < iheap.length; i++)
				bdd.andWith(ithVar(0, iheap[i]));
		}
		if (isptr != null) {
			bdd.andWith(ithVar(0, iptr));
		}
		if (ilv != null) {
			for (int i = 0; i < ilv.length; i++)
				bdd.andWith(ithVar(0, ilv[i]));
		}
		
		return new PoolSemiring(this, bdd);
	}
	
	int[] iglobal(String name) {
		return iglobal[bddmanager.globals.get(name).getIndex()];
	}
	
	int sptr(BDD bdd) {
		return (int) BDDManager.scanVar(bdd, isptr);
	}
	
	BDDVarSet sptrSet() {
		return bddmanager.getFactory().makeSet(isptr);
	}
	
	BDD ithVarSptr(int value) {
		return ithVar(value, isptr);
	}
	
//	int[] istack(int sp) {
//		return istack[sp];
//	}
	
	BDDVarSet stackSet(int sp) {
		return bddmanager.getFactory().makeSet(istack[sp]);
	}
	
	BDD ithVarStack(int sp, long value) {
		return ithVar(value, istack[sp]);
	}
	
	BDD ithVar(long value, int[] ivar) {
		return bddmanager.ithVar(ivar, value);
	}
	
//	static long scanVar(BDD bdd, int[] ivar) {
//		long value = 0;
//		for (int i = 0; i < ivar.length; i++) {
//			value <<= 1;
//			value += scanVar(bdd, ivar[i]);
//		}
//		return value;
//	}
//	
//	static int scanVar(BDD bdd, int var) {
//        int thisvar = bdd.var();
//        if (thisvar < var) {
//			if (bdd.low().isZero()) return scanVar(bdd.high(), var);
//			return scanVar(bdd.low(), var);
//		}
//		if (thisvar == var) {
//			if (bdd.low().isZero()) return 1;
//			else return 0;
//		}
//		return 0;
//	}
	
	public static long encode(int raw, int[] ivar) {
		return BDDManager.encode(raw, (long) (1 << ivar.length));
	}
	
	public static int decode(long encoded, int[] ivar) {
		return BDDManager.decode(encoded, 1 << ivar.length);
	}
	
	public long encode(float raw, int[] ivar) {
		return bddmanager.encode(raw, 1 << ivar.length);
	}
	
	public long encode(String raw, int[] ivar) {
		return bddmanager.encode(raw, 1 << ivar.length);
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
	public BDD bddRange(int[] ivar, int min, int max) {
		
		if (min == max)
			return bddmanager.ithVar(ivar, min);
		
		BDD a = bddmanager.getFactory().zero();
		for (int i = min; i <= max; i++) {
			long e = encode(i, ivar);
			a.orWith(bddmanager.ithVar(ivar, e));
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
	public BDD bddRange(int[] ivar, float min, Number next, float max) {
		
		float step = (next == null) ? (max - min)/(bddmanager.size() - 1) : next.floatValue();
		
		BDD a = bddmanager.getFactory().zero();
		for (float i = min; i <= max; i += step) {
			long v = encode(i, ivar);
			a.orWith(ithVar(v, ivar));
		}
		
		return a;
	}
	
	public BDDIterator iterator(BDD bdd, int[] ivar) {
		BDDFactory factory = bddmanager.getFactory();
		BDDVarSet abs = factory.emptySet();
		int j = 0;
		int bits = ivar.length;
		for (int i = 0; i < factory.varNum(); i++) {
			if (j == bits || i < ivar[j]) {
				abs.unionWith(i);
			} else {	// i == ivar[j]
				j++;
			}
		}
		BDD c = bdd.exist(abs);
		abs.free();
		
		return c.iterator(factory.makeSet(ivar));
	}
	
	public PoolManager combine(PoolManager that) {
		if (iglobal.equals(that.iglobal) && iheap.equals(that.iheap))
			return this;
		
		PoolManager newmanager = new PoolManager(bddmanager);
		if (iglobal != null) {
			newmanager.iglobal = new int[iglobal.length][];
			for (int i = 0; i < iglobal.length; i++) {
				if (iglobal[i].length < that.iglobal[i].length)
					newmanager.iglobal[i] = that.iglobal[i];
				
			}
		}
		return null;
	}
	
	public PoolManager id() {
		PoolManager newmanager = new PoolManager(bddmanager);
		newmanager.iglobal = this.iglobal;
		newmanager.iptr = this.iptr;
		newmanager.iheap = this.iheap;
		newmanager.ilv = this.ilv;
		newmanager.isptr = this.isptr;
		newmanager.istack = this.istack;
		
		return newmanager;
	}
	
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("Global variables:\n");
		for (Variable v : bddmanager.globals.values()) {
			builder.append(String.format("\t%s: %s%n", 
					v.getName(), Arrays.toString(iglobal[v.getIndex()])));
		}
		builder.append("Heap:\n");
		if (bddmanager.heaplength > 0)
			builder.append(String.format("\tptr: %s%n", Arrays.toString(iptr)));
		for (int i = 0; i < bddmanager.heaplength; i++) {
			builder.append(String.format("\t%d: %s%n", i, iheap[i]));
		}
		builder.append("Local variables:\n");
		for (int i = 0; i < bddmanager.lvmax; i++) {
			builder.append(String.format("\t%d: %s%n", i, ilv[i]));
		}
		builder.append("Stack:\n");
		if (bddmanager.smax > 0)
			builder.append(String.format("\tsptr: %s%n", Arrays.toString(isptr)));
		for (int i = 0; i < bddmanager.lvmax; i++) {
			builder.append(String.format("\t%d: %s%n", i, istack[i]));
		}
		return builder.toString();
	}
}
