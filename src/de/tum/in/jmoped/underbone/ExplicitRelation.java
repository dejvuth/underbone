package de.tum.in.jmoped.underbone;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.logging.Logger;

import net.sf.javabdd.BDDDomain;

import de.tum.in.wpds.Utils;

public class ExplicitRelation {
	
	static int bits;
	
	/**
	 * Maps names to global variables
	 */
	static HashMap<String, Variable> globals;
	
	static int lvmax;
	static int smax;
	static int tbound;
	static boolean lazy;
	
	/**
	 * Maps names of constants to their values.
	 */
	private static HashMap<String, Number> constants;
	
	private static ArrayList<String> strings;
	
	static final int G0L0 = 0;
	static final int G0L0G1L1 = 1;
	static final int G2L2L0 = 2;
	static final int G2L2L0G1L1 = 3;
	static final int G0 = 4;
	static final int G0G2L2 = 5;
	
	static final String RETVAR = "ret";
	
	static final Number ZERO = new Integer(0);
	
	/**
	 * The logger.
	 */
	static Logger logger = Utils.getLogger(ExplicitRelation.class);
	
	int type;
	V[] rel;
	
	ExplicitRelation(int type, V[] rel) {
		this.type = type;
		this.rel = rel;
	}
	
	public static ExplicitRelation init(int b, Collection<Variable> g, int l, int s, int t, boolean z) {
		bits = b;
		
		// Adds return variable
		if (g == null)
			g = new HashSet<Variable>();
		g.add(new Variable(VariableType.INT, RETVAR, b));
		
		int index = 0;
		globals = new HashMap<String, Variable>(g.size() + 5, 0.95f);
		for (Variable v : g) {
			log("name:%s, index:%d%n", v.getName(), index);
			v.setIndex(index++);
			globals.put(v.getName(), v);
		}
		lvmax = l;
		smax = s;
		tbound = t;
		lazy = z;
		if (constants != null)
			constants.clear();
		if (strings != null)
			strings.clear();
		
		ExplicitRelation r = new ExplicitRelation(
				G0L0,  new V[] { new G(), new L(), new S() });
		return r;
	}
	
	G g() {
		if (type == G0L0 || type == G0L0G1L1 || type == G0 || type == G0G2L2)
			return (G) rel[0];
		throw new RemoplaError("Invalid signature: %d.", type);
	}
	
	L l() {
		if (type == G0L0 || type == G0L0G1L1)
			return (L) rel[1];
		
		if (type == G2L2L0 || type == G2L2L0G1L1)
			return (L) rel[2];
		
		throw new RemoplaError("Invalid signature: %d.", type);
	}
	
	G g1() {
		if (type == G0L0G1L1)
			return (G) rel[3];
		
		if (type == G2L2L0G1L1)
			return (G) rel[4];
		
		throw new RemoplaError("Invalid signature: %d.", type);
	}
	
	L l1() {
		if (type == G0L0G1L1)
			return (L) rel[4];
		
		if (type == G2L2L0G1L1)
			return (L) rel[5];
		
		throw new RemoplaError("Invalid signature: %d.", type);
	}
	
	G g2() {
		if (type == G2L2L0 || type == G2L2L0G1L1)
			return (G) rel[0];
		
		if (type == G0G2L2)
			return (G) rel[1];
		
		throw new RemoplaError("Invalid signature: %d.", type);
	}
	
	L l2() {
		if (type == G2L2L0 || type == G2L2L0G1L1)
			return (L) rel[1];
		
		if (type == G0G2L2)
			return (L) rel[2];
		
		throw new RemoplaError("Invalid signature: %d.", type);
	}
	
	S s() {
		if (type == G0L0 || type == G0L0G1L1)
			return (S) rel[2];
		
		if (type == G2L2L0 || type == G2L2L0G1L1)
			return (S) rel[3];
		
		throw new RemoplaError("Invalid signature: %d.", type);
	}
	
	void setGlobal(String name, Number value) {
		g().setGlobal(name, value);
	}
	
	Number global(String name) {
		return g().getGlobal(name);
	}
	
	int allocate(int size) {
		return g().allocate(size);
	}
	
	void newheap() {
		Number[] heap = g().heap;
		Number[] newheap = new Number[heap.length];
		System.arraycopy(heap, 0, newheap, 0, heap.length);
		g().heap = newheap;
	}
	
	void setHeap(int index, Number value) {
		g().heap[index] = value;
	}
	
	Number[] heap() {
		return g().heap;
	}
	
	static int getMaxHeap() {
		return G.maxheap;
	}
	
	Number heap(int index) {
		return g().heap[index];
	}
	
	void setLocal(int index, Number value) {
		l().local[index] = value;
	}
	
	Number[] local() {
		return l().local;
	}
	
	Number local(int index) {
		return l().local[index];
	}
	
	void setSptr(int value) {
		s().sptr = value;
	}
	
	int sptr() {
		return s().sptr;
	}
	
	void setStack(int index, Number value) {
		s().stack[index] = value;
	}
	
	Number stack(int index) {
		return s().stack[index];
	}
	
	public static boolean multithreading() {
		return tbound > 1;
	}
	
	/**
	 * Returns the number of blocks required for storing
	 * auxiliary information of an array.
	 * 
	 * @return two in normal case; or four in case of lazy splitting.
	 */
	static int getArrayAuxSize() {
		//FIXME why 4 in lazy???
		return (multithreading() && lazy) ? 4 : 2;
	}
	
	int arraylength(int ptr) {
		return g().heap[ptr + getArrayAuxSize() - 1].intValue();
	}
	
	void setArray(int ptr, int index, Number value) {
		g().heap[ptr + getArrayAuxSize() + index] = value;
	}
	
	Number array(int ptr, int index) {
		return g().heap[ptr + getArrayAuxSize() + index];
	}
	
	public static Number getConstant(String name) {
		if (constants == null)	// Shouldn't be possible, a precaution.
			constants = new HashMap<String, Number>();
		return constants.get(name);
	}
	
	public static void putConstant(String name, Number value) {
		if (constants == null)
			constants = new HashMap<String, Number>();
		constants.put(name, value);
	}
	
	public static List<String> getStrings() {
		return strings;
	}
	
	public static int encode(String raw) {
		if (strings == null)
			strings = new ArrayList<String>();
		
		// Adds a dummy string at index zero for preventing NPE
		if (strings.isEmpty())
			strings.add("");
		
		// Returns the index if the string already exists
		int index = strings.indexOf(raw);
		if (index != -1) return index;
		
		index = strings.size();
		strings.add(raw);
		return index;
	}
	
	public static String decodeString(long encoded) {
		return strings.get((int) encoded);
	}
	
	public RawArgument getRawArgument() {
		Number[] heap = g1().heap;
		RawArgument arg = new RawArgument(lvmax, heap.length - 1);
		for (int i = 0; i < lvmax; i++) {
			arg.lv[i] = l1().local[i];
		}
		for (int i = 0; i < heap.length - 1; i++) {
			arg.heap[i] = heap[i+1];
		}
		return arg;
	}
	
	/**
	 * Pushes <code>value</code>.
	 * 
	 * @param category
	 * @param value
	 * @return
	 */
	ExplicitRelation push(int category, Number value) {
		S s = s();
		s.stack[s.sptr] = value;
		if (category == 2)
			s.stack[s.sptr + 1] = 0;
		s.sptr += category;
		return this;
	}
	
	public ExplicitRelation id() {
		ExplicitRelation r = new ExplicitRelation(type, new V[rel.length]);
		for (int i = 0; i < rel.length; i++)
			r.rel[i] = rel[i].id();
		return r;
	}
	
	public String toString() {
		return String.format("type:%d, rel:%s", type, Arrays.toString(rel));
	}
	
	public boolean equals(Object obj) {
		if (obj == null || !(obj instanceof ExplicitRelation))
			return false;
		
		ExplicitRelation r = (ExplicitRelation) obj;
		if (type != r.type)
			return false;
		
		for (int i = 0; i < rel.length; i++)
			if (!rel[i].equals(r.rel[i]))
				return false;
		
		return true;
	}
	
	public int hashCode() {
		int hash = type;
		for (int i = 0; i < rel.length; i++)
			hash = 31*hash + rel[i].hashCode();
		return hash;
	}

	/**
	 * V
	 */
	static interface V {
		public V id();
	}
	
	/**
	 * G
	 */
	static class G implements V {
		Number[] global;
		Number[] heap;
		
		private static int maxheap;
		
		public G() {
			global = new Number[globals.size()];
			Arrays.fill(global, ZERO);
			heap = new Number[1];
			heap[0] = ZERO;
			maxheap = 1;
		}
		
		public G(Number[] global, Number[] heap) {
			this.global = global;
//			this.global = new Number[global.length];
//			System.arraycopy(global, 0, this.global, 0, global.length);
			if (heap != null) {
				this.heap = heap;
//				this.heap = new Number[heap.length];
//				System.arraycopy(heap, 0, this.heap, 0, heap.length);
			}
		}
		
		public void setGlobal(String name, Number value) {
			Number[] newglobal = new Number[global.length];
			System.arraycopy(global, 0, newglobal, 0, global.length);
			this.global = newglobal;
			this.global[globals.get(name).getIndex()] = value;
		}
		
		public Number getGlobal(String name) {
			return global[globals.get(name).getIndex()];
		}
		
		public int allocate(int size) {
			int ptr = heap.length;
			Number[] newheap = new Number[ptr + size];
			Arrays.fill(newheap, ZERO);
			System.arraycopy(heap, 0, newheap, 0, ptr);
			this.heap = newheap;
			maxheap = newheap.length;
			return ptr;
		}
		
		public String toString() {
			return String.format("global:%s, heap:%s", 
					Arrays.toString(global), Arrays.toString(heap));
		}
		
		public V id() {
			return new G(global, heap);
		}
		
		public boolean equals(Object obj) {
			if (obj == null || !(obj instanceof G))
				return false;
			
			G g = (G) obj;
			return Arrays.equals(global, g.global) && Arrays.equals(heap, g.heap);
		}
		
		public int hashCode() {
			return 31*Arrays.hashCode(global) + Arrays.hashCode(heap);
		}
	}
	
	/**
	 * L
	 */
	static class L implements V {
		Number[] local;
		
		public L() {
			local = new Number[lvmax];
		}
		
		public L(Number[] local) {
			this.local = new Number[local.length];
			System.arraycopy(local, 0, this.local, 0, local.length);
		}
		
		public String toString() {
			return String.format("local:%s", Arrays.toString(local));
		}
		
		public V id() {
			return new L(local);
		}
		
		public boolean equals(Object obj) {
			if (obj == null || !(obj instanceof L))
				return false;
			
			L l = (L) obj;
			return Arrays.equals(local, l.local);
		}
		
		public int hashCode() {
			return Arrays.hashCode(local);
		}
	}
	
	/**
	 * S
	 */
	static class S implements V {
		int sptr;
		Number[] stack;
		
		public S() {
			sptr = 0;
			stack = new Number[smax];
		}
		
		public S(int sptr, Number[] stack) {
			this.sptr = sptr;
			this.stack = new Number[stack.length];
			System.arraycopy(stack, 0, this.stack, 0, stack.length);
		}
		
		public String toString() {
			return String.format("sptr:%d, stack:%s", sptr, Arrays.toString(stack));
		}
		
		public V id() {
			return new S(sptr, stack);
		}
		
		public boolean equals(Object obj) {
			if (obj == null || !(obj instanceof S))
				return false;
			
			S s = (S) obj;
			return (sptr == s.sptr) && Arrays.equals(stack, s.stack);
		}
		
		public int hashCode() {
			return 31*sptr + Arrays.hashCode(stack);
		}
	}
	
	public static void log(String msg, Object... args) {
		VarManager.log(msg, args);
	}
}
