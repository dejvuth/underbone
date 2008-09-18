package de.tum.in.jmoped.underbone;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.logging.Logger;

import de.tum.in.wpds.Utils;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

/**
 * The manager that manipulates BDDs.
 * 
 * @author suwimont
 *
 */
public class BDDManager {

	/**
	 * The default bits.
	 */
	protected int bits;
	
	/**
	 * The heap length.
	 */
	protected int heaplength;
	
	/**
	 * The maximum stack depth.
	 */
	protected int smax;
	
	/**
	 * The maximum number of local variables.
	 */
	protected int lvmax;
	
	/**
	 * The thread bound.
	 */
	protected int tbound;
	
	/**
	 * Indicates lazy splitting.
	 */
	protected boolean lazy;
	
	/**
	 * The BDD factory.
	 */
	protected BDDFactory factory;
	
	/**
	 * The default number of copies of variables.
	 */
	public static int varcopy = 3;
	
	/**
	 * The number of copies of globals.
	 */
	protected int globalcopy;
	
	/**
	 * Ordering of BDD variables for globals.
	 */
	protected int[] gindex;
	
	/**
	 * Starting domain index of globals.
	 */
	protected static final int g0 = 0;
	
	/**
	 * Starting domain index of locals
	 */
	protected int l0;
	
	/**
	 * Maps names to global variables
	 */
	protected HashMap<String, Variable> globals;
	
//	protected int hcount;
	protected int[] hmap;
	
	protected int[] omap;
	
	/**
	 * Records the maximum number of BDD nodes. For statistics purpose.
	 */
	protected static int maxNodeNum;
	
	/**
	 * Maps names of constants to their values.
	 */
	protected HashMap<String, Integer> constants;
	
	/**
	 * Verbosity level.
	 */
	private static int verbosity = 0;
	
	/**
	 * The logger.
	 */
	private static Logger logger = Utils.getLogger(BDDManager.class);
	
	/**
	 * Constructs a BDD manager.
	 * 
	 * @param bddpackage the BDD package: "cudd" or "java".
	 * @param nodenum the estimated number of BDD nodes.
	 * @param cachesize the cache size.
	 * @param bits the number of variable bits.
	 * @param g the global variables.
	 * @param heaplength the heap length.
	 * @param smax the maximum stack depth.
	 * @param lvmax the maximum number of local variables.
	 * @param tbound the thread bound.
	 * @param lazy lazy splitting?
	 */
	public BDDManager(String bddpackage, int nodenum, int cachesize, 
			int bits, Collection<Variable> g, int heaplength,
			int smax, int lvmax, int tbound, boolean lazy) {
		maxNodeNum = 0;
		this.bits = bits;
		this.heaplength = heaplength;
		this.smax = smax;
		this.lvmax = lvmax;
		this.tbound = tbound;
		this.lazy = lazy;
		this.globalcopy = (!multithreading() || !lazy()) ? varcopy : varcopy + 2;
//		System.out.println(globalcopy);
		
		// Initializes global ordering
		if (multithreading() && lazy()) {
			gindex = new int[] { 0, 3, 4, 1, 2 };
		} else {
			gindex = new int[] { 0, 1, 2, 3, 4 };
		}
		
		// Initializes mapping of global variables
		if (g != null && !g.isEmpty()) {
			globals = new HashMap<String, Variable>(g.size() + 1, 0.999f);
			for (Variable v : g) {
				globals.put(v.name, v);
			}
		}
		
		if (heaplength > 0) {
//			hcount = 1;
			hmap = new int[1 << bits];
			if (hmap.length > 1)
				hmap[1] = 1;
			omap = new int[1 << bits];
		}
		
		factory = BDDFactory.init(bddpackage, nodenum, cachesize);
		if (info())
			info("BDD package: %s%n", factory.getClass().getName());
	}
	
	/**
	 * Returns the default integer bits.
	 * 
	 * @return the default integer bits.
	 */
	public int getBits() {
		return bits;
	}
	
	/**
	 * Returns the maximum positive integer.
	 * 
	 * @return 2^(bits - 1) - 1.
	 */
	public int getMaxInt() {
		return (1 << (bits - 1)) - 1;
	}
	
	/**
	 * Returns 2^bits.
	 * 
	 * @return 2^bits.
	 */
	public long size() {
		return 1 << bits;
	}
	
	/**
	 * Gets the heap length.
	 * 
	 * @return the heap length.
	 */
	public int getHeapLength() {
		return heaplength;
	}
	
	public int encodeHeapIndex(int hp) {
		if (hp == 0)
			return 0;
		
		int size = 1 << bits;
		int index = hp % size;
		int startindex = index;
		int h = hmap[index];
		while (index == 0 || (h != hp && h != 0)) {
			index = (index + 1) % size;
			if (startindex == index)
				throw new RemoplaError("Too many objects for %d bits", bits);
			h = hmap[index];
		}
//		if (log()) log("\t\tencodeHeapIndex(%d) -> %d%n", hp, index);
		hmap[index] = hp;
		return index;
		
//		int i = hcount++;
//		hmap[i] = hp;
//		return i;
	}
	
	public int decodeHeapIndex(int index) {
		return hmap[index];
	}
	
	public int findObjectIdIndex(int id) {
		if (id == 0)
			return 0;
		
		int size = 1 << bits;
		int index = id % size;
		int startindex = index;
		int o = omap[index];
		while ((index == 0) || (o != id && o != 0)) {
			index = (index + 1) % size;
			if (startindex == index)
				return -1;
			o = omap[index];
		}
		return index;
	}
	
	public int encodeObjectId(int id) {
		int index = findObjectIdIndex(id);
//		if (log()) log("\t\tencodeObjectId(%d) -> %d%n", id, index);
		if (index < 0)
			throw new RemoplaError("Too many object types for %d bits", bits);
		
		omap[index] = id;
		return index;
		
		
//		if (id == 0)
//			return 0;
//		
//		int size = 1 << bits;
//		int index = id % size;
//		int startindex = index;
//		int o = omap[index];
//		while ((index == 0) || (o != id && o != 0)) {
//			index = (index + 1) % size;
//			if (startindex == index)
//				throw new RemoplaError("Too many object types for %d bits", bits);
//			o = omap[index];
//		}
//		omap[index] = id;
//		return index;
	}
	
	public int decodeObjectId(int index) {
		return omap[index];
	}
	
	/**
	 * Returns the variable having the specified name.
	 * 
	 * @param name the name of the variable.
	 * @return the variable.
	 */
	public Variable getGlobalVar(String name) {	
		if (globals == null) return null;
		return globals.get(name);
	}
	
	/**
	 * Gets the BDD factory.
	 * 
	 * @return the BDD factory.
	 */
	public BDDFactory getFactory() {
		return factory;
	}
	
	/**
	 * Gets the maximum number of local variables.
	 * 
	 * @return the maximum number of local variables.
	 */
	public int getMaxLocalVars() {
		return lvmax;
	}
	
	/**
	 * Returns <code>true</code> if multithreading.
	 * 
	 * @return <code>true</code> if multithreading.
	 */
	public boolean multithreading() {
		return tbound > 1;
	}
	
	/**
	 * Gets the maximum number of threads allowed.
	 * 
	 * @return the thread bound.
	 */
	public int getThreadBound() {
		return tbound;
	}
	
	/**
	 * Returns <code>true</code> if lazy splitting.
	 * 
	 * @return <code>true</code> if lazy splitting.
	 */
	public boolean lazy() {
		return lazy;
	}
	
	protected void updateMaxNodeNum() {
		int num = factory.getNodeNum();
		if (num > maxNodeNum) maxNodeNum = num;
	}
	
	public static int getMaxNodeNum() {
		return maxNodeNum;
	}
		
	public Integer getConstant(String name) {
		if (constants == null)	// Shouldn't be possible, a precaution.
			constants = new HashMap<String, Integer>();
		return constants.get(name);
	}
	
	public void putConstant(String name, Integer value) {
		if (constants == null)
			constants = new HashMap<String, Integer>();
		constants.put(name, value);
	}
	
	/**
	 * Returns the number of blocks required for storing
	 * auxiliary information of an array.
	 * 
	 * @return two in normal case; or four in case of lazy splitting.
	 */
	protected int getArrayAuxSize() {
		//FIXME why 4 in lazy???
		return (multithreading() && lazy()) ? 4 : 2;
	}
	
	/**
	 * Encodes <code>raw</code> in two-complement format.
	 * 
	 * @param raw
	 * @return
	 */
	public static long encode(int raw, long size) {
		if (raw >= 0)
			return ((long) raw) & (size - 1);
		
		long result = (long) raw;
		do
			result += size;
		while (result < 0);
		return result;
	}
	
	public static int decode(long encoded, long size) {
		int maxint = (int) (size/2 - 1);
		if (maxint == 0 || encoded <= maxint) 
			return (int) encoded;
		
		return (int) (encoded - size);
	}
	
	public static long neg(long encoded, long size) {
		if (encoded == 0) return 0;
		return size - encoded;
	}
	
	private ArrayList<Float> floats;
	
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
	public long encode(float raw, int size) {
		if (floats == null)
			floats = new ArrayList<Float>();
		
		int index = floats.indexOf(raw);
		if (index != -1) return index;
		
		index = floats.size();
		if (index >= size)
			System.err.println("Too many floats");
		floats.add(raw);
		return index;
	}
	
	public float decodeFloat(long encoded) {
		return floats.get((int) encoded);
	}
	
	private ArrayList<String> strings;
	
	public List<String> getStrings() {
		return strings;
	}
	
	public long encode(String raw, int size) {
		if (strings == null)
			strings = new ArrayList<String>();
		
		// Adds a dummy string at index zero for preventing NPE
		if (strings.isEmpty())
			strings.add("");
		
		// Returns the index if the string already exists
		int index = strings.indexOf(raw);
		if (index != -1) return index;
		
		index = strings.size();
		if (index >= size)
			System.err.println("Too many strings");
		strings.add(raw);
		return index;
	}
	
	public String decodeString(long encoded) {
		return strings.get((int) encoded);
	}
	
	/**
	 * The variable scanner. Used in {@link BDDManager#scanVar(BDD, int[])}.
	 * 
	 * @author suwimont
	 *
	 */
	private static class VarScanner {
		BDD bdd;
		int[] ivar;
		int index = -1;
		
		VarScanner(BDD bdd, int[] ivar) {
			this.bdd = bdd.id();
			this.ivar = ivar;
		}
		
		int scan() {
			if (bdd.isZero())
				return -1;
			
			index++;
			if (index >= ivar.length)
				return -1;
			
			while (bdd.var() < ivar[index]) {
				BDD low = bdd.low();
				if (!low.isZero()) {
					bdd.free();
					bdd = low;
				} else {
					BDD high = bdd.high();
					bdd.free();
					bdd = high;
				}
			}
			
			if (bdd.var() == ivar[index]) {
				if (!bdd.low().isZero()) return 0;
				else return 1;
			}
			
			return 0;
		}
		
		void free() {
			bdd.free();
		}
	}
	
	/**
	 * Scans a value represented by the variables <code>ivar</code>
	 * from the BDD. A faster substitution of 
	 * {@link BDD#scanVar(net.sf.javabdd.BDDDomain)}.
	 * 
	 * @param bdd the BDD.
	 * @param ivar the BDD variable indices.
	 * @return the value.
	 */
	public static long scanVar(BDD bdd, int[] ivar) {
        VarScanner scanner = new VarScanner(bdd, ivar);
        long value = 0;
        for (int i = 0; i < ivar.length; i++) {
        	value += scanner.scan() << i;
        }
        scanner.free();
        return value;
	}
	
	/**
	 * Returns a BDD representing the <code>value</code> 
	 * with the variables specified by <code>ivar</code>.
	 * 
	 * @param value the value.
	 * @param ivar the BDD variable indices.
	 * @return the BDD.
	 */
	public BDD ithVar(int[] ivar, long value) {
		int size = 1 << ivar.length;
        if (value < 0 || value >= size) {
            throw new RemoplaError("%d is out of range. ivar: %s.", 
            		value, Arrays.toString(ivar));
        }

        BDD v = factory.one();
        for (int n = 0; n < ivar.length; n++) {
            if ((value & 1) != 0)
                v.andWith(factory.ithVar(ivar[n]));
            else
                v.andWith(factory.nithVar(ivar[n]));
            value >>= 1;
        }
        return v;
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
	protected static void log(String msg, Object... args) {
		log(2, msg, args);
	}
	
	/**
	 * Logs translator information.
	 * 
	 * @param msg
	 * @param args
	 */
	protected static void info(String msg, Object... args) {
		log(1, msg, args);
	}
	
	protected static boolean info() {
		return verbosity >= 1;
	}
	
	protected static boolean log() {
		return verbosity >= 2;
	}
	
	private static void log(int threshold, String msg, Object... args) {
		if (verbosity >= threshold)
			logger.fine(String.format(msg, args));
	}
}
