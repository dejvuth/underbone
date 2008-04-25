package de.tum.in.jmoped.underbone;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;

import net.sf.javabdd.BDD;

import de.tum.in.wpds.Dpn;
import de.tum.in.wpds.DpnReach;
import de.tum.in.wpds.DpnSat;
import de.tum.in.wpds.Fa;
import de.tum.in.wpds.LifoWorkSet;
import de.tum.in.wpds.Pds;
import de.tum.in.wpds.PdsSat;
import de.tum.in.wpds.Rule;
import de.tum.in.wpds.Sat;
import de.tum.in.wpds.Semiring;
import de.tum.in.wpds.Transition;
import de.tum.in.wpds.Utils;
import de.tum.in.wpds.WorkSet;

/**
 * The Remopla class represents the underlying computational model.
 * 
 * @author suwimont
 *
 */
public class Remopla {
	
	/**
	 * The bit size
	 */
	int bits;
	
	/**
	 * The sizes of heap elements
	 */
	long[] heapSizes;
	
	/**
	 * The global variables
	 */
	Collection<Variable> globals;
	
	/**
	 * The maximum depth of the operand stack
	 */
	int smax;
	
	/**
	 * The maximum number of local variables
	 */
	int lvmax;

	/**
	 * The variable manager
	 */
	VarManager manager;
	
	/**
	 * The Remopla modules
	 */
	Collection<Module> modules;
	
	/**
	 * The initial label
	 */
	String init;
	
	/**
	 * The initial finite automaton
	 */
	Fa fa;
	
	/**
	 * The saturated automaton
	 */
	Fa post;
	
	/**
	 * The saturator
	 */
	Sat sat;
	
	private DpnReach reach;
	private VirtualMachine vm;
	
	/**
	 * The listener
	 */
	RemoplaListener listener = new NullRemoplaListener();
	
	/**
	 * Default state
	 */
	public static final String p = Fa.q_i;
	
	/**
	 * Final state
	 */
	public static final String s = Fa.q_f;
	
	/**
	 * The logger.
	 */
	private static Logger logger = Utils.getLogger(Remopla.class);
	
	/**
	 * Verbosity level.
	 */
	private static int verbosity = 0;
	
	/**
	 * Creates a Remopla model.
	 * 
	 * @param bits the bit size of variables.
	 * @param heapSizes the sizes of heap elements.
	 * @param g the global variables.
	 * @param modules the Remopla module.
	 * @param init the initail label.
	 */
	public Remopla(int bits, long[] heapSizes, Collection<Variable> g, 
			Collection<Module> modules, String init) {
		
		this.bits = bits;
		this.heapSizes = heapSizes;
		this.globals = g;
		this.modules = modules;
		this.init = init;
		
		for (Module m : modules) {
			
			int tmp = m.sdepth;
			if (tmp > smax) smax = tmp;
			
			tmp = m.lvnum;
			if (tmp > lvmax) lvmax = tmp;
		}
	}
	
	/**
	 * Sets the listener.
	 * 
	 * @param listener the listener.
	 */
	public void setListener(RemoplaListener listener) {
		
		this.listener = listener;
	}
	
	/**
	 * Gets the listener.
	 * 
	 * @return the listener.
	 */
	public RemoplaListener getRemoplaListener() {
		
		return listener;
	}
	
	/**
	 * Gets the module having the given <code>name</code>
	 * 
	 * @param name the name of the module.
	 * @return the module; or <code>null</code> if not exist.
	 */
	public Module getModule(String name) {
		
		for (Module module : modules) {
			if (module.getName().equals(name))
				return module;
		}
		
		return null;
	}
	
	/**
	 * Returns the name of module in which init module calls the latest.
	 * 
	 * @return the name of module in which init module calls the latest.
	 */
	String getLastCalledName() {
		
		String[] names = getModule(init).getCalledNames();
		return LabelUtils.trimOffset(names[names.length - 1]);
	}
	
	/**
	 * Performs sequential coverage analysis for this Remopla code.
	 * 
	 * @param bddpackage the BDD package.
	 * @param nodenum the number of BDD nodes to initialize.
	 * @param cachesize the size of caches for the BDD library.
	 * @param monitor the progress monitor.
	 * @return the saturated finite automaton.
	 */
	public Fa coverage(String bddpackage, int nodenum, int cachesize, ProgressMonitor monitor) {
		
		// First post*
		Pds pds = getPds();
		fa = new Fa();
		fa.add(new NullSemiring(), p, init, s);
		sat = new PdsSat(pds);
		post = (Fa) sat.poststar(fa);
		Set<String> labels = post.getLabels();
		for (String label : labels)
			log("%s%n", label);
		
		// Creates variable manager
		manager = new VarManager(bddpackage, nodenum, cachesize, 
				bits, heapSizes, globals, smax, lvmax, 1, false);
		log("manager:%n%s%n", manager.toString());
		
		listener.setProgressMonitor(monitor);
		listener.beginTask(getLastCalledName(), labels);
		monitor.subTask("Analyzing ...");
		
		fa = new Fa();
		fa.add(new BDDSemiring(manager, manager.initVars()), p, init, s);
		
		// Second post*
		sat = new PdsSat(pds);
		sat.setListener(listener);
		post = (Fa) sat.poststar(fa, monitor);
		
		listener.done();
		return post;
	}
	
	/**
	 * Returns <code>true</code> if {@link #coverage(ProgressMonitor)}
	 * was previously called, and a label with assertion error is reachable.
	 * 
	 * @return <code>true</code> if a label with assertion error is reachable.
	 */
	public boolean hasAssertionError() {
		
		if (post == null) return false;
		
		Set<String> labels = getLabels();
		for (String label : labels) {
			if (!(LabelUtils.isAssertionName(label)))
				continue;
			
			if (post.reachable(label)) {
				log("AssertionError found: %s%n", label);
				return true;
			}
		}
		
		return false;
	}
	
	/**
	 * Performs multithreaded coverage analysis for this Remopla code.
	 * 
	 * @param bddpackage the BDD package.
	 * @param nodenum the number of BDD nodes to initialize.
	 * @param cachesize the size of caches for the BDD library.
	 * @param n the thread bound.
	 * @param k the context bound.
	 * @param lazy determines whether to use the lazy splitting technique.
	 * @param monitor the progress monitor.
	 * @return the saturated finite automaton.
	 */
	public void coverage(String bddpackage, int nodenum, int cachesize, 
			int n, int k, boolean lazy, ProgressMonitor monitor) {
		
		// First post*
		Pds pds = getPds();
		info("Total: %d labels%n", pds.getStackSymbols().size());
		fa = new Fa();
		fa.add(new NullSemiring(), p, init, s);
		sat = new PdsSat(pds);
		post = (Fa) sat.poststar(fa);
		Set<String> labels = post.getLabels();
		
		// Creates variable manager
		manager = new VarManager(bddpackage, nodenum, cachesize, 
				bits, heapSizes, globals, smax, lvmax, n, lazy);
		log("manager:%n%s%n", manager.toString());
		
		Dpn dpn = getDpn();
		info("DPN contains %d rules%n", dpn.size());
		listener.setProgressMonitor(monitor);
		listener.beginTask(getLastCalledName(), labels/*dpn.getStackSymbols()*/);
		monitor.subTask("Analyzing ...");
		
		fa = new Fa();
		fa.add(new BDDSemiring(manager, manager.initVars()), p, init, s);
		
		// Second post*
		Semiring g0 = (lazy) ? null : new BDDSemiring(manager, manager.initSharedVars());
		sat = new DpnSat(dpn, g0, n, k, lazy);
		sat.setListener(listener);
		reach = (DpnReach) sat.poststar(fa, monitor);
		
		listener.done();
	}
	
	public boolean reachable(String a, String b) {
		
		log("reachable(%s, %s)%n", a, b);
		if (reach == null) return false;
		
		return reach.reachable(a, b);
	}
	
	/**
	 * Creates a virtual machine and executes this Remopla.
	 * 
	 * @param monitor
	 */
	public void run(ProgressMonitor monitor) {
		
		vm = new VirtualMachine(this);
		vm.run(monitor);
	}
	
	/**
	 * Creates a PDS from this Remopla.
	 * 
	 * @return a PDS.
	 */
	public Pds getPds() {
		
		Pds pds = new Pds();
		for (Module module : modules) {
			for (Rule rule : module.rules) {

				if (rule.isDynamic()) {
					// Transforms DPN rule to two PDS rules.
					pds.add(rule.d, rule.left.p, rule.left.w[0], rule.right.p, rule.right.w[0]);
					pds.add(rule.d, rule.left.p, rule.left.w[0], rule.dynamic.p, rule.dynamic.w[0]);
				} else {
					pds.add(rule);
				}
			}
		}
		
		return pds;
	}
	
	/**
	 * Creates a DPN from this Remopla.
	 * 
	 * @return a DPN.
	 */
	public Dpn getDpn() {
		
		Dpn dpn = new Dpn();
		for (Module module : modules) {
			for (Rule rule : module.rules) {
				dpn.add(rule);
			}
		}
		
		return dpn;
	}
	
	/**
	 * Gets all labels of this module.
	 * 
	 * @return the labels of this module.
	 */
	public Set<String> getLabels() {
		return getLabels(modules);
	}
	
	/**
	 * Gets all labels inside <code>modules</code>.
	 * 
	 * @param modules the collection of modules.
	 * @return the labels.
	 */
	public static Set<String> getLabels(Collection<Module> modules) {
		
		HashSet<String> labels = new HashSet<String>();
		for (Module module : modules) {
			for (Rule rule : module.rules) {
				
				// Adds the lhs
				labels.add(rule.left.w[0]);
				
				// Adds the rhs
				String[] w = rule.right.w;
				if (w == null) continue;
				for (int i = 0; i < w.length; i++)
					labels.add(w[i]);
			}
		}
		
		return labels;
	}
	
	public List<Float> getFloats() {
		if (manager == null) return null;
		return manager.getFloats();
	}
	
	public VarManager getVarManager() {
		return manager;
	}
	
	public List<RawArgument> getRawArguments(String label) {
		
		if (post != null) {
		
			Set<Transition> trans = post.getTransitions(p, label);
			List<RawArgument> raws = new ArrayList<RawArgument>();
			for (Transition t : trans)
				raws.addAll(manager.getRawArguments(((BDDSemiring) post.getWeight(t)).bdd));
			
			return raws;
		} else if (vm != null) {
			
			return vm.getRawArguments(label);
		}
		
		return null;
	}
	
	public List<RawArgument> getRawArguments2(String label) {
		
		if (vm != null) return vm.getRawArguments(label);
		
		if (post == null) return null;
		
		Set<Transition> trans = post.getTransitions(p, label);
		WorkSet<String> workset = new LifoWorkSet<String>();
		HashMap<String, BDD> rels = new HashMap<String, BDD>();
		for (Transition t : trans) {
			workset.add(t.getToState());
			rels.put(t.getToState(), ((BDDSemiring) post.getWeight(t)).bdd.id());
		}
		
		// States that has transitions to the final state.
		HashSet<String> toS = new HashSet<String>();
		
		while (!workset.isEmpty()) {
			
			// Removes q from workset
			String q = workset.remove();
			
			// Continues if there is no transitions leaving q
			trans = post.getTransitions(q);
			if (trans == null) continue;
			
			// For all transitions leaving q
			for (Transition t : trans) {
				
				log("t: %s%n", t);
				String q_t = t.getToState();
				if (q_t.equals(s)) {
					toS.add(q);
					continue;
				}
				
				BDD bdd1 = rels.get(q);
				BDD bdd2 = ((BDDSemiring) post.getWeight(t)).bdd;
				BDD bdd = manager.conjoin(bdd1, bdd2);
				log("bdd1: %s%n", bdd1.toStringWithDomains());
				log("bdd2: %s%n", bdd2.toStringWithDomains());
				log("bdd: %s%n", bdd.toStringWithDomains());
				
				/*
				 * If the bdd is new, puts the state 
				 * and the corresponding bdd into the workset.
				 */
				if (!rels.containsKey(q_t)) {
					workset.add(q_t);
					rels.put(q_t, bdd);
					continue;
				}
				
				// Ignores if the new bdd equals the existing bdd
				BDD bdd_t = rels.get(q_t);
				if (bdd.equals(bdd_t)) {
					bdd.free();
					continue;
				}
				
				// Disjuncts the new bdd with the existing bdd
				bdd = bdd_t.id().orWith(bdd);
				
				// Ignores if the new bdd equals the existing bdd
				if (bdd.equals(bdd_t)) {
					bdd.free();
					continue;
				}
				
				// Puts the state and the corresponding bdd into the workset
				bdd_t.free();
				workset.add(q_t);
				rels.put(q_t, bdd);
			}
		}
		
		List<RawArgument> raws = new ArrayList<RawArgument>();
		for (String q : toS) 
			raws.addAll(manager.getRawArguments2(rels.get(q)));
		
		for (BDD bdd : rels.values())
			bdd.free();
		
		return raws;
	}
	
	/**
	 * Frees all analysis results.
	 */
	public void free() {
				
		modules = null;
		
		if (fa != null) {
			log("Freeing fa ...");
			fa.free();
			fa = null;
			log("done%n");
		}
		
		if (post != null) {
			log("Freeing post");
			post.free();
			post = null;
		}
		reach = null;
		if (manager != null) {
			log("Freeing manager");
			manager.free();
			manager = null;
		}
	}
	
	/**
	 * Sets the verbosity level.
	 * 
	 * @param level the verbosity level.
	 */
	public static void setVerbosity(int level) {
		verbosity = level;
		VarManager.setVerbosity(level);
		VirtualMachine.setVerbosity(level);
	}
	
	/**
	 * Logs translator information.
	 * 
	 * @param msg the message.
	 * @param args the arguments of the message.
	 */
	public static void log(String msg, Object... args) {
		log(2, msg, args);
	}
	
	/**
	 * Logs translator information.
	 * 
	 * @param msg the message.
	 * @param args the arguments of the message.
	 */
	public static void info(String msg, Object... args) {
		log(1, msg, args);
	}
	
	private static void log(int threshold, String msg, Object... args) {
		if (verbosity >= threshold)
			logger.fine(String.format(msg, args));
	}
	
	/**
	 * Renames the <code>name</code> to the one that is legal in Moped.
	 * 
	 * @param name the name.
	 * @return the Moped's legal name.
	 */
	static String mopedize(String name) {
		return name.replaceAll("/|\\.|\\[|\\(|\\)|<|>|\\$|#|;", "_");
	}
	
	static final String error = "error";
	static final String ioob = "ioob";
	static final String npe = "npe";
	static final String notenoughheap = "notenoughheap";
	
	/**
	 * Returns the string representation of this Remopla in Moped's syntax.
	 * 
	 * @return this Rempla in Moped's syntax.
	 */
	public String toMoped() {
		
		StringBuilder out = new StringBuilder();
		
		// Default bits
		Utils.append(out, "define DEFAULT_INT_BITS %d%n%n", bits);
		
		// Heap
		Utils.append(out, "int heap[%d];%n", heapSizes.length);
		Utils.append(out, "int ptr;%n");
		
		// Globals
		Utils.append(out, "int ret;%n");
		if (globals != null && !globals.isEmpty()) {
			for (Variable global : globals) {
				Utils.append(out, "int %s(%d);%n", mopedize(global.getName()), global.getBits(bits));
			}
		}
		
		// Constants
		Set<String> constants = new HashSet<String>();
		for (Module module : modules) {
			module.fillConstants(constants);
		}
		for (String c : constants) {
			Utils.append(out, "int %s;%n", mopedize(c));
		}
		constants = null;
		Utils.append(out, "%n");
		
		// Headers
		for (Module module : modules) {
			Utils.append(out, "%s;%n", module.toMopedHeader());
		}
		Utils.append(out, "%n");
		
		// Init
		Utils.append(out, "init %s;%n%n", "mopedwrapper");
		
		// Moped's wrapper
		Utils.append(out, "module void mopedwrapper() {%n");
		Utils.append(out, "A i (0,%d) heap[i] = 0, ptr = 1;%n", heapSizes.length - 1);
		Utils.append(out, "goto %s0;%n", mopedize(init));
		Utils.append(out, "}%n%n");
		
		// Modules
		for (Module module : modules) {
			Utils.append(out, module.toMoped(heapSizes.length));
			Utils.append(out, "%n");
		}
		
		// Errors;
		Utils.append(out, "%s: goto %s;%n", npe, error);
		Utils.append(out, "%s: goto %s;%n", ioob, error);
		Utils.append(out, "%s: goto %s;%n", notenoughheap, error);
		Utils.append(out, "%s: goto %s;%n%n", error, error);
		
		return out.toString();
	}
	
	/**
	 * Returns the string representation of this Remopla.
	 * 
	 * @return the string representation of this Remopla.
	 */
	public String toString() {
		
		StringBuilder out = new StringBuilder();
		if (globals != null && !globals.isEmpty()) {
			out.append("Global variables:\n");
			for (Variable global : globals) {
				out.append('\t').append(global).append('\n');
			}
		}
		out.append(String.format("Initial symbol: %s%n", init));
		for (Module module : modules) {
			out.append(module);
		}
		
		return out.toString();
	}
	
	private class NullRemoplaListener implements RemoplaListener {

		public void beginTask(String name, Set<String> labels) {
		}

		public void done() {
		}

		public void setProgressMonitor(ProgressMonitor monitor) {
		}

		public void reach(String label) {
		}
		
	}
}
