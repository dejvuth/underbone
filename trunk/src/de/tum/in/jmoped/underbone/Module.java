package de.tum.in.jmoped.underbone;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Set;

import de.tum.in.jmoped.underbone.ExprSemiring.ArithType;
import de.tum.in.jmoped.underbone.ExprSemiring.Condition;
import de.tum.in.jmoped.underbone.ExprSemiring.DupType;
import de.tum.in.wpds.Config;
import de.tum.in.wpds.Rule;
import de.tum.in.wpds.Semiring;
import de.tum.in.wpds.Utils;

/**
 * Remopla's module.
 * 
 * @author suwimont
 *
 */
public class Module {
	
	/**
	 * Module name
	 */
	private String name;
	
	/**
	 * True iff long or double. Length determines the number of parameters.
	 */
	private boolean[] params;
	
	/**
	 * True if the method does not return a value.
	 */
	private boolean isVoid;
	
	/**
	 * Stack depth
	 */
	int sdepth;
	
	/**
	 * Number of local variables
	 */
	int lvnum;
	
	/**
	 * List of pushdown rules
	 */
	ArrayList<Rule> rules = new ArrayList<Rule>();
	
	/**
	 * Constructs a Remopla module.
	 * 
	 * @param name the name of the module.
	 * @param params the parameters.
	 * @param isVoid determines whether the module is void.
	 * @param sdepth the operand stack depth.
	 * @param lvnum the number of local variables.
	 */
	public Module (String name, boolean[] params, boolean isVoid, 
			int sdepth, int lvnum) {
		
		this.name = name;
		this.params = params;
		this.isVoid = isVoid;
		this.sdepth = sdepth;
		this.lvnum = lvnum;
	}
	
	/**
	 * Sets the maximum number of local variables.
	 * 
	 * @param lvnum the maximum number of local variables.
	 */
	public void setMaxLocals(int lvnum) {
		
		this.lvnum = lvnum;
	}
	
	/**
	 * Ensures the maximum operand stack depth.
	 * 
	 * @param sdepth the stack depth.
	 */
	public void ensureMaxStack(int sdepth) {
		if (this.sdepth < sdepth)
			this.sdepth = sdepth;
	}
	
	/**
	 * Sets the maximum operand stack depth.
	 * 
	 * @param sdepth the stack depth.
	 */
	public void setMaxStack(int sdepth) {
		
		this.sdepth = sdepth;
	}
	
	/**
	 * Adds the rule <code>r</code> to this module.
	 * 
	 * @param r the rule.
	 */
	public void addRule(Rule r) {
		
		rules.add(r);
	}
	
	/**
	 * Adds the rule <code>&lt;p,y&gt; -&gt; &lt;p,w&gt;</code>
	 * with weight <code>d</code> to this module,
	 * where <code>p</code> is the default control state.
	 * 
	 * @param y the left-hand-side stack symbol.
	 * @param d the weight of the rule.
	 * @param w the right-hand-side stack symbols.
	 */
	public void addRule(String y, Semiring d, String... w) {
		
		addRule(new Rule(d, Remopla.p, y, Remopla.p, w));
	}
	
	/**
	 * Adds the rule <code>&lt;p,y&gt; -&gt; &lt;p&gt;</code>,
	 * where <code>t</code> specifies type of the rule and
	 * <code>p</code> is the default control state.
	 * 
	 * @param y the left-hand-side stack symbol.
	 * @param t the type of the weight for this rule.
	 */
	public void addRule(String y, ExprType t) {
		
		addRule(y, new ExprSemiring(t));
	}
	
	/**
	 * Adds the rule <code>&lt;p,y&gt; -&gt; &lt;p,w&gt;</code>,
	 * where <code>t</code> specifies type of the rule and
	 * <code>p</code> is the default control state.
	 * 
	 * @param y the left-hand-side stack symbol.
	 * @param t the type of the weight for this rule.
	 * @param w the right-hand-side stack symbols.
	 */
	public void addRule(String y, ExprType t, String w) {
		
		addRule(y, new ExprSemiring(t), w);
	}
	
	/**
	 * Adds the rule <code>&lt;p,y&gt; -&gt; &lt;p,w&gt;</code>,
	 * where <code>t</code> and <code>v</code> specify type and value 
	 * of the rule, respectively.
	 * <code>p</code> is the default control state.
	 * 
	 * @param y the left-hand-side stack symbol.
	 * @param t the type of the weight for this rule.
	 * @param v the value of the weight for this rule.
	 * @param w the right-hand-side stack symbols.
	 */
	public void addRule(String y, ExprType t, Object v, String w) {
		
		addRule(y, new ExprSemiring(t, v), w);
	}
	
	/**
	 * Adds the rule <code>&lt;p,y&gt; -&gt; &lt;p,w&gt;</code>,
	 * where <code>t</code>, <code>v1</code>, and <code>v2</code> 
	 * specify type, value 1, and value 2 of the rule, respectively.
	 * <code>p</code> is the default control state.
	 * 
	 * @param y the left-hand-side stack symbol.
	 * @param t the type of the weight for this rule.
	 * @param v the value of the weight for this rule.
	 * @param w the right-hand-side stack symbols.
	 */
	public void addRule(String y, ExprType t, Object v1, Object v2, String w) {
		
		addRule(y, new ExprSemiring(t, v1, v2), w);
	}
	
	/**
	 * Adds the dynamic rule 
	 * <code>&lt;p,y&gt; -&gt; &lt;p,y1&gt; |&gt; &lt;p,y2&gt;</code>
	 * with weight <code>d</code> to this module,
	 * where <code>p</code> is the default control state.
	 * 
	 * @param y the left-hand-side stack symbol.
	 * @param d the weight of the rule.
	 * @param y1 the right-hand-side stack symbol of this thread.
	 * @param y2 the right-hand-side stack symbol of the new thread.
	 */
	public void addDynamicRule(String y, Semiring d, String y1, String y2) {
		
		addRule(new Rule(d, new Config(Remopla.p, y), new Config(Remopla.p, y1),
				new Config(Remopla.p, y2)));
	}
	
	/**
	 * Adds the shared rule <code>&lt;p,y&gt; -&gt; &lt;p,w&gt;</code>
	 * with weight <code>d</code> to this module,
	 * where <code>p</code> is the default control state.
	 * 
	 * @param y the left-hand-side stack symbol.
	 * @param d the weight of the rule.
	 * @param w the right-hand-side stack symbols.
	 */
	public void addSharedRule(String y, Semiring d, String... w) {
		
		Rule r = new Rule(d, Remopla.p, y, Remopla.p, w);
		r.setGlobal(true);
		addRule(r);
	}
	
	/**
	 * Gets the name of this module.
	 * 
	 * @return the name of this module.
	 */
	public String getName() {
		return name;
	}
	
	/**
	 * Returns the names in which this module calls.
	 * 
	 * @return the names in which this module calls.
	 */
	public String[] getCalledNames() {
		
		ArrayList<String> names = new ArrayList<String>();
		for (Rule rule : rules) {
			String[] w = rule.right.w;
			if (w != null && w.length > 1)
				names.add(w[0]);
		}
		
		return names.toArray(new String[names.size()]);
	}
	
	/**
	 * Fills <code>set</code> with all constant names in this module.
	 * 
	 * @param set the set of constants to be filled.
	 */
	void fillConstants(Set<String> set) {
		for (Rule r : rules) {
			ExprSemiring d = (ExprSemiring) r.getWeight();
			if (d.type == ExprType.CONSTLOAD || d.type == ExprType.CONSTSTORE) {
				set.add((String) d.value);
			}
		}
	}
	
	/**
	 * Returns the string representation of this module.
	 * 
	 * @return the string representation of this module.
	 */
	public String toString() {
		
		StringBuilder out = new StringBuilder();
		out.append(String.format("Module %s, stack depth=%d, local vars=%d%n", 
				name, sdepth, lvnum));
		for (Rule r : rules) {
			out.append(String.format("\t%s%n", r));
		}
		
		return out.toString();
	}
	
	private static Rule rule;
	
	/**
	 * Default prefix of local variables.
	 */
	static final String lv = "lv";
	
	/**
	 * Default operand stack name.
	 */
	static final String stack = "s";
	
	/**
	 * Default stack pointer name.
	 */
	static final String sptr = "sptr";
	
	/**
	 * Default heap name.
	 */
	static final String heap = "heap";
	
	/**
	 * Default heap pointer name.
	 */
	static final String hptr = "ptr";
	
	/**
	 * Default name of the return variable.
	 */
	static final String ret = "ret";
	
	/**
	 * Returns the string that represents the header of this module 
	 * in Moped's syntax.
	 * 
	 * @return the header of this module in Moped's syntax.
	 */
	public String toMopedHeader() {
		StringBuilder out = new StringBuilder();
		
		Utils.append(out, "module %s %s0(", "void", Remopla.mopedize(name));
		for (int i = 0; i < params.length; i++) {
			if (i > 0) out.append(", ");
			Utils.append(out, "int %s%d", lv, i);
		}
		Utils.append(out, ")");
		return out.toString();
	}
	
	/**
	 * Returns the string that represents this module in Moped's syntax.
	 * 
	 * @return this module in Moped's syntax.
	 */
	public String toMoped(int heapsize) {
		
		StringBuilder out = new StringBuilder();
		
		// Header
		out.append(toMopedHeader());
		Utils.append(out, " {%n");
		
		// Operand stack
		if (sdepth > 0) {
			Utils.append(out, "int %s[%d];%n", stack, sdepth);
			Utils.append(out, "int %s;%n", sptr);
		}
		
		// Local vars
		for (int i = params.length; i < lvnum; i++) {
			Utils.append(out, "int %s%d;%n", lv, i);
		}
		
		// Init operand stack
		if (sdepth > 0)
			Utils.append(out, "%s = 0;%n", sptr);
		Utils.append(out, "%n");
		
		// Rules
		Iterator<Rule> itr = rules.iterator();
		rule = itr.next();
		while (rule != null) {
			// To be iterated?
			boolean toIterate = true;
			
			String label = rule.getLabel();
			if (LabelUtils.isNpeName(label)
					|| LabelUtils.isIoobName(label)
					|| LabelUtils.isHeapOverflowName(label)) {
				if (itr.hasNext()) rule = itr.next();
				continue;
			}
			
			String s = null;
			ExprSemiring d = (ExprSemiring) rule.getWeight();
			switch (d.type) {
			case ARITH: s = arith(d); break;
			case ARRAYLENGTH: s = arraylength(); break;
			case ARRAYLOAD: s = arrayload(); break;
			case ARRAYSTORE: s = arraystore(); break;
			case CONSTLOAD: s = constload(d); break;
			case CONSTSTORE: s = conststore(d); break;
			case DUP: s = dup(d); break;
			case ERROR: s = error(); break;
			case FIELDLOAD: s = fieldload(itr); toIterate = false; break;
			case FIELDSTORE: s = fieldstore(itr); toIterate = false; break;
			case GETRETURN : s = getreturn(); break;
			case GLOBALLOAD: s = globalload(d); break;
			case GLOBALPUSH: s = globalpush(d); break;
			case GLOBALSTORE: s = globalstore(d); break;
			case HEAPLOAD: s = heapload(); break;
			case HEAPOVERFLOW: break;
			case IF: s = ifexpr(itr); toIterate = false; break;
			case IFCMP: s = ifcmp(itr); toIterate = false; break;
			case INC: s = inc(d); break;
			case INVOKE: s = invoke(itr); toIterate = false; break;
			case IOOB: break;
			case LOAD: s = load(d); break;
			case MONITORENTER: s = monitorenter(d); break;
			case MONITOREXIT: s = monitorexit(); break;
			case NEW: s = newexpr(itr, heapsize); toIterate = false; break;
			case NEWARRAY: s = newarray(d, heapsize); break;
			case NPE: break;
			case ONE: s = one(itr); toIterate = false; break;
			case POPPUSH: s = poppush(d); break;
			case PRINT: s = skip(); break;
			case PUSH: s = push(d); break;
			case RETURN: s = returnexpr(d); break;
			case STORE: s = store(d); break;
			case UNARYOP: s = unaryop(d); break;
			}
			
			if (s != null) {
				if (LabelUtils.getOffset(label) == 0)
					Utils.append(out, "%s%n", s);
				else
					Utils.append(out, "%s: %s%n", Remopla.mopedize(label), s);
			}
			
			// Iterates if toIterate is true
			if (toIterate) {
				rule = (itr.hasNext()) ? itr.next() : null;
			}
		}
		
		Utils.append(out, "}%n");
		
		return out.toString();
	}
	
	private static String s(int x) {
		return String.format("%s[%s - %d]", stack, sptr, x);
	}
	
	private static String s0() {
		return s(1);
	}
	
	private static String s1() {
		return s(2);
	}
	
	private static String s2() {
		return s(3);
	}
	
	private static String lv(int x) {
		return String.format("%s%d", lv, x);
	}
	
	private static String arith(ExprSemiring d) {
		ArithType type = (ArithType) d.value;
		String op = null;
		switch (type) {
		case ADD: op = "+"; break;
		case AND: op = "-"; break;
		case CMP:
			StringBuilder b = new StringBuilder();
			Utils.append(b, "if%n");
			Utils.append(b, "\t:: (%s[%s - 2] > %s[%s - 1]) -> %s[%s - 1] = 1, %s = %s - 1;%n", 
					stack, sptr, stack, sptr, stack, sptr, sptr, sptr);
			Utils.append(b, "\t:: (%s[%s - 2] == %s[%s - 1]) -> %s[%s - 1] = 0, %s = %s - 1;%n", 
					stack, sptr, stack, sptr, stack, sptr, sptr, sptr);
			Utils.append(b, "\t:: (%s[%s - 2] < %s[%s - 1]) -> %s[%s - 1] = undef, %s = %s - 1;%n", 
					stack, sptr, stack, sptr, stack, sptr, sptr, sptr);
			Utils.append(b, "fi;");
			return b.toString();
		case DIV: op = "/"; break;
		case MUL: op = "*"; break;
		case OR: op = "|"; break;
		case REM: op = "%"; break;
		case SHL: op = "<<"; break;
		case SHR: op = ">>"; break;
		case SUB: op = "-"; break;
		case USHR: op = ">>>"; break;
		case XOR: op = "^"; break;
		default:
			throw new RemoplaError("Cannot Translate floating points into Remopla.");
		}
		return String.format("%s[%s - 2] = %s[%s - 2] %s %s[%s - 1], %s = %s - 1;", 
				stack, sptr, stack, sptr, op, stack, sptr, sptr, sptr);
	}
	
	private static String arraylength(String arrayref) {
		return String.format("%s[%s + 1]", heap, arrayref);
	}
	
	private static String arrayelement(String arrayref, String index, boolean prime) {
		return String.format("%s%s[%s + %s + 2]", heap, (prime) ? "'" : "", arrayref, index);
	}
	
	private static String arrayelement(String arrayref, String index) {
		return arrayelement(arrayref, index, false);
	}
	
	private static String arraylength() {
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		Utils.append(b, npe(s0()));
		Utils.append(b, "\t:: (%s != 0) -> %s = %s;%n", s0(), s0(), arraylength(s0()));
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	private static String ioob(String arrayref, String index) {
		return String.format("\t:: (%s != 0 && %s >= %s) -> %s: goto %s;%n", 
				arrayref, index, arraylength(arrayref), 
				Remopla.mopedize(LabelUtils.formatIoobName(rule.getLabel())), 
				Remopla.ioob);
	}
	
	private static String npe(String ref) {
		return String.format("\t:: (%s == 0) -> %s: goto %s;%n", 
				ref, 
				Remopla.mopedize(LabelUtils.formatNpeName(rule.getLabel())), 
				Remopla.npe);
	}
	
	/*
	 * Operand stack: ..., arrayref (s1), index (s0)
	 */
	private static String arrayload() {
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		Utils.append(b, npe(s1()));
		Utils.append(b, ioob(s1(), s0()));
		Utils.append(b, "\t:: (%s != 0 && %s < %s) -> %s = %s, %s = %s - 1;%n", 
				s1(), s0(), arraylength(s1()), s1(), arrayelement(s1(), s0()), sptr, sptr);
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	/*
	 * Operand stack: ..., arrayref (s2), index (s1), value (s0)
	 */
	private static String arraystore() {
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		Utils.append(b, npe(s2()));
		Utils.append(b, ioob(s2(), s1()));
		Utils.append(b, "\t:: (%s != 0 && %s < %s) -> %s = %s, %s = %s - 3;%n", 
				s2(), s1(), arraylength(s2()), arrayelement(s2(), s1()), s0(), sptr, sptr);
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	private static String constload(ExprSemiring d) {
		return String.format("%s[%s] = %s, %s = %s + 1;", 
				stack, sptr, Remopla.mopedize((String) d.value), sptr, sptr);
	}
	
	private static String conststore(ExprSemiring d) {
		return String.format("%s = %s, %s = %s - 1;", 
				Remopla.mopedize((String) d.value), s0(), sptr, sptr);
	}
	
	private static String dup(ExprSemiring d) {
		DupType type = (DupType) d.value;
		switch (type) {
		case DUP: {
			return String.format("%s[%s] = %s[%s - 1], %s = %s + 1;",
					stack, sptr, stack, sptr, sptr, sptr);
		}
		case DUP_X1: {
			return String.format("%s[%s] = %s[%s - 1], %s[%s - 1] = %s[%s - 2], " +
					"%s[%s - 2] = %s[%s - 3], %s = %s + 1;",
					stack, sptr, stack, sptr, stack, sptr, stack, sptr, stack, sptr, stack, sptr, sptr, sptr);
		}
		case DUP2: {
			return String.format("%s[%s + 1] = %s[%s - 1], %s[%s] = %s[%s - 2], " +
					"%s = %s + 2;", stack, sptr, stack, sptr, stack, sptr, stack, sptr, sptr, sptr);
		}
		default:
			throw new IllegalArgumentException(
					String.format("Instruction %s not supported", type));
		}
	}
	
	private static String error() {
		return String.format("goto error;");
	}
	
	private static StringBuilder fulfillsCondition(Condition cond, int s) {
		
		if (cond == null)
			return new StringBuilder("true");
		
		StringBuilder b = new StringBuilder();
		switch (cond.type) {
		case CONTAINS:
			Set<Integer> set = (Set<Integer>) cond.value;
			int count = 0;
			for (Integer index : set) {
				if (count > 0) Utils.append(b, " || ");
				Utils.append(b, "%s[%s] == %d", heap, s(s), index);
				count++;
			}
			break;
		case ZERO:
			Utils.append(b, "%s == 0", (String) cond.value);
			break;
		case ONE:
			Utils.append(b, "%s == 1", (String) cond.value);
			break;
		}
		
		return b;
	}
	
	/*
	 * ..., objectref (s0)
	 */
	private static String fieldload(Iterator<Rule> itr) {
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		Utils.append(b, npe(s0()));
		
		String label = rule.getLabel();
		do {
			Utils.append(b, "\t:: (%s != 0 && (", s0());
			ExprSemiring d = (ExprSemiring) rule.getWeight();
			b.append(fulfillsCondition((Condition) d.aux, 1));
			Utils.append(b, ")) -> %s = %s[%s + %d];%n", 
					s0(), heap, s0(), (Integer) d.value);

			// Next rule
			if (itr.hasNext()) rule = itr.next();
			else rule = null;
		} while (rule != null && rule.getLabel().equals(label));
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	/*
	 * ..., objecref (s1), value (s0)
	 */
	private static String fieldstore(Iterator<Rule> itr) {
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		Utils.append(b, npe(s1()));
		
		String label = rule.getLabel();
		do {
			Utils.append(b, "\t:: (%s != 0 && (", s1());
			ExprSemiring d = (ExprSemiring) rule.getWeight();
			b.append(fulfillsCondition((Condition) d.aux, 2));
			Utils.append(b, ")) -> %s[%s + %d] = %s, sptr = sptr - 2;%n", 
					heap, s1(), (Integer) d.value, s0());

			// Next rule
			if (itr.hasNext()) rule = itr.next();
			else rule = null;
		} while (rule != null && rule.getLabel().equals(label));
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	private static String getreturn() {
		return String.format("%s[%s] = %s, %s = %s + 1;", 
				stack, sptr, ret, sptr, sptr);
	}
	
	private static String globalload(ExprSemiring d) {
		return String.format("%s[%s] = %s, %s = %s + 1;", 
				stack, sptr, (String) d.value, sptr, sptr);
	}
	
	private static String globalpush(ExprSemiring d) {
		return String.format("%s = %d;", 
				(String) d.value, (Integer) d.aux);
	}
	
	private static String globalstore(ExprSemiring d) {
		return String.format("%s = %s[%s - 1], %s = %s - 1;", 
				(String) d.value, stack, sptr, sptr, sptr);
	}
	
	private static String heapload() {
		return String.format("%s[%s] = %s[%s[%s - 1]], %s = %s + 1;", 
				stack, sptr, heap, stack, sptr, sptr, sptr);
	}
	
	private static String iftype(ExprSemiring.If.Type type) {
		switch (type) {
		case EQ: return "==";
		case NE: return "!=";
		case LT: return "<";
		case GE: return ">=";
		case GT: return ">";
		case LE: return "<=";
		default:
			throw new RemoplaError("Unexpected if type");
	}
	}
	
	private static String ifexpr(ExprSemiring.If expr) {
		
		ExprSemiring.If.Type type = expr.type;
		switch (type) {
		case IS: return String.format("%s == %d", s0(), expr.getValue());
		case LG: return String.format("%s < %d || %s > %d", 
				s0(), expr.getLowValue(), s0(), expr.getHighValue());
		case NOT: {
			StringBuilder b = new StringBuilder();
			Set<Integer> not = expr.getNotSet();
			int count = 0;
			for (Integer n : not) {
				if (count > 0) b.append(" && ");
				Utils.append(b, "%s != %d", s0(), n);
				count++;
			}
			return b.toString();
		}
		default:
			return String.format("%s %s 0", s0(), iftype(type));
		}
	}
	
	private static String ifexpr(Iterator<Rule> itr) {
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		
		String label = rule.getLabel();
		do {
			Utils.append(b, "\t:: (");
			ExprSemiring d = (ExprSemiring) rule.getWeight();
			b.append(ifexpr((ExprSemiring.If) d.value));
			Utils.append(b, ") -> goto %s, %s = %s - 1;%n", Remopla.mopedize(rule.getRightLabel()), sptr, sptr);

			// Next rule
			if (itr.hasNext()) rule = itr.next();
			else rule = null;
		} while (rule != null && rule.getLabel().equals(label));
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	private static String ifcmp(Iterator<Rule> itr) {
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		
		String label = rule.getLabel();
		do {
			Utils.append(b, "\t:: (");
			ExprSemiring d = (ExprSemiring) rule.getWeight();
			Utils.append(b, "%s %s %s", s1(), ((ExprSemiring.CompType) d.value).getName(), s0());
			Utils.append(b, ") -> goto %s, %s = %s - 2;%n", Remopla.mopedize(rule.getRightLabel()), sptr, sptr);
			
			// Next rule
			if (itr.hasNext()) rule = itr.next();
			else rule = null;
		} while (rule != null && rule.getLabel().equals(label));
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	private static String inc(ExprSemiring d) {
		ExprSemiring.Inc inc = (ExprSemiring.Inc) d.value;
		if (inc.value > 0)
			return String.format("%s = %s + %d;", lv(inc.index), lv(inc.index), inc.value);
		else
			return String.format("%s = %s - %d;", lv(inc.index), lv(inc.index), -1*inc.value);
	}
	
	private static String invoke(Iterator<Rule> itr) {
		StringBuilder b = new StringBuilder();
		String label = rule.getLabel();
		boolean npeprinted = false;
		
		Utils.append(b, "if%n");
		do {
			ExprSemiring d = (ExprSemiring) rule.getWeight();
			ExprSemiring.Invoke invoke = (ExprSemiring.Invoke) d.value;
			boolean[] params = invoke.params;
			int nargs = params.length;
			
			// NPE
			if (!npeprinted && !invoke.isStatic) {
				Utils.append(b, npe(s(nargs)));
				npeprinted = true;
			}
			
			Utils.append(b, "\t:: (");
			if (!invoke.isStatic)
				Utils.append(b, "%s != 0 && (", s(nargs));
			b.append(fulfillsCondition((Condition) d.aux, nargs));
			if (!invoke.isStatic)
				b.append(')');
			Utils.append(b, ") -> %s(", Remopla.mopedize(rule.getRightLabel()));
			for (int i = 0; i < nargs; i++) {
				if (i > 0) b.append(", ");
				b.append(s(nargs - i));
			}
			b.append(")");
			if (nargs > 0)
				Utils.append(b, ", %s = %s - %d", sptr, sptr, nargs);
			b.append(";%n");
			
			// Next rule
			if (itr.hasNext()) rule = itr.next();
			else rule = null;
		} while (rule != null && rule.getLabel().equals(label));
		
		// GLOBALLOAD, GLOBALSTORE
		if (rule != null) {
			ExprSemiring d = (ExprSemiring) rule.getWeight();
			if (d.type == ExprType.GLOBALLOAD || d.type == ExprType.GLOBALSTORE) {
				Utils.append(b, "\t\t%s%n", 
						(d.type == ExprType.GLOBALLOAD) ? globalload(d) : globalstore(d));
				
				// Next rule guarantees to be either globalload or globalstore
				rule = itr.next();
				d = (ExprSemiring) rule.getWeight();
				Utils.append(b, "\t:: (");
				b.append(fulfillsCondition((Condition) d.aux, 0));
				Utils.append(b, ") -> %s%n;", 
						(d.type == ExprType.GLOBALLOAD) ? globalload(d) : globalstore(d));
				
				// Next rule
				rule = itr.next();
			}
		}
		
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	private static String load(ExprSemiring d) {
		return String.format("%s[%s] = %s, %s = %s + 1;", 
			stack, sptr, lv((Integer) d.value), sptr, sptr);
	}
	
	private static String monitorenter(ExprSemiring d) {
		ExprSemiring.Monitorenter expr = (ExprSemiring.Monitorenter) d.value;
		if (expr.type == ExprSemiring.Monitorenter.Type.POP)
			return String.format("%s = %s - 1;", sptr, sptr);
		return "skip;";
	}
	
	private static String monitorexit() {
		return String.format("%s = %s - 1;", sptr, sptr);
	}
	
	private static String newexpr(Iterator<Rule> itr, int heapsize) {
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		boolean nehprinted = false;
		
		String label = rule.getLabel();
		do {
			ExprSemiring d = (ExprSemiring) rule.getWeight();
			ExprSemiring.New n = (ExprSemiring.New) d.value;
			
			// Checks whether heap is enough
			if (!nehprinted) {
				Utils.append(b, "\t :: (%s + %s + 1 > %d) -> %s: goto %s;%n", 
						hptr, n.size, heapsize, 
						Remopla.mopedize(LabelUtils.formatHeapOverflowName(rule.getLabel())),
						Remopla.notenoughheap);
				nehprinted = true;
			}
			
			Utils.append(b, "\t:: (%s + %s + 1 <= %d && ", hptr, n.size, heapsize);
			b.append(fulfillsCondition((Condition) d.aux, 0));
			Utils.append(b, ") -> %s[%s] = %d", heap, hptr, n.id);
			for (int i = 1; i <= n.size; i++)
				Utils.append(b, ", %s[%s + %d] = 0", heap, hptr, i);
			Utils.append(b, ", %s[%s] = %s, %s = %s + %d, %s = %s + 1;%n", 
					stack, sptr, hptr, hptr, hptr, n.size + 1, sptr, sptr);

			// Next rule
			if (itr.hasNext()) rule = itr.next();
			else rule = null;
		} while (rule != null && rule.getLabel().equals(label));
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	private static String newarray(ExprSemiring d, int heapsize) {
		ExprSemiring.Newarray newarray = (ExprSemiring.Newarray) d.value;
		if (newarray.dim > 1)
			throw new RemoplaError("Multi-dimensional arrays not supported");
		
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		Utils.append(b, "\t:: (%s + %s + 2 > %d) -> %s: goto %s;%n", 
				hptr, s0(), heapsize, 
				Remopla.mopedize(LabelUtils.formatHeapOverflowName(rule.getLabel())),
				Remopla.notenoughheap);
		Utils.append(b, "\t:: (%s + %s + 2 <= %d) -> %s[%s] = %d, %s[%s + 1] = %s, %s = %s + %s + 2, %s = %s, %s = 0;%n", 
				hptr, s0(), heapsize, heap, hptr, newarray.types[0], heap, hptr, s0(), hptr, hptr, s0(), s0(), hptr, ret);
		Utils.append(b, "fi;%n");
		
		ExprSemiring.Value value = newarray.init;
		Utils.append(b, "do%n");
		Utils.append(b, "\t:: (%s < %s) -> ", ret, arraylength(s0()), heap, s0());
		if (value.all()) {
			Utils.append(b, "%s = undef, %s = %s + 1;%n", 
					arrayelement(s0(), ret), ret, ret);
		} else if (value.deterministic()) {
			if (!value.isInteger())
				throw new RemoplaError("Floating Points or Strings not supported");
			Utils.append(b, "%s = %d, %s = %s + 1;%n", 
					arrayelement(s0(), ret), value.intValue(), ret, ret);
		} else {
			Utils.append(b, "skip (%s >= %d && %s <= %d && %s' == %s + 1);%n",
					arrayelement(s0(), ret, true), value.intValue(), 
					arrayelement(s0(), ret, true), value.to.intValue(), 
					ret, ret);
		}
		
		Utils.append(b, "\t:: else -> break;%n");
		Utils.append(b, "od;");
		return b.toString();
	}
	
	private static String one(Iterator<Rule> itr) {
		StringBuilder b = new StringBuilder();
		Utils.append(b, "if%n");
		boolean npeprinted = false;
		
		String label = rule.getLabel();
		do {
			Condition c = (Condition) ((ExprSemiring) rule.getWeight()).aux;
			boolean contains = (c == null) 
				? false 
				: (c.type == Condition.ConditionType.CONTAINS);
			if (contains && !npeprinted) {
				npe(s0());
				npeprinted = true;
			}
			
			Utils.append(b, "\t:: (");
			if (contains)
				Utils.append(b, "%s != 0 && (", s0());
			b.append(fulfillsCondition(c, 1));
			if (contains)
				b.append(')');
			Utils.append(b, ") -> goto %s;%n",
					Remopla.mopedize(rule.getRightLabel()));

			// Next rule
			if (itr.hasNext()) rule = itr.next();
			else rule = null;
		} while (rule != null && rule.getLabel().equals(label));
		Utils.append(b, "fi;");
		return b.toString();
	}
	
	private static String poppush(ExprSemiring d) {
		int pop = (Integer) d.value;
		int push = ((Boolean) d.aux) ? 1 : 0;
		
		if (pop == 0 && push == 0)
			return "skip;";
		
		if (push == 0)
			return String.format("%s = %s - %d;", sptr, sptr, pop);
		
		// Remains: push == 1
		
		if (pop == 0)
			return String.format("%s[%s] = undef, %s = %s + 1;", 
					stack, sptr, sptr, sptr);
		
		if (pop == 1)
			return String.format("%s = undef;", 
					s0(), sptr, sptr);
		
		return String.format("%s[%s - %d] = undef, %s = %s - %d;", 
					stack, sptr, pop, sptr, sptr, pop - 1);
	}
	
	private static String push(ExprSemiring d) {
		ExprSemiring.Value value = (ExprSemiring.Value) d.value;
		String topush = null;
		if (value.all() || value.isString() || value.isReal()) {
			topush = "undef"; 
		} else if (value.deterministic()) {
			int n = value.intValue();
			topush = (n >= 0) ? String.valueOf(n) : "undef";
		} else {
			if (value.intValue() < 0 || value.to.intValue() < 0) {
				topush = "undef";
			}
		}
		
		// Total nondeterministic or deterministic
		if (topush != null) {
			return String.format("%s[%s] = %s, %s = %s + 1;",
					stack, sptr, topush, sptr, sptr);
		}
		
		// Value range
		return String.format("skip (%s'[%s] >= %d && %s'[%s] <= %d && %s' == %s + 1);",
				stack, sptr, value.intValue(), stack, sptr, value.to.intValue(), sptr, sptr);
	}
	
	private static String returnexpr(ExprSemiring d) {
		if ((Integer) d.value > 0)
			return String.format("%s = %s[sptr - 1]; return;", ret, stack, sptr);
		return "return;";
	}
	
	private static String skip() {
		return "skip;";
	}
	
	private static String store(ExprSemiring d) {
		return String.format("%s = %s, %s = %s - 1;", 
				lv((Integer) d.value), s0(), sptr, sptr);
	}
	
	private static String unaryop(ExprSemiring d) {
		ExprSemiring.UnaryOpType type = (ExprSemiring.UnaryOpType) d.value;
		switch (type) {
		case NEG:
		case FNEG:
			return String.format("%s = undef;", s0());
		case F2I:
		case I2F:
			return "skip;";
		}
		throw new RemoplaError("Floating points not supported");
	}
}
