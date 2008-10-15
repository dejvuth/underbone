package de.tum.in.jmoped.underbone;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.logging.Logger;

import de.tum.in.jmoped.underbone.expr.Arith;
import de.tum.in.jmoped.underbone.expr.Category;
import de.tum.in.jmoped.underbone.expr.Comp;
import de.tum.in.jmoped.underbone.expr.Condition;
import de.tum.in.jmoped.underbone.expr.Dup;
import de.tum.in.jmoped.underbone.expr.ExprSemiring;
import de.tum.in.jmoped.underbone.expr.ExprType;
import de.tum.in.jmoped.underbone.expr.Field;
import de.tum.in.jmoped.underbone.expr.If;
import de.tum.in.jmoped.underbone.expr.Inc;
import de.tum.in.jmoped.underbone.expr.Invoke;
import de.tum.in.jmoped.underbone.expr.Jump;
import de.tum.in.jmoped.underbone.expr.Local;
import de.tum.in.jmoped.underbone.expr.Monitorenter;
import de.tum.in.jmoped.underbone.expr.New;
import de.tum.in.jmoped.underbone.expr.Newarray;
import de.tum.in.jmoped.underbone.expr.Npe;
import de.tum.in.jmoped.underbone.expr.Poppush;
import de.tum.in.jmoped.underbone.expr.Print;
import de.tum.in.jmoped.underbone.expr.Return;
import de.tum.in.jmoped.underbone.expr.Unaryop;
import de.tum.in.jmoped.underbone.expr.Value;
import de.tum.in.wpds.Config;
import de.tum.in.wpds.Fa;
import de.tum.in.wpds.Pds;
import de.tum.in.wpds.PdsSat;
import de.tum.in.wpds.Rule;
import de.tum.in.wpds.Utils;

/**
 * The virtual machine that runs Remopla codes.
 * 
 * @author suwimont
 *
 */
public class VirtualMachine {

	/**
	 * The Remopla model.
	 */
	private Remopla remopla;
	
	/**
	 * The global values.
	 */
	HashMap<String, Number> globals;
	
	/**
	 * The heap.
	 */
	Heap heap;
	
	/**
	 * The current call frame.
	 */
	Frame frame;
	
	/**
	 * Maps labels to list of raw arguments that lead to the labels.
	 */
	private Map<String, List<RawArgument>> raws;
	
	/**
	 * Controls whether to display method arguments when executing Remopla.
	 */
	private boolean displayArgs = true;
	
	/**
	 * Verbosity level.
	 */
	private static int verbosity = 0;
	
	/**
	 * The logger.
	 */
	private static Logger logger = Utils.getLogger(VirtualMachine.class, "%t/VirtualMachine%g.log");
	
	/**
	 * Initializes the virtual machine the Remopla model specified by 
	 * <code>remopla</code>.
	 * 
	 * @param remopla the Remopla modeul.
	 */
	public VirtualMachine(Remopla remopla) {
		this.remopla = remopla;
	}
	
	/**
	 * Gets the raw arguments that lead to <code>label</code>.
	 * 
	 * @param label the label.
	 * @return the list of raw arguments.
	 */
	public List<RawArgument> getRawArguments(String label) {
		return raws.get(label);
	}
	
	ArrayList<String> strings;
	
	private int encode(String s) {
		int index = strings.indexOf(s);
		if (index != -1) return index;
		
		index = strings.size();
		strings.add(s);
		return index;
	}
	
	private Number arraylength(int index) {
		return heap.get(index + 1);
	}
	
	private int indexOfArrayElement(int ref, int index) {
		return ref + index + 2;
	}
	
	/**
	 * Runs the virtual machine.
	 * 
	 * @param monitor the progress monitor.
	 */
	public void run(ProgressMonitor monitor) {
		
		// First post*: collecting reachable labels
		Pds pds = remopla.getPds();
		Fa fa = new Fa();
		fa.add(new NullSemiring(), Remopla.p, remopla.init, Remopla.s);
		PdsSat sat = new PdsSat(pds);
		Fa post = (Fa) sat.poststar(fa);
		Set<String> labels = post.getLabels();
//		for (String label : labels)
//			log("%s%n", label);
		
		// Creates Remopla listener and wraps the monitor
		RemoplaListener listener = remopla.getRemoplaListener();
		listener.setProgressMonitor(monitor);
		listener.beginTask(remopla.getLastCalledName(), labels);
		monitor.subTask("Analyzing ...");
		
		HashMap<Config, Set<Rule>> rmap = remopla.getPds().getLeftMapper();
		
		// Constants
		HashMap<String, Number> constants = new HashMap<String, Number>();
		
		// Strings
		strings = new ArrayList<String>();
		strings.add("");
		
		// Global variables
		globals = new HashMap<String, Number>();
		if (remopla.globals != null) {
			for (Variable global : remopla.globals) {
				globals.put(global.name, 0);
			}
		}
		
		// Heap
		heap = new Heap();
		heap.add(0);
		
		Heap heapsave = null;
		HashMap<String, Number> globalssave = null;
		RawArgument raw = null;
		raws = new HashMap<String, List<RawArgument>>();
		
		// Stack of frames
		Stack<Frame> frames = new Stack<Frame>();
		frame = new Frame(remopla.init);
		
		// Return variable
		Number retvar = null;
		
		while (frame.label != null) {
			
			if (monitor.isCanceled()) break;
			
			if (all()) {
				debug("ptr: %d, heap: %s%n", heap.size(), heap);
				debug("globals: %s%n", globals);
			}
			debug("frame: %s%n%n", frame);
			if (listener != null) listener.reach(frame.label);
			
			Config config = new Config(Remopla.p, frame.label);
			Set<Rule> rules = rmap.get(config);
			if (rules == null) break;
			
			// Loops for each rule beginning with <p, label>
			boolean thisrule = false;
			for (Rule rule : rules) {
				
				debug("\t%s%n", rule);
				
				/*
				 *  Controls whether this rule is the right rule.
				 *  Sets this variable to false and the next rule will be
				 *  considered.
				 */
				thisrule = true;
				
				String[] w = rule.right.w;
				if (w != null && w.length > 0)
					frame.label = w[0];
				
				ExprSemiring d = (ExprSemiring) rule.d;
				switch (d.type) {
				
				case ExprType.ARITH: {
					Arith arith = (Arith) d.value;
					int type = arith.getType();
					boolean two = arith.getCategory() == Category.TWO;
					Number s0 = frame.pop();
					if (two && type != Arith.SHL && type != Arith.SHR && type != Arith.USHR) 
						s0 = frame.pop();
					Number s1 = frame.pop();
					if (two) s1 = frame.pop();
					
					switch (type) {
						case Arith.ADD: s0 = s1.longValue() + s0.longValue(); break;
						case Arith.AND: s0 = s1.longValue() & s0.longValue(); break;
						case Arith.CMP:
							if (s1.longValue() > s0.longValue()) s0 = 1;
							else if (s1.longValue() == s0.longValue()) s0 = 0;
							else s0 = -1;
							break;
						case Arith.DIV: s0 = s1.longValue() / s0.longValue(); break;
						case Arith.MUL: s0 = s1.longValue() * s0.longValue(); break;
						case Arith.OR: s0 = s1.longValue() | s0.longValue(); break;
						case Arith.REM: s0 = s1.longValue() % s0.longValue(); break;
						case Arith.SHL: s0 = s1.longValue() << (s0.intValue() & 31); break;
						case Arith.SHR: s0 = s1.longValue() >> (s0.intValue() & 31); break;
						case Arith.SUB: s0 = s1.longValue() - s0.longValue(); break;
						case Arith.USHR: s0 = s1.longValue() >>> (s0.intValue() & 31); break;
						case Arith.XOR: s0 = s1.longValue() ^ s0.longValue(); break;
						case Arith.FADD: s0 = s1.doubleValue() + s0.doubleValue(); break;
						case Arith.FCMPG: 
						case Arith.FCMPL: {
							if (s1.doubleValue() > s0.doubleValue()) s0 = 1f;
							else if (s1.doubleValue() == s0.doubleValue()) s0 = 0f;
							else if (s1.doubleValue() < s0.doubleValue()) s0 = -1f;
							// At least one must be NaN
							else if (type == Arith.FCMPG) s0 = 1f;
							else s0 = -1f;
							break;
						}
						case Arith.FDIV: s0 = s1.doubleValue() / s0.doubleValue(); break;
						case Arith.FMUL: s0 = s1.doubleValue() * s0.doubleValue(); break;
						case Arith.FREM: s0 = s1.doubleValue() % s0.doubleValue(); break;
						case Arith.FSUB: s0 = s1.doubleValue() - s0.doubleValue(); break;
						case Arith.NDT: {
							double p = s0.doubleValue() - s1.doubleValue() + 1.0;
							s0 = ((long) (p * Math.random())) + s1.longValue();
							break;
						}
					}
					frame.stack.push(s0);
					if (two && type != Arith.CMP) frame.stack.push(0);
					break;
				}
				
				case ExprType.ARRAYLENGTH: {
					// Checks NPE
					int s0 = frame.pop().intValue();
					if (npe(s0, rule.left.w[0], listener, raw, frames)) break;
					
					// Pushes array length
					frame.stack.push(arraylength(s0));
					break;
				}
				
				case ExprType.ARRAYLOAD: {
					// Checks NPE
					int s0 = frame.pop().intValue();	// index
					int s1 = frame.pop().intValue();	// arrayref
					if (npe(s1, rule.left.w[0], listener, raw, frames)) 
						break;
					
					// Checks IOOB
					int length = arraylength(s1).intValue();
//					log("length: %d, s0: %d%n", length, s0);
					if (ioob(length, s0, rule.left.w[0], listener, raw, frames)) 
						break;
					
					// Pushes
					frame.stack.push(heap.get(indexOfArrayElement(s1, s0)));
					
					// Category 2
					if (((Category) d.value).two())
						frame.stack.push(0);
					break;
				}
				
				case ExprType.ARRAYSTORE: {
					// Category 2
					if (((Category) d.value).two())
						frame.pop();
					
					// Checks NPE
					Number s0 = frame.pop();			// value
					int s1 = frame.pop().intValue();	// index
					int s2 = frame.pop().intValue();	// arrayref
					if (npe(s2, rule.left.w[0], listener, raw, frames)) 
						break;
					
					// Checks IOOB
					int length = arraylength(s2).intValue();
					if (ioob(length, s1, rule.left.w[0], listener, raw, frames)) 
						break;
					
					// Stores s0 to the array
					heap.set(indexOfArrayElement(s2, s1), s0);
					break;
				}
				
				case ExprType.CONSTLOAD: {
					// Checks whether the condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					// Pushes constant
					Field field = (Field) d.value;
					frame.push(constants.get(field.getName()));
					if (field.getCategory().two())
						frame.push(0);
					break;
				}
				
				case ExprType.CONSTSTORE: {
					// Checks whether the condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					// Pops and stores constant
					Field field = (Field) d.value;
					if (field.getCategory().two())
						frame.pop();
					constants.put(field.getName(), frame.pop());
					break;
				}
				
				case ExprType.DUP: {
					// Pops
					Dup type = (Dup) d.value;
					Number[] values = new Number[type.down];
					for (int i = 0; i < type.down; i++)
						values[i] = frame.stack.pop();
					
					// Pushes
					for (int i = type.push - 1; i >= 0; i--)
						frame.stack.push(values[i]);
					
					// Shifts
					for (int i = type.down - 1; i >= 0; i--)
						frame.stack.push(values[i]);
					break;
				}
				
				case ExprType.ERROR: {
					error(rule.left.w[0], raw, frames);
					break;
				}
				
				case ExprType.FIELDLOAD: {
					// Checks condition
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					// Checkes NPE
					int s0 = frame.pop().intValue();
					if (npe(s0, rule.left.w[0], listener, raw, frames)) break;
					
					// Pushes
					Field field = (Field) d.value;
					frame.stack.push(heap.get(s0 + field.getId()));
					if (field.getCategory().two())
						frame.stack.push(0);
					break;
				}
				
				case ExprType.FIELDSTORE: {
					// Checks condition
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					// Checkes NPE
					Field field = (Field) d.value;
					Number s0 = frame.pop();
					if (field.getCategory().two())
						s0 = frame.pop();
					int s1 = frame.pop().intValue();
//					System.out.printf("s1: %d, s0: %d%n", s1, s0.intValue());
					if (npe(s1, rule.left.w[0], listener, raw, frames)) break;
					
					// Stores s0 to heap
					heap.set(s1 + field.getId(), s0);
					break;
				}
				
				case ExprType.GETRETURN: {
					frame.stack.push(retvar);
					if (((Category) d.value).two())
						frame.stack.push(0);
					break;
				}
				
				// Pushes from global
				case ExprType.GLOBALLOAD: {
					// Checks whether the invoke condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					Field field = (Field) d.value;
					frame.stack.push(globals.get(field.getName()));
					if (field.getCategory().two())
						frame.stack.push(0);
					break;
				}
				
//				// Constant to global
//				case ExprType.GLOBALPUSH: {
//					globals.put((String) d.value, (Integer) d.aux);
//					break;
//				}
				
				// Pops to global
				case ExprType.GLOBALSTORE: {
					// Checks whether the invoke condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					Field field = (Field) d.value;
					Number value = frame.pop();
					if (field.getCategory().two()) value = frame.pop();
					globals.put(field.getName(), value);
					break;
				}
				
//				case ExprType.HEAPLOAD: {
//					frame.stack.push(heap.get(frame.stack.pop().intValue()));
//					break;
//				}
				
				case ExprType.HEAPOVERFLOW: {
					// Always has enough heap
					thisrule = false;
					break;
				}
				
				case ExprType.HEAPRESTORE: {
					info("Heap used: %d blocks%n", heap.size());
					heap = heapsave;
					globals = globalssave;
					break;
				}
				
				case ExprType.HEAPRESET: {
					heap.clear();
					heap.add(0);
					break;
				}
				
				case ExprType.HEAPSAVE: {
					heapsave = new Heap((int) (1.4*heap.size()));
					heapsave.addAll(heap);
					globalssave = new HashMap<String, Number>(globals);
					break;
				}
				
				case ExprType.IF: {
					Number s0 = frame.pop();
					int i = s0.intValue();
					If expr = (If) d.value;
					switch (expr.getType()) {
						case If.EQ: if (i != 0) thisrule = false; break;
						case If.NE: if (i == 0) thisrule = false; break;
						case If.LT: if (i >= 0) thisrule = false; break;
						case If.GE: if (i < 0) thisrule = false; break;
						case If.GT: if (i <= 0) thisrule = false; break;
						case If.LE: if (i > 0) thisrule = false; break;
						case If.ID:
						case If.IS: 
							if (i != expr.getValue()) thisrule = false; break;
						case If.LG: 
							if (i >= expr.getLowValue() && i <= expr.getHighValue()) 
								thisrule = false; 
							break;
						case If.NOT:
							if (expr.getNotSet().contains(i))
								thisrule = false;
							break;
					}
					if (!thisrule) {
						frame.stack.push(s0);
						frame.label = null;
					}
					break;
				}
				
				case ExprType.IFCMP: {
					Number s0 = frame.pop();
					Number s1 = frame.pop();
					int i0 = s0.intValue();
					int i1 = s1.intValue();
					switch ((Integer) d.value) {
						case Comp.EQ: if (i1 != i0) thisrule = false; break;
						case Comp.NE: if (i1 == i0) thisrule = false; break;
						case Comp.LT: if (i1 >= i0) thisrule = false; break;
						case Comp.GE: if (i1 < i0) thisrule = false; break;
						case Comp.GT: if (i1 <= i0) thisrule = false; break;
						case Comp.LE: if (i1 > i0) thisrule = false; break;
					}
					if (!thisrule) {
						frame.stack.push(s1);
						frame.stack.push(s0);
						frame.label = null;
					}
					break;
				}
				
				case ExprType.INC: {
					Inc inc = (Inc) d.value;
					frame.lv[inc.index] = ((Number) frame.lv[inc.index]).intValue() + inc.value;
					break;
				}
				
				case ExprType.INVOKE: {
					// Checks NPE
					Invoke invoke = (Invoke) d.value;
					int nargs = invoke.nargs;
					if (!invoke.isStatic) {
						if (npe(frame.get(frame.stack.size() - nargs).intValue(), 
								rule.left.w[0], listener, raw, frames)) {
							break;
						}
					}
					
					// Checks whether the invoke condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					// Collects the arguments
					Number[] args = new Number[nargs];
					for (int i = nargs - 1; i >= 0; i--) {
						args[i] = frame.pop();
					}
					
					// Creates new frame and pushes the current frame
					Frame newframe = new Frame(w[0]);
					int j = 0;
					for (int i = 0; i < nargs; i++, j++) {
						newframe.lv[j] = args[i];
					}
					frame.label = w[1];
					frames.push(frame);
					frame = newframe;
					
					// The followings only for wrapper module
					if (!invoke.init)
						break;
					
					// Creates raw argument
					raw = new RawArgument(frame.lv.length, heap.size() - 1);
					System.arraycopy(frame.lv, 0, raw.lv, 0, frame.lv.length);
					System.arraycopy(heap.toArray(), 1, raw.heap, 0, heap.size() - 1);

					
					/*
					 * The rest is for display only:
					 * Subtasks with the arguments when the selected method is called
					 */
					if (!displayArgs)
						break;
					
					String desc = LabelUtils.extractMethodDescriptorFromLabel(w[0]);
					List<String> types = LabelUtils.getParamTypes(desc);
					List<String> display = new LinkedList<String>();
					
					j = (invoke.isStatic) ? 0 : 1;
					for (int i = 0; i < types.size(); i++, j++) {
						if (types.get(i).charAt(0) != '[') {
							display.add(String.valueOf(frame.lv[j]));
						} else {
							int ptr = ((Number) frame.lv[j]).intValue();
							int length = arraylength(ptr).intValue();
							ArrayList<Number> array = new ArrayList<Number>();
							for (int k = 0; k < length; k++) {
								array.add(heap.get(indexOfArrayElement(ptr, k)));
							}
							display.add(array.toString());
						}
					}
					
					String msg = "(" + toCommaString(display) + ")";
					debug("\t\t%s%n", msg);
					monitor.subTask(msg);
					break;
				}
				
				case ExprType.IOOB: {
					Npe npe = (Npe) d.value;
					int ptr = frame.get(frame.stack.size() - npe.depth - 1).intValue();
					int index = frame.get(frame.stack.size() - npe.depth).intValue();
					debug("\t\tptr: %d, index: %d%n", ptr, index);
					if (arraylength(ptr).intValue() > index) {
						thisrule = false;
						break;
					}
					debug("\tArrayIndexOutOfBoundException%n");
					break;
				}
				
				case ExprType.JUMP: {
					// Checks whether the invoke condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					Jump type = (Jump) d.value;
					if (type.equals(Jump.ONE))
						break;
					
					// JumpType.THROW
					Number s0 = frame.stack.pop();
					frame.stack.clear();
					frame.stack.push(s0);
					globals.put(Remopla.e, 0);
					break;
				}
				
				case ExprType.LOAD: {
					Local local = (Local) d.value;
					frame.stack.push(frame.lv[local.index]);
					if (local.getCategory().two())
						frame.stack.push(0);
					break;
				}
				
				case ExprType.MONITORENTER: {
					Monitorenter expr = (Monitorenter) d.value;
					if (expr.type == Monitorenter.Type.POP)
						frame.pop();
					break;
				}
				
				case ExprType.MONITOREXIT: {
					frame.pop();
					break;
				}
				
				case ExprType.NEW: {
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					New n = (New) d.value;
					int index = heap.size();
					heap.add(n.id);
					for (int i = 0; i < n.size; i++)
						heap.add(0);
					frame.stack.push(index);
					break;
				}
				
				case ExprType.NEWARRAY: {
					// Pops the dimensions
					Newarray newarray = (Newarray) d.value;
					int dim = newarray.getDimension();
					int[] s = new int[dim];
					for (int i = 0; i < dim; i++) {
						s[i] = frame.pop().intValue();
					}
					
					// Computes heap requirement
					int require = 0;
					int acc = 1;
					for (int i = dim - 1; i >= 0; i--) {
						require += acc * (s[i] + 1);
						acc *= s[i];
					}
					debug("\t\trequire: %d%n", require);
					
					Queue<Integer> indices = new LinkedList<Integer>();
					for (int i = 1; i <= dim; i++) {
						
						// Computes number of blocks
						int blocknum = 1;
						for (int j = i; j < dim; j++) {
							blocknum *= s[j];
						}
						
						// Fills blocks
						int blocksize = s[i - 1];
						debug("\t\tblocknum: %d, blocksize: %d%n", blocknum, blocksize);
						for (int j = 0; j < blocknum; j++) {
							
							// Remember the index
							indices.offer(heap.size());
							
							// Fills the array type
							heap.add(newarray.types[dim-i]);
							
							// Fills the array length
							heap.add(blocksize);
							
							// Fills the array elements
							for (int k = 0; k < blocksize; k++) {
								if (i == 1) {
									if (newarray.init.isString())
										heap.add(encode(newarray.init.stringValue()));
									else
										heap.add((Number) newarray.init.getValue());
								} else {
									heap.add(indices.remove());
								}
							}
						}
					}
					frame.stack.push(indices.remove());
					break;
				}
				
				case ExprType.NPE: {
					Npe npe = (Npe) d.value;
					Object o = frame.get(frame.stack.size() - npe.depth - 1);
					if (!(o instanceof Number)) break;
					if (((Number) o).intValue() != 0) {
						thisrule = false;
						break;
					}
					break;
				}
				
				case ExprType.POPPUSH: {
					Poppush poppush = (Poppush) d.value;
					for (int i = 0; i < poppush.pop; i++)
						frame.pop();
					for (int i = 0; i < poppush.push; i++)
						frame.stack.push(0);
					break;
				}
				
				case ExprType.PRINT: {
					Print print = (Print) d.value;
					switch (print.type) {
					case Print.NOTHING: break;
					case Print.INTEGER: System.out.print(frame.pop().longValue()); break;
					case Print.LONG: frame.pop(); System.out.print(frame.pop().longValue()); break;
					case Print.FLOAT: System.out.print(frame.pop().doubleValue()); break;
					case Print.DOUBLE: frame.pop(); System.out.print(frame.pop().doubleValue()); break;
					case Print.CHARACTER: System.out.print((char) frame.pop().intValue()); break;
					case Print.STRING: System.out.print(strings.get(frame.pop().intValue())); break;
					}
					if (print.newline)
						System.out.println();
					
					// Pops the PrintStream instance
					frame.pop();
					break;
				}
				
				case ExprType.PUSH: {
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					Value value = (Value) d.value;
					if (value.all()) frame.stack.push(0);
					else if (value.isString()) 
						frame.push(encode(value.stringValue()));
					else if (value.deterministic())
						frame.push((Number) value.getValue());
					else if (value.isInteger()) {
						double p = value.to.intValue() - value.intValue() + 1;
						frame.push(((int) (p * Math.random())) + value.intValue());
					} else {
						if (value.floatValue() != 0f || value.floatValue() != 1f)
							throw new RemoplaError("Unsupported operation");
						frame.push(Math.random());
					}
					
					if (value.getCategory().two())
						frame.stack.push(0);
					break;
				}
				
				case ExprType.RETURN: {
					Return ret = (Return) d.value;
					if (ret.type == Return.SOMETHING) {
						retvar = frame.stack.pop();
						if (ret.getCategory().two())
							retvar = frame.stack.pop();
					}
					frame = frames.pop();
					break;
				}
				
				case ExprType.STORE: {
					Local local = (Local) d.value;
					if (local.getCategory().one()) {
						frame.lv[local.index] = frame.pop();
					}
					else {
						frame.lv[local.index + 1] = frame.pop();
						frame.lv[local.index] = frame.pop();
					}
					break;
				}
				
				case ExprType.SWAP: {
					Number s0 = frame.stack.pop();
					Number s1 = frame.stack.pop();
					frame.stack.push(s0);
					frame.stack.push(s1);
					break;
				}
				
				case ExprType.UNARYOP: {
					Unaryop unaryop = (Unaryop) d.value;
					Number v = frame.pop();
					if (unaryop.pop.two())
						v = frame.pop();
					switch (unaryop.type) {
					case Unaryop.LNEG:	
					case Unaryop.INEG:
						v = -v.longValue();
						break;
					case Unaryop.DNEG:
					case Unaryop.FNEG:
						v = -v.doubleValue();
						break;
					case Unaryop.D2I:
					case Unaryop.D2L:
					case Unaryop.F2I:
					case Unaryop.F2L:
					case Unaryop.L2I:
					case Unaryop.I2L:
						v = v.intValue();
						break;
					case Unaryop.D2F:
					case Unaryop.F2D:
					case Unaryop.I2D:
					case Unaryop.I2F:
					case Unaryop.L2D:
					case Unaryop.L2F:
						v = v.doubleValue();
						break;
					case Unaryop.CONTAINS:
						v = (unaryop.set.contains(v.intValue())) ? 1 : 0;
						break;
					}
					frame.stack.push(v);
					if (unaryop.push.two())
						frame.stack.push(0);
					break;
				}
				}
				
				if (thisrule) break;
			}
			
			// If no matching rule found
			if (!thisrule) {
				debug("\tno matching rule found%n");
				do {
					frame = frames.pop();
				} while (!frames.isEmpty());
			}
			debug("%n");
		}
		
		listener.done();
	}
	
	/**
	 * Returns <code>true</code> if an ArrayIndexOutOfBoundException occurs.
	 * 
	 * @param length the length of the array
	 * @param index the index to the array
	 * @param label the current label
	 * @param listener the listener
	 * @param raw the raw argument
	 * @param frames the stack of frames
	 * @return <code>true</code> if an ArrayIndexOutOfBoundException occurs.
	 */
	private boolean ioob(int length, int index, String label, 
			RemoplaListener listener, RawArgument raw, Stack<Frame> frames) {
		
		if (length > index) return false;
		
		debug("\tArrayIndexOutOfBoundException%n");
		System.err.printf("ArrayIndexOutOfBoundException - length:%d, index:%d%n", 
				length, index);
		String ioob = LabelUtils.formatIoobName(label);
		if (listener != null) listener.reach(ioob);
		error(ioob, raw, frames);
		
		return true;
	}
	
	private boolean npe(int ptr, String label, RemoplaListener listener, 
			RawArgument raw, Stack<Frame> frames) {
		
		if (ptr != 0) return false;
		
		debug("\tNullPointerException%n");
		System.err.printf("NullPointerException at %s", label);
		String npe = LabelUtils.formatNpeName(label);
		if (listener != null) listener.reach(npe);
		error(npe, raw, frames);
		
		return true;
	}
	
	private void error(String label, RawArgument raw, Stack<Frame> frames) {
		
		// Saves the raw argument of the corresponding label to raws
		List<RawArgument> list = raws.get(label);
		if (list == null) { 
			list = new ArrayList<RawArgument>();
			raws.put(label, list);
		}
		list.add(raw);
		
		// Pops all call frames; the current frame updates to the last frame
		do {
			frame = frames.pop();
		} while (!frames.isEmpty());
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
	 * Logs the information message.
	 * 
	 * @param msg the message.
	 * @param args the message arguments.
	 */
	static void info(String msg, Object... args) {
		log(1, msg, args);
	}
	
	/**
	 * Logs the debug message.
	 * 
	 * @param msg the message.
	 * @param args the message arguments.
	 */
	static void debug(String msg, Object... args) {
		log(2, msg, args);
	}
	
	private static boolean all() {
		return verbosity >= 3;
	}
	
	private static void log(int threshold, String msg, Object... args) {
		if (verbosity >= threshold)
			logger.fine(String.format(msg, args));
	}
	
	/**
	 * Returns <code>true</code> if A.aux is of type InvokeCondition, and
	 * the given condition fulfills. The condition contains a variable
	 * and a comparison type. The condition is fulfilled iff the current
	 * value of the variable satisfies the comparison.
	 * 
	 * @param A
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private boolean fulfillsCondition(ExprSemiring A, int s) {
		
		if (A.aux == null) return true;
		
		Condition cond = (Condition) A.aux;
		int type = cond.getType();
		if (type == Condition.CONTAINS || type == Condition.NOTCONTAINS) {
			
			Set<Integer> set = cond.getSetValue();
			int ptr = ((Number) frame.stack.elementAt(frame.stack.size() - s)).intValue();
			int id = heap.get(ptr).intValue();
			if (type == Condition.CONTAINS)
				return set.contains(id);
			else
				return !set.contains(id);
		}
		
		int g = ((Number) globals.get(cond.getStringValue())).intValue();
		switch (type) {
		case Condition.ZERO:
			if (g == 0) return true;
			break;
		case Condition.ONE:
			if (g == 1) return true;
			break;
		}
		
		return false;
	}
	
	private boolean fulfillsCondition(ExprSemiring A) {
		
		int id = 0;
		switch (A.type) {
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
	 * Call frame.
	 */
	private class Frame {
		
		String label;
		Number[] lv = new Number[remopla.lvmax];
		Stack<Number> stack = new Stack<Number>();
		
		public Frame(String label) {	
			this.label = label;
		}
		
		public void push(Number number) {
			stack.push(number);
		}
		
		public Number pop() {
			return stack.pop();
		}
		
		public Number get(int index) {
			return stack.get(index);
		}
		
		public String toString() {
			
			return String.format("label: %s, %nlv:%s, %nstack:%s", 
					label, Arrays.toString(lv), stack);
		}
	}
	
	/**
	 * The heap.
	 */
	private class Heap {
		
		ArrayList<Number> heap = new ArrayList<Number>();
		
		public Heap() {
			heap = new ArrayList<Number>();
		}
		
		public Heap(int size) {
			heap = new ArrayList<Number>(size);
		}
		
		public void add(Number element) {
			heap.add(element);
		}
		
		/**
		 * Sets the heap at <code>index</code> to <code>element</code>.
		 * 
		 * @param index the index.
		 * @param element the element to set.
		 */
		public void set(int index, Number element) {
			heap.set(index, element);
		}
		
		/**
		 * Adds all elements from <code>another</code> heap.
		 * 
		 * @param another another heap.
		 */
		public void addAll(Heap another) {
			heap.addAll(another.heap);
		}
		
		/**
		 * Returns the element at <code>index</code>.
		 * 
		 * @param index the index.
		 * @return the element at index.
		 */
		public Number get(int index) {
			return heap.get(index);
		}
		
		public void clear() {
			heap.clear();
		}
		
		public int size() {
			return heap.size();
		}
		
		/**
		 * Returns an array representing the current heap values.
		 * 
		 * @return an array representing the current heap values.
		 */
		public Number[] toArray() {
			return heap.toArray(new Number[heap.size()]);
		}
		
		public String toString() {
			return heap.toString();
		}
	}
	
	public static String toCommaString(List<String> list) {
		
		if (list == null) return null;
		if (list.size() == 0) return "";
		
		StringBuilder out = new StringBuilder();
		Iterator<String> itr = list.iterator();
		out.append(itr.next());
		while (itr.hasNext()) {
			out.append(", ");
			out.append(itr.next());
		}
		
		return out.toString();
	}
}
