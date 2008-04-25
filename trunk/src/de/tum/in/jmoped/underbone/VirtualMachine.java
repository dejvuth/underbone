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

import de.tum.in.jmoped.underbone.ExprSemiring.ArithType;
import de.tum.in.jmoped.underbone.ExprSemiring.Condition;
import de.tum.in.jmoped.underbone.ExprSemiring.DupType;
import de.tum.in.jmoped.underbone.ExprSemiring.Condition.ConditionType;
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
		for (String label : labels)
			log("%s%n", label);
		
		RemoplaListener listener = remopla.getRemoplaListener();
		listener.setProgressMonitor(monitor);
		listener.beginTask(remopla.getLastCalledName(), labels);
		
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
		RawArgument raw = null;
		raws = new HashMap<String, List<RawArgument>>();
		
		// Stack of frames
		Stack<Frame> frames = new Stack<Frame>();
		frame = new Frame(remopla.init);
		
		// Return variable
		Number retvar = null;
		
		while (frame.label != null) {
			
			if (monitor.isCanceled()) break;
			
			log("ptr: %d, heap: %s%n", heap.size(), heap);
			log("globals: %s%n", globals);
			log("frame: %s%n%n", frame);
			if (listener != null) listener.reach(frame.label);
			
			Config config = new Config(Remopla.p, frame.label);
			Set<Rule> rules = rmap.get(config);
			if (rules == null) break;
			
			// Loops for each rule beginning with <p, label>
			boolean thisrule = false;
			for (Rule rule : rules) {
				
				log("\t%s%n", rule);
				
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
				
				case ARITH: {
					Number s0 = frame.pop();
					Number s1 = frame.pop();
					ArithType type = (ArithType) d.value;
					switch (type) {
						case ADD: s0 = s1.longValue() + s0.longValue(); break;
						case AND: s0 = s1.longValue() & s0.longValue(); break;
						case CMP:
							if (s1.longValue() > s0.longValue()) s0 = 1;
							else if (s1.longValue() == s0.longValue()) s0 = 0;
							else s0 = -1;
							break;
						case DIV: s0 = s1.longValue() / s0.longValue(); break;
						case MUL: s0 = s1.longValue() * s0.longValue(); break;
						case OR: s0 = s1.longValue() | s0.longValue(); break;
						case REM: s0 = s1.longValue() % s0.longValue(); break;
						case SHL: s0 = s1.longValue() << (s0.intValue() & 31); break;
						case SHR: s0 = s1.longValue() >> (s0.intValue() & 31); break;
						case SUB: s0 = s1.longValue() - s0.longValue(); break;
						case USHR: s0 = s1.longValue() >>> (s0.intValue() & 31); break;
						case XOR: s0 = s1.longValue() ^ s0.longValue(); break;
						case FADD: s0 = s1.doubleValue() + s0.doubleValue(); break;
						case FCMPG: 
						case FCMPL: {
							if (s1.doubleValue() > s0.doubleValue()) s0 = 1f;
							else if (s1.doubleValue() == s0.doubleValue()) s0 = 0f;
							else if (s1.doubleValue() < s0.doubleValue()) s0 = -1f;
							// At least one must be NaN
							else if (type == ArithType.FCMPG) s0 = 1f;
							else s0 = -1f;
							break;
						}
						case FDIV: s0 = s1.doubleValue() / s0.doubleValue(); break;
						case FMUL: s0 = s1.doubleValue() * s0.doubleValue(); break;
						case FREM: s0 = s1.doubleValue() % s0.doubleValue(); break;
						case FSUB: s0 = s1.doubleValue() - s0.doubleValue(); break;
					}
					frame.stack.push(s0);
					break;
				}
				
//				case ARRAYCOPY: {
//					int newindex = heap.size();
//					Number oldindex = frame.stack.peek();
//					Number length = heap.get(oldindex.intValue());
//					heap.add(length);
//					for (int i = 0; i < length; i++)
//						heap.add(heap.get(oldindex + i + 1));
//					frame.stack.push(newindex);
//					break;
//				}
				
				case ARRAYLENGTH: {
					// Checks NPE
					int s0 = frame.pop().intValue();
					if (npe(s0, rule.left.w[0], listener, raw, frames)) break;
					
					// Pushes array length
					frame.stack.push(arraylength(s0));
					break;
				}
				
				case ARRAYLOAD: {
					// Checks NPE
					int s0 = frame.pop().intValue();	// index
					int s1 = frame.pop().intValue();	// arrayref
					if (npe(s1, rule.left.w[0], listener, raw, frames)) 
						break;
					
					// Checks IOOB
					int length = arraylength(s1).intValue();
					if (ioob(length, s0, rule.left.w[0], listener, raw, frames)) 
						break;
					
					// Pushes
					frame.stack.push(heap.get(indexOfArrayElement(s1, s0)));
					break;
				}
				
//				case ARRAYPUSH: {
//					int ptr = frame.stack.peek();
//					int length = heap.get(ptr);
//					int value = (Integer) d.value;
//					for (int i = 0; i < length; i++) {
//						heap.set(ptr + i + 1, value);
//					}
//					break;
//				}
				
				case ARRAYSTORE: {
					// Checks NPE
					Number s0 = frame.pop();	// value
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
				
				case CONSTLOAD: {
					// Checks whether the invoke condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					frame.push(constants.get((String) d.value));
					break;
				}
				
				case CONSTSTORE: {
					// Checks whether the invoke condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					constants.put((String) d.value, frame.pop());
					break;
				}
				
				case DUP: {
					DupType type = (DupType) d.value;
					switch (type) {
					case DUP: {
						Number s0 = frame.pop();
						frame.stack.push(s0);
						frame.stack.push(s0);
						break;
					}
					case DUP_X1: {
						Number s0 = frame.pop();
						Number s1 = frame.pop();
						frame.stack.push(s0);
						frame.stack.push(s1);
						frame.stack.push(s0);
						break;
					}
					case DUP2: {
						Number s0 = frame.pop();
						Number s1 = frame.pop();
						frame.stack.push(s1);
						frame.stack.push(s0);
						frame.stack.push(s1);
						frame.stack.push(s0);
						break;
					}
					default:
						throw new IllegalArgumentException(
								String.format("Instruction %s not supported", type));
					}
					break;
				}
				
				case ERROR: {
					error(rule.left.w[0], raw, frames);
					break;
				}
				
				case FIELDLOAD: {
					// Checks condition
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					// Checkes NPE
					int s0 = frame.pop().intValue();
					if (npe(s0, rule.left.w[0], listener, raw, frames)) break;
					
					// Pushes
					frame.stack.push(heap.get(s0 + (Integer) d.value));
					break;
				}
				
				case FIELDSTORE: {
					// Checks condition
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					// Checkes NPE
					Number s0 = frame.pop();
					int s1 = frame.pop().intValue();
					if (npe(s1, rule.left.w[0], listener, raw, frames)) break;
					
					// Stores s0 to heap
					heap.set(s1 + (Integer) d.value, s0);
					break;
				}
				
				case GETRETURN: {
					frame.stack.push(retvar);
					break;
				}
				
				// Pushes from global
				case GLOBALLOAD: {
					// Checks whether the invoke condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					frame.stack.push(globals.get((String) d.value));
					break;
				}
				
				// Constant to global
				case GLOBALPUSH: {
					globals.put((String) d.value, (Integer) d.aux);
					break;
				}
				
				// Pops to global
				case GLOBALSTORE: {
					// Checks whether the invoke condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					globals.put((String) d.value, frame.pop());
					break;
				}
				
				case HEAPLOAD: {
					frame.stack.push(heap.get(frame.stack.pop().intValue()));
					break;
				}
				
				case HEAPOVERFLOW: {
					// Always has enough heap
					thisrule = false;
					break;
				}
				
				case HEAPRESTORE: {
					heap = heapsave;
					break;
				}
				
				case HEAPRESET: {
					heap.clear();
					heap.add(0);
					break;
				}
				
				case HEAPSAVE: {
					heapsave = new Heap((int) (1.4*heap.size()));
					heapsave.addAll(heap);
					break;
				}
				
				case IF: {
					Number s0 = frame.pop();
					int i = s0.intValue();
					ExprSemiring.If expr = (ExprSemiring.If) d.value;
					switch (expr.type) {
						case EQ: if (i != 0) thisrule = false; break;
						case NE: if (i == 0) thisrule = false; break;
						case LT: if (i >= 0) thisrule = false; break;
						case GE: if (i < 0) thisrule = false; break;
						case GT: if (i <= 0) thisrule = false; break;
						case LE: if (i > 0) thisrule = false; break;
						case IS: if (i != expr.getValue()) thisrule = false; break;
						case LG: 
							if (i >= expr.getLowValue() && i <= expr.getHighValue()) 
								thisrule = false; 
							break;
						case NOT:
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
				
				case IFCMP: {
					Number s0 = frame.pop();
					Number s1 = frame.pop();
					int i0 = s0.intValue();
					int i1 = s1.intValue();
					switch ((ExprSemiring.CompType) d.value) {
						case EQ: if (i1 != i0) thisrule = false; break;
						case NE: if (i1 == i0) thisrule = false; break;
						case LT: if (i1 >= i0) thisrule = false; break;
						case GE: if (i1 < i0) thisrule = false; break;
						case GT: if (i1 <= i0) thisrule = false; break;
						case LE: if (i1 > i0) thisrule = false; break;
					}
					if (!thisrule) {
						frame.stack.push(s1);
						frame.stack.push(s0);
						frame.label = null;
					}
					break;
				}
				
				case INC: {
					ExprSemiring.Inc inc = (ExprSemiring.Inc) d.value;
					frame.lv[inc.index] = ((Number) frame.lv[inc.index]).intValue() + inc.value;
					break;
				}
				
				case INVOKE: {
					// Checks NPE
					ExprSemiring.Invoke invoke = (ExprSemiring.Invoke) d.value;
					boolean[] params = invoke.params;
					int nargs = params.length;
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
						if (params[i]) j++;
					}
					frame.label = w[1];
					frames.push(frame);
					frame = newframe;
					
					// The followings only for wrapper module
					if (!invoke.init)
						break;
					
					// Creates raw argument
					raw = new RawArgument(frame.lv.length, heap.size() - 1);
					for (int i = 0; i < frame.lv.length; i++)
						raw.lv[i] = frame.lv[i];
					for (int i = 0; i < heap.size() - 1; i++)
						raw.heap[i] = heap.get(i + 1);
					
					/*
					 * The rest is for display only:
					 * Subtasks with the arguments when the selected method is called
					 */
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
						if (params[i]) j++;
					}
					
//					try {
//						for (int i = nargs - 1; i >= 0; i--) {
//							if (types.get(i).charAt(0) != '[') {
//								display.push(String.valueOf(frame.lv[i]));
//							} else {
//								int ptr = frame.lv[i].intValue();
//								int length = heap.get(ptr).intValue();
//								ArrayList<Number> array = new ArrayList<Number>();
//								for (j = 0; j < length; j++) {
//									array.add(heap.get(ptr + j + 1));
//								}
//								display.push(array.toString());
//							}
//						}
//					} catch (IndexOutOfBoundsException e) {
//					}
					String msg = "(" + toCommaString(display) + ")";
					log("\t\t%s%n", msg);
					monitor.subTask(msg);
					break;
				}
				
				case IOOB: {
					ExprSemiring.Npe npe = (ExprSemiring.Npe) d.value;
					int ptr = frame.get(frame.stack.size() - npe.depth - 1).intValue();
					int index = frame.get(frame.stack.size() - npe.depth).intValue();
					log("\t\tptr: %d, index: %d%n", ptr, index);
					if (arraylength(ptr).intValue() > index) {
						thisrule = false;
						break;
					}
					break;
				}
				
				case LOAD: {
					frame.stack.push(frame.lv[(Integer) d.value]);
					break;
				}
				
				case MONITORENTER: {
					ExprSemiring.Monitorenter expr = (ExprSemiring.Monitorenter) d.value;
					if (expr.type == ExprSemiring.Monitorenter.Type.POP)
						frame.pop();
					break;
				}
				
				case MONITOREXIT: {
					frame.pop();
					break;
				}
				
				case NEW: {
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					ExprSemiring.New n = (ExprSemiring.New) d.value;
					int index = heap.size();
					heap.add(n.id);
					for (int i = 0; i < n.size; i++)
						heap.add(0);
					frame.stack.push(index);
					break;
				}
				
				case NEWARRAY: {
					// Pops the dimensions
					ExprSemiring.Newarray newarray = (ExprSemiring.Newarray) d.value;
					int[] s = new int[newarray.dim];
					for (int i = 0; i < newarray.dim; i++) {
						s[i] = frame.pop().intValue();
					}
					
					// Computes heap requirement
					int require = 0;
					int acc = 1;
					for (int i = newarray.dim - 1; i >= 0; i--) {
						require += acc * (s[i] + 1);
						acc *= s[i];
					}
					log("\t\trequire: %d%n", require);
					
					Queue<Integer> indices = new LinkedList<Integer>();
					for (int i = 1; i <= newarray.dim; i++) {
						
						// Computes number of blocks
						int blocknum = 1;
						for (int j = i; j < newarray.dim; j++) {
							blocknum *= s[j];
						}
						
						// Fills blocks
						int blocksize = s[i - 1];
						log("\t\tblocknum: %d, blocksize: %d%n", blocknum, blocksize);
						for (int j = 0; j < blocknum; j++) {
							
							// Remember the index
							indices.offer(heap.size());
							
							// Fills the array type
							heap.add(newarray.types[newarray.dim-i]);
							
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
					
//					int index = heap.size();
//					int length = frame.popNumber().intValue();
//					heap.add(length);
//					for (int i = 0; i < length; i++)
//						heap.add((Integer) d.value);
//					frame.stack.push(index);
					break;
				}
				
				case NPE: {
					ExprSemiring.Npe npe = (ExprSemiring.Npe) d.value;
					Object o = frame.get(frame.stack.size() - npe.depth - 1);
					if (!(o instanceof Number)) break;
					if (((Number) o).intValue() != 0) {
						thisrule = false;
						break;
					}
					break;
				}
				
				case ONE: {
					// Checks whether the invoke condition is fulfilled
					if (!fulfillsCondition(d)) {
						thisrule = false;
						break;
					}
					
					break;
				}
				
				case POPPUSH: {
					int pop = (Integer) d.value;
					for (int i = 0; i < pop; i++)
						frame.pop();
					if ((Boolean) d.aux)
						frame.stack.push(0);
					break;
				}
				
				case PRINT: {
					Number s0 = frame.pop();
					ExprSemiring.Print print = (ExprSemiring.Print) d.value;
					switch (print.type) {
					case INTEGER: System.out.print(s0.longValue()); break;
					case FLOAT: System.out.print(s0.doubleValue()); break;
					case CHARACTER: System.out.print((char) s0.intValue()); break;
					case STRING: System.out.print(strings.get(s0.intValue())); break;
					}
					if (print.newline)
						System.out.println();
					break;
				}
				
				case PUSH: {
					ExprSemiring.Value value = (ExprSemiring.Value) d.value;
					if (value.all()) frame.stack.push(0);
					else if (value.isString()) frame.push(encode(value.stringValue()));
					else frame.push((Number) value.getValue());
					break;
				}
				
				case RETURN: {
					if ((Integer) d.value > 0)
						retvar = frame.pop();
					frame = frames.pop();
					break;
				}
				
				case STORE: {
					frame.lv[(Integer) d.value] = frame.pop();
					break;
				}
				
				case UNARYOP: {
					ExprSemiring.UnaryOpType type = (ExprSemiring.UnaryOpType) d.value;
					Number s0 = frame.pop();
					switch (type) {
					case NEG:
						s0 = -s0.longValue();
						break;
					case FNEG:
						s0 = -s0.doubleValue();
						break;
					case F2I:
						s0 = s0.intValue();
						break;
					case I2F:
						s0 = s0.doubleValue();
						break;
					}
					frame.stack.push(s0);
					break;
				}
				}
				
				if (thisrule) break;
			}
			
			// If no matching rule found
			if (!thisrule) {
				log("\tno matching rule found%n");
				do {
					frame = frames.pop();
				} while (!frames.isEmpty());
			}
			log("%n");
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
		
		log("\tArrayIndexOutOfBoundException%n");
		String ioob = LabelUtils.formatIoobName(label);
		if (listener != null) listener.reach(ioob);
		error(ioob, raw, frames);
		
		return true;
	}
	
	private boolean npe(int ptr, String label, RemoplaListener listener, 
			RawArgument raw, Stack<Frame> frames) {
		
		if (ptr != 0) return false;
		
		log("\tNullPointerException%n");
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
	
	public static void log(String msg, Object... args) {
		if (verbosity >= 2)
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
		if (cond.type == ConditionType.CONTAINS) {
			
			Set<Integer> set = (Set<Integer>) cond.value;
			int ptr = ((Number) frame.stack.elementAt(frame.stack.size() - s)).intValue();
			int id = heap.get(ptr).intValue();
			return set.contains(id);
		}
		
		int g = ((Number) globals.get((String) cond.value)).intValue();
		switch (cond.type) {
		case ZERO:
			if (g == 0) return true;
			break;
		case ONE:
			if (g == 1) return true;
			break;
		}
		
		return false;
	}
	
	private boolean fulfillsCondition(ExprSemiring A) {
		
		int id = 0;
		switch (A.type) {
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
	 * Call frame.
	 * 
	 * @author suwimont
	 *
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
		
//		public Number popAsNumber() {
//			return (Number) stack.pop();
//		}
		
		public Number get(int index) {
			return stack.get(index);
		}
		
//		public Number getAsNumber(int index) {
//			return (Number) stack.get(index);
//		}
		
		public String toString() {
			
			return String.format("label: %s, lv:%s, stack:%s", 
					label, Arrays.toString(lv), stack);
		}
	}
	
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
