package de.tum.in.jmoped.underbone;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDVarSet;
import net.sf.javabdd.BDD.BDDIterator;

import de.tum.in.jmoped.underbone.ExplicitRelation.V;
import de.tum.in.jmoped.underbone.ExplicitRelation.G;
import de.tum.in.jmoped.underbone.ExplicitRelation.L;
import de.tum.in.jmoped.underbone.ExplicitRelation.S;
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
import de.tum.in.jmoped.underbone.expr.New;
import de.tum.in.jmoped.underbone.expr.Newarray;
import de.tum.in.jmoped.underbone.expr.Npe;
import de.tum.in.jmoped.underbone.expr.Poppush;
import de.tum.in.jmoped.underbone.expr.Print;
import de.tum.in.jmoped.underbone.expr.Return;
import de.tum.in.jmoped.underbone.expr.Unaryop;
import de.tum.in.jmoped.underbone.expr.Value;
import de.tum.in.wpds.CancelMonitor;
import de.tum.in.wpds.Sat;
import de.tum.in.wpds.Semiring;

public class ExplicitSemiring implements Semiring {
	
	HashSet<ExplicitRelation> rels;
	
	public ExplicitSemiring(ExplicitRelation rel) {
		rels = new HashSet<ExplicitRelation>();
		rels.add(rel);
	}
	
	public ExplicitSemiring(HashSet<ExplicitRelation> rels) {
		this.rels = rels;
	}

	public Semiring andWith(Semiring arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring combine(Semiring a) {
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>(id(rels));
		newrels.addAll(id(((ExplicitSemiring) a).rels));
		
//		for (ExplicitRelation rel : newrels) {
//			log("\t\thashCode: %d%n", rel.hashCode());
//		}
//		ExplicitRelation[] r = newrels.toArray(new ExplicitRelation[2]);
//		log("\t\tequals: %b%n", r[0].equals(r[1]));
		
//		log("\t\tcombine%n");
//		log(newrels);
//		try {
//			for (ExplicitRelation rel : newrels) {
//				if (rel.heap(3).intValue() == 1 && rel.heap(4).intValue() == 0
//						&& rel.heap(5).intValue() == 1) {
//					Number[] heap = rel.g2().heap;
//					if (heap[3].intValue() == 1 && heap[4].intValue() == 1
//							&& heap[5].intValue() == 1)
//						return null;
//				}
//			}
//		} catch (Throwable t) {}
		
		return new ExplicitSemiring(newrels);
	}

	public Semiring extendDynamic(Semiring arg0, CancelMonitor arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * (G0,G2,L2) + (G2,L2,L0,G1,L1) -> (G0,L0,G1,L1)
	 */
	public Semiring extendPop(Semiring a, CancelMonitor monitor) {
		log("\t\textendPop%n");
		log();
		
		ExplicitSemiring A = (ExplicitSemiring) a;
		log("\t\twith%n");
		log(A);
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			for (ExplicitRelation arel : A.rels) {
				if (!rel.g2().equals(arel.g2()) || !rel.l2().equals(arel.l2()))
					continue;
				
				if (arel.type == ExplicitRelation.G2L2L0)
					newrels.add(new ExplicitRelation(ExplicitRelation.G0L0,
							new V[] { rel.g().id(), arel.l().id(), arel.s().id() }));
				else	// G2L2L0G1L1
					newrels.add(new ExplicitRelation(ExplicitRelation.G0L0G1L1,
							new V[] { rel.g().id(), arel.l().id(), arel.s().id(), 
									arel.g1().id(), arel.l1().id() }));
			}
		}
		
		return new ExplicitSemiring(newrels);
	}

	public Semiring extendPush(Semiring a, CancelMonitor monitor) {
		ExprSemiring A = (ExprSemiring) a;
		int nargs = ((Invoke) A.value).nargs;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			S s = rel.s();
			L newl = new L();
			for (int i = 0; i < nargs; i++) {
				newl.local[i] = s.stack[s.sptr - nargs + i];
			}
			
			newrels.add(new ExplicitRelation(ExplicitRelation.G0L0G1L1, 
					new V[] { rel.g().id(), newl, new S(), rel.g().id(), newl.id() }));
		}
		
		return new ExplicitSemiring(newrels);
	}

	public void free() {
	}

	public Semiring getEqClass(int arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring getEqRel(int arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring getGlobal() {
		// TODO Auto-generated method stub
		return null;
	}

	public Set<Semiring> getGlobals() {
		// TODO Auto-generated method stub
		return null;
	}
	
	static HashSet<ExplicitRelation> id(HashSet<ExplicitRelation> rels) {
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			newrels.add(rel.id());
		}
		return newrels;
	}

	public Semiring id() {
		return new ExplicitSemiring(id(rels));
	}

	public boolean isZero() {
		return rels.isEmpty();
	}

	public Semiring lift(Semiring arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public Semiring orWith(Semiring a) {
		rels.addAll(((ExplicitSemiring) a).rels);
		return this;
	}

	public Semiring restrict(Semiring arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	public void sliceWith(Semiring arg0, int arg1) {
		// TODO Auto-generated method stub

	}

	public String toRawString() {
		return toString();
	}

	public void updateGlobal(Semiring arg0) {
		// TODO Auto-generated method stub

	}
	
	public boolean equals(Object obj) {
		if (obj == null || !(obj instanceof ExplicitSemiring))
			return false;
		
		ExplicitSemiring s = (ExplicitSemiring) obj;
		return rels.equals(s.rels);
	}
	
	public Semiring extend(Semiring a, CancelMonitor monitor) {
		ExprSemiring A = (ExprSemiring) a;
		
		log();
//		try {
//		for (ExplicitRelation rel : rels) {
//			if (rel.heap(3).intValue() == 1 && rel.heap(4).intValue() == 0
//					&& rel.heap(5).intValue() == 1) {
//				Number[] heap = rel.g1().heap;
//				if (heap[3].intValue() == 1 && heap[4].intValue() == 1
//						&& heap[5].intValue() == 1)
//					return null;
//			}
//		}
//		} catch (Throwable t) {
//		}
		
		switch (A.type) {
		case ExprType.ARITH:
			return arith(A);
		case ExprType.ARRAYLENGTH:
			return arraylength(A);
		case ExprType.ARRAYLOAD:
			return arrayload(A);
		case ExprType.ARRAYSTORE:
			return arraystore(A);
		case ExprType.CONSTLOAD:
			return constload(A);
		case ExprType.CONSTSTORE:
			return conststore(A);
		case ExprType.DUP:
			return dup(A);
		case ExprType.DYNAMIC:
			return dynamic(A);
		case ExprType.ERROR:
			return error(A);
		case ExprType.FIELDLOAD:
			return fieldload(A);
		case ExprType.FIELDSTORE:
			return fieldstore(A);
		case ExprType.GETRETURN:
			return getreturn(A);
		case ExprType.GLOBALLOAD:
			return globalload(A);
		case ExprType.GLOBALPUSH:
			return globalpush(A);
		case ExprType.GLOBALSTORE:
			return globalstore(A);
		case ExprType.HEAPLOAD:
			return heapload(A);
		case ExprType.HEAPOVERFLOW:
			return heapoverflow(A);
		case ExprType.IF:
			return ifExpr(A);
		case ExprType.IFCMP:
			return ifcmp(A);
		case ExprType.INC:
			return inc(A);
		case ExprType.INVOKE:
			return invoke(A);
		case ExprType.IOOB:
			return ioob(A);
		case ExprType.JUMP:
			return jump(A);
		case ExprType.LOAD:
			return load(A);
//		case ExprType.MONITORENTER:
//			return monitorenter(A);
//		case ExprType.MONITOREXIT:
//			return monitorexit(A);
		case ExprType.NEW:
			return newExpr(A);
		case ExprType.NEWARRAY:
			return newarray(A);
//		case ExprType.NOTIFY:
//			return notify(A);
		case ExprType.NPE:
			return npe(A);
		case ExprType.POPPUSH:
			return poppush(A);
		case ExprType.PRINT:
			return print(A);
		case ExprType.PUSH:
			return push(A);
		case ExprType.RETURN:
			return returnExpr(A);
		case ExprType.STORE:
			return store(A);
		case ExprType.SWAP:
			return swap(A);
		case ExprType.UNARYOP:
			return unaryop(A);
//		case ExprType.WAITINVOKE:
//			return waitinvoke(A);
//		case ExprType.WAITRETURN:
//			return waitreturn(A);
		}
		
		return null;
	}
	
	private Semiring arith(ExprSemiring A) {
		Arith arith = (Arith) A.value;
		int cat = arith.getCategory().intValue();
		boolean two = (cat == 2) && arith.getType() != Arith.CMP;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			Number v1 = rel.stack(sp - 2*cat);
			Number v2 = rel.stack(sp - cat);
			
			// Shortcuts nondeterministic range
			if (arith.getType() == Arith.NDT) {
				for (int i = v1.intValue(); i <= v2.intValue(); i++) {
					ExplicitRelation newrel = rel.id();
					newrel.setSptr(sp - 2*cat + ((two) ? 2 : 1));
					newrel.setStack(sp - 2*cat, i);
					if (cat == 2)
						newrel.setStack(sp - 3, 0);
					newrels.add(newrel);
				}
				continue;
			}

			Number r = arith(arith.getType(), v1, v2);
			ExplicitRelation newrel = rel.id();
			newrel.setSptr(sp - 2*cat + ((two) ? 2 : 1));
			newrel.setStack(sp - 2*cat, r);
			if (two)
				newrel.setStack(sp - 3, 0);
			
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring arraylength(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			
			ExplicitRelation newrel = rel.id();
			newrel.setStack(sp - 1, rel.arraylength(rel.stack(sp - 1).intValue()));
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring arrayload(ExprSemiring A) {
		Category cat = (Category) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			int ptr = rel.stack(sp - 2).intValue();
			if (ptr == 0) {
				log("\t\tNullPointerException%n");
				System.err.printf("NullPointerExceptio%n");
				continue;
			}
			
			int index = rel.stack(sp - 1).intValue();
			int length = rel.arraylength(ptr);
			if (index < 0 || index >= length) {
				log("\t\tArray bound violation: length %d, index %d%n", length, index);
				System.err.printf("Array bound violation: length %d, index %d%n", length, index);
				continue;
			}
			
			ExplicitRelation newrel = rel.id();
			newrel.setStack(sp - 2, rel.array(ptr, index));
			if (cat.one())
				newrel.setSptr(sp - 1);
			else
				newrel.setStack(sp - 1, 0);
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring arraystore(ExprSemiring A) {
		int cat = ((Category) A.value).intValue();
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			int ptr = rel.stack(sp - cat - 2).intValue();
			if (ptr == 0) {
				log("\t\tNullPointerException%n");
				System.err.printf("NullPointerExceptio%n");
				continue;
			}
			
			int index = rel.stack(sp - cat - 1).intValue();
			int length = rel.arraylength(ptr);
			if (index < 0 || index >= length) {
				log("\t\tArray bound violation: length %d, index %d%n", length, index);
				System.err.printf("Array bound violation: length %d, index %d%n", length, index);
				continue;
			}
			
			ExplicitRelation newrel = rel.id();
			newrel.newheap();
			newrel.setArray(ptr, index, rel.stack(sp - cat));
			newrel.setSptr(sp - cat - 2);
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring constload(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		Field field = (Field) A.value;
		Number value = ExplicitRelation.getConstant(field.getName());
		
		for (ExplicitRelation rel : newrels) {
			rel.push(field.getCategory().intValue(), value);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring conststore(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		Field field = (Field) A.value;
		int cat = field.getCategory().intValue();
		
		for (ExplicitRelation rel : newrels) {
			int sp = rel.sptr();
			Number value = rel.stack(sp - cat);
			ExplicitRelation.putConstant(field.getName(), value);
			
			rel.setSptr(sp - cat);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring dynamic(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		for (ExplicitRelation rel : newrels) {
			rel.setSptr(rel.sptr() - 1);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring dup(ExprSemiring A) {
		Dup dup = (Dup) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			
			ExplicitRelation newrel = rel.id();
			for (int i = 0; i < dup.down; i++) {
				newrel.setStack(sp + dup.push - i - 1, rel.stack(sp - i - 1));
			}
			for (int i = 0; i < dup.push; i++) {
				newrel.setStack(sp - dup.down + i, newrel.stack(sp + i));
			}
			newrel.setSptr(sp + dup.push);
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring error(ExprSemiring A) {
		return id();
	}
	
	private Semiring fieldload(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		Field field = (Field) A.value;
		
		for (ExplicitRelation rel : newrels) {
			int sp = rel.sptr();
			int ref = rel.stack(sp - 1).intValue();
			if (ref == 0) {
				log("\t\tNullPointerException%n");
				continue;
			}
			
			rel.setStack(sp - 1, rel.heap(ref + field.getId()));
			if (field.getCategory().two()) {
				rel.setStack(sp, 0);
				rel.setSptr(sp + 1);
			}
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring fieldstore(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		Field field = (Field) A.value;
		int cat = field.getCategory().intValue();
		
		for (ExplicitRelation rel : newrels) {
			int sp = rel.sptr();
			int ref = rel.stack(sp - cat - 1).intValue();
			if (ref == 0) {
				log("\t\tNullPointerException%n");
				continue;
			}
			
			rel.newheap();
			rel.setHeap(ref + field.getId(), rel.stack(sp - cat));
			rel.setSptr(sp - cat - 1);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	
	
	private Semiring getreturn(ExprSemiring A) {
		int category = ((Category) A.value).intValue();
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			newrels.add(rel.id().push(category, rel.global(ExplicitRelation.RETVAR)));
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring globalload(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		Field field = (Field) A.value;
		int cat = field.getCategory().intValue();
		
		for (ExplicitRelation rel : newrels) {
			rel.push(cat, rel.global(field.getName()));
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring globalpush(ExprSemiring A) {
		String name = (String) A.value;
		int value = (Integer) A.aux;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			ExplicitRelation newrel = rel.id();
			newrel.setGlobal(name, value);
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring globalstore(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		Field field = (Field) A.value;
		int cat = field.getCategory().intValue();
		
		for (ExplicitRelation rel : newrels) {
			int sp = rel.sptr();
			rel.setGlobal(field.getName(), rel.stack(sp - cat));
			rel.setSptr(sp - cat);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring heapload(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			
			ExplicitRelation newrel = rel.id();
			newrel.setStack(sp - 1, rel.heap(rel.stack(sp - 1).intValue()));
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring heapoverflow(ExprSemiring A) {
		return new ExplicitSemiring(new HashSet<ExplicitRelation>(1));
	}
	
	private Semiring ifExpr(ExprSemiring A) {
		If expr = (If) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			int value = rel.stack(sp - 1).intValue();
			
			if (expr.getType() == If.LG) {
				if (value >= expr.getLowValue() && value <= expr.getHighValue())
					continue;
			}
			
			else if (expr.getType() == If.NOT) {
				Set<Integer> set = expr.getNotSet();
				if (set.contains(value))
					continue;
			}
			
			else {	// Compares with a single value
				if (!satisfy(expr, value))
					continue;
			}
			
			ExplicitRelation newrel = rel.id();
			newrel.setSptr(sp - 1);
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring ifcmp(ExprSemiring A) {
		int type = (Integer) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			int value1 = rel.stack(sp - 2).intValue();
			int value2 = rel.stack(sp - 1).intValue();
			
			if (!satisfy(type, value1, value2))
				continue;
			
			ExplicitRelation newrel = rel.id();
			newrel.setSptr(sp - 2);
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring inc(ExprSemiring A) {
		Inc inc = (Inc) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			ExplicitRelation newrel = rel.id();
			newrel.setLocal(inc.index, rel.local(inc.index).intValue() + inc.value);
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring invoke(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		int nargs = ((Invoke) A.value).nargs;
		
		HashSet<ExplicitRelation> newrels2 = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : newrels) {
			
			// New local
			S s = rel.s();
			L newl = new L();
			for (int i = 0; i < nargs; i++) {
				newl.local[i] = s.stack[s.sptr - nargs + i];
			}
			
			// New stack
			S news = (S) s.id();
			news.sptr = s.sptr - nargs;
			
			if (rel.type == ExplicitRelation.G0L0) {
				newrels2.add(new ExplicitRelation(ExplicitRelation.G2L2L0, 
						new V[] { rel.g().id(), newl, rel.l().id(), news }));
			} else {	// G0L0G1L1
				newrels2.add(new ExplicitRelation(ExplicitRelation.G2L2L0G1L1, 
						new V[] { rel.g().id(), newl, rel.l().id(), news, 
						rel.g1().id(), rel.l1().id() }));
			}
		}
		
		return new ExplicitSemiring(newrels2);
	}
	
	private Semiring ioob(ExprSemiring A) {
		Npe ioob = (Npe) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			int ref = rel.stack(sp - ioob.depth - 1).intValue();
			if (ref == 0) {
				log("\t\tIOOB%n");
				continue;
			}
			
			int index = rel.stack(sp - ioob.depth).intValue();
			int length = rel.arraylength(ref);
			if (index < 0 || index >= length)
				newrels.add(rel.id());
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring jump(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		Jump type = (Jump) A.value;
		
		if (type.equals(Jump.ONE))
			return new ExplicitSemiring(newrels);
		
		// Jump.THROW
		for (ExplicitRelation rel : newrels) {
			rel.setGlobal(Remopla.e, 0);
			rel.setStack(0, rel.stack(rel.sptr() - 1));
			rel.setSptr(1);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring load(ExprSemiring A) {
		Local local = (Local) A.value;
		int cat = local.getCategory().intValue();
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			
			ExplicitRelation newrel = rel.id();
			newrel.setStack(sp, rel.local(local.index));
			if (cat == 2) 
				newrel.setStack(sp + 1, rel.local(local.index + 1));
			newrel.setSptr(sp + cat);
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring newExpr(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		New n = (New) A.value;
		
		for (ExplicitRelation rel : newrels) {
			int sp = rel.sptr();
			int ptr = rel.allocate(n.size + 1);
			
			rel.newheap();
			rel.setHeap(ptr, n.id);
			rel.setStack(sp, ptr);
			rel.setSptr(sp + 1);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring newarray(ExprSemiring A) {
		Newarray newarray = (Newarray) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			int[] lengths = new int[newarray.dim];
			for (int i = 0; i < newarray.dim; i++)
				lengths[i] = rel.stack(sp - i - 1).intValue();
			
			// Calculates required heap elements
			int require = 0;
			int acc = 1;
			for (int i = newarray.dim - 1; i >= 0; i--) {
				require += acc * (lengths[i] + ExplicitRelation.getArrayAuxSize());
				acc *= lengths[i];
			}
			log("\t\trequire: %d%n", require);
			
			ExplicitRelation newrel = rel.id();
			newrel.newheap();
			int oldptr = newrel.allocate(require);
			newrel.setStack(sp - 1, oldptr);
			
			int ptr = oldptr;
			Queue<Integer> indices = new LinkedList<Integer>();
			for (int i = 1; i <= newarray.dim; i++) {
				
				// Computes number of blocks
				int blocknum = 1;
				for (int j = i; j < newarray.dim; j++) {
					blocknum *= lengths[j];
				}
				
				// Fills blocks
				int blocksize = lengths[i - 1];
				log("\t\tblocknum: %d, blocksize: %d%n", blocknum, blocksize);
				for (int j = 0; j < blocknum; j++) {
					
					// Remember the index
					indices.offer(ptr);
					
					// Fills the array type
					newrel.setHeap(ptr++, newarray.types[newarray.dim-i]);
					log("\t\tptr: %d%n", ptr);
					
					// Updtes ptr wrt. owner & counter
					for (int k = 2; k < ExplicitRelation.getArrayAuxSize(); k++)
						newrel.setHeap(ptr++, 0);
					
					// Fills the array length
					newrel.setHeap(ptr++, blocksize);
					
					// Fills the array elements
					if (i != 1) {
						// Initializes the array indices
						for (int k = 0; k < blocksize; k++) {
							newrel.setHeap(ptr++, indices.remove());
						}
					} 
					
					// Initializes the array values
					else {
						for (int k = 0; k < blocksize; k++) {
							if (newarray.init.isString())
								newrel.setHeap(ptr++, ExplicitRelation.encode(newarray.init.stringValue()));
							else
								newrel.setHeap(ptr++, (Number) newarray.init.getValue());
						}
					}
				}
			}
			
			
			if (newarray.init.deterministic()) {
				newrels.add(newrel);
			}
			
			else {
				if (newarray.dim > 1)
					throw new RemoplaError("Nondeterministic multidimensional array not supported.");
				
				ptr = oldptr + ExplicitRelation.getArrayAuxSize();
				
				int min, max;
				if (newarray.init.all()) {
					min = -(1 << (ExplicitRelation.bits - 1));
					max = (1 << (ExplicitRelation.bits - 1)) - 1;
				} else {
					min = newarray.init.intValue();
					max = newarray.init.to.intValue();
				}
				
				Number a[] = new Number[lengths[0]];
				for (int k = 0; k < a.length; k++)
					a[k] = min;
				
				// Updates element values
				label: while (true) {
					System.arraycopy(a, 0, newrel.heap(), ptr, lengths[0]);
					newrels.add(newrel);
					newrel = newrel.id();
					newrel.newheap();
					
					if (a.length == 0) break;
					for (int l = a.length - 1; l >= 0; l--) {
						if (a[l].intValue() != max) {
							a[l] = a[l].intValue() + 1;
							break;
						} else {
							if (l == 0) break label;
							a[l] = min;
						}
					}
				}
			}
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring npe(ExprSemiring A) {
		Npe npe = (Npe) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			S s = rel.s();
			if (s.stack[s.sptr - npe.depth - 1].intValue() == 0)
				newrels.add(rel.id());
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring poppush(ExprSemiring A) {
		Poppush poppush = (Poppush) A.value;
		if (poppush.nochange())
			return id();
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			sp = sp - poppush.pop + poppush.push;
			
			ExplicitRelation newrel = rel.id();
			for (int i = 1; i <= poppush.push; i++)
				newrel.setStack(sp - i, 0);
			newrel.setSptr(sp);
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	
	
	private Semiring push(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = fulfillsCondition(A);
		if (newrels.isEmpty()) 
			return new ExplicitSemiring(newrels);
		
		Value value = (Value) A.value;
		int cat = value.getCategory().intValue();
		
		HashSet<ExplicitRelation> newrels2 = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : newrels) {
			if (value.deterministic()) {
				if (value.isString())
					rel.push(cat, ExplicitRelation.encode(value.stringValue()));
				else
					rel.push(cat, (Number) value.getValue());
				newrels2.add(rel);
			}
			
			// Nondeterministic push
			else {
				int min, max;
				if (value.all()) {
					int bits = ExplicitRelation.bits;
					min = -(1 << (bits - 1));
					max = (1 << (bits - 1)) - 1;
				} else {
					min = value.intValue();
					max = value.to.intValue();
				}
				for (int i = min; i <= max; i++) {
					ExplicitRelation newrel = rel.id();
					newrels2.add(newrel.push(cat, i));
				}
			}
		}
		
		return new ExplicitSemiring(newrels2);
	}
	
	private Semiring print(ExprSemiring A) {
		Print print = (Print) A.value;
		StringBuilder out = new StringBuilder();
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			ExplicitRelation newrel = rel.id();
			if (print.type == Print.NOTHING) {
				newrel.setSptr(rel.sptr() - 1);
			} else {
				out.append(rel.stack(rel.sptr() - 1));
				out.append(" ");
				newrel.setSptr(rel.sptr() - 2);
			}
			newrels.add(newrel);
		}
		
		// Prints out
		if (out.length() > 0) {
			out.insert(0, "[ ");
			out.append("]");
		}
		System.out.print(out);
		if (print.newline) System.out.println();
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring returnExpr(ExprSemiring A) {
		Return ret = (Return) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			G newg = (G) rel.g().id();
			if (ret.type != Return.Type.VOID) {
				newg.setGlobal(ExplicitRelation.RETVAR, 
						rel.stack(rel.sptr() - ret.getCategory().intValue()));
			}
			
			if (rel.type == ExplicitRelation.G0L0) {
				newrels.add(new ExplicitRelation(ExplicitRelation.G0, 
						new V[] { newg }));
			} else {	// G0L0G1L1
				newrels.add(new ExplicitRelation(ExplicitRelation.G0G2L2, 
						new V[] { newg, rel.g1().id(), rel.l1().id() }));
			}
		}
		
//		log(newrels);
//		try {
//			for (ExplicitRelation rel : newrels) {
//				if (rel.heap(3).intValue() == 1 && rel.heap(4).intValue() == 0
//						&& rel.heap(5).intValue() == 1) {
//					Number[] heap = rel.g2().heap;
//					if (heap[3].intValue() == 1 && heap[4].intValue() == 1
//							&& heap[5].intValue() == 1)
//						return null;
//				}
//			}
//		} catch (Throwable t) {}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring store(ExprSemiring A) {
		Local local = (Local) A.value;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			S s = rel.s();
			ExplicitRelation newrel = rel.id();
			if (local.getCategory().one()) {
				newrel.l().local[local.index] = s.stack[s.sptr - 1];
				newrel.s().sptr = s.sptr - 1;
			} else {
				newrel.l().local[local.index] = s.stack[s.sptr - 2];
				newrel.l().local[local.index + 1] = s.stack[s.sptr - 1];
				newrel.s().sptr = s.sptr - 2;
			}
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring swap(ExprSemiring A) {
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			
			ExplicitRelation newrel = rel.id();
			newrel.setStack(sp - 1, rel.stack(sp - 2));
			newrel.setStack(sp - 2, rel.stack(sp - 1));
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	private Semiring unaryop(ExprSemiring A) {
		Unaryop unaryop = (Unaryop) A.value;
		
		// Narrows: D2F, L2I
		if (unaryop.type == Unaryop.Type.D2F
				|| unaryop.type == Unaryop.Type.L2I)
			return poppush(new ExprSemiring(ExprType.POPPUSH, new Poppush(1, 0)));
		
		// Widens: F2D, I2L
		if (unaryop.type == Unaryop.Type.F2D
				|| unaryop.type == Unaryop.Type.I2L)
			return push(new ExprSemiring(ExprType.PUSH, 
					new Value(Category.ONE, 0)));
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			int sp = rel.sptr();
			Number value = rel.stack(sp - unaryop.type.pop.intValue());
			Number result = unaryop(unaryop, value);
			
			ExplicitRelation newrel = rel.id();
			newrel.setStack(sp - unaryop.type.pop.intValue(), result);
			if (unaryop.type.pop != unaryop.type.push) {
				if (unaryop.type.pop.one()) {	// && unaryop.type.push == 2
					newrel.setSptr(sp + 1);
					newrel.setStack(sp, 0);
				} else {	// unaryop.type.pop == 2 && unaryop.type.push == 1
					newrel.setSptr(sp - 1);
				}
			}
			newrels.add(newrel);
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	/**
	 * Signature of a: (G0,L0,G1,L1)
	 * 
	 * @param a
	 * @return
	 */
	public Set<RawArgument> getRawArguments() {
		
		Set<RawArgument> args = new HashSet<RawArgument>();
		for (ExplicitRelation rel : rels) {
			RawArgument arg = rel.getRawArgument();
			log("arg: %s%n", arg);
			args.add(arg);
		}
		return args;
	}
	
	public ExplicitSemiring conjoin(ExplicitSemiring that) {
		HashSet<ExplicitRelation> thatrels = that.rels;
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		for (ExplicitRelation rel : rels) {
			for (ExplicitRelation thatrel : thatrels) {
				if (!rel.g1().equals(thatrel.g2()) || !rel.l1().equals(thatrel.l2()))
					continue;
				
				newrels.add(new ExplicitRelation(ExplicitRelation.G0L0G1L1,
						new V[] { rel.g().id(), thatrel.l().id(), thatrel.s().id(), thatrel.g1().id(), thatrel.l1().id() }));
			}
		}
		
		return new ExplicitSemiring(newrels);
	}
	
	/*************************************************************************
	 * Helper methods
	 *************************************************************************/
	
	private HashSet<ExplicitRelation> fulfillsCondition(ExprSemiring A, int id) {
		Condition cond = (Condition) A.aux;
		int type = cond.getType();
		
		HashSet<ExplicitRelation> newrels = new HashSet<ExplicitRelation>();
		if (type == Condition.CONTAINS 
				|| type == Condition.NOTCONTAINS) {
			
			Set<Integer> set = cond.getSetValue();
			
			for (ExplicitRelation rel : rels) {
				int ref = rel.stack(rel.sptr() - id).intValue();
				if (ref == 0) {
					if (type == Condition.CONTAINS)
						newrels.add(rel.id());	// Null pointer
					continue;
				}
				
				Number h = rel.heap(ref);
				if (type == Condition.CONTAINS && !set.contains(h)) {
					log("\t\tbypassing id %d%n", h);
					continue;
				}
				if (type == Condition.NOTCONTAINS && set.contains(h)) {
					log("\t\tbypassing id %d%n", h);
					continue;
				}
				newrels.add(rel.id());
			}
			return newrels;
		}
		
		// type is either ZERO or ONE
		String name = cond.getStringValue();
		for (ExplicitRelation rel : rels) {
			switch (type) {
			case Condition.ZERO:
				if (rel.global(name).intValue() == 0)
					newrels.add(rel.id());
				break;
			case Condition.ONE:
				if (rel.global(name).intValue() == 1)
					newrels.add(rel.id());
				break;
			}
		}
		return newrels;
	}
	
	private HashSet<ExplicitRelation> fulfillsCondition(ExprSemiring A) {
		
		if (A.aux == null) {
			log("\t\tno condition%n");
			return id(rels);
		}
		
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
	
	private static Number arith(int type, Number v1, Number v2) {
		switch (type) {
		case Arith.ADD:
			return v1.longValue() + v2.longValue();
		case Arith.AND:
			return v1.longValue() & v2.longValue();
		case Arith.CMP: {
			if (v1.longValue() > v2.longValue()) return 1;
			if (v1.longValue() == v2.longValue()) return 0;
			return -1;
		}
		case Arith.DIV:
			return v1.longValue() / v2.longValue();
		case Arith.MUL:
			return v1.longValue() * v2.longValue();
		case Arith.OR:
			return v1.longValue() | v2.longValue();
		case Arith.REM:
			return v1.longValue() % v2.longValue();
		case Arith.SHL:
			return v1.longValue() << (v2.longValue() & 31);
		case Arith.SHR:
			return v1.longValue() >> (v2.longValue() & 31);
		case Arith.SUB:
			return v1.longValue() - v2.longValue();
		case Arith.USHR:
			return v1.longValue() >>> (v2.longValue() & 31);
		case Arith.XOR:
			return v1.longValue() ^ v2.longValue();
		case Arith.FADD:
			return v1.doubleValue() + v2.doubleValue();
		case Arith.FCMPG: 
		case Arith.FCMPL: {
			double d1 = v1.doubleValue();
			double d2 = v2.doubleValue();
			if (d1 > d2) return 1;
			else if (d1 == d2) return 0;
			else if (d1 < d2) return -1;
			// At least one must be NaN
			else if (type == Arith.FCMPG) return 1;
			else return -1;
		}
		case Arith.FDIV:
			return v1.doubleValue() / v2.doubleValue();
		case Arith.FMUL:
			return v1.doubleValue() * v2.doubleValue();
		case Arith.FREM:
			return v1.doubleValue() % v2.doubleValue();
		case Arith.FSUB:
			return v1.doubleValue() - v2.doubleValue();
//		case Arith.NDT:
//			return range(rdom, decode(v1, dom1), decode(v2, dom2));
			
		default:
			throw new IllegalArgumentException("Invalid ArithType: " + type);
		}
	}
	
	private static boolean satisfy(If expr, int value) {
		log("\t\tvalue: %d%n", value);
		switch (expr.getType()) {
		case If.EQ:
			return value == 0;
				
		case If.NE:
			return value != 0;
			
		case If.LT:
			return value < 0;
			
		case If.GE:
			return value >= 0;
			
		case If.GT:
			return value > 0;
			
		case If.LE:
			return value <= 0;
			
		case If.IS:
			return value == expr.getValue();
		}
		
		throw new IllegalArgumentException("Invalid comparison type: " + expr.getType());
	}
	
	private static boolean satisfy(int type, int value1, int value2) {
		switch(type) {
		case Comp.EQ:
			return value1 == value2;
		case Comp.NE:
			return value1 != value2;
		case Comp.LT:
			return value1 < value2;
		case Comp.GE:
			return value1 >= value2;
		case Comp.GT:
			return value1 > value2;
		case Comp.LE:
			return value1 <= value2;
		default:
			throw new IllegalArgumentException("Invalid comparison type: " + type);
		}
	}
	
	private static Number unaryop(Unaryop unaryop, Number value) {
		switch (unaryop.type) {
		case INEG:
		case LNEG:
			return -value.longValue();
		case DNEG:
		case FNEG:
			return -value.doubleValue();
		case D2I:
		case D2L:
		case F2I:
		case F2L:
			return value.longValue();
		case I2D:
		case I2F:
		case L2D:
		case L2F:
			return value.doubleValue();
		case CONTAINS:
			return (unaryop.set.contains(value.intValue())) ? 1 : 0;
		default:
			throw new IllegalArgumentException("Invalid operation: " + unaryop);
		}
	}
	
	public String toString() {
		StringBuilder out = new StringBuilder();
		for (ExplicitRelation rel : rels) {
			out.append(rel.toString());
			out.append("\n");
		}
		return out.toString();
	}
	
	private static void log(HashSet<ExplicitRelation> rels) {
		if (!Sat.debug())
			return;
		
		log("%n");
		for (ExplicitRelation rel : rels) {
			log("\t\t%s%n", rel.toString());
		}
		log("%n");
	}
	
	private static void log(ExplicitSemiring a) {
		log(a.rels);
	}
	
	private void log() {
		log(this);
	}
	
	public static void log(String msg, Object... args) {
		Sat.logger.fine(String.format(msg, args));
	}
}
