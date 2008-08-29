package de.tum.in.jmoped.underbone;

import static de.tum.in.jmoped.underbone.ExprType.ARRAYLOAD;
import static de.tum.in.jmoped.underbone.ExprType.ARRAYSTORE;
import static de.tum.in.jmoped.underbone.ExprType.NEWARRAY;
import static de.tum.in.jmoped.underbone.ExprType.PUSH;
import static de.tum.in.jmoped.underbone.ExprType.SWAP;
import static de.tum.in.jmoped.underbone.ExprType.UNARYOP;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Stack;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDD.BDDIterator;

import org.junit.Assert;
import org.junit.Test;

import de.tum.in.jmoped.underbone.expr.Category;
import de.tum.in.jmoped.underbone.expr.Invoke;
import de.tum.in.jmoped.underbone.expr.Local;
import de.tum.in.jmoped.underbone.expr.Newarray;
import de.tum.in.jmoped.underbone.expr.Unaryop;
import de.tum.in.jmoped.underbone.expr.Value;
import de.tum.in.wpds.CancelMonitor;
import de.tum.in.wpds.DefaultMonitor;
import de.tum.in.wpds.Sat;
import de.tum.in.wpds.Semiring;

public class BDDSemiringTest {
	
	/**
	 * Starts a variable manager.
	 * 
	 * @return a variable manager.
	 */
	static VarManager init() {
		VarManager.setVerbosity(2);
		VarManager manager =  new VarManager("cudd", 10000, 10000, 
				3, new long[] { 8, 8, 8, 8, 8, 8, 8 }, null, 3, 3, 1, false);
		System.out.printf("Factory used: %s%n", manager.getFactory().getClass().getName());
		return manager;
	}
	
	private static Stack<Semiring> stack;
	private static CancelMonitor monitor = new DefaultMonitor();
	
	private void extend(Semiring d) {
		if (stack.isEmpty()) {
			stack.push(d);
			return;
		}
		stack.push(stack.peek().extend(d, monitor));
	}
	
	private BDD peek() {
		return ((BDDSemiring) stack.peek()).bdd;
	}
	
	private BDD run(Semiring[] expr) {
		stack = new Stack<Semiring>();
		for (int i = 0; i < expr.length; i++)
			extend(expr[i]);
		return peek();
	}
	
	private void print() {
		Iterator<Semiring> itr = stack.iterator();
		int count = 0;
		while (itr.hasNext()) {
			System.out.printf("\t%d:\t", count++);
			System.out.println(itr.next());
			System.out.println();
		}
	}
	
	private void printBDD() {
		Iterator<Semiring> itr = stack.iterator();
		int count = 0;
		while (itr.hasNext()) {
			System.out.printf("\t%d:\t", count++);
			System.out.println(((BDDSemiring) itr.next()).bdd.toStringWithDomains());
			System.out.println();
		}
	}
	
	private void free() {
		Iterator<Semiring> itr = stack.iterator();
		while (itr.hasNext()) {
			itr.next().free();
		}
	}
	
	@Test public void testPush() {
		VarManager manager = init();
		Semiring[] expr = new Semiring[] {
				new BDDSemiring(manager, manager.initVars()),
				new ExprSemiring(PUSH, new Value(Category.ONE, 4)),
				new ExprSemiring(ExprType.STORE, new Local(Category.ONE, 1))
		};
		BDD bdd = run(expr);
		printBDD();
	}
	
	@Test public void testInvoke() {
		VarManager manager = init();
		Semiring[] expr = new Semiring[] {
				new BDDSemiring(manager, manager.initVars()),
//				new ExprSemiring(PUSH, new Value(Category.ONE, 4)),
				new ExprSemiring(ExprType.INVOKE, new Invoke())
		};
		BDD bdd = run(expr);
		printBDD();
	}
	
	/**
	 * Tests {@link ExprType#ARRAYLOAD}.
	 */
	@Test public void testArrayload() {
		
		VarManager manager = init();
		
		/*
		 * Creates a new array with size [0,3] and load the element at index 1.
		 * Note that there are two array bound violations.
		 */
		Semiring[] expr = new Semiring[] {
				new BDDSemiring(manager, manager.initVars()),
				new ExprSemiring(PUSH, new Value(Category.ONE, 0, 1, 3)),
				new ExprSemiring(NEWARRAY, new Newarray(new Value(Category.ONE,2))),
				new ExprSemiring(PUSH, new Value(Category.ONE,1)),
				new ExprSemiring(ARRAYLOAD)
		};
		BDD bdd = run(expr);
		print();
		
		// Tests whether the top of stack is 2
		Set<Long> set = manager.valuesOf(bdd, manager.getStackDomain(0));
		Assert.assertEquals(set.size(), 1);
		Assert.assertTrue(set.contains(2l));
		
		free();
		manager.free();
	}
	
	/**
	 * Tests {@link ExprType#ARRAYSTORE}.
	 */
	@Test public void testArraystore() {
		
		VarManager manager = init();
		
		/*
		 * Creates a new array with size [0,3] and store value 2 at index 1.
		 * Note that there are two array bound violations.
		 */
		Semiring[] expr = new Semiring[] {
				new BDDSemiring(manager, manager.initVars()),
				new ExprSemiring(PUSH, new Value(Category.ONE,0, 1, 3)),
				new ExprSemiring(NEWARRAY, new Newarray()),
				new ExprSemiring(PUSH, new Value(Category.ONE,1)),
				new ExprSemiring(PUSH, new Value(Category.ONE,2)),
				new ExprSemiring(ARRAYSTORE)
		};
		BDD bdd = run(expr);
		
		// Tests whether the array at index 1 is 2
		Set<Long> set = manager.valuesOf(bdd, manager.getHeapDomain(4));
		Assert.assertEquals(set.size(), 1);
		Assert.assertTrue(set.contains(2l));
		
		free();
		manager.free();
	}
	
	/**
	 * Tests {@link ExprType#SWAP}.
	 */
	@Test public void testSwap() {
		
		VarManager manager = init();
		
		// Pushes and swaps
		Semiring[] expr = new Semiring[] {
				new BDDSemiring(manager, manager.initVars()),
				new ExprSemiring(PUSH, new Value(Category.ONE, -1, 1, 1)),
				new ExprSemiring(PUSH, new Value(Category.ONE, 2, 1, 3)),
				new ExprSemiring(SWAP)
		};
		BDD bdd = run(expr);
		
		// The top of stack must be -1, 0, or 1
		Set<Long> set = manager.valuesOf(bdd, manager.getStackDomain(1));
		Assert.assertEquals(set.size(), 3);
		Assert.assertTrue(set.containsAll(Arrays.asList( 7l, 0l, 1l )));
		
		// The second top of stack must be 2 or 3
		set = manager.valuesOf(bdd, manager.getStackDomain(0));
		Assert.assertEquals(set.size(), 2);
		Assert.assertTrue(set.containsAll(Arrays.asList( 2l, 3l )));
		
		free();
		manager.free();
	}
	
	/**
	 * Tests {@link ExprType#UNARYOP} 
	 * having value {@link ExprSemiring.UnaryOpType#CONTAINS}.
	 */
	@Test public void testUnaryopContains() {
		
		VarManager manager = init();
		
		// Pushes and checks for containment.
		Semiring[] expr = new Semiring[] {
				new BDDSemiring(manager, manager.initVars()),
				new ExprSemiring(PUSH, new Value(Category.ONE, 3)),
				new ExprSemiring(UNARYOP, new Unaryop(Unaryop.Type.CONTAINS, 
						new HashSet<Integer>(Arrays.asList(1, 3, 4))))
		};
		BDD bdd = run(expr);
		
		// The top of stack must be 1
		Set<Long> set = manager.valuesOf(bdd, manager.getStackDomain(0));
		Assert.assertEquals(set.size(), 1);
		Assert.assertTrue(set.contains(1l));
		
		// Pushes and checks for containment.
		expr = new Semiring[] {
				new BDDSemiring(manager, manager.initVars()),
				new ExprSemiring(PUSH, new Value(Category.ONE, 2)),
				new ExprSemiring(UNARYOP, new Unaryop(Unaryop.Type.CONTAINS, 
						new HashSet<Integer>(Arrays.asList(1, 3, 4))))
		};
		bdd = run(expr);
		
		// The top of stack must be 0
		set = manager.valuesOf(bdd, manager.getStackDomain(0));
		Assert.assertEquals(set.size(), 1);
		Assert.assertTrue(set.contains(0l));
		
		free();
		manager.free();
	}
	
//	@Test public void testGetEqRel() {
//		
//		VarManager manager = new VarManager(2, new long[] { 4, 4 }, null, 1, 1, 2, true);
//		CancelMonitor monitor = new DefaultMonitor();
//		
//		BDDSemiring A = (BDDSemiring) new BDDSemiring(manager, manager.initVars()).lift(null, -1);
//		BDDDomain dom8 = manager.getDomain(8);
//		BDDDomain dom13 = manager.getDomain(13);
//		
//		A.bdd = A.bdd.exist(dom8.set().unionWith(dom13.set()))
//				.andWith(dom8.ithVar(0).andWith(dom13.ithVar(0))
//						.orWith(dom8.ithVar(1).andWith(dom13.ithVar(1))));
////		A = (BDDSemiring) A.extend(new ExprSemiring(PUSH, new ExprSemiring.Value(0, 1, 1)), monitor);
//		System.out.println("A: " + A.toRawString());
//		
//		BDDSemiring B = (BDDSemiring) A.getEqRel(0);
//		System.out.println("B: " + B.toRawString());
//		
//		BDDSemiring C = (BDDSemiring) B.getEqClass();
//		System.out.println("C: " + C.toRawString());
//		System.out.println(A.id().andWith(C.id()).toRawString());
//		
//		B.andWith(C.not());
//		C = (BDDSemiring) B.getEqClass();
//		System.out.println("B: " + B.toRawString());
//		System.out.println("C: " + C.toRawString());
//		System.out.println(A.id().andWith(C.id()).toRawString());
//		
//		B.andWith(C.not());
//		C = (BDDSemiring) B.getEqClass();
//		System.out.println("C: " + C.toRawString());
//		
//		BDDIterator itr = C.bdd.iterator(manager.getG3VarSet());
//		while (itr.hasNext()) {
//			System.out.println(itr.nextBDD().toStringWithDomains());
//		}
//		
//		A.free(); B.free();
//		manager.free();
//	}
}
