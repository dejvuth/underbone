package de.tum.in.jmoped.underbone;

import static de.tum.in.jmoped.underbone.ExprType.PUSH;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDD.BDDIterator;

import org.junit.Test;

import de.tum.in.wpds.CancelMonitor;
import de.tum.in.wpds.DefaultMonitor;
import de.tum.in.wpds.Semiring;

public class BDDSemiringTest {

	@Test public void testArraystore() {
		
		VarManager manager = new VarManager("cudd", 10000, 10000, 
				3, new long[] { 8, 8, 8, 8, 8, 8, 8 }, null, 3, 0, 1, false);
		CancelMonitor monitor = new DefaultMonitor();
		
		BDDSemiring A = new BDDSemiring(manager, manager.initVars());
		BDDSemiring B = (BDDSemiring) A.extend(new ExprSemiring(ExprType.PUSH, 3, 0), monitor);
		BDDSemiring C = (BDDSemiring) B.extend(new ExprSemiring(ExprType.NEWARRAY), monitor);
		BDDSemiring D = (BDDSemiring) C.extend(new ExprSemiring(ExprType.PUSH, 1), monitor);
		BDDSemiring E = (BDDSemiring) D.extend(new ExprSemiring(ExprType.PUSH, 2), monitor);
		BDDSemiring F = (BDDSemiring) E.extend(new ExprSemiring(ExprType.ARRAYSTORE), monitor);
		
		System.out.println("A: " + A);
		System.out.println("B: " + B);
		System.out.println("C: " + C);
		System.out.println("D: " + D);
		System.out.println("E: " + E);
		System.out.println("F: " + F);
		
		A.free(); B.free(); C.free(); D.free(); E.free(); F.free();
		manager.free();
	}
	
	@Test public void test() {
		
		testArraystore();
		VarManager manager = new VarManager("cudd", 10000, 10000, 
				4, new long[] { 16, 16, 16, 16 }, null, 2, 2, 1, false);
		CancelMonitor monitor = new DefaultMonitor();
		
		BDDSemiring A = new BDDSemiring(manager, manager.initVars());
		BDDSemiring B = (BDDSemiring) A.extend(new ExprSemiring(ExprType.PUSH, 2), monitor);
		
		A.free(); B.free();// C.free(); D.free(); E.free(); F.free();
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
