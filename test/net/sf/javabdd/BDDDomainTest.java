package net.sf.javabdd;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import net.sf.javabdd.BDD.BDDIterator;

import org.junit.Assert;
import org.junit.Test;

public class BDDDomainTest {

	/**
	 * Bug in JavaBDD. The method varRange does not work correctly.
	 */
	@Test public void testVarRange() {
		BDDFactory factory = BDDFactory.init("cudd", 10000, 10000);
		BDDDomain[] doms = factory.extDomain(new long[] { 8 });
		
		BDD bdd = doms[0].varRange(2, 5);
		System.out.println(bdd.toStringWithDomains());
		
		HashSet<Integer> set = new HashSet<Integer>(Arrays.asList( 2, 3, 4, 5 ));
		BDDIterator itr = bdd.iterator(doms[0].var);
		while (itr.hasNext()) {
			BDD tmp = itr.nextBDD();
			Assert.assertTrue(set.contains(tmp.scanVar(doms[0]).longValue()));
		}
		bdd.free();
		factory.done();
	}
	
	static Set<Integer> setOf(BDD bdd, BDDDomain dom) {
		if (bdd == null) return null;
		
		Set<Integer> set = new HashSet<Integer>();
		if (bdd.isZero()) return set;
		
		BDDIterator itr = bdd.iterator(dom.set());
		while (itr.hasNext()) {
			BDD a = itr.nextBDD();
			set.add(a.scanVar(dom).intValue());
			a.free();
		}
		return set;
	}
	
	@Test public void testIthVar() {
		BDDFactory factory = BDDFactory.init("cudd", 10000, 10000);
		BDDDomain[] doms = factory.extDomain(new long[] { 4, 4 });
		BDDDomain dom = doms[0];
		
		try {
			dom.ithVar(4);
		} catch (BDDException e) {
			System.out.println("falls through");
		}
		
		BDD a = dom.ithVar(0);
		Assert.assertEquals(1, setOf(a, dom).size());
		Assert.assertTrue(setOf(a, dom).contains(0));
		Assert.assertEquals(1, doms[0].usedbits);
		
		BDD b = dom.ithVar(1);
		Assert.assertEquals(1, doms[0].usedbits);
		
		BDD c = dom.ithVar(2);
		System.out.println(setOf(a, dom));
		Assert.assertEquals(1, setOf(a, dom).size());		// Wrong
		Assert.assertTrue(setOf(a, dom).contains(0));
		Assert.assertEquals(1, setOf(c, dom).size());
		Assert.assertTrue(setOf(c, dom).contains(2));
		Assert.assertEquals(2, doms[0].usedbits);
		
		BDD d = dom.ithVar(3);
		Assert.assertEquals(2, doms[0].usedbits);
		
//		doms[0].extendCapacity(4);
//		Assert.assertEquals(4, doms[0].ithVar(4).scanVar(doms[0]).intValue());
//		Assert.assertEquals(4, doms[0].varNum());
//		
//		doms[0].extendCapacity(50);
//		Assert.assertEquals(50, doms[0].ithVar(50).scanVar(doms[0]).intValue());
//		Assert.assertEquals(7, doms[0].varNum());
	}
	
	@Test public void testOverlapDomain() {
		BDDFactory factory = BDDFactory.init("cudd", 10000, 10000);
		BDDDomain[] doms = factory.extDomain(new long[] { 8, 8 });
		Assert.assertEquals(8, doms[0].size().longValue());
		Assert.assertEquals(8, doms[1].size().longValue());
		
		BDD bdd = doms[0].ithVar(5);
		Assert.assertEquals(5, bdd.scanVar(doms[0]).intValue());
		
		doms[0] = factory.overlapDomain(doms[0], doms[1]);
		Assert.assertEquals(64, doms[0].size().longValue());
		
		// Corrupted
		Assert.assertEquals(5, bdd.scanVar(doms[0]).intValue());
	}
	
//	@Test public void testScanVarMax() {
//		BDDFactory factory = BDDFactory.init("cudd", 10000, 10000);
//		BDDDomain[] doms = factory.extDomain(new long[] { 8, 8 });
//		
//		BDD bdd = factory.one();
//		Assert.assertEquals(7, bdd.scanVarMax(doms[0]).intValue());
//		
//		bdd = doms[1].ithVar(4);
//		Assert.assertEquals(4, bdd.scanVarMax(doms[1]).intValue());
//		
//		bdd.orWith(doms[1].ithVar(2));
//		System.out.println(bdd);
//		Assert.assertEquals(4, bdd.scanVarMax(doms[1]).intValue());
//		
//		bdd.orWith(doms[1].ithVar(7));
//		Assert.assertEquals(7, bdd.scanVarMax(doms[1]).intValue());
//	}
//	
//	@Test public void testExtendCapacity() {
//		BDDFactory factory = BDDFactory.init("cudd", 10000, 10000);
//		BDDDomain[] doms = factory.extDomain(new long[] { 4, 4 });
//		Assert.assertEquals(4, doms[0].size().intValue());
//		
//		doms[0].extendCapacity(7);
//		Assert.assertEquals(16, doms[0].size().intValue());
//		
//		BDD bdd = doms[0].ithVar(7);
//		Assert.assertEquals(7, bdd.scanVar(doms[0]).intValue());
//	}
	
	@Test public void testBigInteger() {
		for (int i = -8; i <= 7; i++) {
			System.out.println(i + ": " + BigInteger.valueOf(i).bitLength());
		}
	}
}
