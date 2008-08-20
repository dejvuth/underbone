package net.sf.javabdd;

import java.util.Arrays;
import java.util.HashSet;

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
	
	@Test public void testIthVar() {
		BDDFactory factory = BDDFactory.init("cudd", 10000, 10000);
		BDDDomain[] doms = factory.extDomain(new long[] { 4, 4 });
		
		try {
			doms[0].ithVar(4);
		} catch (BDDException e) {
			System.out.println("falls through");
		}
		
		doms[0].extendCapacity(4);
		Assert.assertEquals(4, doms[0].ithVar(4).scanVar(doms[0]).intValue());
		Assert.assertEquals(4, doms[0].varNum());
		
		doms[0].extendCapacity(50);
		Assert.assertEquals(50, doms[0].ithVar(50).scanVar(doms[0]).intValue());
		Assert.assertEquals(7, doms[0].varNum());
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
		
		Assert.assertEquals(5, bdd.scanVar(doms[0]).intValue());
	}
}
