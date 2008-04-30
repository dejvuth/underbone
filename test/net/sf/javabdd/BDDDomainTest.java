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
}
