package de.tum.in.jmoped.underbone;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDVarSet;
import net.sf.javabdd.CUDDFactory;
import net.sf.javabdd.JFactory;
import net.sf.javabdd.BDD.BDDIterator;

import org.junit.Test;


public class BDDTest {

	/**
	 * BDDs from BDDIterator.nextBDD() should be freed afterwards.
	 */
	@Test public void testIterator() {
		
		BDDFactory factory = CUDDFactory.init(1000, 100);
		BDDDomain[] doms = factory.extDomain(new int[] { 8, 16 });
		
		BDD a = doms[0].ithVar(2).orWith(doms[0].ithVar(3));
		System.out.println(a.toStringWithDomains());
		
		// It doesn't necessary to free BDDVarSet 
		BDDVarSet set = doms[0].set();
		BDDIterator itr = a.iterator(set);
		set.free();
		
		while (itr.hasNext()) {
			BDD tmp = itr.nextBDD();
			System.out.println(tmp.scanVar(doms[0]).intValue());
			
			// tmp must be freed!
			tmp.free();
		}
		System.out.println(a.toStringWithDomains());
		
		a.free();
		factory.clearAllDomains();
		factory.done();
	}
}
