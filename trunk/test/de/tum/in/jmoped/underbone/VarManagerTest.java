package de.tum.in.jmoped.underbone;

import java.util.Arrays;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDVarSet;
import net.sf.javabdd.JFactory;
import net.sf.javabdd.BDD.BDDIterator;

import org.junit.Assert;
import org.junit.Test;


public class VarManagerTest {

	@Test public void testEncode() {
		
		BDDFactory factory = JFactory.init(10000, 1000);
		for (int bits = 1; bits <= 32; bits++) {
			System.out.printf("bits: %d%n", bits);
			long size = (long) Math.pow(2, bits);
			BDDDomain[] doms = factory.extDomain(new long[] { size });
			
//			long en = VarManager.encode(-1, doms[0]);
//			System.out.printf("i: %d, encode(i): %d, expected: %d%n", -1, en, 4294967295L);
//			Assert.assertEquals(4294967295L, en);
			
			long j = 0;
			for (long i = 0; i <= size/2 - 1; i++) {
				long en = VarManager.encode((int) i, doms[0]);
				Assert.assertEquals(j++, en);
			}
			for (long i = -size/2; i <= -1; i++) {
				long en = VarManager.encode((int) i, doms[0]);
				Assert.assertEquals(j++, en);
			}
		}
		factory.done();
	}
	
	@Test public void testDecode() {
		
		BDDFactory factory = JFactory.init(10000, 1000);
		for (int bits = 1; bits <= 32; bits++) {
			System.out.printf("bits: %d%n", bits);
			long size = (long) Math.pow(2, bits);
			BDDDomain[] doms = factory.extDomain(new long[] { size });
			int j = 0;
			for (long i = 0; i < size; i++, j++) {
				if (size > 2 && i == size/2) j = (int) (-size/2);
				int de = VarManager.decode(i, doms[0]);
				try {
					Assert.assertEquals(j, de);
				} catch (AssertionError e) {
					System.out.printf("i: %d, de: %d, expected: %d%n", i, de, j);
					throw e;
				}
			}
		}
		factory.done();
	}
	
	@Test public void testIthVar() {
		
		VarManager manager = new VarManager("cudd", 10000, 10000, 
				4, new long[] { 4, 4, 4 }, null, 1, 1, 1, false);
		BDDDomain dom = manager.getHeapDomain(1);
		Assert.assertEquals(4, dom.size().longValue());
		
		BDD a = dom.ithVar(1);
		Assert.assertEquals(4, dom.size().longValue());
		Assert.assertEquals(1, a.scanVar(dom).intValue());
		System.out.println(a);
		System.out.println(dom.set());
//		BDDIterator itr = a.iterator(dom.set());
//		while (itr.hasNext()) {
//			BDD b = itr.nextBDD();
//			count++;
//		}
		
//		manager.extendCapacity(dom, 6);
		BDD b = dom.ithVar(3);
		System.out.println(a);
		System.out.println(dom.set());
		System.out.println(b);
		Assert.assertEquals(4, dom.size().longValue());
		Assert.assertEquals(1, a.scanVar(dom).intValue());
		Assert.assertEquals(3, b.scanVar(dom).intValue());
	}
	
	@Test public void testBDDEquals() {
		VarManager manager = new VarManager("cudd", 10000, 10000, 
				4, new long[] { 4, 4, 4 }, null, 1, 1, 1, false);
		BDDDomain dom1 = manager.getHeapDomain(1);
		System.out.printf("dom1: %s%n", Arrays.toString(dom1.vars()));
		BDDDomain dom2 = manager.getLocalVarDomain(0);
		System.out.printf("dom2: %s%n", Arrays.toString(dom2.vars()));
		BDDVarSet varset = dom1.set().union(dom2.set());
		
		BDD bdd = manager.bddEquals(dom1, dom2);
		System.out.println(bdd);
		
		BDDIterator itr = bdd.iterator(varset);
		while (itr.hasNext()) {
			BDD x = itr.nextBDD();
			int a = VarManager.decode(x.scanVar(dom1).longValue(), dom1);
			int b = VarManager.decode(x.scanVar(dom2).longValue(), dom2);
			System.out.printf("a: %d, b: %d%n", a, b);
			Assert.assertEquals(a, b);
		}
		
		bdd.andWith(dom1.ithVar(VarManager.encode(-1, dom1)));
		itr = bdd.iterator(varset);
		while (itr.hasNext()) {
			BDD x = itr.nextBDD();
			int a = VarManager.decode(x.scanVar(dom1).longValue(), dom1);
			int b = VarManager.decode(x.scanVar(dom2).longValue(), dom2);
			System.out.printf("a: %d, b: %d%n", a, b);
			Assert.assertEquals(-1, a);
			Assert.assertEquals(-1, b);
		}
	}
	
	@Test public void testToString() {
		VarManager manager = new VarManager("cudd", 10000, 10000, 
				4, new long[] { 4, 4, 4 }, null, 1, 1, 1, false);
		BDD init = manager.initVars();
		System.out.println(init);
		System.out.println(init.toStringWithDomains());
		System.out.println(manager.toString(init));
	}
	
	@Test public void testLoad() {
		VarManager manager = new VarManager("cudd", 10000, 10000, 
				4, new long[] { 4, 4, 4 }, null, 1, 1, 1, false);
	}
}
