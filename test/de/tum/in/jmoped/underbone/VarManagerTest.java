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
				long en = DomainManager.encode((int) i, doms[0]);
				Assert.assertEquals(j++, en);
			}
			for (long i = -size/2; i <= -1; i++) {
				long en = DomainManager.encode((int) i, doms[0]);
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
				int de = DomainManager.decode(i, doms[0]);
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
		
		DomainManager manager = new DomainManager("cudd", 10000, 10000, 
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
		DomainManager manager = new DomainManager("cudd", 10000, 10000, 
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
			int a = DomainManager.decode(x.scanVar(dom1).longValue(), dom1);
			int b = DomainManager.decode(x.scanVar(dom2).longValue(), dom2);
			System.out.printf("a: %d, b: %d%n", a, b);
			Assert.assertEquals(a, b);
		}
		
		bdd.andWith(dom1.ithVar(DomainManager.encode(-1, dom1)));
		itr = bdd.iterator(varset);
		while (itr.hasNext()) {
			BDD x = itr.nextBDD();
			int a = DomainManager.decode(x.scanVar(dom1).longValue(), dom1);
			int b = DomainManager.decode(x.scanVar(dom2).longValue(), dom2);
			System.out.printf("a: %d, b: %d%n", a, b);
			Assert.assertEquals(-1, a);
			Assert.assertEquals(-1, b);
		}
	}
	
	private static void testScanVar(DomainManager manager, BDD bdd, BDDDomain dom, long expected) {
		BDDIterator itr = bdd.iterator(dom.set());
		int count = 0;
		long elapsed1 = 0, elapsed2 = 0;
		while (itr.hasNext()) {
			BDD b = itr.nextBDD();
			
			long startTime = System.currentTimeMillis();
			long value1 = DomainManager.scanVar(b, dom);
			elapsed1 += System.currentTimeMillis() - startTime;
			
			startTime = System.currentTimeMillis();
			long value2 = b.scanVar(dom).longValue();
			elapsed2 += System.currentTimeMillis() - startTime;
			
			Assert.assertEquals(value1, value2);
			b.free();
			count++;
		}
		System.out.printf("scanVar - New: %d, Original: %d%n", elapsed1, elapsed2);
		Assert.assertEquals(expected, count);
	}
	
	@Test public void testScanVar() {
		int bits = 20;
		long size = 1 << bits;
		DomainManager manager = new DomainManager("cudd", 10000, 10000, 
				bits, new long[] { size, size, size }, null, 1, 1, 1, false);
		BDDDomain hdom = manager.getHeapDomain(1);
		
		BDD a = manager.initVars();
		Assert.assertEquals(0, DomainManager.scanVar(a, hdom));
		Assert.assertEquals(1, DomainManager.scanVar(a, manager.getHeapPointerDomain()));
		a.free();
		
		a = manager.getFactory().one();
		testScanVar(manager, a, hdom, size);
		a.free();
		
		a = manager.bddRange(hdom, 5, 234565);
		testScanVar(manager, a, hdom, 234561);
		a.free();
	}
	
	@Test public void testIthVar2() {
		int bits = 20;
		long size = 1 << bits;
		DomainManager manager = new DomainManager("cudd", 10000, 10000, 
				bits, new long[] { size, size, size }, null, 1, 1, 1, false);
		BDDDomain hdom = manager.getHeapDomain(1);
		
		long startTime = System.currentTimeMillis();
		for (int i = 0; i < size; i++) {
			BDD bdd = hdom.ithVar(i);
			Assert.assertEquals(i, DomainManager.scanVar(bdd, hdom));
			bdd.free();
		}
		System.out.printf("ithVar - Original: %dms%n", 
				System.currentTimeMillis() - startTime);
		
		startTime = System.currentTimeMillis();
		for (int i = 0; i < size; i++) {
			BDD bdd = manager.ithVar(hdom, i);
			Assert.assertEquals(i, DomainManager.scanVar(bdd, hdom));
			bdd.free();
		}
		System.out.printf("ithVar - New: %dms%n", 
				System.currentTimeMillis() - startTime);
		
	}
	
	@Test public void testToString() {
		DomainManager manager = new DomainManager("cudd", 10000, 10000, 
				4, new long[] { 4, 4, 4 }, null, 1, 1, 1, false);
		BDD init = manager.initVars();
		System.out.println(init);
		System.out.println(init.toStringWithDomains());
		System.out.println(manager.toString(init));
	}
	
	@Test public void testLoad() {
		DomainManager manager = new DomainManager("cudd", 10000, 10000, 
				4, new long[] { 4, 4, 4 }, null, 1, 1, 1, false);
	}
}
