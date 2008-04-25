package de.tum.in.jmoped.underbone;

import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.JFactory;

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
}
