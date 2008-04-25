package de.tum.in.jmoped.underbone;

import org.junit.Assert;
import org.junit.Test;


public class VirtualMachineTest {

	@Test public void test1() {
		
		Assert.assertEquals(5, (int) 1.4*5);
		Assert.assertEquals(7, (int) (1.4*5));
	}
}
