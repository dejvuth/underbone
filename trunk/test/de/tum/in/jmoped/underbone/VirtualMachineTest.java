package de.tum.in.jmoped.underbone;

import java.util.Stack;

import org.junit.Assert;
import org.junit.Test;


public class VirtualMachineTest {

	@Test public void test1() {
		
		Assert.assertEquals(5, (int) 1.4*5);
		Assert.assertEquals(7, (int) (1.4*5));
	}
	
	@Test public void testStack() {
		Stack<Number> stack = new Stack<Number>();
		stack.push(2);
		stack.push(3);
		stack.push(7);
		Assert.assertEquals(2, stack.elementAt(0));
		Assert.assertEquals(3, stack.elementAt(1));
		
		stack.add(stack.size() - 1, 5);
		Assert.assertEquals(5, stack.elementAt(2));
		System.out.println(stack);
	}
}
