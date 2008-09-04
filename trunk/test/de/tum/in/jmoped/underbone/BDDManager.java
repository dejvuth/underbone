//package de.tum.in.jmoped.underbone;
//
//import java.util.Collection;
//
//import net.sf.javabdd.BDDFactory;
//
//
//public class BDDManager {
//
//	int ihptr;
//	int[][] iheap;
//	int isptr;
//	int ilv;
//	
//	public BDDManager(int bits, Collection<Variable> g, int hsize, int smax, int lvmax) {
//		
//		
//		int varnum = 0;
//		if (g != null) varnum += 3*g.size();
//		if (hsize != 0) varnum += 3*(hsize + 1);
//		if (lvmax != 0) varnum += 3*lvmax;
//		if (smax != 0) varnum += smax + 1;
//		varnum++;
//		
//		BDDFactory factory = BDDFactory.init("cudd", 100000, 100000);
//		factory.setVarNum(varnum);
//		
//		int index = 0;
//		if (g != null && !g.isEmpty()) {
//			for (Variable v : g) {
//				v.setIndex(index);
//				index += 3;
//			}
//		}
//		
//		if (hsize > 0) {
//			
//			ihptr = index;
//			index += 3;
//			
//			iheap = new int[hsize][];
//			for (int i = 0; i < hsize; i++) {
//				
//			}
//		}
//	}
//}
