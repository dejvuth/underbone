package de.tum.in.jmoped.underbone;

import java.util.List;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDVarSet;
import net.sf.javabdd.BDD.BDDIterator;

import de.tum.in.wpds.TraceNode;

public class TraceManager {

	private TraceNode[] rawtrace;
	private VarManager varmanager;
	
	private BDDVarSet var;
	private BDDIterator itr;
	
	public TraceManager(List<TraceNode> trace, VarManager manager) {
		
		rawtrace = trace.toArray(new TraceNode[trace.size()]);
		varmanager = manager;
		
		var = varmanager.getVarSet0();
		itr = ((BDDSemiring) rawtrace[rawtrace.length-1].d).bdd.iterator(var);
	}
	
	public boolean hasNext() {
		
		return itr.hasNext();
	}
	
	/** UNFINISHED **/
}
