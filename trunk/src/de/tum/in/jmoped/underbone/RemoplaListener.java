package de.tum.in.jmoped.underbone;

import java.util.Set;

import de.tum.in.wpds.SatListener;

/**
 * A listener that wraps {@link ProgressMonitor}.
 * 
 * @author suwimont
 *
 */
public interface RemoplaListener extends SatListener {

	/**
	 * Wraps the progress monitor.
	 * 
	 * @param monitor the progress monitor.
	 */
	public void setProgressMonitor(ProgressMonitor monitor);
	
	/**
	 * Starts the listener.
	 * 
	 * @param labels the labels to be tested.
	 * @see ProgressMonitor#beginTask(String, int).
	 */
	public void beginTask(String name, Set<String> labels);
	
	/**
	 * Ends the listener.
	 * 
	 * @see ProgressMonitor#done().
	 */
	public void done();
}
