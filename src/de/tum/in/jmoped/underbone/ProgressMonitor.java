package de.tum.in.jmoped.underbone;

import de.tum.in.wpds.CancelMonitor;

/**
 * A progress monitor.
 * 
 * @author suwimont
 *
 */
public interface ProgressMonitor extends CancelMonitor {

	/**
	 * Tells the monitor to begin the task <code>name</code>.
	 * <code>totalWork</code> determines the work to be done.
	 * 
	 * @param name the task name.
	 * @param totalWork the total work.
	 */
	void beginTask(String name, int totalWork);
	
	/**
	 * Tells the monitor that the task is done.
	 */
	void done();
	
	/**
	 * Tells the monitor to the amount specified by <code>work</code> 
	 * has been processed.
	 * 
	 * @param work the amount that already processed.
	 */
	void worked(int work);
}
