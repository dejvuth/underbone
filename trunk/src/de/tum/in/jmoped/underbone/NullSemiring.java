package de.tum.in.jmoped.underbone;

import java.util.Set;

import de.tum.in.wpds.CancelMonitor;
import de.tum.in.wpds.Semiring;

/**
 * A null semiring.
 * 
 * @author suwimont
 *
 */
public class NullSemiring implements Semiring {

	public Semiring combine(Semiring a) {
		return this;
	}

	public Semiring extend(Semiring a, CancelMonitor monitor) {
		return this;
	}

	public Semiring extendDynamic(Semiring a, CancelMonitor monitor) {
		return this;
	}

	public Semiring extendPop(Semiring a, CancelMonitor monitor) {
		return this;
	}

	public Semiring extendPush(Semiring a, CancelMonitor monitor) {
		return this;
	}

	public void free() {
	}

	public Semiring id() {
		return this;
	}

	public Semiring lift(Semiring a) {
		return this;
	}

	public Semiring restrict(Semiring a) {
		return this;
	}

	public String toRawString() {
		return toString();
	}

	public String toString() {
		return "1";
	}

	public Set<Semiring> getGlobals() {
		return null;
	}

	public Semiring andWith(Semiring a) {
		return null;
	}

	public Semiring getEqClass() {
		return null;
	}

	public Semiring getEqRel(int flag) {
		return null;
	}

	public Semiring getGlobal() {
		return null;
	}

	public boolean isZero() {
		return false;
	}

	public Semiring orWith(Semiring a) {
		return null;
	}

	public void updateGlobal(Semiring a) {
	}

	public Semiring getEqClass(int flag) {
		return null;
	}

	public void sliceWith(Semiring eqclass, int approach) {
	}
}
