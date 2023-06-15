package org.key_project.slicing.graph;

import java.util.Objects;

import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.BranchLocation;

/**
 * A skolem constant tracked in the dependency graph.
 *
 * @author Arne Keller
 */
public class TrackedFunction extends GraphNode {
    private final Function function;

    public TrackedFunction(Function f, BranchLocation loc) {
        super(loc);

        this.function = f;
    }

    @Override
    public GraphNode popLastBranchID() {
        return new TrackedFunction(function, getBranchLocation().removeLast());
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "variable " + function.toString();
    }

    public Function getFunction() {
        return function;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        TrackedFunction that = (TrackedFunction) o;

        return Objects.equals(function, that.function);
    }

    @Override
    public int hashCode() {
        return function != null ? function.hashCode() : 0;
    }
}
