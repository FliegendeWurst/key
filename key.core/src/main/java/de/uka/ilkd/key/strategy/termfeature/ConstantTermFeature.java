/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;

public class ConstantTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new ConstantTermFeature();

    private ConstantTermFeature() {
    }

    @Override
    protected boolean filter(Term term, Services services) {
        return term.op() instanceof Function && term.arity() == 0;
    }

}
