/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramPrefix;

import org.key_project.util.ExtList;

/**
 * Miscellaneous static methods related to Java blocks or statements in KeY. Mostly moved from
 * key.util.MiscTools here.
 *
 * @author bruns
 *
 */
public final class JavaTools {

    /**
     * Returns the active statement of the passed a java block.
     */
    public static SourceElement getActiveStatement(JavaBlock jb) {
        assert jb.program() != null;

        SourceElement result = jb.program().getFirstElement();
        while ((result instanceof ProgramPrefix || result instanceof CatchAllStatement)
                && !(result instanceof StatementBlock && ((StatementBlock) result).isEmpty())) {
            if (result instanceof LabeledStatement) {
                result = ((LabeledStatement) result).getChildAt(1);
            } else if (result instanceof CatchAllStatement) {
                result = ((CatchAllStatement) result).getBody();
            } else {
                result = result.getFirstElement();
            }
        }
        return result;
    }

    /**
     * Returns the passed java block without its active statement.
     */
    public static JavaBlock removeActiveStatement(JavaBlock jb, Services services) {
        assert jb.program() != null;
        final SourceElement activeStatement = JavaTools.getActiveStatement(jb);
        Statement newProg = (Statement) (new CreatingASTVisitor(jb.program(), false, services) {
            private boolean done = false;

            public ProgramElement go() {
                stack.push(new ExtList());
                walk(root());
                ExtList el = stack.peek();
                return el.get(ProgramElement.class);
            }

            @Override
            public void doAction(ProgramElement node) {
                if (!done && node == activeStatement) {
                    done = true;
                    stack.pop();
                    changed();
                } else {
                    super.doAction(node);
                }
            }
        }).go();

        StatementBlock newSB = newProg instanceof StatementBlock ? (StatementBlock) newProg
                : new StatementBlock(newProg);
        return JavaBlock.createJavaBlock(newSB);
    }

    /**
     * Returns the innermost method frame of the passed java block
     */
    public static MethodFrame getInnermostMethodFrame(ProgramElement pe, Services services) {
        final MethodFrame result = new JavaASTVisitor(pe, services) {
            private MethodFrame res;

            protected void doAction(ProgramElement node) {
                node.visit(this);
            }

            protected void doDefaultAction(SourceElement node) {
                if (node instanceof MethodFrame && res == null) {
                    res = (MethodFrame) node;
                }
            }

            public MethodFrame run() {
                walk(pe);
                return res;
            }
        }.run();

        return result;
    }

    /**
     * Returns the innermost method frame of the passed java block
     */
    public static MethodFrame getInnermostMethodFrame(JavaBlock jb, Services services) {
        return getInnermostMethodFrame(jb.program(), services);
    }

    public static ExecutionContext getInnermostExecutionContext(JavaBlock jb, Services services) {
        final MethodFrame frame = getInnermostMethodFrame(jb, services);
        return frame == null ? null : (ExecutionContext) frame.getExecutionContext();
    }

}
