/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.Serializable;

/**
 * Data structure for RunAllProofs test results consisting of a string message and a boolean value
 * which specifies whether a test run was successful or not.
 */
public class TestResult implements Serializable {
    private static final long serialVersionUID = 7635762713077999920L;

    public final String message;
    public final boolean success;

    public TestResult(String message, boolean success) {
        this.message = message;
        this.success = success;
    }
}
