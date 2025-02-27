/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import antlr.Token;

public class JavaParserException extends antlr.SemanticException {

    /**
     *
     */
    private static final long serialVersionUID = 3858933208298220420L;
    String cat;
    String filename;
    String jb;

    public JavaParserException(String cat, Token t, String filename, int lineOffset,
            int colOffset) {
        super("JavaParser");
        this.cat = cat;
        this.jb = t.getText();
        this.filename = filename;
        this.line = (lineOffset >= 0) ? t.getLine() + lineOffset : 0;
        this.column = (colOffset >= 0) ? t.getColumn() + colOffset : 0;
    }

    public JavaParserException(Throwable e, Token t, String filename, int lineOffset,
            int colOffset) {
        this(e.getMessage(), t, filename, lineOffset, colOffset);
        initCause(e);
    }


    public JavaParserException(String cat, Token t, String filename) {
        super("JavaParser");
        this.cat = cat;
        this.jb = t.getText();
        this.filename = filename;
        this.line = t.getLine();
        this.column = t.getColumn();

    }

    public JavaParserException(String message) {
        super(message);
    }

    public JavaParserException(Throwable e, Token t, String filename) {
        this(e.getMessage(), t, filename);
        initCause(e);
    }

    public String getFilename() {
        return filename;
    }

    public int getLine() {
        return line;
    }

    public int getColumn() {
        return column;
    }

    /**
     * Returns a clean error message (no line number/column information)
     *
     * @deprecated
     */
    @Deprecated
    public String getErrorMessage() {
        return getMessage();
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getMessage() {
        return cat;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return filename + "(" + this.getLine() + ", " + this.getColumn() + "): " + getMessage();
    }
}
