/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.tests;

import java.io.IOException;
import java.io.StringReader;

import org.joogie.js.JsTranslator;

import org.mozilla.javascript.CompilerEnvirons;
import org.mozilla.javascript.Context;
import org.mozilla.javascript.ErrorReporter;
import org.mozilla.javascript.EvaluatorException;
import org.mozilla.javascript.Parser;
import org.mozilla.javascript.Token;
import org.mozilla.javascript.ast.AstNode;
import org.mozilla.javascript.ast.AstRoot;
import org.mozilla.javascript.ast.Name;
import org.mozilla.javascript.ast.NodeVisitor;

/**
 * @author schaef
 */
public class JSTest {

	/**
	 * @param args
	 * @throws IOException
	 */
	public static void main(String[] args) throws IOException {
		if (args.length == 0) {
			System.err.println("please specify normalized js file");
			return;
		}
		
		JsTranslator jst = new JsTranslator();
		jst.translateJs(args[0]);

		// String demoString =
		// "(function(__global) { alert('Hello, world!'); })(this);";
		// debugPrintJs(demoString);
	}

	/*
	 * From here on it's only debug printing code.
	 */

	protected static void debugPrintJs(String input) {
		StringReader testinput = new StringReader(input);
		Context ctx = Context.enter();
		ctx.initStandardObjects();
		CompilerEnvirons compenv = new CompilerEnvirons();
		compenv.initFromContext(ctx);
		Parser p = new Parser(compenv, new ErrorReporter() {

			@Override
			public void warning(String message, String sourceName, int line,
					String lineSource, int lineOffset) {
				System.err.println(message);
			}

			@Override
			public EvaluatorException runtimeError(String message,
					String sourceName, int line, String lineSource,
					int lineOffset) {
				System.err.println(message);
				return null;
			}

			@Override
			public void error(String message, String sourceName, int line,
					String lineSource, int lineOffset) {
				System.err.println(message);
			}
		});

		StringBuilder buf = new StringBuilder();
		AstRoot ast;
		try {
			ast = p.parse(testinput, "", 1);
			ast.visit(new DebugPrintVisitor(buf));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		System.out.println(buf);
	}

	protected static class DebugPrintVisitor implements NodeVisitor {
		private StringBuilder buffer;
		private static final int DEBUG_INDENT = 2;

		public DebugPrintVisitor(StringBuilder buf) {
			buffer = buf;
		}

		public String toString() {
			return buffer.toString();
		}

		private String makeIndent(int depth) {
			StringBuilder sb = new StringBuilder(DEBUG_INDENT * depth);
			for (int i = 0; i < (DEBUG_INDENT * depth); i++) {
				sb.append(" ");
			}
			return sb.toString();
		}

		public boolean visit(AstNode node) {
			int tt = node.getType();
			String name = Token.typeToName(tt);

			buffer.append(node.getAbsolutePosition()).append("\t");
			buffer.append(makeIndent(node.depth()));
			buffer.append(name).append(" ");
			buffer.append(node.getPosition()).append(" ");
			buffer.append(node.getLength());
			if (tt == Token.NAME) {
				buffer.append(" ").append(((Name) node).getIdentifier());
			}
			buffer.append("\n");
			return true; // process kids
		}
	}

}