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

package org.joogie.js;

import java.util.List;

import normalizer.Normalizer;

import org.joogie.js.exception.JsNotNormalizedException;
import org.joogie.js.visitor.JsStatementVisitor;
import org.joogie.util.Log;
import org.mozilla.javascript.CompilerEnvirons;
import org.mozilla.javascript.Context;
import org.mozilla.javascript.ErrorReporter;
import org.mozilla.javascript.EvaluatorException;
import org.mozilla.javascript.Parser;
import org.mozilla.javascript.ast.AstNode;
import org.mozilla.javascript.ast.AstRoot;
import org.mozilla.javascript.ast.Block;
import org.mozilla.javascript.ast.ExpressionStatement;
import org.mozilla.javascript.ast.FunctionCall;
import org.mozilla.javascript.ast.FunctionNode;
import org.mozilla.javascript.ast.Name;
import org.mozilla.javascript.ast.ParenthesizedExpression;

/**
 * 
 * @author schaef
 * 
 */
public class JsTranslator {

	private Name globalHeapVar = null;

	public void translateJs(String input) {
		// normalize java script
		String content = Normalizer.normalize(input);

		AstNode root = getRealJsRootNode(content);
		Log.error("Your global heapvar is: "
				+ this.globalHeapVar.getIdentifier());
		// TODO: this is not the right type and probably too simple
		JsGlobalsCache.v().setHeapVariable(globalHeapVar);
		
		if (!(root instanceof Block)) {
			throw new JsNotNormalizedException("CRASH!");
		}
		Block rootBlock = (Block) root;
		JsStatementVisitor visitTopLevel = new JsStatementVisitor(
				new JsScopeInfo());
		visitTopLevel.visit(rootBlock);

		// TODO: collect data from the global visitor
		//this, in particular concerns top level statements
		//that are not function declarations, as these statements
		//do not show up in the boogie program right now.
		//probably it would be best to collect all of them and put
		//them into a special booige procedure...
	}

	private AstNode getRealJsRootNode(String content) {
		AstNode root = null;

		Context ctx = Context.enter();
		ctx.initStandardObjects();
		CompilerEnvirons compenv = new CompilerEnvirons();
		compenv.initFromContext(ctx);
		Parser p = new Parser(compenv, new ErrorReporter() {

			@Override
			public void warning(String message, String sourceName, int line,
					String lineSource, int lineOffset) {
				throw new JsNotNormalizedException("Rhino parser: " + message);
			}

			@Override
			public EvaluatorException runtimeError(String message,
					String sourceName, int line, String lineSource,
					int lineOffset) {
				throw new JsNotNormalizedException("Rhino parser: " + message);
			}

			@Override
			public void error(String message, String sourceName, int line,
					String lineSource, int lineOffset) {
				throw new JsNotNormalizedException("Rhino parser: " + message);
			}
		});

		try {
			AstRoot ast = p.parse(content, "", 1);

			/*
			 * Read the default code used by the normalizer to wrap the js
			 * procedures into a program.
			 */
			List<AstNode> statements = ast.getStatements();
			if (statements.size() != 1) {
				throw new JsNotNormalizedException(
						"Not normalized, cannot start translation!");
			}
			AstNode node = statements.get(0);
			if (!(node instanceof ExpressionStatement)) {
				throw new JsNotNormalizedException(node,
						"Not normalized, cannot start translation!");
			}
			ExpressionStatement exp = (ExpressionStatement) node;
			AstNode expression = exp.getExpression();

			if (!(expression instanceof ParenthesizedExpression)) {
				throw new JsNotNormalizedException(node,
						"Not normalized, cannot start translation!");
			}
			ParenthesizedExpression para = (ParenthesizedExpression) expression;
			AstNode paraexp = para.getExpression();
			if (!(paraexp instanceof FunctionCall)) {
				throw new JsNotNormalizedException(paraexp,
						"Not normalized, cannot start translation!");
			}

			FunctionCall funcall = (FunctionCall) paraexp;
			AstNode target = funcall.getTarget();
			if (!(target instanceof FunctionNode)) {
				throw new JsNotNormalizedException(target,
						"Not normalized, cannot start translation!");
			}

			FunctionNode funnode = (FunctionNode) target;

			/*
			 * TODO: improve comment this must be the global heap variable
			 * introduced by the normalizer
			 */
			List<AstNode> params = funnode.getParams();
			if (params.size() != 1) {
				throw new JsNotNormalizedException(
						"Not normalized, cannot start translation!");
			}
			AstNode heapVar = params.get(0);
			if (!(heapVar instanceof Name)) {
				throw new JsNotNormalizedException(
						"Not normalized, cannot start translation!");
			}
			/*
			 * if we reach here, we have successfully identified all global
			 * statements and can start the translation
			 */
			this.globalHeapVar = (Name) heapVar;
			root = funnode.getBody();
		} catch (JsNotNormalizedException e) {
			// TODO: the program was not normalized and we have to roll back
			Log.error(e.toString());
		} catch (Exception e) {
			// TODO: something else happened and we didn't consider that yet.
			Log.error(e.toString());
		}
		return root;
	}

}
