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

import org.joogie.boogie.LocationTag;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.statements.AssertStatement;
import org.joogie.boogie.statements.AssumeStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.js.exception.JsNotNormalizedException;
import org.joogie.js.factories.JsConstantFactory;
import org.joogie.js.factories.JsOperatorFunctionFactory;
import org.mozilla.javascript.Token;
import org.mozilla.javascript.ast.AstNode;

/**
 * 
 * @author schaef
 * 
 */
public class JsTranslationHelper {

	/**
	 * 
	 * @param e
	 * @param negateE
	 * @return
	 */
	public static AssumeStatement createAssumeStatement(Expression e,
			LocationTag tag, boolean negateE) {
		int token = Token.EQ;
		if (negateE) {
			token = Token.NE;
		}
		Expression assme = JsOperatorFunctionFactory.v().createBinOp(
				token, e, JsConstantFactory.v().getNullConstant());
		AssumeStatement assumption = new AssumeStatement(assme);
		assumption.setLocationTag(tag);
		return assumption;
	}

	/**
	 * creates an assertion statement for e!=null
	 * 
	 * @param e
	 * @return
	 */
	public static Statement assertNonNull(Expression e, LocationTag tag) {
		Expression assrt = JsOperatorFunctionFactory.v().createBinOp(
				Token.NE, e, JsConstantFactory.v().getNullConstant());
		AssertStatement assertion = new AssertStatement(assrt);
		assertion.setLocationTag(tag);
		return assertion;
	}

	/**
	 * creates an assertion statement for e==null
	 * 
	 * @param e
	 * @return
	 */
	public static Statement assertIsNull(Expression e, LocationTag tag) {
		Expression assrt = JsOperatorFunctionFactory.v().createBinOp(
				Token.EQ, e, JsConstantFactory.v().getNullConstant());
		AssertStatement assertion = new AssertStatement(assrt);
		assertion.setLocationTag(tag);
		return assertion;
	}

	/**
	 * creates an assertion statement for lower<=arr<upper
	 * 
	 * @param idx
	 *            the arry index that is to be guarded
	 * @return
	 */
	public static Statement assertInBounds(Expression idx, Expression upper,
			Expression lower) {
		throw new JsNotNormalizedException("not implemented");
	}

	/**
	 * creates an assertion statement for 0<=arr<upper
	 * 
	 * @param idx
	 *            the arry index that is to be guarded
	 * @return
	 */
	public static Statement assertInBounds(Expression idx, Expression upper) {
		return assertInBounds(idx, upper, new UboundedIntConstant(0L));
	}

	public static LocationTag computeLocationTag(AstNode node) {
		int line = node.getLineno();
		int offset = node.getPosition();
		int absoffset = node.getAbsolutePosition();
		int length = node.getLength();
		String comment = "line:" + line + "/offset:" + offset + "/absoffset:"
				+ absoffset + "/length" + length;
		if (node.getJsDocNode() != null) {
			comment += node.getJsDocNode().getValue();
		}
		return new LocationTag(new StringBuilder(comment), line);
	}

	public static String getBoogieFriendlyVarName(String varname) {
		// TODO: implement
		return varname;
	}

}
