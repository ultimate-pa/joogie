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

package org.joogie.js.exception;

import org.mozilla.javascript.ast.AstNode;

/**
 * @author schaef
 */
public class JsNotNormalizedException extends RuntimeException {

	private String msg = "";
	private AstNode astNode = null;

	public JsNotNormalizedException(AstNode node) {
		this.astNode = node;
	}

	public JsNotNormalizedException(AstNode node, String comment) {
		this.astNode = node;
		msg = comment;
	}

	public JsNotNormalizedException(String comment) {
		msg = comment;
	}

	@Override
	public String toString() {
		StringBuffer buf = new StringBuffer();
		buf.append("JsNotNormalizedException: ");
		if (this.astNode != null) {
			buf.append(this.astNode.toSource());
			buf.append(" token id: ");
			buf.append(this.astNode.getClass());
		} else {
			buf.append("node is null");
		}
		buf.append(" " + this.msg);
		return buf.toString();
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = -4960029498876424080L;

}
