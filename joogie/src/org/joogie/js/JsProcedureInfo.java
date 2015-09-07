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

import java.util.HashMap;

import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.expressions.Variable;
import org.joogie.js.factories.JsBoogieTypeFactory;
import org.mozilla.javascript.ast.FunctionNode;
import org.mozilla.javascript.ast.Name;

/**
 * 
 * @author schaef
 * 
 */
public class JsProcedureInfo {

	private FunctionNode functionNode;
	private BoogieProcedure procedure;

	private HashMap<Name, Variable> localMap = new HashMap<Name, Variable>();

	public JsProcedureInfo(FunctionNode fnode, BoogieProcedure proc) {
		this.functionNode = fnode;
		this.procedure = proc;
	}

	public Variable lookupLocal(Name local) {
		if (!this.localMap.containsKey(local)) {
			Variable tmp = new Variable(
					JsTranslationHelper.getBoogieFriendlyVarName(local
							.getIdentifier()), JsBoogieTypeFactory
							.v().translateJsType(local.getType()));
			this.localMap.put(local, tmp);
			this.procedure.addLocal(tmp);
		}
		return this.localMap.get(local);
	}

}
