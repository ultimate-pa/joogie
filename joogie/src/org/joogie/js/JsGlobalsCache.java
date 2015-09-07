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

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.SimpleHeapAccess;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.HeapType;
import org.joogie.js.factories.JsBoogieTypeFactory;
import org.mozilla.javascript.ast.AstNode;
import org.mozilla.javascript.ast.FunctionNode;
import org.mozilla.javascript.ast.Name;

/**
 * 
 * @author schaef
 * 
 */
public class JsGlobalsCache {

	public static JsGlobalsCache v() {
		if (instance == null) {
			instance = new JsGlobalsCache();
		}
		return instance;
	}

	public void resetInstance() {
		instance = null;
	}

	private static JsGlobalsCache instance = null;

	private JsGlobalsCache() {

	}

	private int counter = 0;

	public int getUniqueNumber() {
		return ++counter;
	}

	/**
	 * a map to check for which Label we have created a block already this is
	 * needed because every time we encounter a jump to label, we create a stub
	 * of a basic block, when we encounter a stmt labeled with this label, we
	 * reuse the stub.
	 */
	public HashMap<String, BasicBlock> labeledBlocks = new HashMap<String, BasicBlock>();

	private HashMap<FunctionNode, BoogieProcedure> procedureMap = new HashMap<FunctionNode, BoogieProcedure>();

	private HashMap<BoogieProcedure, JsProcedureInfo> procedureInfoMap = new HashMap<BoogieProcedure, JsProcedureInfo>();

	private HashMap<Name, Variable> globalVariables = new HashMap<Name, Variable>();

	public BoogieProcedure lookUpProcedure(Variable funvar, FunctionNode fun) {
		if (!procedureMap.containsKey(fun)) {
			String funname = funvar.getName();
			if (fun.getName() != null) {
				// TODO: something strange happened here
				funname += fun.getName();
			}

			BoogieType rettype = JsBoogieTypeFactory.v()
					.translateJsType(fun.getFunctionType());
			LinkedList<BoogieType> parameters = new LinkedList<BoogieType>();
			for (AstNode node : fun.getParams()) {
				// TODO:
				parameters.add(BoogieBaseTypes.getRefType());
			}
			// TODO: no exception analysis yet.
			BoogieProcedure proc = new BoogieProcedure(funname, rettype,
					JsTranslationHelper.computeLocationTag(fun), funname,
					parameters);
			procedureMap.put(fun, proc);
			// add the procedure to the program
			BoogieProgram.v().addProcedure(proc);
			// create procedure infos
			procedureInfoMap.put(proc, new JsProcedureInfo(fun, proc));
		}
		return procedureMap.get(fun);
	}

	public Variable lookupLocalVariable(BoogieProcedure proc, Name varname) {
		return procedureInfoMap.get(proc).lookupLocal(varname);
	}

	
	public boolean isGlobalVariable(Name var) {
		return globalVariables.containsKey(var);
	}
	
	public Variable lookupGlobalVariable(Name var) {
		if (!globalVariables.containsKey(var)) {
			Variable tmp = new Variable(
					JsTranslationHelper.getBoogieFriendlyVarName(var
							.getIdentifier()), JsBoogieTypeFactory
							.v().translateJsType(var.getType()));
			globalVariables.put(var, tmp);
			BoogieProgram.v().addGlobalVar(tmp);
		}
		return this.globalVariables.get(var);
	}

	public Variable getHeapVariable() {
		//TODO: the heap variable should not be in the boogie program
		//as the boogie program shouldn't know anything about it's 
		//underlying memory model
		return BoogieProgram.v().heapVariable;
	}
	
	public void setHeapVariable(Name heapVarName) {
		BoogieProgram prog = BoogieProgram.v();
		prog.heapVariable = new Variable(
				JsTranslationHelper.getBoogieFriendlyVarName(heapVarName.getIdentifier()), 
						new HeapType());
		globalVariables.put(heapVarName, prog.heapVariable);
	}
	
	private Variable nullVariable = null;
	private Variable undefinedVariable = null;

	public Variable getNullVariable() {
		if (this.nullVariable == null) {
			this.nullVariable = new Variable("$null",
					BoogieBaseTypes.getRefType(), true);
			BoogieProgram.v().addGlobalVar(nullVariable);
		}
		return this.nullVariable;
	}

	public Variable getUndefinedVariable() {
		if (this.undefinedVariable == null) {
			this.undefinedVariable = new Variable("$undefined",
					BoogieBaseTypes.getRefType(), true);
			BoogieProgram.v().addGlobalVar(undefinedVariable);
		}
		return this.undefinedVariable;
	}

	
	/*
	 */
	public Collection<Statement> createMemoryAccessAssertions(Expression base, Expression idx) {
		LinkedList<Statement> asserts = new LinkedList<Statement>();
		//TODO: implement
		return asserts;
	}
	
	/*
	 * TODO: does this work for arrays and heap access?
	 * TODO: the in-bounds, and is-defined assertions should be created here!
	 */
	public Expression createMemoryAccess(Expression base, Expression idx) {
		return new SimpleHeapAccess(base, idx);
	}
	
}
