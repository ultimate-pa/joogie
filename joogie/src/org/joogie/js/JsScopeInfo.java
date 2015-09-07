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

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.statements.AssumeStatement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.js.factories.JsOperatorFunctionFactory;
import org.joogie.js.factories.JsVariableFactory;
import org.mozilla.javascript.Token;

/**
 * 
 * @author schaef
 * 
 */
public class JsScopeInfo {

	public BoogieProcedure containingProcedure = null;

	public BasicBlock currentCatchBlock = null;
	
	/*
	 * when we run into a finally-block, we have to create a helper variable
	 * and some enumerator variable that number. Each time we jump into the
	 * finally, we set this enumerator variable to a unique value and add a
	 * goto to the finally block. Then, we add a conditional choice to the
	 * finally-exit checking if the enumerator variable has this specific value
	 * and if so jump back to where the flow should go. 
	 */
	public BasicBlock currentFinallyBlock = null;
	public BasicBlock currentFinallyExitBlock = null;
	public Variable currentFinallyVariable = null;
	
	private int finallyEnumerator = 0;
		
	public void connectToFinally(BasicBlock current, BasicBlock next) {
		//TODO: the creation of the finally-variable
		//should be somewhere else. We also need a
		//LocationTag for all the stuff created in ths method.
		if (this.currentFinallyVariable==null) {
			if (this.containingProcedure!=null) {
				this.currentFinallyVariable = JsVariableFactory.v()
						.getFreshLocal(BoogieBaseTypes.getRefType(), this.containingProcedure);
			} else {
				//TODO: not sure if this can happen anyway
				this.currentFinallyVariable = JsVariableFactory.v()
						.getFreshGlobal(BoogieBaseTypes.getRefType());
			}
		}
		
		AssignStatement assign = new AssignStatement(this.currentFinallyVariable, 
				new UboundedIntConstant((long)(++this.finallyEnumerator)) );
		current.addStatement(assign);
		
		BasicBlock jumpback = new BasicBlock();
		Expression condtrue = JsOperatorFunctionFactory.v().createBinOp(Token.EQ, this.currentFinallyVariable, 
				new UboundedIntConstant((long)(this.finallyEnumerator)));
		jumpback.addStatement(new AssumeStatement(condtrue));
		jumpback.connectToSuccessor(next);
		
		BasicBlock dontjump = new BasicBlock();
		Expression condfalse = JsOperatorFunctionFactory.v().createBinOp(Token.NE, this.currentFinallyVariable, 
				new UboundedIntConstant((long)(this.finallyEnumerator)));
		dontjump.addStatement(new AssumeStatement(condfalse));
		
		for (BasicBlock b : this.currentFinallyExitBlock.Successors) {
			dontjump.Successors.add(b);
		}
		currentFinallyExitBlock.Successors.clear();		
		currentFinallyExitBlock.Successors.add(jumpback);
		currentFinallyExitBlock.Successors.add(dontjump);
		//TODO: again, this is untested!
	}
	
}
