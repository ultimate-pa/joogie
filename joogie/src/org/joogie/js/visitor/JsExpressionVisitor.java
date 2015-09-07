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

package org.joogie.js.visitor;

import java.util.LinkedList;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.js.JsGlobalsCache;
import org.joogie.js.JsScopeInfo;
import org.joogie.js.exception.JsNotNormalizedException;
import org.joogie.js.factories.JsConstantFactory;
import org.joogie.js.factories.JsOperatorFunctionFactory;
import org.joogie.js.factories.JsVariableFactory;
import org.mozilla.javascript.Token;
import org.mozilla.javascript.ast.ArrayLiteral;
import org.mozilla.javascript.ast.AstNode;
import org.mozilla.javascript.ast.Block;
import org.mozilla.javascript.ast.ElementGet;
import org.mozilla.javascript.ast.FunctionCall;
import org.mozilla.javascript.ast.FunctionNode;
import org.mozilla.javascript.ast.InfixExpression;
import org.mozilla.javascript.ast.KeywordLiteral;
import org.mozilla.javascript.ast.Name;
import org.mozilla.javascript.ast.NodeVisitor;
import org.mozilla.javascript.ast.NumberLiteral;
import org.mozilla.javascript.ast.ObjectLiteral;
import org.mozilla.javascript.ast.RegExpLiteral;
import org.mozilla.javascript.ast.StringLiteral;
import org.mozilla.javascript.ast.UnaryExpression;

/**
 * @author schaef
 */
public class JsExpressionVisitor implements NodeVisitor {

	private BoogieProcedure currentProcedure = null;

	private JsScopeInfo currentScope = null;
	
	private Expression expression = null;
	
	private LinkedList<Statement> guardingStatements = new LinkedList<Statement>();

	

	public JsExpressionVisitor(JsScopeInfo scope) {
		currentProcedure=scope.containingProcedure;
		currentScope = scope;
	}
	
	
	public Expression getExpression() {
		return expression;
	}
	
	public LinkedList<Statement> getGuardingStatements() {
		LinkedList<Statement> ret = guardingStatements;
		guardingStatements = new LinkedList<Statement>();
		return ret;
	}
	
	
	@Override
	public boolean visit(AstNode node) {

		if (node instanceof FunctionCall) {
			// is expression...
			// in normalized code only as x=f()
			// if f() is void, it returns Undefined ...
			FunctionCall exp = (FunctionCall) node;
			JsExpressionVisitor jevFun = new JsExpressionVisitor(this.currentScope);
			jevFun.visit(exp.getTarget());
			this.guardingStatements.addAll(jevFun.getGuardingStatements());				
				
			LinkedList<Expression> argExpr = new LinkedList<Expression>();
			for (AstNode arg : exp.getArguments()) {
				JsExpressionVisitor jevArg = new JsExpressionVisitor(this.currentScope);
				jevArg.visit(arg);
				this.guardingStatements.addAll(jevArg.getGuardingStatements());
				argExpr.addLast(jevArg.getExpression());
			}
			

			if (exp.getTarget() instanceof ElementGet) {
				//TODO: I have no idea how to model the fact that a name
				//variable could be a boogie procedure. just putting
				//an invoke statement here will not work. Maybe we have to
				//maintain a table to look up if we know for sure that this
				//is a function and then insert the function. Otherwise, i.e.,
				//if this function variable has been written more than once,
				//we basically have to havoc everything.
				ElementGet eget = (ElementGet)exp.getTarget();
				JsExpressionVisitor jeveget = new JsExpressionVisitor(this.currentScope);
				jeveget.visit(eget.getElement());
				this.guardingStatements.addAll(jeveget.getGuardingStatements());
				//TODO: here, we can assume that jeveget.expression is a heap access
				//and we have to assert that the field to referes to is actually
				//a function.
				
				this.expression = JsVariableFactory.v().getFreshGlobal(BoogieBaseTypes.getRefType());
			} else if (exp.getTarget() instanceof Name) {
				//TODO: I have no idea how to model the fact that a name
				//variable could be a boogie procedure. just putting
				//an invoke statement here will not work. Maybe we have to
				//maintain a table to look up if we know for sure that this
				//is a function and then insert the function. Otherwise, i.e.,
				//if this function variable has been written more than once,
				//we basically have to havoc everythin.
				this.expression = JsVariableFactory.v().getFreshGlobal(BoogieBaseTypes.getRefType());
			} else {
				throw new JsNotNormalizedException(exp.getTarget() ,
						"You have to run the js normalizer first");				
			}
			
			
			return false;
		} else if (node instanceof InfixExpression) {
			InfixExpression exp = (InfixExpression) node;
			JsExpressionVisitor jevLeft = new JsExpressionVisitor(this.currentScope);
			jevLeft.visit(exp.getLeft());
			JsExpressionVisitor jevRight = new JsExpressionVisitor(this.currentScope);
			jevRight.visit(exp.getRight());
			this.guardingStatements.addAll(jevLeft.getGuardingStatements());
			this.guardingStatements.addAll(jevRight.getGuardingStatements());
			this.expression = JsOperatorFunctionFactory.v()
					.createBinOp(exp.getOperator(), jevLeft.getExpression(), jevRight.getExpression());
			return false;
		} else if (node instanceof KeywordLiteral) {
			KeywordLiteral kwl = (KeywordLiteral) node;
			Expression constant = null;
			if (kwl.getType() == Token.DEBUGGER) {
				throw new JsNotNormalizedException(node);
			} else if (kwl.getType() == Token.THIS) {
				constant = currentProcedure.getThisVariable();
			} else if (kwl.getType() == Token.NULL) {
				constant = JsConstantFactory.v().getNullConstant();
			} else if (kwl.getType() == Token.TRUE) {
				constant = JsConstantFactory.v().getBooleanConstant(true);
			} else if (kwl.getType() == Token.FALSE) {
				constant = JsConstantFactory.v().getBooleanConstant(false);
			}
			this.expression = constant;
			return false;
		} else if (node instanceof Name) {
			// locals
			Name exp = (Name) node;
			//TODO: how can I identify if this is a local or a global?
			if (this.currentProcedure!=null && !JsGlobalsCache.v().isGlobalVariable(exp)) {
				//TODO: for some reason __global shows up in the set of local variables
				this.expression = JsGlobalsCache.v().lookupLocalVariable(this.currentProcedure, exp);
			} else {
				this.expression = JsGlobalsCache.v().lookupGlobalVariable(exp);				
			}
			return false;
		} else if (node instanceof ArrayLiteral) {
			throw new JsNotNormalizedException("ArrayLiteral is handled in the statement section");
		} else if (node instanceof NumberLiteral) {
			NumberLiteral exp = (NumberLiteral) node;
			this.expression = JsConstantFactory.v()
					.getNumberLiteralConstant(exp);
			return false;
		} else if (node instanceof ObjectLiteral) {			
			throw new JsNotNormalizedException("ObjectLiteral is handled in the statement section");
		} else if (node instanceof RegExpLiteral) {
			RegExpLiteral exp = (RegExpLiteral) node;
			//TODO: we treat regular expressions just
			//like strings. That is not really precise
			//but I don't think that it's worth the
			//effort to be more precise here.
			this.expression = JsConstantFactory.v()
					.getStringLiteralConstant(exp.getFlags());
			//TODO: assert that this.expression has a certain length
			return false;
			
		} else if (node instanceof StringLiteral) {
			StringLiteral exp = (StringLiteral) node;
			this.expression = JsConstantFactory.v()
					.getStringLiteralConstant(exp.getValue() );
			//TODO: assert that this.expression has a certain length			
			return false;
		} else if (node instanceof UnaryExpression) {
			UnaryExpression exp = (UnaryExpression) node;
			//Log.error("Unop: " + exp.getOperator());
			JsExpressionVisitor jev = new JsExpressionVisitor(this.currentScope);
			jev.visit(exp.getOperand());
			this.guardingStatements.addAll(jev.getGuardingStatements());
			this.expression = JsOperatorFunctionFactory.v()
					.createUnOp(exp.getOperator(), jev.getExpression());
			return false;
		} else if (node instanceof FunctionNode) {
			FunctionNode exp = (FunctionNode) node;			
			translateFunctionNode(exp);
		} else if (node instanceof ElementGet) {
			ElementGet exp = (ElementGet) node;
			JsExpressionVisitor jevTarget = new JsExpressionVisitor(this.currentScope);
			jevTarget.visit(exp.getTarget());
			this.guardingStatements.addAll(jevTarget.getGuardingStatements());			
			JsExpressionVisitor jevElement = new JsExpressionVisitor(this.currentScope);
			jevElement.visit(exp.getElement());
			this.guardingStatements.addAll(jevElement.getGuardingStatements());

			Expression base = jevTarget.getExpression();
			Expression idx = jevElement.getExpression();

			this.guardingStatements.addAll(JsGlobalsCache.v().createMemoryAccessAssertions(base, idx));
			this.expression =  JsGlobalsCache.v().createMemoryAccess(base, idx);
			
			return false;
		} else {
			throw new JsNotNormalizedException(node,
					"You have to run the js normalizer first");
		}
		return false;
	}

	/**
	 * A function node is when we have to declare a new BoogieProcedure
	 * @param fun
	 */
	private void translateFunctionNode(FunctionNode fun) {
		//TODO: review if tmpvar is supposed to be global or local
		//TODO: we need a function type. tmpvar cannot be of reftype
		Variable tmpvar = JsVariableFactory.v().getFreshGlobal(BoogieBaseTypes.getRefType());
		
		//THIS IS THE IMPORTANT LINE
		this.expression = tmpvar;
		
		
		BoogieProcedure proc = JsGlobalsCache.v().lookUpProcedure(tmpvar, fun);

		proc.setJavaName("generated:"+proc.getName());
		
		if (!(fun.getBody() instanceof Block)) {
			throw new JsNotNormalizedException("CRASH!");
		}
		Block funbody = (Block) fun.getBody();	
		
		BasicBlock newroot = new BasicBlock();
		JsScopeInfo newScope = new JsScopeInfo();
		newScope.containingProcedure = proc;
		newScope.currentCatchBlock = null;
		JsStatementVisitor jsv = new JsStatementVisitor(newScope, newroot, false);
		jsv.visit(funbody);
		proc.setBodyRoot(newroot);
		//proc.setExitBlock(jsv.getCurrentBlock());
		
	}
	
}
