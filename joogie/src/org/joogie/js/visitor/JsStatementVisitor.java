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

import java.util.Collection;
import java.util.HashSet;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.statements.AssumeStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.js.JsGlobalsCache;
import org.joogie.js.JsScopeInfo;
import org.joogie.js.JsTranslationHelper;
import org.joogie.js.exception.JsNotNormalizedException;
import org.joogie.js.factories.JsConstantFactory;
import org.joogie.js.factories.JsOperatorFunctionFactory;
import org.joogie.js.factories.JsVariableFactory;
import org.mozilla.javascript.Node;
import org.mozilla.javascript.Token;
import org.mozilla.javascript.ast.ArrayLiteral;
import org.mozilla.javascript.ast.Assignment;
import org.mozilla.javascript.ast.AstNode;
import org.mozilla.javascript.ast.Block;
import org.mozilla.javascript.ast.BreakStatement;
import org.mozilla.javascript.ast.CatchClause;
import org.mozilla.javascript.ast.EmptyStatement;
import org.mozilla.javascript.ast.ExpressionStatement;
import org.mozilla.javascript.ast.ForInLoop;
import org.mozilla.javascript.ast.FunctionCall;
import org.mozilla.javascript.ast.IfStatement;
import org.mozilla.javascript.ast.KeywordLiteral;
import org.mozilla.javascript.ast.Label;
import org.mozilla.javascript.ast.LabeledStatement;
import org.mozilla.javascript.ast.NodeVisitor;
import org.mozilla.javascript.ast.ObjectLiteral;
import org.mozilla.javascript.ast.ObjectProperty;
import org.mozilla.javascript.ast.PropertyGet;
import org.mozilla.javascript.ast.ReturnStatement;
import org.mozilla.javascript.ast.Scope;
import org.mozilla.javascript.ast.ThrowStatement;
import org.mozilla.javascript.ast.TryStatement;
import org.mozilla.javascript.ast.VariableDeclaration;
import org.mozilla.javascript.ast.VariableInitializer;
import org.mozilla.javascript.ast.WhileLoop;

/**
 * @author schaef
 */
public class JsStatementVisitor implements NodeVisitor {
	
	private BasicBlock currentBlock = null;
	
	private JsScopeInfo currentScope = null;
	
	private BoogieProcedure currentProcedure = null;

	public JsStatementVisitor(JsScopeInfo scope) {
		currentBlock = new BasicBlock();
		this.currentProcedure = scope.containingProcedure;
		this.currentScope = scope;
	}
		
	public JsStatementVisitor(JsScopeInfo scope, BasicBlock current, boolean createNewBlock) {
		if (createNewBlock) {
			this.currentBlock = new BasicBlock();
			current.connectToSuccessor(this.currentBlock);
		} else {
			this.currentBlock = current;
		}
		this.currentScope = scope;
		this.currentProcedure = scope.containingProcedure;
	}
	
	
	public BasicBlock getCurrentBlock() {
		return this.currentBlock;
	}
	
	@Override
	public boolean visit(AstNode node) {

		if (node instanceof Block || node instanceof Scope) {
			translateSequence(node);
		} else if (node instanceof CatchClause) {
			// only after try and not with finally
			CatchClause stmt = (CatchClause) node;
			translateCatchClause(stmt);
		} else if (node instanceof EmptyStatement) {
			// e.g., empty else branch
		} else if (node instanceof ExpressionStatement) {
			// e.g. assignment
			ExpressionStatement stmt = (ExpressionStatement) node;
			AstNode expNode = stmt.getExpression();
			if (expNode instanceof Assignment) {
				Assignment assn = (Assignment) expNode;
				translateAssignment(assn);
			} else if (expNode instanceof PropertyGet) {
				PropertyGet propget = (PropertyGet) expNode;
				JsExpressionVisitor jevTarget = new JsExpressionVisitor(this.currentScope);
				jevTarget.visit(propget.getTarget());				
				JsExpressionVisitor jevProp = new JsExpressionVisitor(this.currentScope);
				jevProp.visit(propget.getProperty());

				//TODO: what can we do with a PropertyGet?
				//base has to be defined, idx has to be in bounds, etc.
				Expression base = jevTarget.getExpression();
				Expression idx = jevProp.getExpression();
				addStatements(this.currentBlock, JsGlobalsCache.v().createMemoryAccessAssertions(base, idx));

				/*
				 * NOTE: there is no need to add a statement here, as the PropertyGet does not
				 * change the state of the execution if it stands by itself and not in an assignment
				 */

			} else if (expNode instanceof FunctionCall) {
				throw new JsNotNormalizedException(expNode,
						"Not normalized, cannot transtlate call without lefthand side.");
			} else {
				throw new JsNotNormalizedException(node);
			}

		} else if (node instanceof IfStatement) {
			IfStatement stmt = (IfStatement) node;
			if (stmt.getThenPart() == null || stmt.getElsePart() == null) {
				throw new JsNotNormalizedException(stmt,
						"Not normalized, branches cannot be null.");
			}
			//translate the branching condition
			JsExpressionVisitor jev = new JsExpressionVisitor(this.currentScope);
			jev.visit(stmt.getCondition());
			Expression cond = jev.getExpression();
			//if there are any guards that need to hold when evaluating
			//the condition, add them to the previous block.
			addStatements(this.currentBlock, jev.getGuardingStatements());
			// add the branching condition cond to the new then-block
			BasicBlock thenBlock = new BasicBlock(); 
			addStatement(thenBlock, 
					JsTranslationHelper.createAssumeStatement(cond,
							JsTranslationHelper.computeLocationTag(stmt.getCondition())
							,false), 
					false);
			this.currentBlock.connectToSuccessor(thenBlock);
			JsStatementVisitor jsvThen = new JsStatementVisitor(this.currentScope, thenBlock, false);
			// visit the then block
			jsvThen.visit(stmt.getThenPart());

			//same story for the else-block
			BasicBlock elseBlock = new BasicBlock();  
			addStatement(elseBlock, 
					JsTranslationHelper.createAssumeStatement(cond, 
							JsTranslationHelper.computeLocationTag(stmt.getCondition())
							, true), 
					false);
			
			this.currentBlock.connectToSuccessor(elseBlock);	
			JsStatementVisitor jsvElse = new JsStatementVisitor(this.currentScope, elseBlock, false);
			jsvElse.visit(stmt.getElsePart());
			//create a join after the if-then-else 
			//BUT: only if the branches do not return
			this.currentBlock = new BasicBlock();
			if (jsvThen.getCurrentBlock().Successors.size()==0) {
				jsvThen.getCurrentBlock().connectToSuccessor(this.currentBlock);
			}
			if (jsvElse.getCurrentBlock().Successors.size()==0) {
				jsvElse.getCurrentBlock().connectToSuccessor(this.currentBlock);
			}
		} else if (node instanceof BreakStatement) {
			// is actually goto
			BreakStatement stmt = (BreakStatement)node;
			if (!JsGlobalsCache.v()
					.labeledBlocks.containsKey(stmt.getBreakLabel())) {
				JsGlobalsCache.v().labeledBlocks
					.put(stmt.getBreakLabel().getIdentifier(), new BasicBlock());
			}
			currentBlock.connectToSuccessor(JsGlobalsCache.v()
					.labeledBlocks.get(stmt.getBreakLabel()));
			//TODO: check if we have to create a new BasicBlock here
			//or if the normalization guarantees us that no statement
			//will follow the break
		} else if (node instanceof ForInLoop) {
			//for now, it is visited but not added to the boogie program
			ForInLoop stmt = (ForInLoop) node;
			// translate the iterated object
			JsExpressionVisitor jevItObject = new JsExpressionVisitor(this.currentScope);
			jevItObject.visit(stmt.getIteratedObject());
			addStatements(this.currentBlock, jevItObject.getGuardingStatements());
			// translate the iterator
			JsExpressionVisitor jevIterator = new JsExpressionVisitor(this.currentScope);
			jevIterator.visit(stmt.getIterator());
			addStatements(this.currentBlock, jevIterator.getGuardingStatements());
			// translate the loop body
			BasicBlock loopHead = new BasicBlock();
			//TODO: add the condition the block
			JsStatementVisitor jsvBody = new JsStatementVisitor(this.currentScope, loopHead, false);
			jsvBody.visit(stmt.getBody());
			//close the loop
			jsvBody.getCurrentBlock().connectToSuccessor(loopHead);			
			// Now build the loop exit			
			BasicBlock loopExit = new BasicBlock();
			//Now add the loop exit conditional
			//TODO: this is not implemented yet
			Variable __tmp = JsVariableFactory.v().getFreshGlobal(BoogieBaseTypes.getIntType());
			Expression pos = JsOperatorFunctionFactory.v().createBinOp(Token.EQ, __tmp, new UboundedIntConstant(42L));
			Expression neg = JsOperatorFunctionFactory.v().createBinOp(Token.NE, __tmp, new UboundedIntConstant(42L));
			addStatement(loopHead, new AssumeStatement(pos), true);
			addStatement(loopExit, new AssumeStatement(neg), true);
			//connect everything.
			this.currentBlock.connectToSuccessor(loopHead);
			this.currentBlock.connectToSuccessor(loopExit);
			this.currentBlock = loopExit;
		} else if (node instanceof WhileLoop) {
			WhileLoop stmt = (WhileLoop) node;
			// translate the iterator
			JsExpressionVisitor jevConditional = new JsExpressionVisitor(this.currentScope);
			jevConditional.visit(stmt.getCondition());
			addStatements(this.currentBlock, jevConditional.getGuardingStatements());
			Expression loopCond = jevConditional.getExpression();
			// translate the loop body
			BasicBlock loopHead = new BasicBlock(JsTranslationHelper.computeLocationTag(stmt.getBody()));
			//add an assumption that the loop condition holds when entering the loop body
			Expression loopentrycond = JsOperatorFunctionFactory.v()
					.createBinOp(Token.EQ, loopCond, 
							JsConstantFactory.v().getBooleanConstant(true)
							);
			AssumeStatement loopentry = new AssumeStatement(loopentrycond);
			loopentry.setLocationTag(JsTranslationHelper.computeLocationTag(stmt.getBody()));
			addStatement(loopHead, loopentry, true); 
			JsStatementVisitor jsvBody = new JsStatementVisitor(this.currentScope, loopHead, false);
			jsvBody.visit(stmt.getBody());
			currentBlock.connectToSuccessor(loopHead);			
			//Now add the looping edge from the last block of the loop
			//to the loop head
			jsvBody.getCurrentBlock().connectToSuccessor(loopHead);
			

			BasicBlock loopExit = new BasicBlock(JsTranslationHelper.computeLocationTag(stmt.getBody()));
			//add an assumption that the loop condition holds when entering the loop body
			Expression loopexitcond = JsOperatorFunctionFactory.v()
					.createBinOp(Token.EQ, loopCond, 
							JsConstantFactory.v().getBooleanConstant(false)
							);
			AssumeStatement loopexit = new AssumeStatement(loopexitcond);
			loopexit.setLocationTag(JsTranslationHelper.computeLocationTag(stmt.getBody()));
			addStatement(loopExit, loopexit, true); 
			currentBlock.connectToSuccessor(loopExit);
			/*
			 * TODO: this is untested! I have no idea how the loop body looks and if
			 * the goto to the loop head actually makes sense!
			 */
			currentBlock = loopExit;
			return false;
		} else if (node instanceof KeywordLiteral) {
			KeywordLiteral kwl = (KeywordLiteral) node;
			if (kwl.getType() != Token.DEBUGGER) {
				throw new JsNotNormalizedException(node);
			}
			// The Keyword Literal "DEBUGGER" is ignored
		} else if (node instanceof LabeledStatement) {
			//For labeled statements, we create a new basic block
			//so that we can direct any jump to this label to
			//it's corresponding block in the boogie program
			LabeledStatement stmt = (LabeledStatement) node;
			BasicBlock nextBlock = null; 
			for (Label label : stmt.getLabels()) {
				if (JsGlobalsCache.v().labeledBlocks.containsKey(label)) {
					nextBlock = JsGlobalsCache.v().labeledBlocks.get(label);
					break;
				}
			}
			if (nextBlock==null) {
				nextBlock = new BasicBlock();
				for (Label label : stmt.getLabels()) {					
					JsGlobalsCache.v().labeledBlocks.put(label.getName(), nextBlock);					
				}				
			}
			if (this.currentBlock!=null) {
				this.currentBlock.connectToSuccessor(nextBlock);				
			}
			this.currentBlock = nextBlock;
			this.visit(stmt.getStatement());
		} else if (node instanceof ReturnStatement) {
			//TODO: check if there is a finally somewhere...
			// only one per method
			ReturnStatement stmt = (ReturnStatement) node;
			if (stmt.getReturnValue() != null) {
				JsExpressionVisitor jev = new JsExpressionVisitor(this.currentScope);
				jev.visit(stmt.getReturnValue());
				addStatements(this.currentBlock, jev.getGuardingStatements());
				if (this.currentProcedure!=null) {
					addStatement(this.currentBlock, 
							new AssignStatement(this.currentProcedure.getReturnVariable(),
							jev.getExpression()), 
							false
							);					
					//Note: the normalizer guarantees us that
					//there is no statement after the return
					//otherwise additional stuff has to be done.
				} else {
					//TODO: this should only happen once
					//and can be ignored, right?
				}				
			} else {
				//TODO: is this correct?
				if (this.currentProcedure!=null) {
					addStatement(this.currentBlock, 
							new AssignStatement(this.currentProcedure.getReturnVariable(),
							JsConstantFactory.v().getUndefinedConstant()), 
							false
							);		
				}
			}
			return false;
		} else if (node instanceof ThrowStatement) {
			ThrowStatement stmt = (ThrowStatement) node;
			JsExpressionVisitor jev = new JsExpressionVisitor(this.currentScope);
			jev.visit(stmt.getExpression());
			if (this.currentScope.currentCatchBlock!=null) {
				//TODO: check if jev.getExpression() is not null and use a dummy variable then
				HashSet<BasicBlock> succs = this.currentBlock.Successors;
				for (BasicBlock b : succs ) {
					this.currentBlock.disconnectFromSuccessor(b);
				}				
				this.currentBlock.connectToSuccessor(this.currentScope.currentCatchBlock);
				
			} else {
				//TODO: throw an exception.
			}			
			// TODO: assemble
		} else if (node instanceof TryStatement) {
			TryStatement stmt = (TryStatement) node;
			if (stmt.getCatchClauses().size() > 1) {
				throw new JsNotNormalizedException(node,
						"You have to run the js normalizer first");
			} else if (stmt.getCatchClauses().size() == 1) {
				if (stmt.getFinallyBlock() != null) {
					throw new JsNotNormalizedException(node,
							"You have to run the js normalizer first");
				}
				if (stmt.getCatchClauses().size()!=1) {
					throw new JsNotNormalizedException(node,
							"You have to run the js normalizer first");
				}				
				BasicBlock catchBlock = new BasicBlock();
				JsStatementVisitor jsvCatch = new JsStatementVisitor(this.currentScope, catchBlock, false);				
				jsvCatch.visit(stmt.getCatchClauses().get(0));
				JsScopeInfo newScope = new JsScopeInfo();
				
				//this is the block that is reached after the try-block
				//and after the finally block.
				BasicBlock exitBlock = new BasicBlock();
				
				if (this.currentScope.currentFinallyBlock!=null) {
					//then we have to wire the catch block to the finally block
					this.currentScope.connectToFinally(jsvCatch.getCurrentBlock(), exitBlock);									
				}
				
				newScope.containingProcedure = this.currentScope.containingProcedure;
				newScope.currentCatchBlock = catchBlock;
				JsStatementVisitor jsvTryBlock = new JsStatementVisitor(newScope);
				jsvTryBlock.visit(stmt.getTryBlock());

				if (this.currentScope.currentFinallyBlock!=null) {
					//then we have to wire the catch block to the finally block
					this.currentScope.connectToFinally(jsvTryBlock.getCurrentBlock(), exitBlock);
					this.currentBlock = exitBlock;
				} else {
					//if there is no finally, we just continue with the current try block.
					this.currentBlock = jsvTryBlock.getCurrentBlock();
				}									
				return false;
			} else if (stmt.getCatchClauses().size() == 0) {
				if (stmt.getFinallyBlock() == null) {
					throw new JsNotNormalizedException(node,
							"You have to run the js normalizer first");
				}
				BasicBlock finallyBlock = new BasicBlock();
				JsStatementVisitor jsvCatch = new JsStatementVisitor(this.currentScope, finallyBlock, false);				
				jsvCatch.visit(stmt.getFinallyBlock());
				JsScopeInfo newScope = new JsScopeInfo();
				newScope.containingProcedure = this.currentScope.containingProcedure;
				newScope.currentFinallyBlock = finallyBlock;
				newScope.currentFinallyExitBlock = jsvCatch.getCurrentBlock();
				
				JsStatementVisitor jsvTryBlock = new JsStatementVisitor(newScope, this.currentBlock, false);
				jsvTryBlock.visit(stmt.getTryBlock());
				//TODO: neither finished nor tested
			} else {
				throw new JsNotNormalizedException(node,
						"You have to run the js normalizer first");
			}
			return false;
		} else if (node instanceof VariableDeclaration) {
			// for locals
			VariableDeclaration stmt = (VariableDeclaration) node;
			for (VariableInitializer vinit : stmt.getVariables()) {
				JsExpressionVisitor jevVar = new JsExpressionVisitor(this.currentScope);
				jevVar.visit(vinit.getTarget());
				if (vinit.getInitializer() != null) {
					JsExpressionVisitor jevInit = new JsExpressionVisitor(this.currentScope);
					jevInit.visit(vinit.getInitializer());
				}
				// TODO: assemble
			}
		} else {
			throw new JsNotNormalizedException(node,
					"You have to run the js normalizer first");
		}
		return false;
	}	
	
	private void translateSequence(AstNode node) {
		if (!(node instanceof Block) && !(node instanceof Scope)) {
			throw new JsNotNormalizedException(node,
					"Somebody did a bad modification to the code: "+node.getClass());			
		}
		JsStatementVisitor jsv = new JsStatementVisitor(this.currentScope, this.currentBlock, false);
		for (Node child : node) {
			jsv.visit((AstNode) child);
		}		
	}
	
	private void translateCatchClause(CatchClause cc) {
		JsExpressionVisitor jevCatchName = new JsExpressionVisitor(this.currentScope);
		jevCatchName.visit(cc.getVarName());
		if (cc.getCatchCondition() != null) {
			JsExpressionVisitor jevCatchCond = new JsExpressionVisitor(this.currentScope);
			jevCatchCond.visit(cc.getCatchCondition());
			// TODO: what is this and what to do with it?
		}
	}

	
	private void addStatements(BasicBlock block, Collection<Statement> stmts) {
		for (Statement stmt : stmts) {
			addStatement(block, stmt, false);
		}
	}
	
	private void addStatement(BasicBlock block, Statement stmt, boolean toFront) {
		block.addStatement(stmt, toFront);
		if ( (toFront && block.getLocationTag()==null)
			|| (block.getLocationTag()==null && stmt.getLocationTag()!=null)){
			block.setLocationTag(stmt.getLocationTag());
		}
	}

	private void translateAssignment(Assignment stmt) {

		if (stmt.getRight() instanceof ArrayLiteral) {
			translateArrayLiteralAssignment(stmt);
			return;
		} else if (stmt.getRight() instanceof ObjectLiteral) {			
			translateObjectLiteralAssignment(stmt);
			return;			
		}
		
		// lhs is evaluated first
		JsExpressionVisitor jevLeft = new JsExpressionVisitor(this.currentScope);
		jevLeft.visit(stmt.getLeft());
		addStatements(this.currentBlock, jevLeft.getGuardingStatements());
		// then rhs		
		JsExpressionVisitor jevRight = new JsExpressionVisitor(this.currentScope);
		jevRight.visit(stmt.getRight());
		addStatements(this.currentBlock, jevRight.getGuardingStatements());

		//TODO: check if lhs or rhs can throw exceptions
		//if so, wrap the statement in a conditional choice

		Statement assgn = new AssignStatement(jevLeft.getExpression(), jevRight.getExpression());
		assgn.setLocationTag(JsTranslationHelper.computeLocationTag(stmt));
		addStatement(this.currentBlock, assgn, false);
		
	}
	
	private void translateArrayLiteralAssignment(Assignment stmt) {
		ArrayLiteral exp = (ArrayLiteral) stmt.getRight();		
		//TODO: what is exp.getDestructuringLength()?
		
		JsExpressionVisitor jevLeft = new JsExpressionVisitor(this.currentScope);
		jevLeft.visit(stmt.getLeft());
		addStatements(this.currentBlock, jevLeft.getGuardingStatements());
		Expression base = jevLeft.getExpression();
		
		int counter = 0; //count the current index starting from zero
		for (AstNode node : exp.getElements()) {
			
			JsExpressionVisitor jevOpLeft = new JsExpressionVisitor(this.currentScope);
			jevOpLeft.visit(node);
			addStatements(this.currentBlock, jevOpLeft.getGuardingStatements());
		
			Expression idx = new UboundedIntConstant((long)(counter++));
			Expression value = jevOpLeft.getExpression();
			addStatements(this.currentBlock, JsGlobalsCache.v().createMemoryAccessAssertions(base, idx));

			Statement assgn = new AssignStatement(JsGlobalsCache.v().createMemoryAccess(base, idx), value);
			assgn.setLocationTag(JsTranslationHelper.computeLocationTag(stmt.getRight()));
			addStatement(this.currentBlock, assgn, false);			
		}
		//TODO: now "counter" gives us the size of the array. Is there anything we can do about it?
	}

	private void translateObjectLiteralAssignment(Assignment stmt) {
		JsExpressionVisitor jevLeft = new JsExpressionVisitor(this.currentScope);
		jevLeft.visit(stmt.getLeft());
		addStatements(this.currentBlock, jevLeft.getGuardingStatements());
		Expression base = jevLeft.getExpression();
		
		ObjectLiteral exp = (ObjectLiteral) stmt.getRight();
		for (ObjectProperty op : exp.getElements()) {
			//this is always of the form var : value
			//here op.operator is Token.COL and the left and right side 
			//are self explaining.
			JsExpressionVisitor jevOpLeft = new JsExpressionVisitor(this.currentScope);
			jevOpLeft.visit(op.getLeft());
			addStatements(this.currentBlock, jevOpLeft.getGuardingStatements());

			JsExpressionVisitor jevOpRight = new JsExpressionVisitor(this.currentScope);
			jevOpRight.visit(op.getRight());
			addStatements(this.currentBlock, jevOpRight.getGuardingStatements());
		
			Expression idx = jevOpLeft.getExpression();
			Expression value = jevOpRight.getExpression();
			addStatements(this.currentBlock, JsGlobalsCache.v().createMemoryAccessAssertions(base, idx));

			Statement assgn = new AssignStatement(JsGlobalsCache.v().createMemoryAccess(base, idx), value);
			assgn.setLocationTag(JsTranslationHelper.computeLocationTag(stmt.getRight()));
			addStatement(this.currentBlock, assgn, false);		
		}
	}

	

}
