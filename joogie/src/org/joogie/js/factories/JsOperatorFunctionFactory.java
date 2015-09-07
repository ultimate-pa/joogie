/**
 * 
 */
package org.joogie.js.factories;

import java.util.HashMap;
import java.util.LinkedList;

import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.IteExpression;
import org.joogie.boogie.expressions.UnaryExpression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieType;
import org.joogie.js.exception.JsNotNormalizedException;
import org.joogie.soot.factories.BoogieVariableFactory;
import org.mozilla.javascript.Token;

/**
 * @author martin
 *
 */
public class JsOperatorFunctionFactory {

	private HashMap<String,BoogieProcedure> operatorFunctions = new HashMap<String,BoogieProcedure>();
	
	private static JsOperatorFunctionFactory instance = null;
	
	public static JsOperatorFunctionFactory v() {
		if (JsOperatorFunctionFactory.instance==null) {
			JsOperatorFunctionFactory.instance = new JsOperatorFunctionFactory();
		}
		return JsOperatorFunctionFactory.instance;
	}
	
	public static void resetInstance() {
		//TODO:
		JsOperatorFunctionFactory.instance=null;
	}
	
	private JsOperatorFunctionFactory() {
		
	}
		
	public Expression createBinOp(int operator, Expression left, Expression right) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(left); args.add(right);
		return createOperatorInvoke(operator,args);
	}
	
	public Expression createUnOp(int operator, Expression exp) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(exp);
		return createOperatorInvoke(operator,args);
	}	
	
	private Expression createOperatorInvoke(int operator, LinkedList<Expression> args) {
		String opname = createOperatorProcedureName(operator,args);
		BoogieProcedure proc = null;
		if (!operatorFunctions.containsKey(opname)) {
			
			BinOpExpression.Operator joogieBinOperator = mapCmpOpTokenToOperator(operator);
			BinOpExpression.Operator joogieArithOperator = mapArithOpTokenToOperator(operator);					
			UnaryExpression.UnaryOperator joogieUnOperator = mapUnOpTokenToOperator(operator);
			
			
			//first check if it is a build in operator
			if (joogieBinOperator==null && joogieUnOperator ==null && joogieArithOperator == null) {
				//if not, use an uninterpreted function
				LinkedList<BoogieType> argtypes = new LinkedList<BoogieType>();
				for (Expression arg : args) {
					argtypes.add(arg.getType());
				}
				proc = new BoogieProcedure(opname, BoogieBaseTypes.getIntType(), argtypes, true);
			} else if (joogieBinOperator!=null && joogieUnOperator ==null && joogieArithOperator == null) {
				//TODO: we don't have a type system yet. Later, we cannot simply
				//use the refType for everything
				proc = new BoogieProcedure(opname, BoogieBaseTypes.getIntType(),						 
						createLogOpExpression(joogieBinOperator, BoogieBaseTypes.getRefType())
						);
				
			} else if (joogieBinOperator==null && joogieUnOperator != null && joogieArithOperator == null) {
				//TODO: we don't have a type system yet. Later, we cannot simply
				//use the refType for everything
				if (joogieUnOperator==UnaryExpression.UnaryOperator.Not) {
					//return new UnaryExpression(UnaryOperator.Not, args.get(0));
					//TODO: implement unary minus depending on the type
					LinkedList<BoogieType> argtypes = new LinkedList<BoogieType>();
					for (Expression arg : args) {
						argtypes.add(arg.getType());
					}
					proc = new BoogieProcedure(opname, BoogieBaseTypes.getIntType(), argtypes, true);
				} else if (joogieUnOperator==UnaryExpression.UnaryOperator.Minus) {
					//TODO: implement unary minus depending on the type
					LinkedList<BoogieType> argtypes = new LinkedList<BoogieType>();
					for (Expression arg : args) {
						argtypes.add(arg.getType());
					}
					proc = new BoogieProcedure(opname, BoogieBaseTypes.getIntType(), argtypes, true);
				} else {
					throw new JsNotNormalizedException("unary minus not implemented");
				}			
			} else if (joogieBinOperator==null && joogieUnOperator == null && joogieArithOperator != null) {
				//TODO: if we have any form of arithmetics, we use
				//uninterpreted functions for now.
				//later, when we have types, we should use something more 
				//sophisticated
				LinkedList<BoogieType> argtypes = new LinkedList<BoogieType>();
				for (Expression arg : args) {
					argtypes.add(arg.getType());
				}
				proc = new BoogieProcedure(opname, BoogieBaseTypes.getRefType(), argtypes, true);

			} else {
				throw new JsNotNormalizedException("Bad operator found");
			}
			
			operatorFunctions.put(opname, proc);
			BoogieProgram.v().addProcedure(proc);
		}
		proc = operatorFunctions.get(opname);
		return new InvokeExpression(proc, args);
		
	}
	
	private String createOperatorProcedureName(int operator, LinkedList<Expression> args) {
		StringBuilder sb = new StringBuilder();
		sb.append("$Op$");
		sb.append(Token.typeToName(operator));
		for (Expression e : args) {
			sb.append("$");
			sb.append(e.getType());
		}
		return sb.toString();
	}

	private BinOpExpression.Operator mapCmpOpTokenToOperator(int optoken) {
		switch (optoken) {
			case Token.EQ: 
				return BinOpExpression.Operator.Eq;
			case Token.NE: 
				return BinOpExpression.Operator.Neq;
			case Token.GT: 
				return BinOpExpression.Operator.Gt;
			case Token.GE: 
				return BinOpExpression.Operator.Ge;
			case Token.LT: 
				return BinOpExpression.Operator.Lt;
			case Token.LE: 
				return BinOpExpression.Operator.Le;
		}
		return null;
	}

	private BinOpExpression.Operator mapArithOpTokenToOperator(int optoken) {
		switch (optoken) {
			case Token.ADD: 
				return BinOpExpression.Operator.Plus;
			case Token.SUB: 
				return BinOpExpression.Operator.Minus;
			case Token.MUL: 
				return BinOpExpression.Operator.Mul;
			case Token.DIV: 
				return BinOpExpression.Operator.Div;
			
		}
		return null;
	}
	
	private UnaryExpression.UnaryOperator mapUnOpTokenToOperator(int optoken) {
		switch (optoken) {
			case Token.NOT: 
				return UnaryExpression.UnaryOperator.Not;
			case Token.NEG: 
				return UnaryExpression.UnaryOperator.Minus;			
		}
		return null;
	}
	
	/* TODO:
	 * once we have a type system, this procedure should be used 
	 * to model arithmetic operations on types that support that
	 * in princess (e.g., Integer)
	 */
	private Expression createBinOpExpression(BinOpExpression.Operator op,
			BoogieType t) {
		Variable x = BoogieVariableFactory.v().createBoogieVariable(
				"x", t, false);
		Variable y = BoogieVariableFactory.v().createBoogieVariable(
				"y", t, false);
		return new BinOpExpression(op, x, y);
	}

	private Expression createLogOpExpression(BinOpExpression.Operator op,
			BoogieType t) {
		Variable x = BoogieVariableFactory.v().createBoogieVariable(
				"x", t, false);
		Variable y = BoogieVariableFactory.v().createBoogieVariable(
				"y", t, false);
		return new IteExpression(new BinOpExpression(op, x, y),
				new UboundedIntConstant(1L), new UboundedIntConstant(0L));
	}	
}
