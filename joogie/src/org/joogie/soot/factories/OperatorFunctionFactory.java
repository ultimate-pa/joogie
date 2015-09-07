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

package org.joogie.soot.factories;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.joogie.Options;
import org.joogie.Options.HeapMode;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.BinOpExpression.Operator;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.IteExpression;
import org.joogie.boogie.expressions.SimpleHeapAccess;
import org.joogie.boogie.expressions.UnaryExpression;
import org.joogie.boogie.expressions.UnaryExpression.UnaryOperator;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.ArrArrayType;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.RefArrayType;
import org.joogie.soot.BoogieHelpers;
import org.joogie.util.Log;

/**
 * @author schaef
 * 
 */
public class OperatorFunctionFactory {

	private static OperatorFunctionFactory instance = null;

	public static OperatorFunctionFactory v() {
		if (instance == null) {			
			instance = new OperatorFunctionFactory();
			//TODO: What is this about? Did I write this?
			// /// BEGIN HACK
			BoogieProcedure dummy = new BoogieProcedure("dummy", null, false,
					false); // Need to create a dummy procedure for
							// initialization
			BoogieProcedure temp = BoogieHelpers.currentProcedure; // Save the
																	// unlucky
																	// procedure
			BoogieHelpers.currentProcedure = dummy;
			instance.Init();
			BoogieHelpers.currentProcedure = temp; // Restore the procedure
			// / END HACK
			// TODO: Do it right: when initializing parameters, the variable
			// factory should receive a reference to the current procedure
		}
		return instance;
	}

	/**
	 * Resets the Singleton
	 */
	public static void resetInstance() {
		instance = null;
	}

	public SimpleHeapAccess createSimpleHeapAccess(Expression base,
			Expression field) {
		// TODO add assertions to guard memory access
		return new SimpleHeapAccess(base, field);
	}

	/**
	 * returns an uninterpreted function that can be used
	 * to create fresh heapvars
	 */
	public BoogieProcedure getNewVarProcedure() {
		return this.newVariable;
	}
	
	public Expression createBinOp(String op, Expression left, Expression right) {
		Expression exp = null;
		op = op.trim();
		if (op.compareTo("+") == 0) {
			exp = getOperatorFun("add", left, right);
		} else if (op.compareTo("-") == 0) {
			exp = getOperatorFun("sub", left, right);
		} else if (op.compareTo("*") == 0) {
			exp = getOperatorFun("mul", left, right);
		} else if (op.compareTo("/") == 0) {
			exp = getOperatorFun("div", left, right);
		} else if (op.compareTo("%") == 0) {
			exp = getOperatorFun("mod", left, right);
		} else if (op.compareTo("cmp") == 0) {
			exp = getOperatorFun("cmp", left, right);
		} else if (op.compareTo("cmpl") == 0) {
			exp = getOperatorFun("cmp", left, right);
		} else if (op.compareTo("cmpg") == 0) {
			exp = getOperatorFun("cmp", left, right);
		} else if (op.compareTo("==") == 0) {
			exp = getOperatorFun("eq", left, right);
		} else if (op.compareTo("<") == 0) {
			exp = getOperatorFun("lt", left, right);
		} else if (op.compareTo(">") == 0) {
			exp = getOperatorFun("gt", left, right);
		} else if (op.compareTo("<=") == 0) {
			exp = getOperatorFun("le", left, right);
		} else if (op.compareTo(">=") == 0) {
			exp = getOperatorFun("ge", left, right);
		} else if (op.compareTo("!=") == 0) {
			exp = getOperatorFun("ne", left, right);
		} else if (op.compareTo("&") == 0) {
			exp = getOperatorFun("and", left, right);
		} else if (op.compareTo("|") == 0) {
			exp = getOperatorFun("or", left, right);
		} else if (op.compareTo("<<") == 0) { // Shiftl
			exp = getOperatorFun("shl", left, right);
		} else if (op.compareTo(">>") == 0) { // Shiftr
			exp = getOperatorFun("shr", left, right);
		} else if (op.compareTo(">>>") == 0) { // UShiftr
			exp = getOperatorFun("ushr", left, right);
		} else if (op.compareTo("^") == 0) { // XOR
			exp = getOperatorFun("xor", left, right);
		} else if (op.compareTo("instanceof") == 0) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(left);
			args.add(right);
			exp = BoogieHelpers.createInvokeExpression(instanceofOp, args);
		} else {
			Log.error(">>>>>>>>>>" + op + "<");
		}
		return exp;
	}

	private Expression getOperatorFun(String opcode, Expression l, Expression r) {
		LinkedList<BoogieProcedure> proctype = null;
		if (l.getType() == r.getType()
				&& l.getType() == BoogieBaseTypes.getIntType()) {
			proctype = intOperators;
		} else if (l.getType() == r.getType()
				&& l.getType() == BoogieBaseTypes.getRealType()) {
			proctype = realOperators;
		} else if (l.getType() instanceof BoogieObjectType
				&& r.getType() instanceof BoogieObjectType) {
			proctype = refOperators;
		} else if (l.getType() == BoogieBaseTypes.getIntType()
				&& r.getType() instanceof BoogieObjectType) {
			r = castToInt(r);
			proctype = intOperators;
		} else if (l.getType() instanceof BoogieObjectType
				&& r.getType() == BoogieBaseTypes.getIntType()) {
			l = castToInt(l);
			proctype = intOperators;
		} else if (l.getType() instanceof BoogieArrayType
				&& r.getType() instanceof BoogieArrayType) { // TODO test,if
																// there are
																// more cases to
																// consider
			if (opcode.compareTo("eq") == 0) {
				return compareArrayEquality(l, r);
			} else if (opcode.compareTo("ne") == 0) {
				return createNegOp(compareArrayEquality(l, r));
			}
		} else if (l == BoogieProgram.v().getNullReference()
				&& r.getType() instanceof BoogieArrayType) {
			l = BoogieProgram.v().getArrayNullReference(
					((BoogieArrayType) r.getType()).getNestedType());
			if (opcode.compareTo("eq") == 0) {
				return compareArrayEquality(l, r);
			} else if (opcode.compareTo("ne") == 0) {
				return createNegOp(compareArrayEquality(l, r));
			}
		} else if (l.getType() instanceof BoogieArrayType
				&& r == BoogieProgram.v().getNullReference()) {
			r = BoogieProgram.v().getArrayNullReference(
					((BoogieArrayType) l.getType()).getNestedType());
			if (opcode.compareTo("eq") == 0) {
				return compareArrayEquality(l, r);
			} else if (opcode.compareTo("ne") == 0) {
				return createNegOp(compareArrayEquality(l, r));
			}
		} else {
			Log.error("Types don't match: " + l.getType().getName() + " and "
					+ r.getType().getName());
			return null;
		}
		BoogieProcedure proc = findProcedureWithPrefix(opcode, proctype);
		if (Options.v().getHeapMode() == HeapMode.SimpleHeap) {
			// BEGIN HACK : Our model checker doesn't understand functions with
			// bodies
			// well, we do equality and inequality inline to avoid the prelude
			if (opcode.compareTo("eq") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Eq, l, r);
				return ex;
			}

			if (opcode.compareTo("ne") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Neq, l, r);
				return ex;
			}

			if (opcode.compareTo("add") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Plus, l, r);
				return ex;
			}

			if (opcode.compareTo("sub") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Minus, l, r);
				return ex;
			}

			if (opcode.compareTo("mul") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Mul, l, r);
				return ex;
			}

			if (opcode.compareTo("div") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Div, l, r);
				return ex;
			}

			if (opcode.compareTo("ge") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Ge, l, r);
				return ex;
			}

			if (opcode.compareTo("le") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Le, l, r);
				return ex;
			}

			if (opcode.compareTo("lt") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Lt, l, r);
				return ex;
			}

			if (opcode.compareTo("gt") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Gt, l, r);
				return ex;
			}
			// // END HACK
		}
		if (proc != null) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(l);
			args.add(r);
			InvokeExpression e = BoogieHelpers.createInvokeExpression(proc, args);
			return e;
		}
		return null;
	}

	private Expression compareArrayEquality(Expression l, Expression r) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(l);
		args.add(r);
		if (l.getType() == BoogieBaseTypes.getIntArrType()) {
			return BoogieHelpers.createInvokeExpression(eqIntArray, args);
		} else if (l.getType() == BoogieBaseTypes.getRealArrType()) {
			return BoogieHelpers.createInvokeExpression(eqRealArray, args);
		} else if (l.getType() instanceof RefArrayType) {
			return BoogieHelpers.createInvokeExpression(eqRefArray, args);
		} else if (l.getType() instanceof ArrArrayType) {
			Log.error("compareArrayEquality: CASE not implemented");
			return BoogieVariableFactory.v().getFreshGlobalConstant(
					BoogieBaseTypes.getIntType());
		}
		Log.error("compareArrayEquality: Type not implemented");
		return BoogieVariableFactory.v().getFreshGlobalConstant(
				BoogieBaseTypes.getIntType());
	}

	private BoogieProcedure findProcedureWithPrefix(String prefix,
			List<BoogieProcedure> l) {
		for (BoogieProcedure proc : l) {
			if (proc == null)
				continue; // This can only occur during the construction of the
							// singleton
			if (proc.getName().startsWith("$" + prefix))
				return proc;
		}

		Log.error("TODO!!! " + prefix); // TODO remove if there are no bugs
										// caused by this method
		return null;
	}

	public Expression createNegOp(Expression exp) {
		BoogieProcedure proc = null;
		if (exp.getType() == BoogieBaseTypes.getIntType()) {
			proc = negInt;
		} else if (exp.getType() == BoogieBaseTypes.getRealType()) {
			proc = negReal;
		} else if (exp.getType() instanceof BoogieObjectType) {
			proc = negRef;
		} else if (exp.getType() == BoogieBaseTypes.getBoolType()) { // Inline
																		// the
																		// negation
																		// operator
																		// for
																		// boolean
																		// expressions
			return new UnaryExpression(UnaryOperator.Not, exp);
		}
		if (proc != null) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			InvokeExpression e = BoogieHelpers.createInvokeExpression(proc, args);
			return e;
		}
		return null;
	}

	private boolean compareTypes(BoogieType a, BoogieType b) {
		if (b instanceof BoogieObjectType && a instanceof RefArrayType) {
			Log.debug("comparing array with object type. this could be a bug");
		}

		if (a == b) {
			return true;
		} else if ((a instanceof BoogieObjectType && b instanceof BoogieObjectType)
				|| (a instanceof RefArrayType && b instanceof RefArrayType)) {
			return true;
		} else if (a instanceof ArrArrayType && b instanceof ArrArrayType) {
			return compareTypes(((ArrArrayType) a).getNestedType(),
					((ArrArrayType) b).getNestedType());
		}
		return false;
	}


	public Expression castIfNecessary(Expression exp, BoogieType targetType) {
		if (compareTypes(exp.getType(), targetType)) {
			return exp;
		} else {
			if (targetType == BoogieBaseTypes.getIntType()) {
				return castToInt(exp);
			} else if (targetType == BoogieBaseTypes.getRealType()) {
				return castToReal(exp);
			} else if (targetType instanceof BoogieObjectType
					&& exp.getType() instanceof BoogieArrayType) {
				return castArrayToRef(exp);
			} else if (targetType instanceof BoogieArrayType) {
				// special case if exp is a null constant:
				if (exp == BoogieProgram.v().getNullReference()) {
					if (targetType instanceof ArrArrayType) {
						Log.debug("castIfNecessary: MultiArray not implemented - sound abstraction");
						return BoogieVariableFactory.v()
								.getFreshGlobalConstant(targetType);
					} else {
						return BoogieProgram.v()
								.getArrayNullReference(
										((BoogieArrayType) targetType)
												.getNestedType());
					}
				} else {
					return castToArray(exp, targetType);
				}
			} else {
				Log.error("FATAL ERROR!!!");
				Log.error("++ " + exp.toBoogie());
				Log.error("++ " + targetType.toBoogie());
				return null;
			}
		}
	}

	private Expression castToInt(Expression exp) {
		if (exp.getType() == BoogieBaseTypes.getIntType()) {
			return exp;
		} else if (exp.getType() == BoogieBaseTypes.getRealType()) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			return BoogieHelpers.createInvokeExpression(realToInt, args);
		} else if (exp.getType() instanceof BoogieObjectType) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			return BoogieHelpers.createInvokeExpression(refToInt, args);
		} else {
			return exp;
		}
	}

	private Expression castToReal(Expression exp) {
		if (exp.getType() == BoogieBaseTypes.getIntType()) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			return BoogieHelpers.createInvokeExpression(intToReal, args);
		} else {
			return exp;
		}
	}

	private Expression castToArray(Expression exp, BoogieType arrtype) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(exp);
		if (exp.getType() instanceof BoogieObjectType) {
			if (arrtype == BoogieBaseTypes.getIntArrType()) {
				return BoogieHelpers.createInvokeExpression(refToIntArr, args);
			} else if (arrtype == BoogieBaseTypes.getRealArrType()) {
				return BoogieHelpers.createInvokeExpression(refToRealArr, args);
			} else if (arrtype instanceof RefArrayType) {
				return BoogieHelpers.createInvokeExpression(refToRefArr, args);
			} else if (arrtype instanceof ArrArrayType) {
				Log.error("castToArray: multiarrays are not really implemented");
				return BoogieVariableFactory.v()
						.getFreshGlobalConstant(arrtype);
			}
		}
		Log.error("castToArray: case is not implemented");
		Log.error("  cast from " + exp.getType().toString() + " to "
				+ arrtype.toString());
		return BoogieVariableFactory.v().getFreshGlobalConstant(
				arrtype);
	}

	private Expression castArrayToRef(Expression exp) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(exp);
		BoogieType arrtype = exp.getType();
		if (arrtype == BoogieBaseTypes.getIntArrType()) {
			return BoogieHelpers.createInvokeExpression(intArrToRef, args);
		} else if (arrtype == BoogieBaseTypes.getRealArrType()) {
			return BoogieHelpers.createInvokeExpression(realArrToRef, args);
		} else if (arrtype instanceof RefArrayType) {
			return BoogieHelpers.createInvokeExpression(refArrToRef, args);
		} else {
			Log.error("castToArray: case is not implemented");
			return BoogieVariableFactory.v().getFreshGlobalConstant(
					BoogieBaseTypes.getRefType());
		}

	}

	public boolean isPreludeProcedure(BoogieProcedure proc) {
		// TODO: there might be certainly more beautiful ways to implement this
		// but the sake of having a class, this should be fine
		if (proc == negInt)
			return true;
		if (proc == negReal)
			return true;
		if (proc == negRef)
			return true;
		if (proc == eqIntArray)
			return true;
		if (proc == eqRealArray)
			return true;
		if (proc == eqRefArray)
			return true;
		if (proc == refToInt)
			return true;
		if (proc == realToInt)
			return true;
		if (proc == intToReal)
			return true;

		if (proc == refArrToRef)
			return true;
		if (proc == realArrToRef)
			return true;
		if (proc == intArrToRef)
			return true;

		if (proc == refToIntArr)
			return true;
		if (proc == refToRealArr)
			return true;
		if (proc == refToRefArr)
			return true;

		if (proc == instanceofOp)
			return true;
		if (proc == newVariable)
			return true;

		if (intOperators.contains(proc))
			return true;
		if (realOperators.contains(proc))
			return true;
		if (refOperators.contains(proc))
			return true;

		return false;
	}

	public String toBoogie() {
		StringBuilder sb = new StringBuilder();

		if (Options.v().getHeapMode() == HeapMode.Default) {
			sb.append("// operator procedures ............\n");
			sb.append(negInt.toBoogie());
			sb.append(negReal.toBoogie());
			sb.append(negRef.toBoogie());

			sb.append(eqIntArray.toBoogie());
			sb.append(eqRealArray.toBoogie());
			sb.append(eqRefArray.toBoogie());

			sb.append("\n // Cast operators");
			sb.append(refToInt.toBoogie());
			sb.append(realToInt.toBoogie());
			sb.append(intToReal.toBoogie());

			sb.append(refArrToRef.toBoogie());
			sb.append(realArrToRef.toBoogie());
			sb.append(intArrToRef.toBoogie());

			sb.append(refToIntArr.toBoogie());
			sb.append(refToRealArr.toBoogie());
			sb.append(refToRefArr.toBoogie());

			sb.append(instanceofOp.toBoogie());
			// sb.append(lengthOp.toBoogie());

			sb.append(newVariable.toBoogie());

			for (BoogieProcedure proc : intOperators) {
				sb.append(proc.toBoogie());
			}
			for (BoogieProcedure proc : realOperators) {
				sb.append(proc.toBoogie());
			}
			for (BoogieProcedure proc : refOperators) {
				sb.append(proc.toBoogie());
			}
		}
		return sb.toString();
	}

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

	/*
	 * Creates a cmp operation (see
	 * http://www.netmite.com/android/mydroid/dalvik/docs/dalvik-bytecode.html)
	 * Perform the indicated floating point or long comparison, storing 0 if the
	 * two arguments are equal, 1 if the second argument is larger, or -1 if the
	 * first argument is larger.
	 */
	private Expression createCmpExpression(BoogieType t) {
		Variable x = BoogieVariableFactory.v().createBoogieVariable(
				"x", t, false);
		Variable y = BoogieVariableFactory.v().createBoogieVariable(
				"y", t, false);

		if (t != BoogieBaseTypes.getIntType()) {
			Expression equality = createBinOp("==", x, y);
			Expression comparison = createBinOp("<", x, y);
			Expression lt;
			Expression eq;

			if (comparison instanceof BinOpExpression)
				lt = comparison;
			else
				lt = new BinOpExpression(Operator.Eq, comparison,
						new UboundedIntConstant(1L));

			if (equality instanceof BinOpExpression)
				eq = equality;
			else
				eq = new BinOpExpression(Operator.Eq, equality,
						new UboundedIntConstant(1L));

			return new IteExpression(lt, new UboundedIntConstant(1L),
					new IteExpression(eq, new UboundedIntConstant(0L),
							new UboundedIntConstant(-1L)));
		} else {
			Expression lt = new BinOpExpression(Operator.Lt, x, y);
			Expression eq = new BinOpExpression(Operator.Eq, x, y);
			return new IteExpression(lt, new UboundedIntConstant(1L),
					new IteExpression(eq, new UboundedIntConstant(0L),
							new UboundedIntConstant(-1L)));
		}
	}

	private Expression createNegIntExpression() {
		Variable x = BoogieVariableFactory.v().createBoogieVariable(
				"x", BoogieBaseTypes.getIntType(), false);
		return new IteExpression(new BinOpExpression(Operator.Eq, x,
				new UboundedIntConstant(0L)), new UboundedIntConstant(1L),
				new UboundedIntConstant(0L));

	}

	private BoogieProcedure createProcedure(String name, BoogieType rettype,
			BoogieType t) {
		return new BoogieProcedure(name, rettype, (new LinkedList<BoogieType>(
				Arrays.asList(new BoogieType[] { t }))), true);
	}

	private BoogieProcedure createProcedure(String name, BoogieType rettype,
			BoogieType t1, BoogieType t2) {
		return new BoogieProcedure(name, rettype, (new LinkedList<BoogieType>(
				Arrays.asList(new BoogieType[] { t1, t2 }))), true);
	}

	/*
	 * Constructor
	 */
	private OperatorFunctionFactory() {

	}

	private HashSet<BoogieProcedure> operatorProcs = new HashSet<BoogieProcedure>();
	
	public HashSet<BoogieProcedure> getPreludProcedures() {
		return this.operatorProcs;
	}
	
	private void Init() {
		newVariable = createProcedure("$newvariable",
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getIntType());
		operatorProcs.add(newVariable);
		
		instanceofOp = createProcedure("$instanceof",
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getClassConstType());
		operatorProcs.add(instanceofOp);
		
		eqIntArray = createProcedure("$eqintarray",
				BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntArrType(),
				BoogieBaseTypes.getIntArrType());
		operatorProcs.add(eqIntArray);
		
		eqRealArray = createProcedure("$eqrealarray",
				BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealArrType(),
				BoogieBaseTypes.getRealArrType());
		operatorProcs.add(eqRealArray);
		
		eqRefArray = createProcedure("$eqrefarray",
				BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefArrType(),
				BoogieBaseTypes.getRefArrType());
		operatorProcs.add(eqRefArray);
		
		intArrToRef = createProcedure("$intarrtoref",
				BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getIntArrType());
		operatorProcs.add(intArrToRef);
		
		realArrToRef = createProcedure("$realarrtoref",
				BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRealArrType());
		operatorProcs.add(realArrToRef);
		
		refArrToRef = createProcedure("$refarrtoref",
				BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefArrType());
		operatorProcs.add(refArrToRef);
		
		refToIntArr = createProcedure("$reftointarr",
				BoogieBaseTypes.getIntArrType(),
				BoogieBaseTypes.getRefType());
		operatorProcs.add(refToIntArr);
		
		refToRealArr = createProcedure("$reftorealarr",
				BoogieBaseTypes.getRealArrType(),
				BoogieBaseTypes.getRefType());
		operatorProcs.add(refToRealArr);
		
		refToRefArr = createProcedure("$reftorefarr",
				BoogieBaseTypes.getRefArrType(),
				BoogieBaseTypes.getRefType());
		operatorProcs.add(refToRefArr);
		
		intToReal = createProcedure("$inttoreal",
				BoogieBaseTypes.getRealType(), BoogieBaseTypes.getIntType());
		operatorProcs.add(intToReal);
		
		refToInt = createProcedure("$reftoint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType());
		operatorProcs.add(refToInt);
		
		realToInt = createProcedure("$realtoint",
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRealType());
		operatorProcs.add(realToInt);
		
		negInt = new BoogieProcedure("$negInt", BoogieBaseTypes.getIntType(),
				createNegIntExpression());
		operatorProcs.add(negInt);
		
		negReal = createProcedure("$negReal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType());
		operatorProcs.add(negReal);
		
		negRef = createProcedure("$negRef", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType());
		operatorProcs.add(negRef);
		
		// Integer operations
		addInt = new BoogieProcedure("$addint", BoogieBaseTypes.getIntType(),
				createBinOpExpression(Operator.Plus,
						BoogieBaseTypes.getIntType()));
		subInt = new BoogieProcedure("$subint", BoogieBaseTypes.getIntType(),
				createBinOpExpression(Operator.Minus,
						BoogieBaseTypes.getIntType()));
		// TODO Don't create a procedure body for mul as Princess cannot deal
		// with that
		// mulInt = new BoogieProcedure("$mulint",
		// BoogieBaseTypes.getIntType(),
		// createBinOpExpression(Operator.Mul,
		// BoogieBaseTypes.getIntType()));
		mulInt = createProcedure("$mulint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType());

		// TODO Don't create a procedure body for div as Princess cannot deal
		// with that
		// divInt = new BoogieProcedure("$divint",
		// BoogieBaseTypes.getIntType(), createBinOpExpression(Operator.Div,
		// BoogieBaseTypes.getIntType()) );
		divInt = createProcedure("$divint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType());
		modInt = createProcedure("$modint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType());

		eqInt = new BoogieProcedure("$eqint", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Eq,
						BoogieBaseTypes.getIntType()));
		neInt = new BoogieProcedure("$neint", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Neq,
						BoogieBaseTypes.getIntType()));
		ltInt = new BoogieProcedure("$ltint", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Lt,
						BoogieBaseTypes.getIntType()));
		leInt = new BoogieProcedure("$leint", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Le,
						BoogieBaseTypes.getIntType()));
		gtInt = new BoogieProcedure("$gtint", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Gt,
						BoogieBaseTypes.getIntType()));
		geInt = new BoogieProcedure("$geint", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Ge,
						BoogieBaseTypes.getIntType()));

		cmpInt = new BoogieProcedure("$cmpint", BoogieBaseTypes.getIntType(),
				createCmpExpression(BoogieBaseTypes.getIntType()));

		andInt = createProcedure("$andint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType());
		orInt = createProcedure("$orint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType());
		xorInt = createProcedure("$xorint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType());
		ushrInt = createProcedure("$ushrint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType());
		shlInt = createProcedure("$shlint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType());
		shrInt = createProcedure("$shrint", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType());

		intOperators = new LinkedList<BoogieProcedure>(
				Arrays.asList(new BoogieProcedure[] { addInt, subInt, mulInt,
						divInt, modInt, cmpInt, eqInt, ltInt, leInt, gtInt,
						geInt, neInt, andInt, orInt, xorInt, shlInt, shrInt,
						ushrInt }));

		operatorProcs.addAll(intOperators);
		
		// Real operations
		// -------------------------------------------------------
		eqReal = new BoogieProcedure("$eqreal", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Eq,
						BoogieBaseTypes.getRealType()));
		neReal = new BoogieProcedure("$nereal", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Neq,
						BoogieBaseTypes.getRealType()));
		addReal = createProcedure("$addreal", BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		subReal = createProcedure("$subreal", BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		mulReal = createProcedure("$mulreal", BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		divReal = createProcedure("$divreal", BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		modReal = createProcedure("$modreal", BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		ltReal = createProcedure("$ltreal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		leReal = createProcedure("$lereal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		gtReal = createProcedure("$gtreal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		geReal = createProcedure("$gereal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		andReal = createProcedure("$andreal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		orReal = createProcedure("$orreal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		xorReal = createProcedure("$xorreal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		ushrReal = createProcedure("$ushrreal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		shlReal = createProcedure("$shlreal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		shrReal = createProcedure("$shrreal", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());

		realOperators = new LinkedList<BoogieProcedure>(
				Arrays.asList(new BoogieProcedure[] { addReal, subReal,
						mulReal, divReal, modReal, eqReal, ltReal, leReal,
						gtReal, geReal, neReal, andReal, orReal, xorReal,
						shlReal, shrReal, ushrReal }));
		
		operatorProcs.addAll(realOperators);
		
		// Ref operations
		addRef = createProcedure("$addref", BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		subRef = createProcedure("$subref", BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		mulRef = createProcedure("$mulref", BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		divRef = createProcedure("$divref", BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		modRef = createProcedure("$modref", BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());

		eqRef = new BoogieProcedure("$eqref", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Eq,
						BoogieBaseTypes.getRefType()));
		neRef = new BoogieProcedure("$neref", BoogieBaseTypes.getIntType(),
				createLogOpExpression(Operator.Neq,
						BoogieBaseTypes.getRefType()));

		ltRef = createProcedure("$ltref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		leRef = createProcedure("$leref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		gtRef = createProcedure("$gtref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		geRef = createProcedure("$geref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());

		andRef = createProcedure("$andref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		orRef = createProcedure("$orref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		xorRef = createProcedure("$xorref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		ushrRef = createProcedure("$ushrref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		shlRef = createProcedure("$shlref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());
		shrRef = createProcedure("$shrref", BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType());

		refOperators = new LinkedList<BoogieProcedure>(
				Arrays.asList(new BoogieProcedure[] { addRef, subRef, mulRef,
						divRef, modRef, eqRef, ltRef, leRef, gtRef, geRef,
						neRef, andRef, orRef, xorRef, shlRef, shrRef, ushrRef }));

		operatorProcs.addAll(refOperators);
		
		// The cmp operators for real and ref are created in the end,
		// because they use other prelude functions
		cmpReal = new BoogieProcedure("$cmpreal",
				BoogieBaseTypes.getIntType(),
				createCmpExpression(BoogieBaseTypes.getRealType()));
		realOperators.add(cmpReal);
		operatorProcs.add(cmpReal);
		
		cmpRef = new BoogieProcedure("$cmpref", BoogieBaseTypes.getIntType(),
				createCmpExpression(BoogieBaseTypes.getRefType()));
		refOperators.add(cmpRef);
		
		operatorProcs.add(cmpRef); //operatorProcs now contains all prelude functions
		
		//BoogieProgram.v().addProcedures(operatorProcs);		
	}

	private BoogieProcedure addInt, subInt, mulInt, divInt, modInt, cmpInt,
			eqInt, ltInt, leInt, gtInt, geInt, neInt, andInt, orInt, xorInt,
			shlInt, shrInt, ushrInt, negInt;

	private BoogieProcedure addReal, subReal, mulReal, divReal, modReal,
			cmpReal, eqReal, ltReal, leReal, gtReal, geReal, neReal, andReal,
			orReal, xorReal, shlReal, shrReal, ushrReal, negReal;

	private BoogieProcedure addRef, subRef, mulRef, divRef, modRef, cmpRef,
			eqRef, ltRef, leRef, gtRef, geRef, neRef, andRef, orRef, xorRef,
			shlRef, shrRef, ushrRef, negRef;

	private BoogieProcedure refToIntArr, refToRealArr, refToRefArr, intToReal,
			refToInt, realToInt, refArrToRef, realArrToRef, intArrToRef;

	private BoogieProcedure instanceofOp, newVariable;

	private BoogieProcedure eqRefArray, eqRealArray, eqIntArray;

	private LinkedList<BoogieProcedure> intOperators, refOperators,
			realOperators;

}
