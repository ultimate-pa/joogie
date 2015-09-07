/*
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

package org.joogie.vcgeneration;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map.Entry;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.constants.Constant;
import org.joogie.boogie.constants.TypeExpression;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.ArrayReadExpression;
import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.IteExpression;
import org.joogie.boogie.expressions.QuantifiedExpression;
import org.joogie.boogie.expressions.QuantifiedExpression.Quantifier;
import org.joogie.boogie.expressions.SimpleHeapAccess;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssertStatement;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.statements.AssumeStatement;
import org.joogie.boogie.statements.ExpressionStatement;
import org.joogie.boogie.statements.InvokeStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogieFieldType;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.HeapType;
import org.joogie.prover.Prover;
import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverFun;
import org.joogie.prover.ProverResult;
import org.joogie.prover.ProverType;
import org.joogie.prover.old.Z3ProverEx;
import org.joogie.prover.princess.PrincessProver;
import org.joogie.report.MethodInfo;
import org.joogie.report.QueryInfo;
import org.joogie.ssa.SSAVariable;
import org.joogie.util.Log;
import org.joogie.util.StopWatch;

/**
 * @author arlt
 */
public abstract class AbstractVCGeneration {

	/**
	 * TODO: z3_ prefixed variables are only a hack for the experiments and
	 * should be removed or at least refactored later
	 */
	private boolean z3_output = false;
	private boolean z3_firstquery = true;
	private StringBuilder z3_stream = new StringBuilder();
	private Z3ProverEx z3 = null;

	/**
	 * Method information
	 */
	protected MethodInfo methodInfo;

	/**
	 * Boogie procedure
	 */
	protected BoogieProcedure proc;

	/**
	 * Used variable
	 */
	protected HashMap<Variable, ProverExpr> usedVariable = new HashMap<Variable, ProverExpr>();

	/**
	 * Used functions
	 */
	protected HashMap<BoogieProcedure, ProverFun> usedFunctions = new HashMap<BoogieProcedure, ProverFun>();

	/**
	 * log the number of conjuncts of the verification condition. For
	 * benchmarking purposes only.
	 */
	protected int numberOfConjuncts = 0;

	/**
	 * Prover
	 */
	protected Prover theoremProver = null;

	/**
	 * C-tor
	 * 
	 * @param methodInfo
	 *            Method information
	 */
	protected AbstractVCGeneration(MethodInfo methodInfo) {
		this.methodInfo = methodInfo;

		if (z3_output) {
			z3 = new Z3ProverEx();
		}
	}

	/**
	 * send an axiom to the prover
	 */
	protected void addAssertion(ProverExpr pexp) {
		/*
		 * if (z3_firstquery) { z3_stream.append(z3_printSMT2Declarations());
		 * z3_firstquery = false; } z3_stream.append(z3_proverExpr2SMT2(pexp));
		 * System.err.println(z3_stream.toString());
		 */

		theoremProver.addAssertion(pexp);

		/*
		 * if (z3_output) { if (z3_firstquery) {
		 * z3_stream.append(z3_printSMT2Declarations()); z3_firstquery = false;
		 * } z3_stream.append(z3_proverExpr2SMT2(pexp)); }
		 */
	}

	/**
	 * push a new frame on the prover stack
	 */
	protected void pushProverStack() {
		theoremProver.push();
		if (z3_output) {
			z3_stream.append("(push)");
		}
	}

	/**
	 * pop the top frame from the prover stack
	 */
	protected void popProverStack() {
		theoremProver.pop();
		if (z3_output) {
			z3_stream.append("(pop)");
		}
	}

	/**
	 * Checks the formula
	 * 
	 * @return Result of the prover
	 */
	protected ProverResult checkSat() {
		// build query info
		QueryInfo qi = new QueryInfo();
		qi.setTime(0);
		qi.setSize(numberOfConjuncts);
		methodInfo.getQueries().add(qi);

		StopWatch sw = StopWatch.getInstanceAndStart();
		ProverResult res = ProverResult.Error;

		// check formula
		if (z3_output) {
			z3_stream.append("(check-sat)"); // not needed actually

			// call Z3 via JNI and map result
			String formula = z3_stream.toString();
			Log.info(formula);

			int result = z3.check(formula);
			if (-1 == result)
				res = ProverResult.Unsat;
			else if (1 == result)
				res = ProverResult.Sat;

		} else {
			res = theoremProver.checkSat(true);
		}

		// measure time
		qi.setTime(sw.stop());

		// log time
		Log.info(String.format("    Query #%d: %s", methodInfo.getQueries()
				.size(), qi.getFormattedTime()));

		return res;
	}

	/**
	 * Generates verification conditions
	 * 
	 * @return List of infeasible blocks
	 */
	public abstract LinkedList<BasicBlock> generateVerificationCondition();

	/*
	 * TODO: this is only a hack for the Z3 pretty printing
	 */
	private HashSet<String> z3_helperVars = new HashSet<String>();

	protected ProverExpr makeHelperVar(String name) {
		z3_helperVars.add(name);
		return theoremProver.mkVariable(name, theoremProver.getBooleanType());
	}

	/**
	 * get a SMT2 String for a ProverExpr
	 */
	private String z3_proverExpr2SMT2(ProverExpr exp) {
		StringBuffer sb = new StringBuffer();
		// TODO: pretty print the SMT formula for
		// hacking in Z3 support.
		if (theoremProver instanceof PrincessProver) {
			sb.append("(assert \n");
			sb.append(((PrincessProver) theoremProver).proverExprToSMT(exp));
			sb.append(" )\n");
		}
		return sb.toString();
	}

	private String z3_type2SMT2(BoogieType t) {
		if (t.getName().compareTo("bool") == 0) {
			return "Bool";
		} else if (t instanceof BoogieArrayType) {
			BoogieArrayType barrt = (BoogieArrayType) t;
			StringBuilder sb = new StringBuilder();
			sb.append("(Array Int ");
			sb.append(z3_type2SMT2(barrt.getNestedType()));
			sb.append(") ");
			return sb.toString();
		} else {
			return "Int";
		}
	}

	private String z3_printSMT2Declarations() {
		StringBuilder sb = new StringBuilder();
		sb.append("(set-logic AUFLIA)\n\n");
		for (String s : z3_helperVars) {
			sb.append("(declare-fun ");
			sb.append(getProverFriendlyName(s));
			sb.append(" () Bool");
			sb.append(")\n");
		}

		for (Entry<Variable, ProverExpr> entry : usedVariable.entrySet()) {
			sb.append("(declare-fun ");
			sb.append(getProverFriendlyName(entry.getKey().getName()));
			sb.append(" () ");
			sb.append(z3_type2SMT2(entry.getKey().getType()));
			sb.append(")\n");
		}
		for (Entry<BoogieProcedure, ProverFun> entry : usedFunctions.entrySet()) {
			// distinguish between prelude functions that have exactly one
			// statement and are pure
			// and all the rest.
			if (proc.isPure() && proc.getRootBlock() != null
					&& proc.getRootBlock().getStatements().size() == 1) {
				// TODO: for some reason this does not happen,
				// as princess already inlines those functions and they
				// are not added to the list of used functions.
				throw new RuntimeException(
						"SMT2 Printer, unexpected prelude function");

			} else {
				sb.append("(declare-fun ");
				sb.append(getProverFriendlyName(entry.getKey().getName()));
				sb.append("( "); // now the params
				for (Variable param : entry.getKey().getParameterList()) {
					sb.append("(");
					sb.append(z3_type2SMT2(param.getType()));
					sb.append(") ");
				}
				sb.append(") "); // done with params
				// not the regular return value:
				if (entry.getKey().getReturnVariable() != null) {
					sb.append(z3_type2SMT2(entry.getKey().getReturnVariable()
							.getType()));
					sb.append(" ");
				}
				// TODO: at this point, the SSA should have removed all
				// calls to non-pure functions already, so no need to
				// worry about exception handling

				sb.append(")\n");
			}

		}

		return sb.toString();
	}

	/*
	 * Procedures to generate a proverexpr TODO: this should be refactored big
	 * time!
	 */

	/**
	 * translate boogie statement to prover expression
	 * 
	 * @param s
	 * @return
	 */
	protected ProverExpr statement2ProverExpr(Statement s) {
		if (s instanceof AssignStatement) {
			AssignStatement st = (AssignStatement) s;
			if (st.getLeft() instanceof SimpleHeapAccess
					|| st.getLeft() instanceof ArrayReadExpression) {
				return arrayWrite2ProverExpr(st.getLeft(),
						expression2ProverExpr(st.getRight()));
			} else {

				return theoremProver.mkEq(expression2ProverExpr(st.getLeft()),
						expression2ProverExpr(st.getRight()));
			}
		} else if (s instanceof AssumeStatement) {
			AssumeStatement st = (AssumeStatement) s;
			return guardExpression2ProverExpr(st.getExpression());
		} else if (s instanceof AssertStatement) {
			AssertStatement st = (AssertStatement) s;
			return guardExpression2ProverExpr(st.getExpression());
		} else if (s instanceof InvokeStatement) {
			InvokeStatement st = (InvokeStatement) s;
			if (st.getReturnTargets().size() > 1) {
				Log.error("A method with too many return parameters! Should have been removed in SSA");
				return null;
			}
			ProverFun fun = procedure2ProverExpr(st.getInvokedProcedure());

			Log.error("This should not happen as calls are removed by SSA: "
					+ fun.toString());// TODO: proper error handling?
										// This can never happen.
			LinkedList<ProverExpr> args = new LinkedList<ProverExpr>();
			for (Expression e : st.getArguments()) {
				args.add(expression2ProverExpr(e));
			}
			ProverExpr ret = fun.mkExpr((ProverExpr[]) args
					.toArray(new ProverExpr[args.size()]));

			if (st.getReturnTargets().size() > 0) {
				ProverExpr lhs = expression2ProverExpr(st.getReturnTargets()
						.get(0));
				if (st.getReturnTargets().get(0) instanceof SimpleHeapAccess
						|| st.getReturnTargets().get(0) instanceof ArrayReadExpression) {
					ret = arrayWrite2ProverExpr(st.getReturnTargets().get(0),
							ret);
					// ((NAryExpression)lhs).addArgument(ret);
					// ret = VCExpressionGenerator.binOp(TmpConstants.Eq,
					// ((NAryExpression)lhs).getArgument(0),lhs);
				} else {
					ret = theoremProver.mkEq(lhs, ret);
				}
			}
			return ret;
		} else if (s instanceof ExpressionStatement) {
			ExpressionStatement es = (ExpressionStatement) s;
			return expression2ProverExpr(es.getExpression());
		} else {
			Log.error("Unmatched Statement " + s.toString());
			return null;
		}
	}

	/**
	 * Translates a guard in an axiom to a prover expression
	 * 
	 * @param exp
	 * @return
	 */
	private ProverExpr guardExpression2ProverExpr(Expression exp) {
		if (exp instanceof BinOpExpression) {
			/*
			 * TODO: this case should only occur for inlined axioms. The current
			 * type system is a bit messed up as it does not really allow
			 * boolean types in the Boogie program. If we do a major revision,
			 * we should definitely take care of this
			 */
			return expression2ProverExpr(exp);
		} else if (exp instanceof IteExpression) {
			return expression2ProverExpr(exp);
		} else {
			return theoremProver.mkEq(expression2ProverExpr(exp),
					theoremProver.mkLiteral(1));
		}
	}

	/**
	 * @param arrexp
	 * @param rhs
	 * @return
	 */
	private ProverExpr arrayWrite2ProverExpr(Expression arrexp, ProverExpr rhs) {
		if (arrexp instanceof SimpleHeapAccess
				|| arrexp instanceof ArrayReadExpression) {
			/*
			 * This is needed here only for one purpose: a[x] = 5 in Boogie is
			 * translated to a__i[x__j] = 5 in SSA-Boogie but in the VC we have
			 * to write (= a__i (store a__(i-1) x__j 5), so we need to be able
			 * to access the previous incarnation of array typed variables
			 * Probably, we should settle this already during SSA and introduce
			 * uninterpreted procedures for store and select
			 */
			Expression base;
			LinkedList<Expression> args = new LinkedList<Expression>();
			if (arrexp instanceof SimpleHeapAccess) {
				SimpleHeapAccess exp = (SimpleHeapAccess) arrexp;
				base = exp.getHeapVariable();
				args.add(exp.getBaseExpression());
				args.add(exp.getFieldExpression());
			} else {
				ArrayReadExpression exp = (ArrayReadExpression) arrexp;
				base = exp.getBaseExpression();
				args.add(exp.getIndexExpression());
			}
			ProverExpr newbase = expression2ProverExpr(base);
			ProverExpr lhs = arrayExpression2ProverExpr(base, args, rhs,
					new HashMap<Variable, ProverExpr>());

			return theoremProver.mkEq(newbase, lhs);
		}
		Log.error("CRAAAAAAAAAASH");
		return null;
	}

	/**
	 * @param base
	 * @param indices
	 * @param rhs
	 *            is null if we have Select operation, otherwise it is the value
	 *            E on the right hand side of an assignment a[x]=E.
	 * @param boundvars
	 * @return This is needed here only for one purpose: a[x] = 5 in Boogie is
	 *         translated to a__i[x__j] = 5 in SSA-Boogie but in the VC we have
	 *         to write (= a__i (store a__(i-1) x__j 5), so we need to be able
	 *         to access the previous incarnation of array typed variables
	 *         Probably, we should settle this already during SSA and introduce
	 *         uninterpreted procedures for store and select.
	 */
	private ProverExpr arrayExpression2ProverExpr(Expression base,
			LinkedList<Expression> indices, ProverExpr rhs,
			HashMap<Variable, ProverExpr> boundvars) {
		LinkedList<ProverExpr> args = new LinkedList<ProverExpr>();
		if (rhs != null) {
			if (base instanceof SSAVariable) {
				SSAVariable var = (SSAVariable) base;
				SSAVariable tmp = null;

				for (Variable v : proc.getVarIncarnationMap().get(
						((SSAVariable) base).getOriginalVar())) {
					if (v instanceof SSAVariable) {
						if (((SSAVariable) v).getIncarnation() == ((SSAVariable) base)
								.getIncarnation() - 1) {
							tmp = (SSAVariable) v;
							break;
						}
					}
				}
				if (tmp == null) {
					tmp = new SSAVariable(var.getOriginalVar(),
							var.getIncarnation() - 1);
					proc.getVarIncarnationMap()
							.get(((SSAVariable) base).getOriginalVar())
							.addFirst(tmp);
				}
				base = tmp;
			} else {
				Log.error("org.joogie.vcgen.VCGeneration.arrayaccess2VCExpression: this case has not been considered ... Joogie will crash!");
			}
		}
		ProverExpr arr = expression2ProverExpr(base, boundvars);
		for (Expression idx : indices) {
			args.add(expression2ProverExpr(idx, boundvars));
		}
		if (rhs != null)
			return theoremProver.mkStore(arr,
					(ProverExpr[]) (args.toArray(new ProverExpr[args.size()])),
					rhs);
		else
			return theoremProver.mkSelect(arr,
					(ProverExpr[]) (args.toArray(new ProverExpr[args.size()])));
	}

	/**
	 * generates a prover expression from an expression e
	 * 
	 * @param e
	 * @return
	 */
	private ProverExpr expression2ProverExpr(Expression e) {
		return this.expression2ProverExpr(e,
				new HashMap<Variable, ProverExpr>());
	}

	/**
	 * generates a prover expression from an expression e
	 * 
	 * @param e
	 * @param boundvars
	 * @return
	 */
	private ProverExpr expression2ProverExpr(Expression e,
			HashMap<Variable, ProverExpr> boundvars) {
		try {
			if (e instanceof ArrayReadExpression) {
				ArrayReadExpression exp = (ArrayReadExpression) e;

				return arrayExpression2ProverExpr(
						exp.getBaseExpression(),
						new LinkedList<Expression>(Arrays
								.asList(new Expression[] { exp
										.getIndexExpression() })), null,
						boundvars);
			} else if (e instanceof InvokeExpression) {
				InvokeExpression exp = (InvokeExpression) e;
				ProverFun fun = procedure2ProverExpr(exp.getInvokedProcedure());
				LinkedList<ProverExpr> args = new LinkedList<ProverExpr>();
				for (Expression e2 : exp.getArguments()) {
					args.add(expression2ProverExpr(e2, boundvars));
				}
				return fun.mkExpr((ProverExpr[]) args
						.toArray(new ProverExpr[args.size()]));
			} else if (e instanceof SimpleHeapAccess) {
				SimpleHeapAccess exp = (SimpleHeapAccess) e;
				return arrayExpression2ProverExpr(
						exp.getHeapVariable(),
						new LinkedList<Expression>(Arrays
								.asList(new Expression[] {
										exp.getBaseExpression(),
										exp.getFieldExpression() })), null,
						boundvars);
			} else if (e instanceof TypeExpression) {
				TypeExpression exp = (TypeExpression) e;
				return expression2ProverExpr(exp.getTypeVariable(), boundvars);
			} else if (e instanceof Variable) {
				Variable exp = (Variable) e;
				if (boundvars.containsKey(exp)) {
					return boundvars.get(exp);
				}
				if (!usedVariable.containsKey(exp)) {
					ProverExpr pe = theoremProver.mkVariable(
							getProverFriendlyName(exp.getName()),
							type2ProverSort(exp.getType()));
					usedVariable.put(exp, pe);
				}
				return usedVariable.get(exp);
			} else if (e instanceof UboundedIntConstant) {
				UboundedIntConstant exp = (UboundedIntConstant) e;
				return theoremProver.mkLiteral(BigInteger.valueOf(exp
						.getValue()));
			} else if (e instanceof Constant) {
				Log.error("DEBUG-ERROR, there should not be any constant but Integers! VC will be wrong!");
				return expression2ProverExpr(BoogieProgram.v()
						.getNullReference(), boundvars);
			} else if (e instanceof QuantifiedExpression) {
				// TODO: right now, Quantifiers can only be used in Axioms
				QuantifiedExpression qe = (QuantifiedExpression) e;
				HashMap<Variable, ProverExpr> bvars = new HashMap<Variable, ProverExpr>(
						boundvars);
				// LinkedList<ProverExpr> localBound = new
				// LinkedList<ProverExpr>();
				int idx = 0;
				for (Variable v : qe.getBoundVariables()) {
					ProverExpr boundvar = theoremProver.mkBoundVariable(idx++,
							type2ProverSort(v.getType()));
					bvars.put(v, boundvar);
					// localBound.add(boundvar);
				}
				ProverExpr boundExp = expression2ProverExpr(qe.getExpression(),
						bvars);
				if (qe.getQuantifier() == Quantifier.ForAll) {
					return theoremProver.mkAll(boundExp,
							theoremProver.getBooleanType());
				} else {
					return theoremProver.mkEx(boundExp,
							theoremProver.getBooleanType());
				}
			} else if (e instanceof BinOpExpression) {
				BinOpExpression be = (BinOpExpression) e;
				ProverExpr left = (expression2ProverExpr(be.getLhs(), boundvars));
				ProverExpr right = (expression2ProverExpr(be.getRhs(),
						boundvars));

				switch (be.getOp()) {
				case Eq: {
					return theoremProver.mkEq(left, right);
				}
				case Lt: {
					return theoremProver.mkLt(left, right);
				}
				case Le: {
					return theoremProver.mkLeq(left, right);
				}
				case Gt: {
					return theoremProver.mkGt(left, right);
				}
				case Ge: {
					return theoremProver.mkGeq(left, right);
				}
				case Neq: {
					return theoremProver.mkNot(theoremProver.mkEq(left, right));
				}
				case Implies: {
					return theoremProver.mkOr(theoremProver.mkNot(left), right);
				}
				case LAnd: {
					return theoremProver.mkAnd(left, right);
				}
				case LOr: {
					return theoremProver.mkOr(left, right);
				}
				case Plus: {
					return theoremProver.mkPlus(left, right);
				}
				case Minus: {
					return theoremProver.mkMinus(left, right);
				}
				case Mul: {
					return theoremProver.mkMult(left, right);
				}
				default: {
					throw new RuntimeException("Unmatched binop: "
							+ be.getOp().toString());
					// TODO: a proper exception might be nice.
					// However, this case can only occur if we screw up the
					// implementation
				}
				}
			} else if (e instanceof IteExpression) {
				IteExpression ite = (IteExpression) e;
				ProverExpr condE = expression2ProverExpr(ite.getCond(),
						boundvars);
				ProverExpr thenE = expression2ProverExpr(ite.getThen(),
						boundvars);
				ProverExpr elseE = expression2ProverExpr(ite.getElse(),
						boundvars);
				return theoremProver.mkIte(condE, thenE, elseE);
			} else {
				Log.error("Unmatched Expression " + e.toString());
				return null;
			}
		} catch (Exception exc) {
			Log.error("expression2ProverExpr failed: " + exc.toString());
			Log.error("Called on expression: " + e.toString());
			if (e instanceof BinOpExpression) {
				BinOpExpression boe = (BinOpExpression) e;
				Log.error(boe.getLhs().getType().toString() + " and "
						+ boe.getRhs().getType());
			}
			return null;
		}
	}

	private ProverFun procedure2ProverExpr(BoogieProcedure proc) {
		HashMap<Variable, ProverExpr> localbound = new HashMap<Variable, ProverExpr>();
		if (!usedFunctions.containsKey(proc)) {
			LinkedList<ProverType> args = new LinkedList<ProverType>();
			int idx = 0;
			for (Variable v : proc.getParameterList()) {
				ProverExpr arg = theoremProver.mkBoundVariable(idx++,
						type2ProverSort(v.getType()));
				args.add(arg.getType());
				localbound.put(v, arg);
			}

			ProverFun vcf = null;
			ProverType[] arr = args.toArray(new ProverType[args.size()]);
			if (proc.isPure() && proc.getRootBlock() != null
					&& proc.getRootBlock().getStatements().size() == 1) {
				// TODO: this is a hack:
				// we assume that this case only occurs for prelude functions
				// which have only one statement
				// this will not work in any other case
				Statement stmt = proc.getRootBlock().getStatements().get(0);
				ProverExpr b = null;
				if (stmt instanceof ExpressionStatement) {
					ExpressionStatement es = (ExpressionStatement) stmt;
					b = expression2ProverExpr(es.getExpression(), localbound);
				} else {
					throw new RuntimeException("procedure2ProverExpr failed");
				}
				vcf = theoremProver.mkDefinedFunction(
						getProverFriendlyName(proc.getName()), arr, b);
			} else {
				vcf = theoremProver.mkUnintFunction(
						getProverFriendlyName(proc.getName()), arr,
						type2ProverSort(proc.getReturnVariable().getType()));

				// TODO: uninterpreted functions?
			}
			usedFunctions.put(proc, vcf);
		}
		return usedFunctions.get(proc);
	}

	/**
	 * Translates a BoogieType to a Prover Type
	 * 
	 * @param t
	 * @return
	 */
	private ProverType type2ProverSort(BoogieType t) {
		if (t.getName().compareTo("int") == 0) {
			return theoremProver.getIntType();
		} else if (t.getName().compareTo("bool") == 0) {
			return theoremProver.getBooleanType();
		} else if (t.getName().compareTo("$stringsizetype") == 0) {
			ProverType[] argTypes = { theoremProver.getIntType() };
			return theoremProver.getArrayType(argTypes,
					theoremProver.getIntType());
		} else if (t instanceof BoogieFieldType) {
			return theoremProver.getIntType();
		} else if (t instanceof BoogieArrayType) {
			ProverType[] argTypes = { theoremProver.getIntType() };
			return theoremProver.getArrayType(argTypes,
					type2ProverSort(((BoogieArrayType) t).getNestedType()));
		} else if (t instanceof HeapType) {
			ProverType[] argTypes = { theoremProver.getIntType(),
					theoremProver.getIntType() };
			return theoremProver.getArrayType(argTypes,
					theoremProver.getIntType());
		} else if (t instanceof BoogieObjectType) {
			return theoremProver.getIntType();
		}
		// TODO: not tested!
		return theoremProver.getIntType();
	}

	/**
	 * replace all characters in the var name that might confuse the prover
	 * 
	 * @param name
	 * @return
	 */
	private String getProverFriendlyName(String name) {
		String newname = name.replace('.', 'P');
		newname = newname.replace('$', 'D');
		return newname;
	}

}
