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

package org.joogie.prover.smtprover;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.joogie.prover.Prover;
import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverFun;
import org.joogie.prover.ProverListener;
import org.joogie.prover.ProverResult;
import org.joogie.prover.ProverType;
import org.joogie.prover.old.Z3ProverEx;

/**
 * @author schaef
 */
public class SMTProver implements Prover {

	protected SMTProverType intType = new SMTProverType("Int");
	protected SMTProverType boolType = new SMTProverType("Bool");
	protected HashSet<SMTProverType> arrayTypes = new HashSet<SMTProverType>();
	protected HashSet<SMTProverExpr> usedVariables = new HashSet<SMTProverExpr>();
	protected HashSet<SMTProverFun> fundecls = new HashSet<SMTProverFun>();
	private LinkedList<ProverExpr> boundVarStack = new LinkedList<ProverExpr>();
	private boolean firstRound = true;

	// private StringBuilder formula = new StringBuilder();
	private List<String> formulae = new LinkedList<String>();
	private int formulaeIndex = 0;
	
	// private Z3Prover z3 = new Z3Prover();
	private Z3ProverEx z3 = new Z3ProverEx();

	public SMTProver() {
		z3.createContext();
	}

	protected String getFormulae() {
		StringBuilder sb = new StringBuilder();
		for (String s : formulae) {
			sb.append(String.format("%s\n", s));
		}
		return sb.toString();
	}

	/*
	 * This procedure must be called only for the first query. After that
	 * variables should be defined and the rest is done with push and pop
	 */
	protected String buildDecels() {
		StringBuilder sb = new StringBuilder();
		sb.append("(set-logic AUFLIA)\n\n");
		for (SMTProverExpr v : this.usedVariables) {
			sb.append("(declare-fun ");
			sb.append(v.toString());
			sb.append(" () ");
			sb.append(v.getType().toString());
			sb.append(")\n");
		}
		for (SMTProverFun fun : this.fundecls) {
			sb.append(fun.toString());
		}
		sb.append("\n");
		return sb.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#getBooleanType()
	 */
	@Override
	public ProverType getBooleanType() {
		return this.boolType;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#getIntType()
	 */
	@Override
	public ProverType getIntType() {
		return this.intType;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.joogie.prover.Prover#getArrayType(org.joogie.prover.ProverType[],
	 * org.joogie.prover.ProverType)
	 */
	@Override
	public ProverType getArrayType(ProverType[] argTypes, ProverType resType) {
		StringBuilder sb = new StringBuilder();
		sb.append("(Array Int");
		for (ProverType arg : argTypes) {
			sb.append(" ");
			sb.append(arg.toString());
		}
		sb.append(")");
		String typename = sb.toString();
		for (SMTProverType typ : this.arrayTypes) {
			if (typ.toString() == typename) {
				return typ;
			}
		}
		SMTProverType at = new SMTProverType(typename);
		this.arrayTypes.add(at);
		return at;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkBoundVariable(int,
	 * org.joogie.prover.ProverType)
	 */
	@Override
	public ProverExpr mkBoundVariable(int deBruijnIndex, ProverType type) {
		SMTProverExpr boundVar = new SMTProverExpr(getUniqueBoundVarName(
				deBruijnIndex, type), type);
		this.boundVarStack.addLast(boundVar);
		return boundVar;
	}

	/**
	 * This is a hack and only used for the experiments. Name might not be
	 * unique, and wrong use of the API might cause them to show up in the wrong
	 * scope!
	 */
	private int boundVarNameCounter = 0;

	private String getUniqueBoundVarName(int deBruijnIndex, ProverType type) {
		String s = "smtprover_boundvar_" + (this.boundVarNameCounter++);
		return s;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkVariable(java.lang.String,
	 * org.joogie.prover.ProverType)
	 */
	@Override
	public ProverExpr mkVariable(String name, ProverType type) {
		SMTProverExpr v = new SMTProverExpr(name, type);
		this.usedVariables.add(v);
		return v;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkUnintFunction(java.lang.String,
	 * org.joogie.prover.ProverType[], org.joogie.prover.ProverType)
	 */
	@Override
	public ProverFun mkUnintFunction(String name, ProverType[] argTypes,
			ProverType resType) {
		SMTProverFun fun = new SMTProverFun(name, argTypes, resType);
		this.fundecls.add(fun);

		// clear the scope for bound variables
		this.boundVarStack.clear();

		return fun;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkDefinedFunction(java.lang.String,
	 * org.joogie.prover.ProverType[], org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverFun mkDefinedFunction(String name, ProverType[] argTypes,
			ProverExpr body) {
		SMTProverFun fun = new SMTProverFun(name, argTypes, body,
				this.boundVarStack);
		this.fundecls.add(fun);
		// clear the scope for bound variables
		this.boundVarStack.clear();
		return fun;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkAll(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverType)
	 */
	@Override
	public ProverExpr mkAll(ProverExpr body, ProverType type) {
		StringBuilder sb = new StringBuilder();
		sb.append("(forall");
		for (ProverExpr arg : this.boundVarStack) {
			sb.append(" (");
			sb.append(arg.toString());
			sb.append(" (");
			sb.append(arg.getType().toString());
			sb.append(")");
		}
		sb.append(body.toString());
		sb.append(")");
		// now clear the scope of bound vars
		this.boundVarStack.clear();
		return new SMTProverExpr(sb.toString(), type);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkEx(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverType)
	 */
	@Override
	public ProverExpr mkEx(ProverExpr body, ProverType type) {
		StringBuilder sb = new StringBuilder();
		sb.append("(exists");
		for (ProverExpr arg : this.boundVarStack) {
			sb.append(" (");
			sb.append(arg.toString());
			sb.append(" (");
			sb.append(arg.getType().toString());
			sb.append(")");
		}
		sb.append(body.toString());
		sb.append(")");
		// now clear the scope of bound vars
		this.boundVarStack.clear();
		return new SMTProverExpr(sb.toString(), type);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkEq(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkEq(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(= ");
		sb.append(left.toString());
		sb.append(" ");

		if (null == right)
			return null;

		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkLiteral(boolean)
	 */
	@Override
	public ProverExpr mkLiteral(boolean value) {
		return new SMTProverExpr(Boolean.toString(value), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkNot(org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkNot(ProverExpr body) {
		StringBuilder sb = new StringBuilder();
		sb.append("(not ");
		sb.append(body.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkAnd(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkAnd(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(and ");
		sb.append(left.toString());
		sb.append(" ");
		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkAnd(org.joogie.prover.ProverExpr[])
	 */
	@Override
	public ProverExpr mkAnd(ProverExpr[] args) {
		StringBuilder sb = new StringBuilder();
		sb.append("(and");
		for (ProverExpr arg : args) {
			sb.append(" ");
			sb.append(arg.toString());
		}
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkOr(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkOr(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(or ");
		sb.append(left.toString());
		sb.append(" ");
		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkOr(org.joogie.prover.ProverExpr[])
	 */
	@Override
	public ProverExpr mkOr(ProverExpr[] args) {
		StringBuilder sb = new StringBuilder();
		sb.append("(or");
		for (ProverExpr arg : args) {
			sb.append(" ");
			sb.append(arg.toString());
		}
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkIte(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr, org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkIte(ProverExpr cond, ProverExpr thenExpr,
			ProverExpr elseExpr) {
		StringBuilder sb = new StringBuilder();
		sb.append("(ite ");
		sb.append(cond.toString());
		sb.append(" ");
		sb.append(thenExpr.toString());
		sb.append(" ");
		sb.append(elseExpr.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), thenExpr.getType());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkLiteral(int)
	 */
	@Override
	public ProverExpr mkLiteral(int value) {
		return new SMTProverExpr(Integer.toString(value), this.intType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkLiteral(java.math.BigInteger)
	 */
	@Override
	public ProverExpr mkLiteral(BigInteger value) {
		return new SMTProverExpr(value.toString(), this.intType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkPlus(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkPlus(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(+ ");
		sb.append(left.toString());
		sb.append(" ");
		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.intType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkPlus(org.joogie.prover.ProverExpr[])
	 */
	@Override
	public ProverExpr mkPlus(ProverExpr[] args) {
		if (args.length==0) {
			return mkLiteral(0);
		}
		StringBuilder sb = new StringBuilder();		
		sb.append("(+");
		for (ProverExpr arg : args) {
			sb.append(" ");
			sb.append(arg.toString());
		}
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.intType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkMinus(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkMinus(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(- ");
		sb.append(left.toString());
		sb.append(" ");
		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.intType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkMult(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkMult(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(* ");
		sb.append(left.toString());
		sb.append(" ");
		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.intType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkGeq(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkGeq(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(>= ");
		sb.append(left.toString());
		sb.append(" ");
		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkGt(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkGt(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(> ");
		sb.append(left.toString());
		sb.append(" ");
		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkLeq(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkLeq(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(<= ");
		sb.append(left.toString());
		sb.append(" ");
		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkLt(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkLt(ProverExpr left, ProverExpr right) {
		StringBuilder sb = new StringBuilder();
		sb.append("(< ");
		sb.append(left.toString());
		sb.append(" ");
		sb.append(right.toString());
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.boolType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkSelect(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr[])
	 */
	@Override
	public ProverExpr mkSelect(ProverExpr ar, ProverExpr[] indexes) {
		StringBuilder sb = new StringBuilder();
		sb.append("(select ");
		sb.append(ar.toString());
		for (ProverExpr arg : indexes) {
			sb.append(" ");
			sb.append(arg.toString());
		}
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.intType);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#mkStore(org.joogie.prover.ProverExpr,
	 * org.joogie.prover.ProverExpr[], org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr mkStore(ProverExpr ar, ProverExpr[] indexes,
			ProverExpr value) {
		StringBuilder sb = new StringBuilder();

		sb.append("(store ");
		sb.append(ar.toString());
		for (ProverExpr arg : indexes) {
			sb.append(" ");
			sb.append(arg.toString());
		}
		sb.append(" ");
		sb.append(value.toString());
		sb.append(")");

		return new SMTProverExpr(sb.toString(), ar.getType());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#push()
	 */
	@Override
	public void push() {
		// formula.append("(push)\n");

		formulaeIndex = formulae.size();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#pop()
	 */
	@Override
	public void pop() {
		// formula.append("(pop)\n");

		while (formulae.size() == formulaeIndex) {
			formulae.remove(formulae.size() - 1);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#addAssertion(org.joogie.prover.ProverExpr)
	 */
	@Override
	public void addAssertion(ProverExpr assertion) {
		if (firstRound) {
			firstRound = false;
			// formula.append(buildDecels());
			formulae.add(buildDecels());
		}

		// formula.append(String.format("(assert %s)\n", assertion));
		formulae.add(String.format("(assert %s)\n", assertion));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#checkSat(boolean)
	 */
	@Override
	public synchronized ProverResult checkSat(boolean block) {
		if (!z3.hasContext()) {
			return ProverResult.Unknown;
		}

		try {
			// String formulaAsString = formula.toString();
			String formulaAsString = getFormulae();
			// Log.error(formulaAsString);
			// FileIO.toFile(formulaAsString, "C:/Temp/formula.txt");

			int result = z3.check(formulaAsString);
			if (1 == result) {
				String modelAsString = z3.getModel();
				// Log.error(modelAsString);
				// FileIO.toFile(modelAsString, "C:/Temp/model.txt");

				String[] model = modelAsString.split("\n");
				for (ProverExpr expr : usedVariables) {
					for (String m : model) {
						if (m.startsWith(expr.toString())) {
							String value = m.substring(m.indexOf(">") + 1);
							((SMTProverExpr) expr).setSmtValue(value.trim());
							break;
						}
					}
				}
				return ProverResult.Sat;
			} else if (-1 == result) {
				return ProverResult.Unsat;
			}

		} catch (Exception e) {
			e.printStackTrace();
		}

		return ProverResult.Error;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#nextModel(boolean)
	 */
	@Override
	public ProverResult nextModel(boolean block) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#getResult(boolean)
	 */
	@Override
	public ProverResult getResult(boolean block) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#stop()
	 */
	@Override
	public ProverResult stop() {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#setConstructProofs(boolean)
	 */
	@Override
	public void setConstructProofs(boolean b) {
		// TODO Auto-generated method stub
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#setPartitionNumber(int)
	 */
	@Override
	public void setPartitionNumber(int num) {
		// TODO Auto-generated method stub
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#interpolate(int[][])
	 */
	@Override
	public ProverExpr[] interpolate(int[][] partitionSeq) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.joogie.prover.Prover#addListener(org.joogie.prover.ProverListener)
	 */
	@Override
	public void addListener(ProverListener listener) {
		// TODO Auto-generated method stub
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#evaluate(org.joogie.prover.ProverExpr)
	 */
	@Override
	public ProverExpr evaluate(ProverExpr expr) {
		ProverType type = expr.getType();
		if (type.equals(intType))
			return mkLiteral(((SMTProverExpr) expr).evalIntValue());
		else if (type.equals(boolType))
			return mkLiteral(((SMTProverExpr) expr).evalBooleanValue());

		throw new RuntimeException();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#shutdown()
	 */
	@Override
	public synchronized void shutdown() {
		z3.deleteContext();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.Prover#reset()
	 */
	@Override
	public void reset() {
		// TODO Auto-generated method stub
	}

}
