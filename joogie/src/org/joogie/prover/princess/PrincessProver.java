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

package org.joogie.prover.princess;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.math.BigInteger;
import java.util.Collection;
import java.util.LinkedList;

import org.joogie.cfgPlugin.CFGPlugin;
import org.joogie.cfgPlugin.Util.Dag;
import org.joogie.prover.Prover;
import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverFun;
import org.joogie.prover.ProverListener;
import org.joogie.prover.ProverResult;
import org.joogie.prover.ProverType;

import scala.collection.JavaConversions;
import scala.collection.Seq;
import scala.collection.immutable.List;
import scala.collection.immutable.Set;
import scala.collection.mutable.ArrayBuffer;
import ap.SimpleAPI;
import ap.SimpleAPI.ProverStatus$;
import ap.basetypes.IdealInt$;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IExpression$;
import ap.parser.IFormula;
import ap.parser.IFormulaITE;
import ap.parser.IFunApp;
import ap.parser.IIntLit;
import ap.parser.INot;
import ap.parser.IPlus;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.parser.IVariable;

public class PrincessProver implements Prover {

	private SimpleAPI api;

	public PrincessProver() {
		api = SimpleAPI.spawn();
		// api = SimpleAPI.spawnWithAssertions();
	}

	public PrincessProver(String basename) {
		api = SimpleAPI.spawnWithLog(basename);
	}

	public ProverType getBooleanType() {
		return BoolType.INSTANCE;
	}

	public ProverType getIntType() {
		return IntType.INSTANCE;
	}

	public ProverType getArrayType(ProverType[] argTypes, ProverType resType) {
		return new ArrayType(argTypes.length);
	}

	public ProverExpr mkBoundVariable(int deBruijnIndex, ProverType type) {
		assert (!type.equals(getBooleanType()));
		return new TermExpr(new IVariable(deBruijnIndex), type);
	}

	public ProverExpr mkVariable(String name, ProverType type) {
		if (type.equals(getIntType())) {
			return new TermExpr(api.createConstant(name), type);
		}

		if (type.equals(getBooleanType())) {
			return new FormulaExpr(api.createBooleanVariable(name));
		}

		// array types
		return new TermExpr(api.createConstant(name), type);

		// throw new RuntimeException();
	}

	public ProverFun mkUnintFunction(String name, ProverType[] argTypes,
			ProverType resType) {
		return new PrincessFun(api.createFunction(name, argTypes.length),
				resType);
	}

	/**
	 * Define a new interpreted function. The body is supposed to contain bound
	 * variables with indexes <code>0, 1, ..., (n-1)</code> representing the
	 * arguments of the function.
	 */
	public ProverFun mkDefinedFunction(String name, ProverType[] argTypes,
			final ProverExpr body) {
		return new ProverFun() {
			public ProverExpr mkExpr(ProverExpr[] args) {
				final ArrayBuffer<ITerm> argsBuf = new ArrayBuffer<ITerm>();
				for (int i = 0; i < args.length; ++i)
					argsBuf.$plus$eq(((TermExpr) args[i]).term);
				final List<ITerm> argsList = argsBuf.toList();

				if (body instanceof TermExpr)
					return new TermExpr(IExpression$.MODULE$.subst(
							((TermExpr) body).term, argsList, 0),
							body.getType());
				else
					return new FormulaExpr(IExpression$.MODULE$.subst(
							((FormulaExpr) body).formula, argsList, 0));
			}
		};
	}

	public ProverExpr mkAll(ProverExpr body, ProverType type) {
		return new FormulaExpr(
				IExpression$.MODULE$.all(((FormulaExpr) body).formula));
	}

	public ProverExpr mkEx(ProverExpr body, ProverType type) {
		return new FormulaExpr(
				IExpression$.MODULE$.ex(((FormulaExpr) body).formula));
	}

	public ProverExpr mkEq(ProverExpr left, ProverExpr right) {
		if (left instanceof TermExpr)
			return new FormulaExpr(
					((TermExpr) left).term.$eq$eq$eq(((TermExpr) right).term));
		else
			return new FormulaExpr(
					((FormulaExpr) left).formula
							.$less$eq$greater(((FormulaExpr) right).formula));
	}

	public ProverExpr mkLiteral(boolean value) {
		return new FormulaExpr(new IBoolLit(value));
	}

	public ProverExpr mkNot(ProverExpr body) {
		return new FormulaExpr(new INot(((FormulaExpr) body).formula));
	}

	public ProverExpr mkAnd(ProverExpr left, ProverExpr right) {
		return new FormulaExpr(new IBinFormula(IBinJunctor.And(),
				((FormulaExpr) left).formula, ((FormulaExpr) right).formula));
	}

	public ProverExpr mkAnd(ProverExpr[] args) {
		final ArrayBuffer<IFormula> argsBuf = new ArrayBuffer<IFormula>();
		for (int i = 0; i < args.length; ++i)
			argsBuf.$plus$eq(((FormulaExpr) args[i]).formula);
		return new FormulaExpr(IExpression$.MODULE$.and(argsBuf));
	}

	public ProverExpr mkOr(ProverExpr left, ProverExpr right) {
		return new FormulaExpr(new IBinFormula(IBinJunctor.Or(),
				((FormulaExpr) left).formula, ((FormulaExpr) right).formula));
	}

	public ProverExpr mkOr(ProverExpr[] args) {
		final ArrayBuffer<IFormula> argsBuf = new ArrayBuffer<IFormula>();
		for (int i = 0; i < args.length; ++i)
			argsBuf.$plus$eq(((FormulaExpr) args[i]).formula);
		return new FormulaExpr(IExpression$.MODULE$.or(argsBuf));
	}

	public ProverExpr mkIte(ProverExpr cond, ProverExpr thenExpr,
			ProverExpr elseExpr) {
		if (thenExpr instanceof TermExpr)
			return new TermExpr(new ITermITE(((FormulaExpr) cond).formula,
					((TermExpr) thenExpr).term, ((TermExpr) elseExpr).term),
					thenExpr.getType());
		else
			return new FormulaExpr(new IFormulaITE(
					((FormulaExpr) cond).formula,
					((FormulaExpr) thenExpr).formula,
					((FormulaExpr) elseExpr).formula));
	}

	public ProverExpr mkLiteral(int value) {
		return new TermExpr(new IIntLit(IdealInt$.MODULE$.apply(value)),
				getIntType());
	}

	public ProverExpr mkLiteral(BigInteger value) {
		return new TermExpr(new IIntLit(IdealInt$.MODULE$.apply(value
				.toString())), getIntType());
	}

	public ProverExpr mkPlus(ProverExpr left, ProverExpr right) {
		return new TermExpr(new IPlus(((TermExpr) left).term,
				((TermExpr) right).term), getIntType());
	}

	public ProverExpr mkPlus(ProverExpr[] args) {
		final ArrayBuffer<ITerm> argsBuf = new ArrayBuffer<ITerm>();
		for (int i = 0; i < args.length; ++i)
			argsBuf.$plus$eq(((TermExpr) args[i]).term);
		return new TermExpr(IExpression$.MODULE$.sum(argsBuf), getIntType());
	}

	public ProverExpr mkMinus(ProverExpr left, ProverExpr right) {
		return new TermExpr(new IPlus(((TermExpr) left).term,
				((TermExpr) right).term.unary_$minus()), getIntType());
	}

	public ProverExpr mkMult(ProverExpr left, ProverExpr right) {
		return new TermExpr(
				((TermExpr) left).term.$times(((TermExpr) right).term),
				getIntType());
	}

	public ProverExpr mkGeq(ProverExpr left, ProverExpr right) {
		return new FormulaExpr(
				((TermExpr) left).term.$greater$eq(((TermExpr) right).term));
	}

	public ProverExpr mkGt(ProverExpr left, ProverExpr right) {
		return new FormulaExpr(
				((TermExpr) left).term.$greater(((TermExpr) right).term));
	}

	public ProverExpr mkLeq(ProverExpr left, ProverExpr right) {
		return new FormulaExpr(
				((TermExpr) left).term.$less$eq(((TermExpr) right).term));
	}

	public ProverExpr mkLt(ProverExpr left, ProverExpr right) {
		return new FormulaExpr(
				((TermExpr) left).term.$less(((TermExpr) right).term));
	}

	public ProverExpr mkSelect(ProverExpr ar, ProverExpr[] indexes) {
		final ArrayBuffer<ITerm> args = new ArrayBuffer<ITerm>();
		args.$plus$eq(((TermExpr) ar).term);
		for (int i = 0; i < indexes.length; ++i)
			args.$plus$eq(((TermExpr) indexes[i]).term);

		return new TermExpr(new IFunApp(api.selectFun(indexes.length),
				args.toSeq()), getIntType());
	}

	public ProverExpr mkStore(ProverExpr ar, ProverExpr[] indexes,
			ProverExpr value) {
		final ArrayBuffer<ITerm> args = new ArrayBuffer<ITerm>();
		args.$plus$eq(((TermExpr) ar).term);
		for (int i = 0; i < indexes.length; ++i)
			args.$plus$eq(((TermExpr) indexes[i]).term);
		args.$plus$eq(((TermExpr) value).term);

		return new TermExpr(new IFunApp(api.storeFun(indexes.length),
				args.toSeq()), getIntType());
	}

	// ////////////////////////////////////////////////////////////////////////////

	public void push() {
		api.push();
	}

	public void pop() {
		api.pop();
	}

	public void addAssertion(ProverExpr assertion) {
		api.addAssertion(((FormulaExpr) assertion).formula);
	}

	// ////////////////////////////////////////////////////////////////////////////

	public ProverResult checkSat(boolean block) {
		return translateRes(api.checkSat(block));
	}

	private ProverResult translateRes(scala.Enumeration.Value result) {
		if (result == ProverStatus$.MODULE$.Sat()
				|| result == ProverStatus$.MODULE$.Invalid())
			return ProverResult.Sat;
		else if (result == ProverStatus$.MODULE$.Unsat()
				|| result == ProverStatus$.MODULE$.Valid())
			return ProverResult.Unsat;
		else if (result == ProverStatus$.MODULE$.Unknown())
			return ProverResult.Unknown;
		else if (result == ProverStatus$.MODULE$.Running())
			return ProverResult.Running;
		else
			return ProverResult.Error;
	}

	public ProverResult getResult(boolean block) {
		return translateRes(api.getStatus(block));
	}

	public ProverResult nextModel(boolean block) {
		return translateRes(api.nextModel(block));
	}

	public ProverResult stop() {
		return translateRes(api.stop());
	}

	public void setConstructProofs(boolean b) {
		api.setConstructProofs(b);
	}

	public void setPartitionNumber(int num) {
		api.setPartitionNumber(num);
	}

	public ProverExpr[] interpolate(int[][] partitionSeq) {
		final ArrayBuffer<Set<Object>> args = new ArrayBuffer<Set<Object>>();
		for (int i = 0; i < partitionSeq.length; ++i) {
			final ArrayBuffer<Object> indexes = new ArrayBuffer<Object>();
			for (int j = 0; j < partitionSeq[i].length; ++j)
				indexes.$plus$eq(new Integer(partitionSeq[i][j]));
			args.$plus$eq(indexes.toSet());
		}

		final Seq<IFormula> ints = api.getInterpolants(args.toSeq());

		final ProverExpr[] res = new ProverExpr[partitionSeq.length - 1];
		for (int i = 0; i < partitionSeq.length - 1; ++i)
			res[i] = new FormulaExpr(ints.apply(i));

		return res;
	}

	public void addListener(ProverListener listener) {
		throw new RuntimeException();
	}

	public ProverExpr evaluate(ProverExpr expr) {
		if (expr instanceof TermExpr)
			return new TermExpr(new IIntLit(api.eval(((TermExpr) expr).term)),
					((TermExpr) expr).getType());
		else
			return new FormulaExpr(new IBoolLit(
					api.eval(((FormulaExpr) expr).formula)));
	}

	public void shutdown() {
		api.shutDown();
	}

	public void reset() {
		api.reset();
	}

	/*
	 * 
	 * class CFGPlugin(cfg : Dag[Predicate], effectualNodes : Seq[Predicate],
	 * ineffectualityFlags : Seq[Predicate], minEffectualNodesCovered : Int)
	 * extends Plugin {
	 */

	public void setupCFGPlugin(Dag<IFormula> dag,
			Collection<ProverExpr> blockVarExpr, Collection<ProverExpr> set,
			int threshold) {

		LinkedList<IFormula> scalaBlock = new LinkedList<IFormula>();
		for (ProverExpr exp : blockVarExpr) {
			scalaBlock.add(proverExpToIFormula(exp));
		}

		LinkedList<IFormula> scalaVar = new LinkedList<IFormula>();
		for (ProverExpr exp : set) {
			scalaVar.add(proverExpToIFormula(exp));
		}

		Seq<IFormula> scala_blocks = JavaConversions
				.asScalaIterable(scalaBlock).toSeq();
		Seq<IFormula> scala_rvars = JavaConversions.asScalaIterable(scalaVar)
				.toSeq();

		api.setupTheoryPlugin(CFGPlugin.apply(dag, scala_blocks, scala_rvars,
				threshold));
	}

	public IFormula proverExpToIFormula(ProverExpr exp) {
		return ((FormulaExpr) exp).formula;
	}

	public String proverExprToSMT(ProverExpr exp) {
		PrintStream originalOut = scala.Console.out();
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream newOut = new PrintStream(baos);
		scala.Console.setOut(newOut);
		ap.parser.SMTLineariser.apply(((FormulaExpr) exp).formula);
		scala.Console.flush();
		scala.Console.setOut(originalOut);
		return baos.toString();
	}
}
