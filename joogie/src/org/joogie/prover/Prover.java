/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2012 Martin Schaef, Stephan Arlt, Sergio Feo, and Philipp Ruemmer
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

package org.joogie.prover;

import java.math.BigInteger;

public interface Prover {

	// Types
	ProverType getBooleanType();

	ProverType getIntType();

	ProverType getArrayType(ProverType[] argTypes, ProverType resType);

	// Variables
	ProverExpr mkBoundVariable(int deBruijnIndex, ProverType type);

	ProverExpr mkVariable(String name, ProverType type);

	ProverFun mkUnintFunction(String name, ProverType[] argTypes,
			ProverType resType);

	/**
	 * Define a new interpreted function. The body is supposed to contain bound
	 * variables with indexes <code>0, 1, ..., (n-1)</code> representing the
	 * arguments of the function.
	 */
	ProverFun mkDefinedFunction(String name, ProverType[] argTypes,
			ProverExpr body);

	// Quantifiers
	ProverExpr mkAll(ProverExpr body, ProverType type);

	ProverExpr mkEx(ProverExpr body, ProverType type);

	// Equations (applicable to all types) (also have n-ary version?)
	ProverExpr mkEq(ProverExpr left, ProverExpr right);

	// Propositional (also have n-ary versions?)
	ProverExpr mkLiteral(boolean value);

	ProverExpr mkNot(ProverExpr body);

	ProverExpr mkAnd(ProverExpr left, ProverExpr right);

	ProverExpr mkAnd(ProverExpr[] args);

	ProverExpr mkOr(ProverExpr left, ProverExpr right);

	ProverExpr mkOr(ProverExpr[] args);

	ProverExpr mkIte(ProverExpr cond, ProverExpr thenExpr, ProverExpr elseExpr);

	// Arithmetic
	ProverExpr mkLiteral(int value);

	ProverExpr mkLiteral(BigInteger value);

	ProverExpr mkPlus(ProverExpr left, ProverExpr right);

	ProverExpr mkPlus(ProverExpr[] args);

	ProverExpr mkMinus(ProverExpr left, ProverExpr right);

	ProverExpr mkMult(ProverExpr left, ProverExpr right);

	ProverExpr mkGeq(ProverExpr left, ProverExpr right);

	ProverExpr mkGt(ProverExpr left, ProverExpr right);

	ProverExpr mkLeq(ProverExpr left, ProverExpr right);

	ProverExpr mkLt(ProverExpr left, ProverExpr right);

	ProverExpr mkSelect(ProverExpr ar, ProverExpr[] indexes);

	ProverExpr mkStore(ProverExpr ar, ProverExpr[] indexes, ProverExpr value);

	// Maintain assertion stack (affects assertions and variable declarations)
	void push();

	void pop();

	void addAssertion(ProverExpr assertion);

	/**
	 * Check satisfiability of the currently asserted formulae. Will block until
	 * completion if <code>block</code> argument is true, otherwise return
	 * immediately.
	 */
	ProverResult checkSat(boolean block);

	/**
	 * After a <code>Sat</code> result, continue searching for the next model.
	 * In most ways, this method behaves exactly like <code>checkSat</code>.
	 */
	ProverResult nextModel(boolean block);

	/**
	 * Query result of the last <code>checkSat</code> or <code>nextModel</code>
	 * call. Will block until a result is available if <code>block</code>
	 * argument is true, otherwise return immediately.
	 */
	ProverResult getResult(boolean block);

	/**
	 * Stop a running prover. If the prover had already terminated, give same
	 * result as <code>getResult</code>, otherwise <code>Unknown</code>.
	 */
	ProverResult stop();

	/**
	 * Construct proofs in subsequent <code>checkSat</code> calls. Proofs are
	 * needed for extract interpolants.
	 */
	void setConstructProofs(boolean b);

	/**
	 * Add subsequent assertions to the partition with index <code>num</code>.
	 * Index <code>-1</code> represents formulae belonging to all partitions
	 * (e.g., theory axioms).
	 */
	void setPartitionNumber(int num);

	/**
	 * If the last call to <code>checkSat</code> returned <code>Unsat</code>,
	 * compute an inductive sequence of interpolants for the given ordering of
	 * the input formulae. Each element of <code>partitionSeq</code> represents
	 * a set of input formulae.
	 */
	ProverExpr[] interpolate(int[][] partitionSeq);

	/**
	 * Listeners that are notified about the results of (non-blocking) calls to
	 * <code>checkSat</code> or <code>nextModel</code>.
	 */
	void addListener(ProverListener listener);

	/**
	 * Evaluate an expression to a literal, in the current model of the prover.
	 * This function must only be used if the result of the last
	 * <code>checkSat</code> or <code>nextModel</code> was <code>Sat</code>.
	 */
	ProverExpr evaluate(ProverExpr expr);

	/**
	 * Shutdown this prover and release resources. (Might stop threads used
	 * internally to implement the prover, etc.)
	 */
	void shutdown();

	/**
	 * Reset to initial state
	 */
	void reset();

}
