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

import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverFun;
import org.joogie.prover.ProverType;

import scala.collection.mutable.ArrayBuffer;
import ap.parser.IExpression$;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.ITerm;

class PrincessFun implements ProverFun {

	private final IFunction fun;
	private final ProverType resType;

	PrincessFun(IFunction fun, ProverType resType) {
		this.fun = fun;
		this.resType = resType;
	}

	public ProverExpr mkExpr(ProverExpr[] args) {
		final ArrayBuffer<ITerm> argsBuf = new ArrayBuffer<ITerm>();
		for (int i = 0; i < args.length; ++i)
			argsBuf.$plus$eq(((TermExpr) args[i]).term);

		final ITerm t = new IFunApp(fun, argsBuf.toSeq());

		if (resType instanceof BoolType)
			return new FormulaExpr(IExpression$.MODULE$.eqZero(t));
		else
			return new TermExpr(t, resType);
	}

	public String toString() {
		return fun.toString();
	}

}
