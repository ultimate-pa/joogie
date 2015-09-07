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

import java.util.LinkedList;

import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverFun;
import org.joogie.prover.ProverType;
import org.joogie.util.Log;

/**
 * @author schaef
 */
public class SMTProverFun implements ProverFun {

	private String functionName;
	private ProverType retType;
	private LinkedList<ProverType> argTypes;

	// only for defined functions
	private LinkedList<ProverExpr> argVars = null;
	private ProverExpr body = null;

	public SMTProverFun(String fname, ProverType[] argTypes, ProverType rettype) {
		this.functionName = fname;
		this.retType = rettype;
		this.argTypes = new LinkedList<ProverType>();
		for (ProverType t : argTypes) {
			this.argTypes.add(t);
		}
	}

	public SMTProverFun(String fname, ProverType[] argTypes, ProverExpr body,
			LinkedList<ProverExpr> boundVarStack) {
		if (boundVarStack.size() != argTypes.length) {
			Log.error("Martin made a mistake while implementing the SMTProverFun! " + boundVarStack.size() + "!=" + argTypes.length);
			//throw new RuntimeException();
		}
		this.functionName = fname;
		this.retType = body.getType();
		this.argTypes = new LinkedList<ProverType>();
		for (ProverType t : argTypes) {
			this.argTypes.add(t);
		}
		argVars = new LinkedList<ProverExpr>(boundVarStack);
		this.body = body;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.ProverFun#mkExpr(org.joogie.prover.ProverExpr[])
	 */
	@Override
	public ProverExpr mkExpr(ProverExpr[] args) {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(this.functionName);
		for (ProverExpr arg : args) {
			sb.append(" ");
			sb.append(arg.toString());
		}
		sb.append(")");
		return new SMTProverExpr(sb.toString(), this.retType);
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if (this.argVars == null) {
			sb.append("(declare-fun ");
			sb.append(this.functionName);
			sb.append("(");
			for (ProverType t : this.argTypes) {
				sb.append(" ");
				sb.append(t.toString());
			}
			sb.append(")");
			sb.append(this.retType.toString());
		} else {
			sb.append("(define-fun ");
			sb.append(this.functionName);
			sb.append("(");
			for (ProverExpr v : this.argVars) {
				sb.append("(");
				sb.append(v.toString());
				sb.append(" ");
				sb.append(v.getType().toString());
				sb.append(")");
			}
			sb.append(") ");
			sb.append(this.retType.toString());
			sb.append(" ");
			sb.append(this.body.toString());
		}

		sb.append(")\n");
		return sb.toString();
	}

}
