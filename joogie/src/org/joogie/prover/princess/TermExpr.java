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

import java.math.BigInteger;

import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverType;

import ap.parser.IIntLit;
import ap.parser.ITerm;

class TermExpr implements ProverExpr {

	protected final ProverType type;
	protected final ITerm term;

	TermExpr(ITerm term, ProverType type) {
		this.term = term;
		this.type = type;
	}

	public String toString() {
		return term.toString();
	}

	public ProverType getType() {
		return type;
	}

	public BigInteger getIntLiteralValue() {
		if (term instanceof IIntLit)
			return new BigInteger(((IIntLit) term).value().toString());
		throw new RuntimeException();
	}

	public boolean getBooleanLiteralValue() {
		throw new RuntimeException();
	}

}
