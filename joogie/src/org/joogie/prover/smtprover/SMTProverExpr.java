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

import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverType;

/**
 * @author schaef
 */
public class SMTProverExpr implements ProverExpr {

	private ProverType type;
	private String smtTerm = "";
	private String smtValue = "";

	public SMTProverExpr(String s, ProverType typ) {
		this.type = typ;
		this.smtTerm = s;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.ProverExpr#getType()
	 */
	@Override
	public ProverType getType() {
		return this.type;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.ProverExpr#getIntLiteralValue()
	 */
	@Override
	public BigInteger getIntLiteralValue() {
		return new BigInteger(smtTerm);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.prover.ProverExpr#getBooleanLiteralValue()
	 */
	@Override
	public boolean getBooleanLiteralValue() {
		return Boolean.parseBoolean(smtTerm);
	}

	public BigInteger evalIntValue() {
		return new BigInteger(smtValue);
	}

	public boolean evalBooleanValue() {
		return Boolean.parseBoolean(smtValue);
	}

	public void setSmtValue(String smtValue) {
		this.smtValue = smtValue;
	}

	@Override
	public String toString() {
		return String.format("%s", smtTerm);
	}

}
