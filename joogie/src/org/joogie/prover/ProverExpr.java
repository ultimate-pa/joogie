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

public interface ProverExpr {
	ProverType getType();

	BigInteger getIntLiteralValue();

	boolean getBooleanLiteralValue();

	// to add: more functions for querying the kind, structure, contents of
	// expression
}