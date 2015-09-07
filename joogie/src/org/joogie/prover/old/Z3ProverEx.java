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

package org.joogie.prover.old;

import org.joogie.util.Log;

/**
 * Facade of the Z3 Prover. For each proof, the same context of Z3 used.
 * 
 * @author arlt
 */
public class Z3ProverEx {

	/**
	 * Load Joogie's Z3-Bridge
	 */
	static {
		System.loadLibrary("libjoogie-z3");
	}

	/**
	 * Creates a new context
	 * 
	 * @return true = success
	 */
	public native boolean createContext();

	/**
	 * Deletes an existing context
	 * 
	 * @return true = success
	 */
	public native boolean deleteContext();

	/**
	 * Checks whether a context is created
	 * 
	 * @return true = context is created
	 */
	public native boolean hasContext();

	/**
	 * Checks a SMT2 formula
	 * 
	 * @param string
	 *            SMT2 formula
	 * @return Result
	 */
	public native int check(String formula);

	/**
	 * Executes the push command
	 * 
	 * @return true = success
	 */
	public native boolean push();

	/**
	 * Executes the pop command
	 * 
	 * @return true = success
	 */
	public native boolean pop();

	/**
	 * Returns the model
	 * 
	 * @return Model
	 */
	public native String getModel();

	/**
	 * For testing purposes
	 * 
	 * @param args
	 *            Command-line arguments
	 */
	public static void main(String[] args) {
		try {
			Z3ProverEx p = new Z3ProverEx();
			p.createContext();

			String s = String.format("%s%s%s", "(set-logic QF_UF)",
					"(declare-fun p () Bool)", "(assert (and p p))");

			Log.info(p.check(s));
			p.deleteContext();

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
