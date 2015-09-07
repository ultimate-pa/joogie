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

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;

import org.joogie.util.FileIO;
import org.joogie.util.Log;

/**
 * Facade of the Princess Prover
 * 
 * @author arlt
 */
public class PrincessProver implements Prover {

	/**
	 * Verbosity flag
	 */
	protected boolean verbose;

	/**
	 * Backup of the default stdout
	 */
	protected PrintStream defaultStdout;

	/**
	 * Backup of the default stderr
	 */
	protected PrintStream defaultStderr;

	/**
	 * New stdout
	 */
	protected ByteArrayOutputStream stdout;

	/**
	 * New stderr
	 */
	protected ByteArrayOutputStream stderr;

	/**
	 * C-tor
	 */
	public PrincessProver() {
		verbose = false;
		stdout = new ByteArrayOutputStream();
		stderr = new ByteArrayOutputStream();
	}

	@Override
	public int check(String formula) {
		// filename for formula file
		String filename = FileIO.generateTempFileName("pri");

		try {
			// write formula to (temporary) file
			FileIO.toFile(formula, filename);

			// launch Princess
			redirectOutput(true);
			ap.CmdlMain.main(new String[] { filename });
			redirectOutput(false);

			// verbose?
			if (isVerbose()) {
				Log.error(getStderr());
				Log.debug(getStdout());
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		return 0;
	}

	@Override
	public String getModel() {
		return getStdout();
	}

	/**
	 * Redirects the output of Princess
	 * 
	 * @param redirect
	 *            true = enable redirect, false = disable redirect
	 */
	protected void redirectOutput(boolean redirect) {
		try {
			if (redirect) {
				// backup default outputs
				defaultStdout = System.out;
				defaultStderr = System.err;

				// create and set new outputs
				stdout = new ByteArrayOutputStream();
				stderr = new ByteArrayOutputStream();
				System.setOut(new PrintStream(stdout));
				System.setErr(new PrintStream(stderr));
			} else {
				// close new outputs
				stdout.close();
				stderr.close();

				// restore default outputs
				System.setOut(defaultStdout);
				System.setErr(defaultStderr);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Checks the output of Princess
	 * 
	 * @return true = formula is valid, false = formula is invalid
	 */
	protected boolean checkOutput() {
		String output = getStdout();
		// TODO: Extend checking of prover result
		return (output.indexOf("formula is valid") >= 0) ? true : false;
	}

	/**
	 * Enables and disables verbosity
	 * 
	 * @param verbose
	 *            true = enable verbosity, false = disable verbosity
	 */
	public void setVerbose(boolean verbose) {
		this.verbose = verbose;
	}

	/**
	 * Checks, if verbosity is on
	 * 
	 * @return true = verbosity is on, false = verbosity is off
	 */
	public boolean isVerbose() {
		return verbose;
	}

	/**
	 * Delivers the stdout of Princess
	 * 
	 * @return stdout of Princess as a string
	 */
	public String getStdout() {
		return stdout.toString();
	}

	/**
	 * Delivers the stderr of Princess
	 * 
	 * @return stderr of Princess as a string
	 */
	public String getStderr() {
		return stderr.toString();
	}

	/**
	 * For testing purposes
	 * 
	 * @param args
	 *            Command-line arguments
	 */
	public static void main(String[] args) {
		try {
			// test Princess
			Prover p = new PrincessProver();
			p.check("\\problem { 1 + 1 >= 2 }");
			Log.info(p.getModel());

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
