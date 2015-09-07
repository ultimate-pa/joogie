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

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;

import org.joogie.util.FileIO;
import org.joogie.util.Log;

/**
 * Facade of the Z3 Prover. For each proof, a new process of Z3 is launched.
 * 
 * @author arlt
 */
public class Z3Prover implements Prover {

	/**
	 * Model
	 */
	private String model;

	@Override
	public int check(String formula) {
		// filename for formula file
		String filename = FileIO.generateTempFileName("smt2");

		int result = 0;
		StringBuffer sb = new StringBuffer();

		try {
			// write formula to (temporary) file
			FileIO.toFile(formula + "\n(check-sat)\n(get-model)", filename);

			// launch Z3
			Process process = Runtime.getRuntime().exec(
					"z3.exe /ini:C:\\Temp\\z3.ini /smt2 " + filename);

			// init Z3 stream
			BufferedReader r = new BufferedReader(new InputStreamReader(
					process.getInputStream()));

			// wait for Z3
			process.waitFor();

			String line;
			boolean firstLine = true;

			// read Z3's output
			while (null != (line = r.readLine())) {
				if (firstLine) {
					firstLine = false;
					if (0 == line.compareToIgnoreCase("sat"))
						result = 1;
					else if (0 == line.compareToIgnoreCase("unsat"))
						result = -1;
					else
						result = 0;
				} else {
					sb.append(line.replace("\"", "") + "\n");
				}
			}

			// assign model
			model = sb.toString();

		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			// delete (temporary) formula file
			new File(filename).delete();
		}

		return result;
	}

	@Override
	public String getModel() {
		return model;
	}

	/**
	 * For testing purposes
	 * 
	 * @param args
	 *            Command-line arguments
	 */
	public static void main(String[] args) {
		try {
			// test Z3
			Prover p = new Z3Prover();
			int result = p.check("(declare-const a Int)"
					+ "(declare-fun f (Int Bool) Int)" + "(assert (> a 10))"
					+ "(assert (< (f a true) 100))");
			Log.info(result);
			Log.info(p.getModel());

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
