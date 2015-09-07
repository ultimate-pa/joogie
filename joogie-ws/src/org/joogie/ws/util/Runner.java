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

package org.joogie.ws.util;

import java.io.File;
import java.io.FileWriter;
import java.util.UUID;

import org.joogie.Dispatcher;
import org.joogie.Options;
import org.joogie.boogie.BoogieProgram;
import org.joogie.report.Report;

/**
 * @author arlt
 */
public class Runner {
	
	/**
	 * Paths where the posts are stored
	 */
	final static String PATH_POSTS = "/tmp";

	/**
	 * Max length of a program to be checked
	 */
	final static int MAX_LENGTH = 1024;
	
	/**
	 * Runs Joogie
	 * @param code Code of the program to be checked
	 * @return Report object
	 */
	public static Report run(String code) throws Exception {
		// pre-analyze code
		if (code.length() > MAX_LENGTH) {
			throw new RuntimeException("Sorry, this program is too large for this web service.");
		}
		if (code.contains("package ") || code.contains("import ")) {
			throw new RuntimeException("Sorry, the keywords 'package' and 'import' are not allowed in this web service.");
		}

		// create UUID
		String uuid = String.format("Joogie%s", UUID.randomUUID().toString().replace("-", ""));
		String fileName = String.format("%s.java", uuid);
		String pathName = String.format("%s/%s", PATH_POSTS, fileName);
		String clazz = String.format("public class %s {}", uuid);

		// create source file
		File sourceFile = new File(pathName);
		FileWriter fw = new FileWriter(sourceFile);
		fw.write(String.format("%s %s", clazz, code));
		fw.flush();
		fw.close();

		// run Joogie
		Options.v().setClasspath(PATH_POSTS);
		Report report = new Report();
		Dispatcher dispatcher = new Dispatcher(fileName, null, null, report);
		dispatcher.run();
		
		// delete source file
		sourceFile.delete();

		// valid Boogie program?
		if (0 == BoogieProgram.v().getProcedures().size()) {
			throw new RuntimeException("Sorry, Joogie could not check this program.");
		}
		
		return report;
	}

}
