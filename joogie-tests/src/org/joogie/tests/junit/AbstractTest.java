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

package org.joogie.tests.junit;

import org.joogie.report.Report;

/**
 * Abstract Test
 * @author arlt
 *
 */
public abstract class AbstractTest {
	
	/**
	 * JAR file
	 */
	protected String jarFile;
	
	/**
	 * Boogie File
	 */
	protected String boogieFile;
	
	/**
	 * Output File
	 */
	protected String outputFile;
	
	/**
	 * Source Directory
	 */
	protected String sourceDir;
	
	/**
	 * C-tor
	 */
	protected AbstractTest(String jarFile, String boogieFile, String outputFile, String sourceDir) {
		// init
		this.jarFile = jarFile;
		this.boogieFile = boogieFile;
		this.outputFile = outputFile;
		this.sourceDir = sourceDir;
	}
	
	/**
	 * Executes Soot and Boogie
	 * @return Report
	 */
	protected Report runSootAndBoogie() {
		/*
		// get Soot and Boogie
		SootRunner soot = SootRunner.getInstance();
		BoogieRunner boogie = BoogieRunner.getInstance();
		
		// create report
		Report report = new Report(jarFile);
		
		try {
			// run Soot
			soot.runWithJar(jarFile, boogieFile, report);
			
			// run Boogie
			boogie.addReceiver(new FileReceiver(new FileWriter(outputFile)));
			boogie.run(boogieFile);
			
			// build Report
			report.build(boogieFile, outputFile, sourceDir);
		
		} catch ( Exception e ) {
			e.printStackTrace();
			report = null;
		} finally {
			boogie.clearReceivers();
		}
		
		return report;
		*/
		
		return null;
	}

}
