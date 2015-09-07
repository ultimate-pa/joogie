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

package org.joogie;

import org.kohsuke.args4j.Option;

/**
 * Options
 * 
 * @author arlt
 */
public class Options {

	/**
	 * Enable GUI mode
	 */
	@Option(name = "-g", usage = "Enable GUI mode")
	private boolean guiMode;

	/**
	 * Suppress False Positives
	 */
	@Option(name = "-sfp", usage = "Suppress False Positives")
	private boolean suppressFalsePositives;

	/**
	 * JAR file
	 */
	@Option(name = "-j", usage = "JAR file")
	private String jarFile;

	/**
	 * Boogie file
	 */
	@Option(name = "-b", usage = "Boogie file")
	private String boogieFile;

	/**
	 * Scope
	 */
	@Option(name = "-s", usage = "Scope")
	private String scope;

	/**
	 * Source directory
	 */
	@Option(name = "-c", usage = "Source (Code) directory")
	private String sourceDir;

	/**
	 * GNU plot file
	 */
	@Option(name = "-gp", usage = "GNU plot file")
	private String gnuPlotFile;

	/**
	 * Classpath
	 */
	@Option(name = "-cp", usage = "Classpath")
	private String classpath;

	/**
	 * Mode of the VC Generation
	 */
	@Option(name = "-vc", usage = "VC Generation Mode")
	private int vcMode = 3;

	/**
	 * Mode of the Loop Unwinding
	 */
	@Option(name = "-lu", usage = "Loop Unwinding Mode")
	private int luMode = 0;

	public enum HeapMode {
		Default, SimpleHeap
	}

	/**
	 * Heap Mode (whether to use the default heap model or not). In the future,
	 * other heap modes could be available, hence enum
	 */
	@Option(name = "-heap", usage = "Heap Mode: ( Default | SimpleHeap ).")
	private HeapMode heapMode = HeapMode.Default;

	/**
	 * Event Flow Graph. The name of the file containing the event flow graph
	 * for the generation of a procedure that reproduces the event flow.
	 */
	@Option(name = "-efg", usage = "Event Flow Graph XML file.")
	private String EFG;

	/**
	 * Determines, whether GUI mode is enabled
	 * 
	 * @return true = GUI mode is enabled
	 */
	public boolean isGUIMode() {
		return guiMode;
	}

	/**
	 * Determines, whether false positives are suppressed
	 * 
	 * @return true = false positives are suppressed
	 */
	public boolean isSuppressFalsePositives() {
		return suppressFalsePositives;
	}

	/**
	 * Returns the JAR file
	 * 
	 * @return JAR file
	 */
	public String getJarFile() {
		return jarFile;
	}

	/**
	 * Returns the Boogie file
	 * 
	 * @return Boogie file
	 */
	public String getBoogieFile() {
		return boogieFile;
	}

	/**
	 * Determines, whether Joogie has a scope
	 * 
	 * @return Scope of Joogie
	 */
	public boolean hasScope() {
		return (null != scope);
	}

	/**
	 * Returns the scope of Joogie
	 * 
	 * @return Scope of Joogie
	 */
	public String getScope() {
		return scope;
	}

	/**
	 * Returns the source directory
	 * 
	 * @return Source directory
	 */
	public String getSourceDir() {
		return sourceDir;
	}

	/**
	 * Determines, whether a GNU plot file is set
	 * 
	 * @return true = GNU plot file is set
	 */
	public boolean hasGnuPlotFile() {
		return (null != this.gnuPlotFile);
	}

	/**
	 * Returns the GNU plot file
	 * 
	 * @return GNU plot file
	 */
	public String getGnuPlotFile() {
		return gnuPlotFile;
	}

	/**
	 * Determines, whether Joogie has an additional classpath
	 * 
	 * @return true = Joogie has an additional classpath
	 */
	public boolean hasClasspath() {
		return (null != classpath);
	}

	/**
	 * Returns the additional classpath
	 * 
	 * @return Additional classpath
	 */
	public String getClasspath() {
		return classpath;
	}
	
	/**
	 * Assigns the additional classpath
	 * @param classpath Additional classpath
	 */
	public void setClasspath(String classpath) {
		this.classpath = classpath;
	}

	/**
	 * Returns the mode of the VC generation
	 * 
	 * @return Mode of the VC generation
	 */
	public int getVCMode() {
		return vcMode;
	}

	/**
	 * Returns the mode of the Loop Unwinding
	 * 
	 * @return Mode of the Loop Unwinding
	 */
	public int getLUMode() {
		return luMode;
	}

	/**
	 * Returns the heap mode of Joogie
	 * 
	 * @return
	 */
	public HeapMode getHeapMode() {
		return heapMode;
	}

	/**
	 * Returns the file name of the event flow graph.
	 * 
	 * @return Event flow graph
	 */
	public String getEFG() {
		return EFG;
	}

	/**
	 * Option object
	 */
	private static Options options;

	/**
	 * Singleton method
	 * 
	 * @return Options
	 */
	public static Options v() {
		if (null == options) {
			options = new Options();
		}
		return options;
	}

	/**
	 * C-tor
	 */
	private Options() {
		// do nothing
	}

}
