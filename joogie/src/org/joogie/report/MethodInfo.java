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

package org.joogie.report;

import java.io.File;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.joogie.Dispatcher;
import org.joogie.Options;
import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.LocationTag;
import org.joogie.soot.BoogieHelpers;
import org.joogie.util.FileIO;
import org.joogie.util.Log;
import org.joogie.util.Util;

import soot.Body;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.util.Chain;

/**
 * Method Info
 * 
 * @author arlt
 */
public class MethodInfo implements Serializable {

	/**
	 * Soot body
	 */
	private Body body;

	/**
	 * List of queries
	 */
	private List<QueryInfo> queries = new ArrayList<QueryInfo>();

	/**
	 * List of infeasible blocks
	 */
	private List<BasicBlock> infeasibleBlocks = new ArrayList<BasicBlock>();

	/**
	 * Timeout flag
	 */
	private boolean hasTimeout = false;

	/**
	 * C-tor
	 * 
	 * @param body
	 *            Soot body
	 */
	public MethodInfo(Body body) {
		this.body = body;
	}

	/**
	 * Determines whether the method info has a timeout
	 * 
	 * @return true = Method info has a timeout
	 */
	public boolean hasTimeout() {
		return hasTimeout;
	}

	/**
	 * Determines whether the method info has a timeout
	 * 
	 * @param hasTimeout
	 *            true = Method info has a timeout
	 */
	public void setTimeout(boolean hasTimeout) {
		this.hasTimeout = hasTimeout;
	}

	/**
	 * Returns the name of the method
	 * 
	 * @return Name of the method
	 */
	public String getName() {
		SootMethod method = body.getMethod();
		return method.getSignature();
	}
	
	/**
	 * Returns a friendly name of the method
	 * 
	 * @return Friendly name of the method
	 */
	public String getFriendlyName() {
		SootMethod method = body.getMethod();
		return method.getName();
	}

	/**
	 * Returns the filename of the method
	 * 
	 * @param sourceDir
	 *            source directory
	 * @return Filename of the method
	 */
	public String getFileName(String sourceDir) {
		SootMethod method = body.getMethod();
		SootClass clazz = method.getDeclaringClass();
		return String.format("%s%s%s.java", sourceDir, File.separator, clazz
				.getName().replace('.', File.separatorChar));
	}

	/**
	 * Returns possible filenames of the method
	 * 
	 * @param sourceDir
	 *            source directory
	 * @return Possible filenames of the method
	 */
	public String[] getFileNames(String sourceDir) {
		SootMethod method = body.getMethod();
		SootClass clazz = method.getDeclaringClass();
		return FileIO.findFiles(sourceDir, clazz.getShortName() + ".java");
	}

	/**
	 * Returns the line number of the first infeasible block
	 * 
	 * @return Line number of the first infeasible block
	 */
	public int getLineNumber() {
		if (infeasibleBlocks.isEmpty()) {
			throw new RuntimeException(
					"Method does not contain infeasible blocks.");
		}

		// get block, tag, and return line number
		BasicBlock infeasibleBlock = infeasibleBlocks.get(0);
		LocationTag locationTag = infeasibleBlock.getLocationTag();
		return locationTag.getLineNumber();
	}

	/**
	 * Calculates the time of the analysis of the method
	 * 
	 * @return Time of the analysis of the method
	 */
	public long getTime() {
		if (hasTimeout()) {
			return Dispatcher.VCGEN_TIMEOUT;
		}

		long time = 0;
		for (QueryInfo qi : queries)
			time += qi.getTime();

		return time;
	}

	/**
	 * Returns the formatted time of the method analysis
	 * 
	 * @return Formatted time of the method analysis
	 */
	public String getFormattedTime() {
		return String.format("%d ms", getTime());
	}

	/**
	 * Returns the LOC
	 * 
	 * @return LOC
	 */
	public int getLOC() {
		Chain<Unit> units = body.getUnits();

		int firstLineNumber = Util.findLineNumber(units.getFirst().getTags());
		int lastLineNumber = Util.findLineNumber(units.getLast().getTags());

		if (0 == firstLineNumber || 0 == lastLineNumber)
			return 0;

		return lastLineNumber - firstLineNumber + 1;
	}

	/**
	 * Returns the number of units
	 * 
	 * @return Number of units
	 */
	public int getUnits() {
		return body.getUnits().size();
	}

	/**
	 * Returns the list of queries
	 * 
	 * @return List of queries
	 */
	public List<QueryInfo> getQueries() {
		return queries;
	}

	/**
	 * Returns the list of infeasible blocks
	 * 
	 * @return List of infeasible blocks
	 */
	public List<BasicBlock> getInfeasibleBlocks() {
		return infeasibleBlocks;
	}

	/**
	 * Checks whether the method contains infeasible blocks
	 * 
	 * @return true = method contains infeasible blocks
	 */
	public boolean isInfeasible() {
		// does method have a timeout?
		if (hasTimeout())
			return false;

		// suppress false positives?
		if (Options.v().isSuppressFalsePositives())
			if (isFalsePositiveInfeasible())
				return false;

		return !infeasibleBlocks.isEmpty();
	}

	/**
	 * Checks whether the method contains false positive infeasible blocks
	 * 
	 * @return true = method contains false positive infeasible blocks
	 */
	public boolean isFalsePositiveInfeasible() {
		if (!isInfeasible())
			return false;

		try {
			for (String filename : getFileNames(Options.v()
					.getSourceDir())) {
				String src = FileIO.fromFile(filename);
				if (src == null || src.isEmpty()) {
					Log.error("No source found for " + filename);
					return false;
				}

				String[] lines = src
						.split(System.getProperty("line.separator"));
				for (BasicBlock infeasibleBlock : new LinkedList<BasicBlock>(
						infeasibleBlocks)) {
					LocationTag locationTag = infeasibleBlock.getLocationTag();
					int linenr = locationTag.getLineNumber();
					if (linenr >= lines.length) {
						throw new RuntimeException(
								"The infeasible code is reported outside the source file.");
					}
					if (linenr < 0) {
						Log.error("We are very sorry, but we still have minor bugs.");
						infeasibleBlocks.remove(infeasibleBlock);
						continue;
					}

					int upperidx = BoogieHelpers.createLocationTag(
							body.getTags()).getLineNumber();
					if (upperidx < 0 || upperidx > linenr) {
						throw new RuntimeException(
								"Something is wrong with the location tags.");
					}
					String prefix = "";
					for (int i = upperidx; i <= linenr; i++) {
						prefix += lines[i];
					}

					boolean checkElseIf = true;

					int lastopen = prefix.lastIndexOf("{");
					int lastclose = prefix.lastIndexOf("}");

					/*
					 * this is the sound suppressor: look for unmatched opening
					 * brackets. if there is one, chop off everything until that
					 * bracket and check what happened before. if it is an
					 * "else if" with "&&" or a finally, suppress the warning as
					 * it might be a false positive.
					 */
					while (prefix.length() > 0 && lastopen > 0 && lastclose > 0) {
						if (lastopen >= lastclose) {
							prefix = prefix.substring(0, lastopen);
							// check what happened before this opening bracket
							String suffix = prefix.substring(lastclose,
									prefix.length());
							if (checkElseIf) {
								checkElseIf = false;
								if (suffix.contains("else")
										&& suffix.contains("if")
										&& (suffix.contains("&&") || suffix
												.contains("||"))) {
									Log.error("Suppressed false positive: else if with and");
									infeasibleBlocks.remove(infeasibleBlock);
									break;
								}
							}
							if (suffix.contains("finally")) {
								Log.error("Suppressed false positive: finally");
								infeasibleBlocks.remove(infeasibleBlock);
								break;
							}
						} else {
							// now we chop off everything for which we found a
							// pair of brackets
							prefix = prefix.substring(0, lastopen);
						}
						lastopen = prefix.lastIndexOf("{");
						lastclose = prefix.lastIndexOf("}");
					}
				}
			}
		} catch (Exception e) {
			return false;
		}

		return (infeasibleBlocks.size() == 0);
	}

}
