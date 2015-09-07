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

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.joogie.util.FileIO;

import soot.SootMethod;

/**
 * Report
 * 
 * @author arlt
 */
public class Report implements Serializable {

	/**
	 * Map of methods
	 */
	private Map<SootMethod, MethodInfo> methods = new HashMap<SootMethod, MethodInfo>();

	/**
	 * C-tor
	 */
	public Report() {
		// do nothing
	}

	/**
	 * Adds a new method info
	 * 
	 * @param sootMethod
	 *            Soot method
	 */
	public void addMethod(SootMethod sootMethod) {
		methods.put(sootMethod, new MethodInfo(sootMethod.getActiveBody()));
	}

	/**
	 * Returns an existing method info
	 * 
	 * @param sootMethod
	 *            Soot method
	 * @return Method info
	 */
	public MethodInfo getMethod(SootMethod sootMethod) {
		if (!methods.containsKey(sootMethod))
			return null;

		return methods.get(sootMethod);
	}

	/**
	 * Returns the list of methods
	 * 
	 * @return List of methods
	 */
	public List<MethodInfo> getMethods() {
		return new ArrayList<MethodInfo>(methods.values());
	}

	/**
	 * Returns the list of infeasible methods
	 * 
	 * @return List of infeasible methods
	 */
	public List<MethodInfo> getInfeasibleMethods() {
		List<MethodInfo> methodInfos = new ArrayList<MethodInfo>();
		for (MethodInfo methodInfo : methods.values()) {
			if (!methodInfo.hasTimeout() && methodInfo.isInfeasible()) {
				methodInfos.add(methodInfo);
			}
		}
		return methodInfos;
	}

	/**
	 * Calculates the time of the analysis
	 * 
	 * @return Time of the analysis
	 */
	public long getTime() {
		long time = 0;
		for (MethodInfo methodInfo : methods.values())
			time += methodInfo.getTime();
		return time;
	}

	/**
	 * Returns the formatted time of the analysis
	 * 
	 * @return Formatted time of the analysis
	 */
	public String getFormattedTime() {
		return String.format("%d ms", getTime());
	}

	/**
	 * Returns the number of methods
	 * 
	 * @return Number of methods
	 */
	public int getMethodCount() {
		return methods.size();
	}

	/**
	 * Returns the number of infeasible methods
	 * 
	 * @return Number of infeasible methods
	 */
	public int getInfeasibleMethodCount() {
		return getInfeasibleMethods().size();
	}

	/**
	 * Returns the number of queries
	 * 
	 * @return Number of queries
	 */
	public int getQueryCount() {
		int queryCount = 0;
		for (MethodInfo method : methods.values()) {
			queryCount += method.getQueries().size();
		}
		return queryCount;
	}

	/**
	 * Returns the average number of queries per method
	 * 
	 * @return Queries per method
	 */
	public int getAvgQueryCount() {
		if (methods.size() == 0) {
			return 0;
		}
		return Math.round(getQueryCount() / methods.size());
	}

	/**
	 * Returns the average time per query
	 * 
	 * @return Time per query
	 */
	public long getAvgTimePerQuery() {
		if (getQueryCount() == 0) {
			return 0;
		}
		return Math.round(getTime() / getQueryCount());
	}

	/**
	 * Returns the average time per method
	 * 
	 * @return Time per method
	 */
	public long getAvgTimePerMethod() {
		if (methods.size() == 0) {
			return 0;
		}
		return Math.round(getTime() / methods.size());
	}

	/**
	 * Exports the report to GnuPlot
	 * 
	 * @param filename
	 *            Filename
	 */
	public void toGnuPlot(String filename) {
		StringBuffer sb = new StringBuffer();
		for (MethodInfo methodInfo : methods.values()) {
			int methodSize = methodInfo.getUnits();
			double methodTime = methodInfo.getTime();
			methodTime /= 1000; // convert time (milliseconds to seconds)
			sb.append(String.format("%d %.3f\r\n", methodSize, methodTime));
		}
		FileIO.toFile(sb.toString(), filename);
	}

}
