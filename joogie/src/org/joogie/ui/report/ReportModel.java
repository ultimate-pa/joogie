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

package org.joogie.ui.report;

import java.util.List;

import javax.swing.ListModel;
import javax.swing.event.ListDataListener;

import org.joogie.report.MethodInfo;

/**
 * Report Model
 * 
 * @author arlt
 */
public class ReportModel implements ListModel<String> {

	/**
	 * List of infeasible methods
	 */
	private List<MethodInfo> infeasibleMethods;

	/**
	 * C-tor
	 * 
	 * @param infeasibleMethods
	 *            Infeasible methods
	 */
	public ReportModel(List<MethodInfo> infeasibleMethods) {
		this.infeasibleMethods = infeasibleMethods;
	}

	@Override
	public void addListDataListener(ListDataListener arg0) {
		// do nothing
	}

	@Override
	public String getElementAt(int arg0) {
		MethodInfo method = infeasibleMethods.get(arg0);
		return String.format("Method: %s; Line: %d", method.getName(),
				method.getLineNumber());
	}

	@Override
	public int getSize() {
		return infeasibleMethods.size();
	}

	@Override
	public void removeListDataListener(ListDataListener arg0) {
		// do nothing
	}

}
