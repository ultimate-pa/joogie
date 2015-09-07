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

/**
 * @author arlt
 */
public class QueryInfo {

	/**
	 * Time
	 */
	private long time;

	/**
	 * Size of blocking / enabling clause
	 */
	private int size;

	/**
	 * Returns the time
	 * 
	 * @return Time
	 */
	public long getTime() {
		return time;
	}

	/**
	 * Sets the time
	 * 
	 * @param time
	 *            Time
	 */
	public void setTime(long time) {
		this.time = time;
	}

	/**
	 * Returns the query size
	 * 
	 * @return Query size
	 */
	public int getSize() {
		return size;
	}

	/**
	 * Sets the query size
	 * 
	 * @param size
	 *            Query size
	 */
	public void setSize(int size) {
		this.size = size;
	}

	/**
	 * Returns the formatted time of the query
	 * 
	 * @return Formatted time
	 */
	public String getFormattedTime() {
		return String.format("%d ms", getTime());
	}

}
