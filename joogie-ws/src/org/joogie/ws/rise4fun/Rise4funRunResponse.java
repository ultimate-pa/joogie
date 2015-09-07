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

package org.joogie.ws.rise4fun;

import java.util.ArrayList;
import java.util.List;

/**
 * @author arlt
 */
public class Rise4funRunResponse {

	String Version;

	Rise4funRunResponseOutput[] Outputs;
	
	public Rise4funRunResponse(String Version) {
		this.Version = Version;
	}
	
	public void assignOutput(String output) {
		Outputs = new Rise4funRunResponseOutput[]{
				new Rise4funRunResponseOutput("text/plain", output)};
	}
	
	public void assignOutput(List<String> outputs) {
		List<Rise4funRunResponseOutput> Outputs = new ArrayList<Rise4funRunResponseOutput>();
		for ( String output : outputs ) {
			Rise4funRunResponseOutput Output = new Rise4funRunResponseOutput("text/plain", output);
			Outputs.add(Output);
		}		
		this.Outputs = Outputs.toArray(new Rise4funRunResponseOutput[Outputs.size()]); 
	}

}
