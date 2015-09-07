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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.LocationTag;
import org.joogie.report.MethodInfo;
import org.joogie.report.Report;
import org.joogie.ws.util.Runner;

import com.google.gson.Gson;

/**
 * @author arlt
 */
@SuppressWarnings("serial")
public class Rise4funRunServlet extends HttpServlet {

	public void doPost(HttpServletRequest req, HttpServletResponse resp)
			throws IOException {
		Rise4funRunRequest runReq = null;
		Rise4funRunResponse runResp = null;
		try {
			// convert request data
			Gson json = new Gson();
			BufferedReader reader = req.getReader();
			runReq = json.fromJson(reader, Rise4funRunRequest.class);
		
			// run Joogie
			runResp = new Rise4funRunResponse(runReq.Version);
			Report report = Runner.run(runReq.Source);
			
			// evaluate report
			if ( 0 == report.getInfeasibleMethodCount() ) {
				runResp.assignOutput("Joogie did not find infeasible code in this program");
			} else {
				List<String> outputs = new ArrayList<String>();
				for ( MethodInfo m : report.getInfeasibleMethods() ) {
			       for (BasicBlock infeasibleBlock : m.getInfeasibleBlocks()) {
			    	   String line = "unknown";
			    	   LocationTag locationTag = infeasibleBlock.getLocationTag();
			    	   if (null != locationTag) {
			    			line = new Integer(locationTag.getLineNumber()).toString();
			    	   }
			    	   String output = String.format("Foo.java(%s) : error C0001: infeasible code in method %s near line %s",
			    			   line, m.getFriendlyName(), line);
			    	   outputs.add(output);
			       }
				}
				runResp.assignOutput(outputs);
			}

		} catch (RuntimeException e) {
			runResp.assignOutput(e.getMessage());
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			// convert response
			Gson json = new Gson();
			String s = json.toJson(runResp);
	
			// send response
			resp.setCharacterEncoding("UTF-8");
			resp.setContentType("application/json");
			PrintWriter writer = resp.getWriter();
			writer.print(s);
			writer.flush();
		}
	}
	
}
