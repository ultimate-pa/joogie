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

package org.joogie.ws;

import java.io.IOException;

import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.joogie.report.Report;
import org.joogie.ws.util.Examples;
import org.joogie.ws.util.Runner;

/**
 * @author arlt
 */
@SuppressWarnings("serial")
public class IndexServlet extends HttpServlet {

	public void doGet(HttpServletRequest req, HttpServletResponse resp)
			throws IOException {
		try {
			// load random example
			String example = Examples.v().getRandomExample(req.getServletContext());
			req.setAttribute("example", example);
			forward(req, resp);

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void doPost(HttpServletRequest req, HttpServletResponse resp)
			throws IOException {
		try {
			// run Joogie
			String code = req.getParameter("code");
			Report report = Runner.run(code);
			req.setAttribute("report", report);

		} catch (RuntimeException e) {
			req.setAttribute("error", e.getMessage());
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			forward(req, resp);
		}
	}
	
	protected void forward(HttpServletRequest req, HttpServletResponse resp) {
		try {
			// forward request
			req.getRequestDispatcher("index.jsp").forward(req, resp);
			
		} catch ( Exception e ) {
			e.printStackTrace();
		}
	}
	
}
