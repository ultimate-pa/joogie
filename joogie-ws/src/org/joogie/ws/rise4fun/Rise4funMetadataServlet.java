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

import java.io.IOException;
import java.io.PrintWriter;

import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import com.google.gson.Gson;

/**
 * @author arlt
 */
@SuppressWarnings("serial")
public class Rise4funMetadataServlet extends HttpServlet {

	public void doGet(HttpServletRequest req, HttpServletResponse resp)
			throws IOException {
		try {
			// convert metadata
			Gson json = new Gson();
			Rise4funMetadata metadata = new Rise4funMetadata(req.getServletContext());
			String s = json.toJson(metadata);
	
			// send response
			resp.setCharacterEncoding("UTF-8");
			resp.setContentType("application/json");
			PrintWriter writer = resp.getWriter();
			writer.print(s);
			writer.flush();
			
		} catch ( Exception e ) {
			e.printStackTrace();
		}
	}

}
