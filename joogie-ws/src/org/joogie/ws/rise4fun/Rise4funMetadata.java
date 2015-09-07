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

import javax.servlet.ServletContext;

import org.joogie.ws.util.Examples;

/**
 * @author arlt
 */
public class Rise4funMetadata {

	String Name = "joogie";

	String DisplayName = "Joogie";

	String Version = "1.0.0.2";

	String Email = "info@joogie.org";

	String SupportEmail = "info@joogie.org";

	String TermsOfUseUrl = "http://www.joogie.org/termsofuse";

	String PrivacyUrl = "http://www.joogie.org/privacy";

	String Institution = "Albert-Ludwigs-Universität Freiburg";

	String InstitutionUrl = "http://swt.informatik.uni-freiburg.de";

	String InstitutionImageUrl = "http://swt.informatik.uni-freiburg.de/unilogo-200x66.gif";

	String MimeType = "text/x-java-source";

	boolean SupportsLanguageSyntax = false;

	String Title = "Infeasible Code Detection for Java";

	String Description = "We present Joogie, a tool that detects infeasible code in Java programs. Infeasible code is code that is either not forward- or backward-reachable. Infeasible code comprises many errors detected by static analysis in modern IDEs such as guaranteed null-pointer dereference or unreachable code. The intriguing property of infeasible code is that it can be detected in a modular, cheap, and precise way."
			+ "Unlike existing techniques, Joogie identifies infeasible code by proving that a particular statement cannot occur on a terminating execution using techniques from static verification. Thus, Joogie is able to detect infeasible code which is overlooked by existing tools. Joogie works fully automatic, it does not require user-provided specifications and (almost) never produces false warnings.";

	String Question = "Does this program contain infeasible code?";

	String Url = "http://sotec.informatik.uni-freiburg.de/joogie/";

	Rise4funMetadataSample Samples[];

	public Rise4funMetadata(ServletContext ctx) {
		// convert all examples
		String[] examples = Examples.v().getExamples(ctx);
		List<Rise4funMetadataSample> samples = new ArrayList<Rise4funMetadataSample>();
		for (int i = 0; i < examples.length; i++) {
			String example = examples[i];
			Rise4funMetadataSample sample = new Rise4funMetadataSample(
					"Example " + (i + 1), example);
			samples.add(sample);
		}

		// assign all examples
		Samples = samples.toArray(new Rise4funMetadataSample[samples.size()]);
	}

}
