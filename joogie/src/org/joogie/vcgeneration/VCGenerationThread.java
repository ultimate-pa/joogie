/*
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

package org.joogie.vcgeneration;

import java.util.List;

import org.joogie.Options;
import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.prover.Prover;
import org.joogie.prover.ProverFactory;
import org.joogie.report.MethodInfo;

/**
 * @author arlt
 */
public class VCGenerationThread implements Runnable {

	/**
	 * Prover Factory
	 */
	private ProverFactory pf;

	/**
	 * Boogie Procedure
	 */
	private BoogieProcedure proc;

	/**
	 * Method information
	 */
	private MethodInfo methodInfo;

	/**
	 * Prover
	 */
	private Prover p;

	/**
	 * C-tor
	 * 
	 * @param pf
	 *            Prover Factory
	 * 
	 * @param proc
	 *            Boogie Procedure
	 * 
	 * @param methodInfo
	 *            Method information
	 */
	public VCGenerationThread(ProverFactory pf, BoogieProcedure proc,
			MethodInfo methodInfo) {
		this.pf = pf;
		this.proc = proc;
		this.methodInfo = methodInfo;
	}

	@Override
	public void run() {
		// spawn prover
		p = pf.spawn();

		AbstractVCGeneration vcg = null;
		switch (Options.v().getVCMode()) {
		case 0:
			vcg = new VCGeneration(proc, p, methodInfo);
			break;

		case 1:
			vcg = new VCGenerationEnablingClause(proc, p, methodInfo);
			break;

		case 2:
			vcg = new VCGenerationVstte(proc, p, methodInfo);
			break;

		case 3:
			vcg = new VCGenerationCfgTheory(proc, p, methodInfo);
			break;

		case 4:
			vcg = new VCGenerationExtWlp(proc, p, methodInfo);
			break;

		case 5:
			vcg = new VCGenerationExtWlpEffectual(proc, p, methodInfo);
			break;

		default:
			throw new IllegalArgumentException();
		}

		// generate VCs (returns list of infeasible blocks)
		List<BasicBlock> infeasibleBlocks = vcg.generateVerificationCondition();
		methodInfo.getInfeasibleBlocks().addAll(infeasibleBlocks);

		shutdownProver();
	}

	/**
	 * Shuts down the prover
	 */
	public void shutdownProver() {
		if (null == p)
			return;

		p.shutdown();
		p = null;
	}

}
