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

package org.joogie;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieAxiom;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.LocationTag;
import org.joogie.boogie.statements.AssumeStatement;
import org.joogie.js.JsTranslator;
import org.joogie.loopunwinding.AbstractLoopUnwinding;
import org.joogie.loopunwinding.HavocOnlyUnwinding;
import org.joogie.loopunwinding.LoopUnwinding;
import org.joogie.prover.ProverFactory;
import org.joogie.report.MethodInfo;
import org.joogie.report.Report;
import org.joogie.runners.SootRunner;
import org.joogie.soot.GlobalsCache;
import org.joogie.ssa.SSA;
import org.joogie.util.FileIO;
import org.joogie.util.Log;
import org.joogie.vcgeneration.VCGenerationThread;
import org.joogie.vcgeneration.VstteHelper;

import soot.SootMethod;

/**
 * Dispatcher
 * 
 * @author arlt
 */
public class Dispatcher {

	/**
	 * Timeout for VC-Generation (in milliseconds)
	 */
	public final static int VCGEN_TIMEOUT = 30000;

	/**
	 * Input
	 */
	private String input;

	/**
	 * Source folder
	 */
	private String sourceFolder;

	/**
	 * Output
	 */
	private String output;

	/**
	 * Report
	 */
	private Report report;

	/**
	 * Soot runner
	 */
	private SootRunner sootRunner;

	/**
	 * C-tor
	 * 
	 * @param input
	 *            Input
	 * @param sourceFolder
	 *            Source folder
	 * @param output
	 *            Output
	 * @param report
	 *            Report
	 */
	public Dispatcher(String input, String sourceFolder, String output,
			Report report) {
		this.input = input;
		this.sourceFolder = sourceFolder;
		this.output = output;
		this.report = report;
		this.sootRunner = new SootRunner();
	}

	/**
	 * Runs the dispatcher
	 */
	public void run() {
		try {
			if (input.endsWith(".js")) {
				Log.debug("Running JSTranslator: JavaScript to Boogie representation");
				runJsTranslator();
			} else {
				Log.debug("Running Soot: Java Bytecode to Boogie representation");
				runSoot();
			}
/*
			Log.debug("Running Loop Unwinding");
			runLoopUnwinding();
			Log.debug("Running SSA Analysis");
			runSSA();
			Log.debug("Checking for Infeasible Code");
			runVCGen();
			*/
			Log.debug("Done");

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Runs JSTranslator
	 */
	protected void runJsTranslator() {
		try {
			JsTranslator jst = new JsTranslator();
			jst.translateJs(input);

			// TODO: place this somewhere else
			// get Boogie program and save to file			
			String boogieProgram = BoogieProgram.v().toBoogie();
			FileIO.toFile(boogieProgram, output);

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Runs Soot
	 */
	protected void runSoot() {
		if (input.endsWith(".jar")) {
			// run with JAR file
			sootRunner.runWithJar(input, output, report);
		} else if ( input.endsWith(".java") ) {
			// run with Source file
			sootRunner.runWithSource(input, report);
		} else {
			// run with class file
			sootRunner.runWithClass(input, sourceFolder, output, report);
		}
	}

	/**
	 * Unwinds the loops
	 */
	protected void runLoopUnwinding() {
		// get Boogie program
		BoogieProgram prog = BoogieProgram.v();

		// unwind all loops
		for (BoogieProcedure proc : prog.getProcedures()) {
			Log.debug("Unwind: " + proc.getName());
			if (proc.getRootBlock() == null)
				continue;

			AbstractLoopUnwinding lu = null;
			switch (Options.v().getLUMode()) {
			case 0:
				lu = new HavocOnlyUnwinding(proc);
				break;

			case 1:
				lu = new LoopUnwinding(proc);
				break;

			default:
				throw new IllegalArgumentException();
			}

			// unwind the loops
			lu.unwind();
			proc.pruneUnreachable();
		}
	}

	/**
	 * Performs the single static assignment
	 */
	protected void runSSA() {
		// get Boogie program
		BoogieProgram prog = BoogieProgram.v();

		// SSA all procedures
		for (BoogieProcedure proc : prog.getProcedures()) {
			Log.debug("SSA: " + proc.getName());
			if (proc.isPure()) {
				Log.debug("no ssa for prelude functions please: "
						+ proc.getName());
				continue;
			}
			if (proc.getRootBlock() == null)
				continue;

			// TODO: replace "2" (VSTTE) by enum
			if (2 == Options.v().getVCMode()) {
				proc.vstteMap = VstteHelper.injectHelperVariables(proc);
			}

			/*
			 * TODO: this should only be done ONCE ... and not for every
			 * procedure. in order to use the axioms, we have to add them to the
			 * root block so that the SSA can update them. Otherwise, the proc
			 * body would speak about SsaVariables but the axioms would still
			 * speak about Variables. This causes double definitions and make
			 * the prover ignore the axioms. However, there might be a more
			 * elegant solution to this, for sure.
			 */
			for (BoogieAxiom bax : BoogieProgram.v().getAxioms()) {
				proc.getRootBlock().addStatement(
						new AssumeStatement(bax.getExpression()), true);
			}
			SSA ssa = new SSA(proc);
			ssa.doSSA();
		}
	}

	/**
	 * Generates the verification conditions
	 */
	protected void runVCGen() {
		// create executor
		ExecutorService executor = Executors.newSingleThreadExecutor();

		// get Boogie program
		BoogieProgram prog = BoogieProgram.v();
		ProverFactory pf = new org.joogie.prover.princess.PrincessProverFactory();
		//ProverFactory pf = new org.joogie.prover.smtprover.SMTProverFactory();

		// generate VC and detect infeasible code
		for (BoogieProcedure proc : prog.getProcedures()) {
			if (proc.isPure()) {
				Log.debug("do not try to verify prelude functions " + proc.getName());
				continue;
			}

			if (proc.getRootBlock() == null) {
				continue;
			}
			
			// find Soot method
			SootMethod method = GlobalsCache.v().findSootMethodForBoogieProcedure(proc);
			if (null == method)
				continue;

			// find method info
			MethodInfo methodInfo = report.getMethod(method);
			if (null == methodInfo)
				continue;

			// generate VC and detect infeasible code (in a thread)
			VCGenerationThread vcgenThread = new VCGenerationThread(pf, proc, methodInfo);
			final Future<?> future = executor.submit(vcgenThread);

			try {
				// start thread and wait 30 seconds
				Log.info("Checking procedure " + proc.getJavaName());
				future.get(VCGEN_TIMEOUT, TimeUnit.MILLISECONDS);

			} catch (TimeoutException e) {
				// set timeout to method info
				methodInfo.setTimeout(true);
				Log.info("Timeout reached for method " + proc.getName());

			} catch (Exception e) {
				e.printStackTrace();

			} finally {
				// shutdown prover
				vcgenThread.shutdownProver();

				// cancel thread if not done
				if (!future.isDone()) {
					future.cancel(true);
				}
			}

			// log time
			Log.info(String.format("    Method: %s", methodInfo.getFormattedTime()));

			// is method not infeasible?
			if ( !methodInfo.isInfeasible() )
				continue;

			// prepare report
			StringBuilder sb = new StringBuilder();
			sb.append(String
					.format("infeasible code in\r\n    class: %s\r\n    method: %s\r\n",
							method.getDeclaringClass().getName(),
							method.getName()));

			for (BasicBlock infeasibleBlock : methodInfo.getInfeasibleBlocks()) {
				// continue report preparation
				LocationTag locationTag = infeasibleBlock.getLocationTag();
				if (null == locationTag) {
					sb.append("    line: unknown");
				} else {
					sb.append(String.format("    line: %d\r\n", locationTag.getLineNumber()));
				}
			}

			// print report
			Log.info(sb.toString());
		}

		// clean up
		executor.shutdown();
		GlobalsCache.resetInstance();

		// log time
		Log.info(String.format("*** Methods: %s ***", report.getMethodCount()));
		Log.info(String.format("*** Infeasible Methods: %s ***", report.getInfeasibleMethodCount()));
		Log.info(String.format("*** Queries: %s ***", report.getQueryCount()));
		Log.info(String.format("*** Avg. Queries per Method: %s ***", report.getAvgQueryCount()));
		Log.info(String.format("*** Avg. Time per Method: %s ms ***", report.getAvgTimePerMethod()));
		Log.info(String.format("*** Avg. Time per Query: %s ms ***", report.getAvgTimePerQuery()));
		Log.info(String.format("*** TOTAL TIME: %s ms ***", report.getTime()));

		// to GNU plot file?
		if (Options.v().hasGnuPlotFile())
			report.toGnuPlot(Options.v().getGnuPlotFile());
	}

	/**
	 * Returns the Soot runner
	 * 
	 * @return Soot runner
	 */
	public SootRunner getSootRunner() {
		return sootRunner;
	}

}
