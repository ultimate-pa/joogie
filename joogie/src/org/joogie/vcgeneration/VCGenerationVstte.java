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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.Statement;
import org.joogie.prover.Prover;
import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverResult;
import org.joogie.report.MethodInfo;
import org.joogie.util.Log;

/**
 * @author schaef
 */
public class VCGenerationVstte extends AbstractVCGeneration {

	/**
	 * C-tor
	 * 
	 * @param proc
	 *            Boogie procedure
	 * @param prover
	 *            Prover
	 * @param methodInfo
	 *            Method information
	 */
	public VCGenerationVstte(BoogieProcedure proc, Prover prover,
			MethodInfo methodInfo) {
		super(methodInfo);
		this.proc = proc;
		this.theoremProver = prover;
	}

	public LinkedList<BasicBlock> generateVerificationCondition() {

		HashMap<BasicBlock, ProverExpr> blockVars = new HashMap<BasicBlock, ProverExpr>();
		LinkedList<ProverExpr> terms = new LinkedList<ProverExpr>();

		// compute for each basic block Bi: Reach_i == not wlp(Bi, /\(not
		// B_successors))
		ProverExpr firstblockreachable = createFwdReachability(
				proc.getRootBlock(), blockVars, terms);
		// assert that wlp for the first block can be satisfied
		terms.add(firstblockreachable);
		// assert everything
		for (ProverExpr pexp : terms) {
			addAssertion(pexp);
		}

		HashMap<BasicBlock, ProverExpr> helperVariabels = new HashMap<BasicBlock, ProverExpr>();
		for (Entry<BasicBlock, Variable> entry : VstteHelper.getSSAHelperVars(
				this.proc).entrySet()) {
			// for some reason we cannot use contains here ... but I dont care
			// as this is only for testing anyway.
			if (!usedVariable.containsKey(entry.getValue())) {
				Log.error("You cannot use vstte mode without creating the helper vars in the dispatcher");
				Log.error("Varname: " + entry.getValue());
				// throw new RuntimeException();
			} else {
				helperVariabels.put(entry.getKey(),
						usedVariable.get(entry.getValue()));
			}
		}

		ProverResult res = checkSat();
		int rounds = 1;// only for pretty printing

		Log.debug("Round " + (rounds++));
		Log.debug("Prover returns " + res.toString());

		boolean firstround = true;

		// this number is just a wild guess
		int threshold = helperVariabels.size() / 4 + 1;

		while (res == ProverResult.Sat || threshold > 1) {

			if (res == ProverResult.Sat) {
				for (Entry<BasicBlock, ProverExpr> entry : new HashMap<BasicBlock, ProverExpr>(
						helperVariabels).entrySet()) {
					ProverExpr val = theoremProver.evaluate(entry.getValue());
					if (val.getIntLiteralValue().longValue() == 1L) {
						// then, we just visited this block and can remove it
						// from our todo list
						helperVariabels.remove(entry.getKey());
					}
				}
				threshold = (helperVariabels.size() < threshold && helperVariabels
						.size() > 0) ? helperVariabels.size() : threshold;
			} else {
				threshold = (int) Math.ceil((double) threshold / 2.0);
			}

			if (firstround) {
				firstround = false;
			} else {
				popProverStack();
				this.numberOfConjuncts--; // Benchmark Code: Remove
			}
			pushProverStack();
			// assert the blocking clause not(rvar0=v0 && ... && rvarN=vN)
			ProverExpr sum = theoremProver.mkPlus(helperVariabels.values()
					.toArray(new ProverExpr[helperVariabels.values().size()]));

			ProverExpr coverquery = // theoremProver.mkNot(
			theoremProver.mkGeq(sum, theoremProver.mkLiteral(threshold));
			// );
			addAssertion(coverquery);
			this.numberOfConjuncts++; // Benchmark Code: Remove
			res = checkSat();

			Log.debug("Round " + (rounds++));
			Log.debug("Prover returns " + res.toString());
		}

		LinkedList<BasicBlock> result = new LinkedList<BasicBlock>();
		Log.debug("Infeasible Blocks: ");

		for (Entry<BasicBlock, ProverExpr> entry : helperVariabels.entrySet()) {
			Log.debug(entry.getValue() + ", ");
			result.add(entry.getKey());
		}
		Log.debug("=====");
		return result;
	}

	// private void printPath(LinkedList<BasicBlock> path) {
	// Log.error("----- Path -----");
	// for (BasicBlock b : path) {
	// Log.error(b.toBoogie());
	// }
	// Log.error("----------");
	// }

	// private String createSMTBlockingClause(VCExpression bc) {
	// StringBuilder sb = new StringBuilder();
	// sb.append("(assert ");
	// sb.append(bc.toSMT());
	// sb.append(")\n");
	// return sb.toString();
	// }
	//
	// private LinkedList<BasicBlock> parseZ3Model(String model,
	// HashMap<BasicBlock, VCFunction> reachVars) {
	// LinkedList<BasicBlock> feasiblePath = new LinkedList<BasicBlock>();
	// if (null == model) {
	// // Log.error("YEAH, we have a proof!");
	// return feasiblePath;
	// }
	// // HACK, the Z3 Model uses char10 for line breaks
	// String[] tokens = model.split(String.valueOf((char) 10));
	// for (String t : tokens) {
	// // Log.debug("----------");
	// // Log.debug(t);
	// boolean checkNextValue = false;
	// String lastVarName = "";
	// String[] linetokens = t.split(" -> ");
	// for (String lt : linetokens) {
	// if (t == "") {
	// continue;
	// }
	// if (checkNextValue) {
	// checkNextValue = false;
	// if (lt.contains("true")) { // this block is on the feasible
	// // path
	// for (Entry<BasicBlock, VCFunction> entry : reachVars
	// .entrySet()) {
	// if (lastVarName.contains(entry.getValue()
	// .getFunName())) {
	// feasiblePath.add(entry.getKey());
	// }
	// }
	//
	// }
	// // Log.error(lastVarName + " is " + lt);
	// }
	// if (lt.contains("_bwd")) {
	// checkNextValue = true;
	// lastVarName = lt;
	// }
	//
	// }
	// }
	// return feasiblePath;
	// }

	/*
	 * TODO: for test purpose only Later, this should be realized over a proper
	 * interface to the solver
	 */
	/*
	 * private String createSMT2Formula(HashMap<BasicBlock, VCFunction>
	 * blockVars, HashMap<BasicBlock, VCFunction> reachVars, List<VCExpression>
	 * terms) { StringBuilder sb = new StringBuilder();
	 * 
	 * // create the smt2 header first sb.append("(set-logic AUFLIA)\n");
	 * 
	 * HashSet<VCFunction> allfuns = new HashSet<VCFunction>(); for (VCFunction
	 * f : usedVariable.values()) allfuns.add(f); for (Entry<BoogieProcedure,
	 * ProverFun> entry : usedFunctions .entrySet())
	 * allfuns.add(entry.getValue());
	 * 
	 * // declare the blockvars allfuns.addAll(blockVars.values());
	 * allfuns.addAll(reachVars.values());
	 * 
	 * for (VCFunction fun : allfuns) { sb.append(fun.getSMTDefinition()); }
	 * 
	 * for (VCExpression t : terms) { sb.append("(assert ");
	 * sb.append(t.toSMT()); sb.append(")\n"); } // sb.append("\n"); //
	 * sb.append("(check-sat)\n"); // sb.append("(exit)\n"); return
	 * sb.toString(); }
	 */

	private ProverExpr createFwdReachability(BasicBlock b,
			HashMap<BasicBlock, ProverExpr> blockVars, List<ProverExpr> terms) {
		ProverExpr v = null;
		/*
		 * The created formula should be B_fwd := \not wlp(Block, /\ (\not
		 * B_succ) )
		 */
		if (blockVars.containsKey(b)) {
			v = blockVars.get(b);
		} else {
			ProverExpr post = null;
			if (b.Successors.size() > 0) {
				/*
				 * compute \not (/\ (\not B_succ)) that is\/ ( B_succ)
				 */
				LinkedList<ProverExpr> targets = new LinkedList<ProverExpr>();
				for (BasicBlock suc : b.Successors) {
					targets.add(createFwdReachability(suc, blockVars, terms));
				}
				post = (targets.size() == 1) ? targets.get(0) : theoremProver
						.mkOr((ProverExpr[]) targets
								.toArray(new ProverExpr[targets.size()]));
				this.numberOfConjuncts += targets.size(); // Benchmark Code:
															// Remove
			} else {
				/*
				 * Because we compute the negation of wlp(B,false), this has to
				 * be true
				 */
				post = theoremProver.mkLiteral(true);
			}

			v = makeHelperVar(b.getName() + "_fwd");

			ProverExpr wlp = null;
			// compute wlp(b.Statemets, post)
			if (b.getStatements().size() > 0) {
				LinkedList<ProverExpr> body = new LinkedList<ProverExpr>();
				for (Statement s : b.getStatements()) {
					body.add(statement2ProverExpr(s));
				}
				body.add(post); // add the conjunction for the goto targets as
								// the last statement

				ProverExpr[] arr = (ProverExpr[]) body
						.toArray(new ProverExpr[body.size()]);

				wlp = (body.size() == 1) ? body.get(0) : theoremProver
						.mkAnd(arr);
				this.numberOfConjuncts += body.size(); // Benchmark Code: Remove
			} else {
				wlp = post;
			}
			terms.add(theoremProver.mkEq(v, wlp));
			blockVars.put(b, v);
		}
		return v;
	}

}
