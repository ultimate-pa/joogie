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
import java.util.Set;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.statements.Statement;
import org.joogie.prover.Prover;
import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverResult;
import org.joogie.report.MethodInfo;
import org.joogie.util.Log;

/**
 * @author schaef
 */
public class VCGenerationEnablingClause extends AbstractVCGeneration {

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
	public VCGenerationEnablingClause(BoogieProcedure proc, Prover prover,
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

		HashMap<BasicBlock, ProverExpr> reachVars = new HashMap<BasicBlock, ProverExpr>();
		// compute the formulas for backward reachability (similar to sp)
		// see the "Towards Bounded Infeasible Code Detection" paper.
		createBwdReachability(proc.getExitBlock(), blockVars, reachVars, terms);

		// assert everything
		for (ProverExpr pexp : terms) {
			addAssertion(pexp);
		}

		ProverResult res = checkSat();
		int rounds = 1;// only for pretty printing

		Log.debug("Round " + (rounds++));
		Log.debug("Prover returns " + res.toString());

		// we could actually start from a smaller set
		// if we use the effectual set here.
		// Set<BasicBlock> effectualSet = EffectualSet.getEffectualSet(proc);
		HashMap<ProverExpr, BasicBlock> ecMap = new HashMap<ProverExpr, BasicBlock>();
		for (Entry<BasicBlock, ProverExpr> entry : reachVars.entrySet()) {
			// if (effectualSet.contains(entry.getValue())) {
			ecMap.put(entry.getValue(), entry.getKey());
			// }
		}

		boolean firstround = true;

		int lastenablingclausesize = 0;// Benchmark Code: Remove

		while (res == ProverResult.Sat && ecMap.size() > 0) {

			LinkedList<ProverExpr> _tmp = new LinkedList<ProverExpr>(
					ecMap.keySet());
			for (ProverExpr pe : _tmp) {
				ProverExpr val = theoremProver.evaluate(pe);
				if (val.getBooleanLiteralValue()) {
					ecMap.remove(pe);
				}
			}

			if (firstround) {
				firstround = false;
			} else {
				popProverStack();
				this.numberOfConjuncts -= lastenablingclausesize; // Benchmark
																	// Code:
																	// Remove
				lastenablingclausesize = ecMap.keySet().size();// Benchmark
																// Code: Remove
			}

			pushProverStack();

			addAssertion(createEnablingClause(ecMap.keySet()));

			res = checkSat();

			Log.debug("Round " + (rounds++));
			Log.debug("Prover returns " + res.toString());
		}

		if (!firstround)
			popProverStack();

		LinkedList<BasicBlock> result = new LinkedList<BasicBlock>();
		Log.debug("Infeasible Blocks: ");

		for (Entry<ProverExpr, BasicBlock> entry : ecMap.entrySet()) {
			result.add(entry.getValue());
			Log.debug(entry.getValue() + ", ");
		}

		return result;
	}

	private ProverExpr createEnablingClause(Set<ProverExpr> set) {
		// enblclause must not be empty, right?
		if (set.size() == 0)
			return theoremProver.mkLiteral(true);
		this.numberOfConjuncts += set.size(); // Benchmark Code: Remove
		return theoremProver.mkOr(set.toArray(new ProverExpr[set.size()]));
	}

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
				this.numberOfConjuncts += body.size(); // Benchmark Code: Remove
				wlp = (body.size() == 1) ? body.get(0) : theoremProver
						.mkAnd(arr);
			} else {
				wlp = post;
			}
			// terms.add(theoremProver.mkEq(v, wlp));
			// try implies instead of Eq ... philipp says it might be faster
			terms.add(theoremProver.mkOr(theoremProver.mkNot(v), wlp));
			this.numberOfConjuncts++; // Benchmark Code: Remove
			blockVars.put(b, v);
		}
		return v;
	}

	private ProverExpr createBwdReachability(BasicBlock b,
			HashMap<BasicBlock, ProverExpr> blockVars,
			HashMap<BasicBlock, ProverExpr> reachVars,
			LinkedList<ProverExpr> terms) {
		ProverExpr v = null;
		/*
		 * create formula as described in http://arxiv.org/pdf/1205.6527v1.pdf
		 * B_bwd = B_fwd /\ (\/ B_bwd_pre)
		 */
		if (reachVars.containsKey(b)) {
			return reachVars.get(b);
		} else {
			ProverExpr pre = null;
			if (b.Predecessors.size() > 0) {
				LinkedList<ProverExpr> targets = new LinkedList<ProverExpr>();
				for (BasicBlock pred : b.Predecessors) {
					targets.add(createBwdReachability(pred, blockVars,
							reachVars, terms));
				}
				pre = (targets.size() == 1) ? targets.get(0) : theoremProver
						.mkOr((ProverExpr[]) targets
								.toArray(new ProverExpr[targets.size()]));
				this.numberOfConjuncts += targets.size(); // Benchmark Code:
															// Remove
			} else {
				pre = theoremProver.mkLiteral(true);
			}
			ProverExpr rhs = theoremProver.mkAnd(blockVars.get(b), pre);
			this.numberOfConjuncts += blockVars.size(); // Benchmark Code:
														// Remove
			v = makeHelperVar(b.getName() + "_bwd");

			terms.add(theoremProver.mkEq(v, rhs));
			// try implies instead of Eq ... philipp says it might be faster
			// terms.add(theoremProver.mkOr(theoremProver.mkNot(v), rhs));

			reachVars.put(b, v);
		}
		return v;
	}

}
