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
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.statements.Statement;
import org.joogie.cfgPlugin.CFGPlugin;
import org.joogie.cfgPlugin.Util.Dag;
import org.joogie.prover.Prover;
import org.joogie.prover.ProverExpr;
import org.joogie.prover.ProverResult;
import org.joogie.prover.princess.PrincessProver;
import org.joogie.report.MethodInfo;
import org.joogie.util.Log;

import ap.parser.IFormula;

/**
 * @author schaef
 */
public class VCGenerationCfgTheory extends AbstractVCGeneration {

	private HashSet<BasicBlock> effectualSet;

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
	public VCGenerationCfgTheory(BoogieProcedure proc, Prover prover,
			MethodInfo methodInfo) {
		super(methodInfo);
		this.proc = proc;
		this.theoremProver = prover;
	}

	public LinkedList<BasicBlock> generateVerificationCondition() {

		if (!(this.theoremProver instanceof PrincessProver)) {
			Log.error("The cfgTheory is only implemented for the Princess Prover");
			throw new RuntimeException();
		}

		this.effectualSet = new HashSet<BasicBlock>(
				EffectualSet.getEffectualSet(proc));

		HashMap<BasicBlock, ProverExpr> blockVars = new HashMap<BasicBlock, ProverExpr>();
		LinkedList<ProverExpr> terms = new LinkedList<ProverExpr>();

		// compute for each basic block Bi: Reach_i == not wlp(Bi, /\(not
		// B_successors))
		ProverExpr firstblockreachable = createFwdReachability(
				proc.getRootBlock(), blockVars, terms);
		// assert that wlp for the first block can be satisfied
		terms.add(firstblockreachable);

		Dag<IFormula> vcdag = procToPrincessDag(blockVars);

		// generate ineff flags; this map is also used to keep
		// track of the remaining uncovered blocks
		LinkedHashMap<ProverExpr, ProverExpr> ineffFlags = new LinkedHashMap<ProverExpr, ProverExpr>();

		for (BasicBlock block : effectualSet) {
			ProverExpr v = blockVars.get(block);
			ineffFlags.put(
					v,
					theoremProver.mkVariable("" + v + "_flag",
							theoremProver.getBooleanType()));
		}

		// assert everything
		for (ProverExpr pexp : terms) {
			addAssertion(pexp);
		}

		// wild guess ... actually, we need to use
		// the max number of effectual elements per path
		int threshold = blockVars.size();
		// slightly better guess
		if (threshold > 1)
			threshold = threshold / 2;

		int rounds = 1;// only for pretty printing

		while (threshold >= 1 && !ineffFlags.isEmpty()) {
			Log.debug("Threshold " + threshold);

			pushProverStack();

			// setup the CFG module
			LinkedList<ProverExpr> remainingBlockVars = new LinkedList<ProverExpr>();
			LinkedList<ProverExpr> remainingIneffFlags = new LinkedList<ProverExpr>();

			for (Entry<ProverExpr, ProverExpr> entry : ineffFlags.entrySet()) {
				remainingBlockVars.add(entry.getKey());
				remainingIneffFlags.add(entry.getValue());
			}

			((PrincessProver) this.theoremProver).setupCFGPlugin(vcdag,
					remainingBlockVars, remainingIneffFlags, threshold);

			// Query the feasible paths for this setup
			ProverResult res = checkSat();
			Log.debug("Round " + (rounds++));
			Log.debug("Prover returns " + res.toString());

			int oldformulasize = this.numberOfConjuncts; // Benchmark Code:
															// Remove

			while (res == ProverResult.Sat) {
				LinkedList<ProverExpr> covered = new LinkedList<ProverExpr>();
				LinkedList<ProverExpr> flagsToAssert = new LinkedList<ProverExpr>();

				for (Entry<ProverExpr, ProverExpr> entry : ineffFlags
						.entrySet()) {
					if (theoremProver.evaluate(entry.getKey())
							.getBooleanLiteralValue()) {
						covered.add(entry.getKey());
						flagsToAssert.add(entry.getValue());
					}
				}

				for (ProverExpr e : covered)
					ineffFlags.remove(e);

				addAssertion(theoremProver.mkAnd(flagsToAssert
						.toArray(new ProverExpr[flagsToAssert.size()])));

				this.numberOfConjuncts += flagsToAssert.size(); // Benchmark
																// Code: Remove

				res = checkSat();

				Log.debug("Round " + (rounds++));
				Log.debug("Prover returns " + res.toString());
			}

			popProverStack();

			this.numberOfConjuncts = oldformulasize; // Benchmark Code: Remove

			if (threshold == 1)
				break;

			threshold = (int) Math.ceil((double) threshold / 2.0);
		}

		LinkedList<BasicBlock> result = new LinkedList<BasicBlock>();
		Log.debug("Infeasible Blocks: ");

		for (Entry<BasicBlock, ProverExpr> entry : blockVars.entrySet()) {
			if (ineffFlags.containsKey(entry.getValue()) /*
														 * &&
														 * !this.effectualSet.
														 * contains
														 * (entry.getKey())
														 */) {
				result.add(entry.getKey());
				Log.debug(entry.getKey() + ", ");
			}
		}

		return result;
	}

	private Dag<IFormula> procToPrincessDag(
			HashMap<BasicBlock, ProverExpr> reachVars) {
		// First transform the CFG into a list and record
		// the index of each block
		// it is imporatant that the list starts with the
		// exitblock
		LinkedList<BasicBlock> todo = new LinkedList<BasicBlock>();
		LinkedList<BasicBlock> done = new LinkedList<BasicBlock>();
		todo.add(proc.getRootBlock());
		while (!todo.isEmpty()) {
			BasicBlock current = todo.pollLast();
			boolean allDone = true;
			for (BasicBlock pre : current.Predecessors) {
				if (!done.contains(pre)) {
					allDone = false;
					continue;
				}
			}
			if (!allDone) {
				todo.addFirst(current);
				continue;
			}
			// store the position the block will have in the 'done' list.
			done.addLast(current);
			for (BasicBlock suc : current.Successors) {
				if (!todo.contains(suc) && !done.contains(suc)) {
					if (suc != current) {
						todo.addLast(suc);
					} else {
						// This has to be checked
						Log.error("The node has a self-loop! This is not supposed to happen.");
					}
				}
			}
		}

		Dag<IFormula> currentNode = CFGPlugin.mkDagEmpty();
		// TODO: assert that the first one in the list is actually the ExitBlock
		for (int j = done.size() - 1; j >= 0; j--) {
			BasicBlock b = done.get(j);
			List<Integer> succIndices = new LinkedList<Integer>();
			for (BasicBlock suc : b.Successors) {
				// TODO: @Philipp willst du die absolute position oder den
				// offset?
				int idx = done.indexOf(suc) - done.indexOf(b);
				succIndices.add(idx);
				// Log.error("\t " +idx+":"+suc.getName() );
			}
			// TODO: review. can be done better
			IFormula d = ((PrincessProver) this.theoremProver)
					.proverExpToIFormula(reachVars.get(b));
			int[] succidx = new int[succIndices.size()];
			for (int i = 0; i < succIndices.size(); i++) {
				succidx[i] = succIndices.get(i);
			}
			currentNode = CFGPlugin.mkDagNode(d, succidx, currentNode);
		}
		// currentNode.prettyPrint();
		return currentNode;
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
			terms.add(theoremProver.mkOr(theoremProver.mkNot(v), wlp));
			blockVars.put(b, v);
		}
		return v;
	}


}
