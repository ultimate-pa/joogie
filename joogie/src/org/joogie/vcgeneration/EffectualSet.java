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
import java.util.LinkedList;
import java.util.Map.Entry;
import java.util.Set;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;

/**
 * @author schaef
 * this class computes an effectual set for a given procedure
 * as described in the vstte'12 paper "infeasible code detection"
 */
public class EffectualSet {
	
	public static Set<BasicBlock> getEffectualSet(BoogieProcedure proc){
		HashMap<BasicBlock, HashSet<BasicBlock>> dom = new HashMap<BasicBlock, HashSet<BasicBlock>>();
		HashMap<BasicBlock, HashSet<BasicBlock>> pdom = new HashMap<BasicBlock, HashSet<BasicBlock>>();
		//compute the (post)dominators for all blocks
		computeDominators(proc.getRootBlock(), dom, true);
		computeDominators(proc.getExitBlock(), pdom, false);
		//merge post-dom into dom
		for (Entry<BasicBlock, HashSet<BasicBlock>>  entry : pdom.entrySet()) {
			dom.get(entry.getKey()).addAll(entry.getValue());
		}		
				
		//actually, we could both loops ... but for now, we don't 
		//to do some debug printing in the middle
		PartialBlockOrder pbo_root = new PartialBlockOrder();
		for (Entry<BasicBlock, HashSet<BasicBlock>>  entry : dom.entrySet()) {
			pbo_root.insert(entry.getKey(), entry.getValue());

		}
		
		HashSet<BasicBlock> ret = pbo_root.getLeafRepresentatives();	
		return ret;
	}
		
	
	private static void computeDominators(BasicBlock b, HashMap<BasicBlock, HashSet<BasicBlock>> dominators, boolean forward) {
		
		LinkedList<BasicBlock> todo = new LinkedList<BasicBlock>();
		LinkedList<BasicBlock> done = new LinkedList<BasicBlock>();

		if (b!=null) todo.add(b);
		
		while (!todo.isEmpty()) {
			BasicBlock current = todo.pollLast();
			//check if all predecessors have been processed already.
			//if not, add the block to the end of the cue and start over
			boolean allGood = true;
			for (BasicBlock prev : getNext(current, !forward)) {
				if (!done.contains(prev)) {
					allGood=false;
					break;
				}
			}		
			if (!allGood){
				todo.addFirst(current);
				continue;
			}
			//if all predecessors have been processed,
			//we can compute the dominators list by
			//intersecting the list of all predecessors
			HashSet<BasicBlock> currentDom = null;
			for (BasicBlock prev : getNext(current, !forward)) {
				if (currentDom == null) {
					currentDom = new HashSet<BasicBlock>(dominators.get(prev));
				} else {
					//retainAll computes the intersection of the two sets.
					currentDom.retainAll(dominators.get(prev));
				}				
			}		

			//special case, only occurs for the root/sink
			if (currentDom == null) {
				currentDom = new HashSet<BasicBlock>();
			}
			
			currentDom.add(current); //of course, a block dominates itself
			dominators.put(current, currentDom);
			done.add(current);
			
			for (BasicBlock next : getNext(current, forward)) {
				if (!todo.contains(next) && !done.contains(next)) {
					todo.addLast(next);
				}
			}
			
		}
	}
	/*
	 * computes this intersection of two hashsets.
	 */
	
	private static HashSet<BasicBlock> getNext(BasicBlock current, boolean forward) {
		HashSet<BasicBlock> nextblocks = current.Successors;
		if (!forward) nextblocks = current.Predecessors;
		return nextblocks;
	}
	
}
