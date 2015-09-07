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

import java.util.HashSet;

import org.joogie.boogie.BasicBlock;
import org.joogie.util.Log;

/**
 * @author schaef
 */
public class PartialBlockOrder {
	
	public PartialBlockOrder() {
		
	}

	public PartialBlockOrder(BasicBlock b, HashSet<BasicBlock> unav) {
		this.unavoidables = unav;
		this.currentClass.add(b);
	}

	public void printLeafInfo() {
		if (this.successors.size()==0) {
			Log.info("LEAF: ");
			StringBuilder sb = new StringBuilder();
			sb.append("Blocks: ");
			for (BasicBlock b : this.currentClass) {
				sb.append(b.getName() + ", ");
			}
			Log.info(sb.toString());
			sb = new StringBuilder();
			sb.append("Unavoidables: ");
			for (BasicBlock b : this.unavoidables) {
				sb.append(b.getName() + ", ");
			}
			Log.info(sb.toString());
			Log.info("============= ");
		}
		for (PartialBlockOrder next : this.successors) {
			next.printLeafInfo();
		}
	}
	
	public HashSet<BasicBlock> getLeafRepresentatives() {
		HashSet<BasicBlock> ret = new HashSet<BasicBlock>();
		if (this.successors.size()==0) {
			BasicBlock b = this.currentClass.iterator().next();
			ret.add(b);
		}
		for (PartialBlockOrder next : this.successors) {
			ret.addAll(next.getLeafRepresentatives());
		}
		return ret;
	}
	
	
	public boolean insert(BasicBlock b, HashSet<BasicBlock> unav) {
		if (unav.containsAll(unavoidables) && unavoidables.containsAll(unav)) {
			this.currentClass.add(b);
			//return true, because we found a node that fits
			return true;
		} else if (unav.containsAll(unavoidables) && !unavoidables.containsAll(unav)) {
			//the unavoidables of the new node are a clear super-set of the current one
			//so try it with all the children
			for (PartialBlockOrder succ : this.successors) {
				//if we can insert it in a child, we are done.
				if (succ.insert(b, unav))  return true;
			}
			//if not, we have to check how many children
			//will be children of the new node.
			PartialBlockOrder newnode = new PartialBlockOrder(b,unav);
			//copy needed for iteration
			HashSet<PartialBlockOrder> tmpcopy = new HashSet<PartialBlockOrder>(this.successors); 
			for (PartialBlockOrder succ : tmpcopy) {
				if (succ.unavoidables.containsAll(unav)) {
					disconnectAfromB(this, succ);
					connectAtoB(newnode,succ);
				}
			}			
			connectAtoB(this, newnode);
			return true;
		} else if (!unav.containsAll(unavoidables) && unavoidables.containsAll(unav)) {
			return false;
		} 
		return false;
	}
	
	private void connectAtoB(PartialBlockOrder a, PartialBlockOrder b) {
		b.parent = a;
		a.successors.add(b);
	}

	private void disconnectAfromB(PartialBlockOrder a, PartialBlockOrder b) {
		b.parent = null;
		a.successors.remove(b);
	}
	
	
	HashSet<BasicBlock> currentClass = new HashSet<BasicBlock>();		
	HashSet<BasicBlock> unavoidables = new HashSet<BasicBlock>();
	
	PartialBlockOrder parent = null;
	HashSet<PartialBlockOrder> successors = new HashSet<PartialBlockOrder>();
	
}
