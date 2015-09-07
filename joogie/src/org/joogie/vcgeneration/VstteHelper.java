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
import java.util.Map.Entry;
import java.util.Set;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.soot.factories.BoogieConstantFactory;

/**
 * @author schaef
 * TODO: this class is only needed for experimental comparison with
 * our old work. It is completely useless - and also not used - when
 * joogie is run normally
 */
public class VstteHelper {

	public static HashMap<BasicBlock, Variable> injectHelperVariables(BoogieProcedure proc) {
		HashMap<BasicBlock, Variable> helpervars = new HashMap<BasicBlock, Variable>();
		Set<BasicBlock> effectual = EffectualSet.getEffectualSet(proc);
		for (BasicBlock b : effectual) {
			Variable v = new Variable(b.getName()+"rvar", BoogieBaseTypes.getIntType());
			helpervars.put(b, v);
			b.addStatement(new AssignStatement(v, BoogieConstantFactory.createConst(1)),true);
		}
		//init the helpervars to zero in the rootblock
		for (Entry<BasicBlock, Variable> entry : helpervars.entrySet()) {
			proc.getRootBlock().addStatement(new AssignStatement(entry.getValue(), 
					BoogieConstantFactory.createConst(0)),true);
		}
		
		return helpervars;
	}		

	public static HashMap<BasicBlock, Variable> getSSAHelperVars(BoogieProcedure proc) {		
		HashMap<BasicBlock, Variable> ret = new HashMap<BasicBlock, Variable>();
		for (Entry<BasicBlock, Variable> entry : proc.vstteMap.entrySet()) {
			ret.put(entry.getKey(),proc.getVarIncarnationMap().get(entry.getValue()).getLast()); 
		}
		return ret;
	}
	
}
