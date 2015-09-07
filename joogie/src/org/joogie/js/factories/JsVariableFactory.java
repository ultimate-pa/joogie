/**
 * 
 */
package org.joogie.js.factories;

import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieType;
import org.joogie.js.JsGlobalsCache;

/**
 * @author martin
 *
 */
public class JsVariableFactory {
	
	private static JsVariableFactory instance = null;
	
	public static JsVariableFactory v() {
		if (instance==null) {
			instance = new JsVariableFactory();
		}
		return instance;
	}
	
	public static void resetInstance() {
		instance = null;
	}
	
	private JsVariableFactory() {
		
	}
	
	public Variable getFreshGlobal(BoogieType t) {
		Variable v = new Variable("$fresh" + (JsGlobalsCache.v().getUniqueNumber()), t); 
		BoogieProgram.v().addGlobalVar(v);
		return v;
	}

	public Variable getFreshGlobal(BoogieType t, boolean constunique) {
		Variable v = new Variable("$fresh" + (JsGlobalsCache.v().getUniqueNumber()), t, constunique); 
		BoogieProgram.v().addGlobalVar(v);
		return v;
	}
	
	
	public Variable getFreshLocal(BoogieType t, BoogieProcedure proc) {
		Variable v = new Variable("$fresh_local" + (JsGlobalsCache.v().getUniqueNumber()), t); 
		proc.addLocal(v);
		return v;
	}
	
}
