/**
 * 
 */
package org.joogie.js.factories;

import java.util.HashMap;

import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.js.JsGlobalsCache;
import org.mozilla.javascript.ast.NumberLiteral;

/**
 * @author martin
 *
 */
public class JsConstantFactory {

	private static JsConstantFactory instance = null;
	
	public static JsConstantFactory v() {
		if (instance==null) {
			instance = new JsConstantFactory();
		}
		return instance;
	}
	
	public static void resetInstance() {
		if (instance!=null) {
			instance.stringMap.clear();
		}
		instance = null;
	}
	
	private JsConstantFactory() {
		
	}
	
	private HashMap<String, Variable> stringMap = new HashMap<String, Variable>();
	
	public Expression getStringLiteralConstant(String str) {
		if (!stringMap.containsKey(str)) {
			Variable v = JsVariableFactory.v()
					.getFreshGlobal(BoogieBaseTypes.getRefType());
			stringMap.put(str, v);
			BoogieProgram.v().addGlobalVar(v);
		}
		return stringMap.get(str);
	}

	
	
	public Expression getNumberLiteralConstant(NumberLiteral num) {
		Double d = num.getDouble();
		//check if we can use integer types in the boogie program
		if ((d == Math.floor(d)) && !Double.isInfinite(d)) {
		    return new UboundedIntConstant(d.longValue());
		} else {
			return JsRealConstantFactory.getRealConstant(d);
		}		
	}
	
	public Expression getBooleanConstant(boolean c) {
		//TODO: maybe we should use a smarter typesystem ;)		
		return new UboundedIntConstant( c ? 1L : 0L );
	}
	
	public Expression getNullConstant() {
		return JsGlobalsCache.v().getNullVariable();
	}

	public Expression getUndefinedConstant() {
		return JsGlobalsCache.v().getUndefinedVariable();
	}
	
}
