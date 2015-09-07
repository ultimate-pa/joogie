/**
 * 
 */
package org.joogie.js.factories;

import java.util.HashMap;

import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.types.BoogieBaseTypes;

/**
 * @author martin
 *
 */
public class JsRealConstantFactory {
	public static void resetFactory() {
		realConstants = new HashMap<Double, Expression>();
	}

	private static HashMap<Double, Expression> realConstants = new HashMap<Double, Expression>();

	public static Expression getRealConstant(Double c) {
		if (!realConstants.containsKey(c)) {
			realConstants.put(
					c,
					JsVariableFactory.v()
					.getFreshGlobal(BoogieBaseTypes.getRealType(), true)
					);
		}
		return realConstants.get(c);
	}

}
