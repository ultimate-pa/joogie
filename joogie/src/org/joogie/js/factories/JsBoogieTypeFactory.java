package org.joogie.js.factories;

import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieType;

public class JsBoogieTypeFactory {
	private static JsBoogieTypeFactory instance = null;
	
	public static JsBoogieTypeFactory v() {
		if (instance==null) {
			instance = new JsBoogieTypeFactory();
		}
		return instance;
	}
	
	public static void resetInstance() {
		instance = null;
	}
	
	private JsBoogieTypeFactory() {
		
	}

	public BoogieType translateJsType(int jstype) {
		//TODO: implement
		return BoogieBaseTypes.getRefType();
	}
	
	
}
