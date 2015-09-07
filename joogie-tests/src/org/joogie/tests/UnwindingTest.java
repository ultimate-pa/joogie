/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
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

package org.joogie.tests;

/**
 * @author schaef
 */
public class UnwindingTest {
	
	private class Test {

		public void mytest(int i) throws Exception {
			if (i==2) throw new Exception();
		}
		
		public boolean hasMoreElements() {
			// TODO Auto-generated method stub
			return false;
		}

		public Object nextElement() {
			// TODO Auto-generated method stub
			return null;
		}
		
	}
	int internalTextLength;
	int caretOffset;
	Test attribEntries1 = new Test();
	int len;
	int dummy;
	
	public void clearFormat() 
	{
		dummy++;
		// clear all character attributes in selection
		for(int i = caretOffset; i <= caretOffset + internalTextLength; i++) {
			dummy--;
			while(attribEntries1.hasMoreElements()) {
				dummy--;
				//System.out.println(entryKey + " = " + entryValue);
				for (int j=0; j < len; j++) {
					dummy++;
				}
			}
			try {
				attribEntries1.mytest(dummy);
			} catch (Exception e) {
				
			}
		}
		return;
	}	
	
//	public Collection<Object> listeners;
//
//	public int tick;
//	public boolean ticking;
//	
//	public abstract void sleep(int tick) throws InterruptedException;
//	
//	public void run() {
//	while (true) {
//	    try { sleep(tick); } catch (InterruptedException e) {
//		System.out.println("Warning: System clock terminated by user.");
//		e.printStackTrace();
//	    }
//	    if (ticking) {
//		synchronized (this) {
//		    Iterator<Object> iterator = listeners.iterator();
//		    while (iterator.hasNext()) {
//		    Iterator<Object> listener = (Iterator<Object>) iterator.next();
//			//listener.tick();
//		    }
//		}
//	    }
//	}
//    }
//	int i =5;
}
