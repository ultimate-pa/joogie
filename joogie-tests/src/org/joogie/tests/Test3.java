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
public class Test3 {

        int [][] x;
        
        private String klaus(String s) {
        	if (s.length()>5) {
        		return "nix";
        	}
        	
        	return "";
        }
        
        private void run () {
            int [] i = new int [9];
            x = new int [3][3];
            x[0][0] = 4;
            System.out.println(x[0][0]);
            x[0][1] = 3;
            System.out.println(x[0][0]);
        }

}
