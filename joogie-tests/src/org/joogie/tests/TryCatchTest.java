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

import java.sql.SQLException;

/**
 * @author schaef
 */
public class TryCatchTest {
	
	private Object throwtest2(int i) throws SQLException {
		if (i>0) throw new SQLException();
		return null;
	}

	
    public void savePayeeBeforeUpdate(int i)
            throws Exception {
    	int k,l,m;
        Object rs = null;

        try {
            rs = throwtest2(i);

            if (rs.hashCode()==0) {
            	k=1;l=2;m=3;
            } else {
            	k=3;
            }
        }
        finally {
        	if (rs != null) { //JOOGIE: Why is this infeasible?
        		i=5;
        	}
        }   
      }

    
	public int test(Object x, Object y) {
		int z=0;
		if (x == null &&  y == null) {
			z=1;			
		} else if 
		
			(x == null 
			
			&& 
			
			y != null
			
					) {
			z=2;
		}
		return z;		
	}
     
}
