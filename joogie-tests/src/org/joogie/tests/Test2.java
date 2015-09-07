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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.EmptyStackException;

/**
 * @author schaef
 */
public class Test2 {
	
	int x = 0;
	
	private void ops(double x) {
		x = x/2;
		boolean b = (x==1)^(x>3);
		x= x*5;
		x= x%5;
	}
	
    private void run(){
        try {
            InputStreamReader isr = new InputStreamReader(System.in);
            BufferedReader br = new BufferedReader(isr);
            while (true){
            String temp = (String)br.readLine();
                if (temp.equals("done")) break;
                System.out.println(temp);
            }
        }
        catch(IOException e) {
            System.out.println(e.getMessage());
            //System.out.println("Error");
        }
        catch(Exception e2) {
            System.out.println(e2.getMessage());
        }
    }
    
    private void run2(int x){
        try {
            InputStreamReader isr = new InputStreamReader(System.in);
            BufferedReader br = new BufferedReader(isr);
            String temp = (String)br.readLine();
            if (temp=="throw") throw new EmptyStackException();
        }
        catch(IOException e) {
            System.out.println(e.getMessage());
            //System.out.println("Error");
        }
    }    

}
