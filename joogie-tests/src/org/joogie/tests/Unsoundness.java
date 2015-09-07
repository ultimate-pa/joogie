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
public class Unsoundness {
	
	public class Test {
		public Test() {
			throw new RuntimeException();
		}
	}
	
	public static class ImageWidth {

		public static String getText() {
			// TODO Auto-generated method stub
			return null;
		}

		public static void requestFocus() {
			// TODO Auto-generated method stub
			
		}
		
	}

	public static class ImageHeight {

		public static String getText() {
			// TODO Auto-generated method stub
			return null;
		}

		public static void requestFocus() {
			// TODO Auto-generated method stub
			
		}
		
	}
	
	private boolean validateControls()
	{		
		boolean result = true;
		if(!ImageWidth.getText().equals(""))
		{
			try
			{
				Integer.parseInt(ImageWidth.getText());
			}
			catch (NumberFormatException e)
			{
				result = false;
				Test sidAbout = new Test();
				//SimpleInfoDialog sidAbout = new SimpleInfoDialog(ParentEkit.getFrame(), "Error", true, "Image Width is not an integer", SimpleInfoDialog.ERROR);
				ImageWidth.requestFocus();
			}
		}
		if( result && !ImageHeight.getText().equals(""))
		{
			try
			{
				Integer.parseInt(ImageHeight.getText());
			}
			catch (NumberFormatException e)
			{
				result = false;
				Test sidAbout = new Test();
				//SimpleInfoDialog sidAbout = new SimpleInfoDialog(ParentEkit.getFrame(), "Error", true, "Image Height is not an integer", SimpleInfoDialog.ERROR);
				ImageHeight.requestFocus();
			}
		}
		return result;
	}

	
}
