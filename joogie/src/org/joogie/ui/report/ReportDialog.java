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

package org.joogie.ui.report;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.List;

import javax.swing.AbstractAction;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JEditorPane;
import javax.swing.JFileChooser;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JToolBar;
import javax.swing.ListSelectionModel;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import org.joogie.report.MethodInfo;
import org.joogie.report.Report;
import org.joogie.util.FileIO;

/**
 * Report Dialog
 * 
 * @author arlt
 */
public class ReportDialog extends JDialog {

	/**
	 * List of infeasible methods
	 */
	private List<MethodInfo> infeasibleMethods;

	/**
	 * Source Directory
	 */
	private String sourceDir;

	/**
	 * Toolbar
	 */
	private JToolBar toolBar = new JToolBar();

	/**
	 * List showing the results
	 */
	private JList<String> listResults = new JList<String>();

	/**
	 * Editor showing the results
	 */
	private JEditorPane editorResults = new JEditorPane();

	/**
	 * Splitpane
	 */
	private JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);

	/**
	 * C-tor
	 * 
	 * @param report
	 *            Report
	 */
	public ReportDialog(Report report, String sourceDir) {
		this.infeasibleMethods = report.getInfeasibleMethods();
		this.sourceDir = sourceDir;
		setTitle("Report");

		// create widgets
		createToolBar();

		// setup split pane
		splitPane.setDividerLocation(200);
		splitPane.setLeftComponent(new JScrollPane(listResults));
		splitPane.setRightComponent(new JScrollPane(editorResults));
		add(splitPane);

		// setup list
		listResults.setModel(new ReportModel(report.getInfeasibleMethods()));
		listResults.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
		listResults.addListSelectionListener(new ListSelectionListener() {
			public void valueChanged(ListSelectionEvent e) {
				if (e.getValueIsAdjusting())
					return;
				onListSelection(listResults.getSelectedIndex());
			}
		});

		// setup editor
		editorResults.setEditable(false);
		editorResults.setContentType("text/java");

		// configure dialog
		setModal(true);
		setSize(640, 480);
		setLocationRelativeTo(null);
	}

	/**
	 * Creates the toolbar
	 */
	protected void createToolBar() {
		// load icons
		ImageIcon iconOpen = new ImageIcon(getClass().getResource("open.png"));
		ImageIcon iconSave = new ImageIcon(getClass().getResource("save.png"));

		// Open
		JButton button = new JButton(new AbstractAction("Open Report") {
			public void actionPerformed(ActionEvent e) {
				onOpenReport();
			}
		});
		button.setIcon(iconOpen);
		//toolBar.add(button);

		// Open
		button = new JButton(new AbstractAction("Save Report") {
			public void actionPerformed(ActionEvent e) {
				onSaveReport();
			}
		});
		button.setIcon(iconSave);
		//toolBar.add(button);

		// add toolbar
		getContentPane().add(toolBar, BorderLayout.PAGE_START);
	}

	/**
	 * Opens a report
	 */
	protected void onOpenReport() {
		try {
			// choose file
			JFileChooser fileChooser = new JFileChooser();
			if (JFileChooser.APPROVE_OPTION != fileChooser.showOpenDialog(this))
				return;

			// deserialize report
			FileInputStream fis = new FileInputStream(fileChooser.getSelectedFile().getPath());
			ObjectInputStream ois = new ObjectInputStream(fis);
			// ois.readObject(...);
			ois.close();
			fis.close();

			// assign new list model
			listResults.setModel(new ReportModel(infeasibleMethods));

		} catch (Exception e) {
			JOptionPane.showMessageDialog(ReportDialog.this, e.getMessage(),
					"Error", JOptionPane.ERROR_MESSAGE);
		}
	}

	/**
	 * Saves a report
	 */
	protected void onSaveReport() {
		try {
			// choose file
			JFileChooser fileChooser = new JFileChooser();
			if (JFileChooser.APPROVE_OPTION != fileChooser.showSaveDialog(this))
				return;
			
			// serialize report
			FileOutputStream fos = new FileOutputStream(fileChooser .getSelectedFile().getPath());
			ObjectOutputStream oos = new ObjectOutputStream(fos);
			//oos.writeObject(...);
			oos.close();
			oos.close();

		} catch (Exception e) {
			JOptionPane.showMessageDialog(ReportDialog.this, e.getMessage(),
					"Error", JOptionPane.ERROR_MESSAGE);
		}
	}

	/**
	 * Handles the list selection event
	 * 
	 * @param index
	 *            Index of selected item
	 */
	protected void onListSelection(int index) {
		try {
			// get method info
			MethodInfo method = infeasibleMethods.get(index);

			// look up filename (use source directory)
			String filename = method.getFileName(sourceDir);
			if (!FileIO.doesFileExist(filename)) {
				throw new RuntimeException("Cannot find source file.");
			}

			// open file
			String file = FileIO.fromFile(filename);
			editorResults.setText(file);

			// go to line number
			int lineNumber = method.getLineNumber();
			gotoLine(lineNumber);

		} catch (RuntimeException e) {
			JOptionPane.showMessageDialog(this, e.getMessage(), "Error",
					JOptionPane.ERROR_MESSAGE);
		}
	}

	/**
	 * Sets the caret of the editor pane to the given line
	 * 
	 * @param line
	 *            Line number
	 */
	private void gotoLine(int line) {
		int currentLine = 1;
		int currentPosition = 0;

		if (line <= 0) {
			throw new IllegalArgumentException("Invalid line number.");
		}

		// compute caret position
		char[] text = editorResults.getText().toCharArray();
		for (char c : text) {
			currentPosition++;
			if (currentLine == line) {
				break;
			}
			if ('\n' == c) {
				currentLine++;
			}
		}

		// set caret position (subtract invisible line breaks)
		editorResults.setCaretPosition(currentPosition - line);
	}
}
