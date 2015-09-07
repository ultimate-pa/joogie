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

package org.joogie.ui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.io.File;

import javax.swing.AbstractAction;
import javax.swing.BorderFactory;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JToolBar;

import org.joogie.Dispatcher;
import org.joogie.Options;
import org.joogie.boogie.BoogieProgram;
import org.joogie.report.Report;
import org.joogie.ui.report.ReportDialog;
import org.joogie.util.FileIO;

/**
 * Mainframe
 * 
 * @author arlt
 */
public class MainFrame extends JFrame {

	/**
	 * Report
	 */
	private Report report;

	/**
	 * Menubar
	 */
	private JMenuBar menuBar = new JMenuBar();

	/**
	 * Toolbar
	 */
	private JToolBar toolBar = new JToolBar();

	/**
	 * Statusbar
	 */
	private JLabel statusBar = new JLabel("Ready");

	/**
	 * Textfield of the Jar file
	 */
	private JTextField tfJarFile = new JTextField();

	/**
	 * Textfield of the Boogie file
	 */
	private JTextField tfBoogieFile = new JTextField();

	/**
	 * Textfield of the Source directory
	 */
	private JTextField tfSourceDir = new JTextField();

	/**
	 * Textarea of the output
	 */
	private JTextArea taOutput = new JTextArea();

	/**
	 * Joogie Thread
	 */
	private Thread thread;

	/**
	 * C-tor
	 */
	public MainFrame() {
		super("Joogie");

		// Border & Layout
		JPanel pane = (JPanel) getContentPane();
		pane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
		BorderLayout borderLayout = new BorderLayout(5, 5);
		pane.setLayout(borderLayout);

		// create widgets
		createMenuBar();
		createToolBar();
		createContent();
		createStatusBar();

		// configure frame
		setSize(800, 600);
		setLocationRelativeTo(null);
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
	}

	/**
	 * Creates the menubar
	 */
	protected void createMenuBar() {
		// File
		JMenu menuFile = new JMenu("File");
		menuFile.setMnemonic('F');

		// File, Exit
		menuFile.add(new AbstractAction("Exit") {
			public void actionPerformed(ActionEvent e) {
				System.exit(0);
			}
		});

		// Help
		JMenu menuHelp = new JMenu("Help");
		menuHelp.setMnemonic('H');

		// Help, About
		menuHelp.add(new AbstractAction("About...") {
			public void actionPerformed(ActionEvent e) {
				JOptionPane
						.showMessageDialog(MainFrame.this, "This is Joogie.");
			}
		});

		// add menus and menubar
		menuBar.add(menuFile);
		menuBar.add(menuHelp);
		setJMenuBar(menuBar);
	}

	/**
	 * Creates the toolbar
	 */
	protected void createToolBar() {
		// load icons
		ImageIcon iconRun = new ImageIcon(getClass().getResource("run.png"));
		ImageIcon iconShow = new ImageIcon(getClass().getResource("show.png"));

		// Run Joogie
		JButton button = new JButton(new AbstractAction("Run Joogie") {
			public void actionPerformed(ActionEvent e) {
				onRunJoogie();
			}
		});
		button.setIcon(iconRun);
		toolBar.add(button);

		// Show Report
		button = new JButton(new AbstractAction("Show Report") {
			public void actionPerformed(ActionEvent e) {
				onShowReport();
			}
		});
		button.setIcon(iconShow);
		toolBar.add(button);

		// add toolbar
		getContentPane().add(toolBar, BorderLayout.PAGE_START);
	}

	/**
	 * Creates the content
	 */
	protected void createContent() {
		// ContentTop panel
		JPanel panelContentTop = new JPanel();
		panelContentTop.setLayout(new GridBagLayout());
		GridBagConstraints gbc = new GridBagConstraints();
		gbc.insets = new Insets(3, 3, 3, 3);

		// Label, Textfield, Button
		gbc.gridx = 0;
		gbc.gridy = 0;
		gbc.fill = GridBagConstraints.NONE;
		gbc.anchor = GridBagConstraints.EAST;
		panelContentTop.add(new JLabel("JAR file:"), gbc);
		gbc.gridx = 1;
		gbc.gridy = 0;
		gbc.fill = GridBagConstraints.HORIZONTAL;
		gbc.anchor = GridBagConstraints.CENTER;
		gbc.weightx = 1.0;
		tfJarFile.setText(Options.v().getJarFile());
		panelContentTop.add(tfJarFile, gbc);
		gbc.gridx = 2;
		gbc.gridy = 0;
		gbc.fill = GridBagConstraints.NONE;
		gbc.anchor = GridBagConstraints.WEST;
		gbc.weightx = 0;
		panelContentTop.add(new JButton(new AbstractAction("...") {
			public void actionPerformed(ActionEvent e) {
				String file = onChooseFile(true);
				if (null != file)
					tfJarFile.setText(file);
			}
		}), gbc);

		// Label, Textfield, Button
		gbc.gridx = 0;
		gbc.gridy = 1;
		gbc.fill = GridBagConstraints.NONE;
		gbc.anchor = GridBagConstraints.EAST;
		panelContentTop.add(new JLabel("Boogie file:"), gbc);
		gbc.gridx = 1;
		gbc.gridy = 1;
		gbc.fill = GridBagConstraints.HORIZONTAL;
		gbc.anchor = GridBagConstraints.CENTER;
		gbc.weightx = 1.0;
		tfBoogieFile.setText(Options.v().getBoogieFile());
		panelContentTop.add(tfBoogieFile, gbc);
		gbc.gridx = 2;
		gbc.gridy = 1;
		gbc.fill = GridBagConstraints.NONE;
		gbc.anchor = GridBagConstraints.WEST;
		gbc.weightx = 0;
		panelContentTop.add(new JButton(new AbstractAction("...") {
			public void actionPerformed(ActionEvent e) {
				String file = onChooseFile(false);
				if (null != file)
					tfBoogieFile.setText(file);
			}
		}), gbc);

		// Label, Textfield, Button
		gbc.gridx = 0;
		gbc.gridy = 2;
		gbc.fill = GridBagConstraints.NONE;
		gbc.anchor = GridBagConstraints.EAST;
		panelContentTop.add(new JLabel("Source directory:"), gbc);
		gbc.gridx = 1;
		gbc.gridy = 2;
		gbc.fill = GridBagConstraints.HORIZONTAL;
		gbc.anchor = GridBagConstraints.CENTER;
		gbc.weightx = 1.0;
		tfSourceDir.setText(Options.v().getSourceDir());
		panelContentTop.add(tfSourceDir, gbc);
		gbc.gridx = 2;
		gbc.gridy = 2;
		gbc.fill = GridBagConstraints.NONE;
		gbc.anchor = GridBagConstraints.WEST;
		gbc.weightx = 0;
		panelContentTop.add(new JButton(new AbstractAction("...") {
			public void actionPerformed(ActionEvent e) {
				String file = onChooseDir();
				if (null != file)
					tfSourceDir.setText(file);
			}
		}), gbc);

		// Content panel
		JPanel panelContent = new JPanel();
		panelContent.setLayout(new BorderLayout(5, 5));
		panelContent.add(panelContentTop, BorderLayout.PAGE_START);

		// add splitPane
		taOutput.setEditable(false);
		taOutput.setBackground(Color.LIGHT_GRAY);
		panelContent.add(new JScrollPane(taOutput), BorderLayout.CENTER);

		// add content panel
		getContentPane().add(panelContent);
	}

	/**
	 * Creates the statusbar
	 */
	protected void createStatusBar() {
		// add statusbar
		getContentPane().add(statusBar, BorderLayout.SOUTH);
	}

	/**
	 * Handles the event "run joogie"
	 */
	protected void onRunJoogie() {
		if (isThreadRunning())
			return;

		// create thread
		thread = new Thread() {
			public void run() {
				try {
					// check files
					checkJarFile(tfJarFile.getText());
					checkBoogieDir(new File(tfBoogieFile.getText()).getParent());

					// setup GUI
					setStatusText("Joogie is running...");

					// reset the instance of the Boogie program, if necessary
					BoogieProgram.resetInstance();

					// create report and run Joogie
					report = new Report();
					Dispatcher dispatcher = new Dispatcher(tfJarFile.getText(),
							null, tfBoogieFile.getText(), report);
					dispatcher.run();

				} catch (RuntimeException e) {
					JOptionPane.showMessageDialog(MainFrame.this,
							e.getMessage(), "Error", JOptionPane.ERROR_MESSAGE);
				} catch (Exception e) {
					e.printStackTrace();
				} finally {
					// setup GUI
					setStatusText(null);
				}
			}
		};

		// start thread
		thread.start();
	}

	/**
	 * Handles the event "show report"
	 */
	protected void onShowReport() {
		try {
			// check files
			checkJarFile(tfJarFile.getText());
			checkBoogieFile(tfBoogieFile.getText());
			checkSourceDir(tfSourceDir.getText());

			// create report, if necessary
			if (null == report) {
				report = new Report();
			}

			// show report dialog
			ReportDialog reportDialog = new ReportDialog(report,
					tfSourceDir.getText());
			reportDialog.setVisible(true);

		} catch (RuntimeException e) {
			JOptionPane.showMessageDialog(MainFrame.this, e.getMessage(),
					"Error", JOptionPane.ERROR_MESSAGE);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Handles the event "choose file"
	 * 
	 * @param openDialog
	 *            true = show open dialog
	 * @return File name
	 */
	protected String onChooseFile(boolean openDialog) {
		JFileChooser fileChooser = new JFileChooser();
		int result = 0;

		// open or save dialog?
		if (openDialog) {
			result = fileChooser.showOpenDialog(this);
		} else {
			result = fileChooser.showSaveDialog(this);
		}

		if (JFileChooser.APPROVE_OPTION == result) {
			return fileChooser.getSelectedFile().getPath();
		}
		return null;
	}

	/**
	 * Handles the event "choose dir"
	 * 
	 * @return Directory name
	 */
	protected String onChooseDir() {
		JFileChooser fileChooser = new JFileChooser();
		fileChooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);

		if (JFileChooser.APPROVE_OPTION == fileChooser.showOpenDialog(this)) {
			return fileChooser.getSelectedFile().getPath();
		}
		return null;
	}

	/**
	 * Determines if the thread is running
	 * 
	 * @return true = thread is running
	 */
	protected boolean isThreadRunning() {
		if (null != thread && thread.isAlive()) {
			JOptionPane.showMessageDialog(this, "Thread is running!");
			return true;
		}
		return false;
	}

	/**
	 * Sets the status text of the statusbar
	 * 
	 * @param statusText
	 *            status text
	 */
	protected void setStatusText(String statusText) {
		if (null == statusText) {
			statusText = "Ready";
		}
		statusBar.setText(statusText);
	}

	/**
	 * Checks if the JAR file exists
	 * 
	 * @param filename
	 *            JAR file
	 * @throws RuntimeException
	 */
	protected void checkJarFile(String filename) throws RuntimeException {
		if (!FileIO.doesFileExist(filename))
			throw new RuntimeException("JAR file does not exist.");
	}

	/**
	 * Checks if the Boogie dir exists
	 * 
	 * @param dirname
	 *            directory
	 * @throws RuntimeException
	 */
	protected void checkBoogieDir(String dirname) throws RuntimeException {
		if (!FileIO.doesDirectoryExist(dirname))
			throw new RuntimeException("Boogie directory does not exist.");
	}

	/**
	 * Checks if the Boogie file exists
	 * 
	 * @param filename
	 *            File name
	 * @throws RuntimeException
	 */
	protected void checkBoogieFile(String filename) throws RuntimeException {
		if (!FileIO.doesFileExist(filename))
			throw new RuntimeException("Boogie file does not exist.");
	}

	/**
	 * Checks if the source dir exists
	 * 
	 * @param dirname
	 *            directory
	 * @throws RuntimeException
	 */
	protected void checkSourceDir(String dirname) throws RuntimeException {
		if (!FileIO.doesDirectoryExist(dirname))
			throw new RuntimeException("Source directory does not exist.");
	}
}
