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

package org.joogie.runners;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FilterOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.jar.Attributes;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import org.joogie.Main;
import org.joogie.Options;
import org.joogie.boogie.BoogieProgram;
import org.joogie.report.Report;
import org.joogie.soot.BoogieBodyTransformer;
import org.joogie.soot.factories.OperatorFunctionFactory;
import org.joogie.util.FileIO;
import org.joogie.util.Log;

import soot.PackManager;
import soot.Transform;

/**
 * The Soot Runner
 * 
 * @author arlt
 */
public class SootRunner extends Runner {

	/**
	 * stderr print stream
	 */
	private PrintStream stderr;

	/**
	 * stdout print stream
	 */
	private PrintStream stdout;

	/**
	 * Runs Soot by using a JAR file
	 * 
	 * @param jarFile
	 *            JAR file
	 * @param boogieFile
	 *            Boogie file
	 * @param report
	 *            Report
	 */
	public void runWithJar(String jarFile, String boogieFile, Report report) {
		try {
			// command-line arguments for Soot
			List<String> args = new ArrayList<String>();
			fillSootArgs(args);

			// extract dependent JARs
			List<File> jarFiles = new ArrayList<File>();
			extractClassPath(new File(jarFile), jarFiles);
			jarFiles.add(new File(jarFile));
			fillClassPath(jarFiles);

			// additional classpath available?
			String cp = buildClassPath(jarFiles);
			if (Options.v().hasClasspath()) {
				cp += File.pathSeparator + Options.v().getClasspath();
			}

			// set soot-class-path
			args.add("-cp");
			args.add(cp);

			// set classes
			enumClasses(new File(jarFile), args);

			// finally, run soot
			run(args, boogieFile, report);

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Runs Soot by using a class (e.g., from Joogie)
	 * 
	 * @param classFile
	 *            Class file
	 * @param sourceFolder
	 *            Source folder
	 * @param boogieFile
	 *            Boogie file
	 * @param report
	 *            Report
	 */
	public void runWithClass(String classFile, String sourceFolder,
			String boogieFile, Report report) {
		try {
			// dependent JAR files
			List<File> jarFiles = new ArrayList<File>();
			fillClassPath(jarFiles);

			// no source folder given?
			if (null == sourceFolder) {
				// get Joogie's folder
				sourceFolder = Main.class.getProtectionDomain().getCodeSource()
						.getLocation().getPath();

				// try to get Joogie tests folder
				File file = new File(sourceFolder);
				file = file.getParentFile();
				file = file.getParentFile();
				file = new File(file, "joogie-tests/bin");
				jarFiles.add(file);
			}

			// command-line arguments for Soot
			List<String> args = new ArrayList<String>();
			fillSootArgs(args);

			// add soot-class-path
			args.add("-cp");
			args.add(buildClassPath(jarFiles));
			args.add(classFile);

			// finally, run soot
			run(args, boogieFile, report);

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Runs Soot by using a source file
	 * 
	 * @param sourceFile
	 *            Source file
	 * @param report
	 *            Report
	 */
	public void runWithSource(String sourceFile, Report report) {
		try {
			// command-line arguments for Soot
			List<String> args = new ArrayList<String>();
			fillSootArgs(args);
			
			// add standard classpath
			List<File> jarFiles = new ArrayList<File>();
			fillClassPath(jarFiles);

			// add additional classpath
			String cp = buildClassPath(jarFiles);
			if (Options.v().hasClasspath()) {
				cp += File.pathSeparator + Options.v().getClasspath();
			}
			
			// add classpath to soot arguments
			args.add("-cp");
			args.add(cp);

			// add source file
			args.add(sourceFile.substring(0, sourceFile.lastIndexOf(".java")));

			// finally, run soot
			run(args, null, report);

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Runs Soot
	 * 
	 * @param args
	 *            Command-line arguments
	 * @param boogieFile
	 *            Boogie file
	 * @param report
	 *            Report
	 */
	protected void run(List<String> args, String boogieFile, Report report) {
		try {
			// init stream redirection
			initStream();

			// init the boogie program and the prelude
			BoogieProgram.v().addProcedures(
					OperatorFunctionFactory.v().getPreludProcedures());

			// reset & init Soot
			soot.G.reset();
			PackManager
					.v()
					.getPack("jtp")
					.add(new Transform("jtp.myTransform",
							new BoogieBodyTransformer(report)));

			// Finally, run Soot
			soot.Main.main(args.toArray(new String[] {}));

			// get Boogie program and save to file
			if (boogieFile != null && boogieFile != "") {
				String boogieProgram = BoogieProgram.v().toBoogie();
				FileIO.toFile(boogieProgram, boogieFile);
			}

		} catch (Exception e) {
			e.printStackTrace();
			BoogieProgram.resetInstance();
		} finally {
			// reset stream redirection
			resetStream();
		}
	}

	/**
	 * Fills a list with the standard command-line arguments needed by Soot
	 * 
	 * @param args
	 *            Command-line arguments
	 */
	protected void fillSootArgs(List<String> args) {
		args.add("-pp");
		args.add("-keep-line-number");
		args.add("-print-tags");
		args.add("-output-format");
		args.add("none");
		// args.add("-allow-phantom-refs");
		// args.add("use-original-names");
	}

	/**
	 * Fills a list with the standard JAR files needed by Soot
	 * 
	 * @param files
	 *            Standard JAR files needed by Soot
	 */
	protected void fillClassPath(List<File> files) {
		// add Runtime Library
		files.add(new File(new File(System.getProperty("java.home"), "lib"),
				"rt.jar"));

		// add Java Cryptography Extension Library
		files.add(new File(new File(System.getProperty("java.home"), "lib"),
				"jce.jar"));
	}

	/**
	 * Returns the class path argument for Soot
	 * 
	 * @param files
	 *            Files in the class path
	 * @return Class path argument for Soot
	 */
	protected String buildClassPath(List<File> files) {
		StringBuilder sb = new StringBuilder();
		for (File file : files) {
			sb.append(file.getPath() + File.pathSeparator);
		}
		return sb.toString();
	}

	/**
	 * Extracts dependent JARs from the JAR's manifest
	 * 
	 * @param file
	 *            JAR file object
	 * @param jarFiles
	 *            List of dependent JARs
	 */
	protected void extractClassPath(File file, List<File> jarFiles) {
		try {
			// open JAR file
			JarFile jarFile = new JarFile(file);

			// get manifest and their main attributes
			Attributes mainAttributes = jarFile.getManifest()
					.getMainAttributes();
			String classPath = mainAttributes
					.getValue(Attributes.Name.CLASS_PATH);
			
			// close JAR file
			jarFile.close();

			// empty class path?
			if (null == classPath)
				return;

			// look for dependent JARs
			String[] classPathItems = classPath.split(" ");
			for (String classPathItem : classPathItems) {
				if (classPathItem.endsWith(".jar")) {
					// add jar
					Log.debug("Adding " + classPathItem
							+ " to Soot's class path");
					jarFiles.add(new File(file.getParent(), classPathItem));
				}
			}

		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Enumerates all classes in a JAR file
	 * 
	 * @param file
	 *            JAR file object
	 * @param classes
	 *            List of classes
	 */
	protected void enumClasses(File file, List<String> classes) {
		try {
			// open JAR file
			Log.debug("Opening jar " + file.getPath());
			JarFile jarFile = new JarFile(file);
			Enumeration<JarEntry> entries = jarFile.entries();

			// iterate JAR entries
			while (entries.hasMoreElements()) {
				JarEntry entry = entries.nextElement();
				String entryName = entry.getName();

				if (entryName.endsWith(".class")) {
					// get class
					String className = entryName.substring(0,
							entryName.length() - ".class".length());
					className = className.replace('/', '.');

					// is class in scope?
					if (Options.v().hasScope()) {
						if (!className.startsWith(Options.v().getScope())) {
							continue;
						}
					}

					// add class
					Log.debug("Adding class " + className);
					classes.add(className);
				}
			}

			// close JAR file
			jarFile.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Initializes stream redirection
	 */
	protected void initStream() {
		// backup stderr and stdout
		stderr = System.err;
		stdout = System.out;

		// redirect stderr and stdout
		// if there is at least one receiver registered
		if (receivers.size() > 0) {
			PrintStream ps = new PrintStream(new FilteredStream(
					new ByteArrayOutputStream()));
			System.setErr(ps);
			System.setOut(ps);
		}
	}

	/**
	 * Resets stream redirection
	 */
	protected void resetStream() {
		// restore stderr and stdout
		System.setErr(stderr);
		System.setOut(stdout);
	}

	/**
	 * FilteredStream
	 * 
	 * @author arlt
	 */
	class FilteredStream extends FilterOutputStream {

		/**
		 * C-tor
		 * 
		 * @param stream
		 *            OutputStream
		 */
		public FilteredStream(OutputStream stream) {
			super(stream);
		}

		@Override
		public void write(byte b[]) throws IOException {
			String s = new String(b);
			SootRunner.this.notifyReceivers(s);
		}

		@Override
		public void write(byte b[], int off, int len) throws IOException {
			String s = new String(b, off, len);
			SootRunner.this.notifyReceivers(s);
		}
	}

}
