/**
 * 
 */
package org.joogie.soot;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathFactory;

import org.joogie.Options;
import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.LocationTag;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssertStatement;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.statements.AssumeStatement;
import org.joogie.boogie.statements.InvokeStatement;
import org.joogie.boogie.statements.ReturnStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieType;
import org.joogie.soot.factories.BoogieTypeFactory;
import org.joogie.soot.factories.BoogieVariableFactory;
import org.joogie.soot.factories.RealConstantFactory;
import org.joogie.soot.factories.StringConstantFactory;
import org.joogie.util.Log;
import org.joogie.util.Util;
import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

import soot.RefType;
import soot.SootField;
import soot.SootMethod;
import soot.UnknownType;
import soot.jimple.ParameterRef;
import soot.jimple.internal.JimpleLocal;

/**
 * @author schaef
 *
 */
public class GlobalsCache {
	
	private HashMap<SootMethod, BoogieProcedure> boogieProcedures = new HashMap<SootMethod, BoogieProcedure>();
	
	private HashMap<BoogieProcedure, BoogieProcedureInfo> boogieProcInfo = new HashMap<BoogieProcedure, BoogieProcedureInfo>();

	private HashMap<SootField, Variable> publicFields = new HashMap<SootField, Variable>();

	private HashMap<RefType, Variable> typeVariables = new HashMap<RefType, Variable>();	

	public SootMethod findSootMethodForBoogieProcedure(BoogieProcedure proc) {
		BoogieProcedureInfo info = getProcedureInfo(proc);
		if (info==null) {
			return null;
		}
		return info.getSootMethod();
	}

	public BoogieProcedureInfo getProcedureInfo(BoogieProcedure proc) {
		return boogieProcInfo.get(proc);
	}

	
	public Variable lookupTypeVariable(RefType t) {
		if (!typeVariables.containsKey(t)) {
			Variable v = BoogieTypeFactory.createTypeVariable(t);
			typeVariables.put(t, v);
			BoogieProgram.v().addTypeVariable(v);
		}
		return typeVariables.get(t);
	}

	public BoogieProcedure lookupProcedure(SootMethod m) {
		BoogieProcedure proc = null;
		if (!boogieProcedures.containsKey(m)) {
			proc = createBoogieProcedure(m);
			BoogieProgram.v().addProcedure(proc);
			//create the boogie procedure info
			BoogieProcedureInfo procinfo = new BoogieProcedureInfo(proc,m); 
			boogieProcInfo.put(proc, procinfo);
						
			//TODO: this is a hack! the exception analysis
			//requires that proc is the "currentProcedure"
			//however, this method is not supposed to change
			//the currentProcedure, so we only  change it
			//for a few statements and change it back again.
			BoogieProcedure old_ = BoogieHelpers.currentProcedure;			
			BoogieHelpers.currentProcedure = proc;
			
			boogieProcedures.put(m, proc);
			if (!BoogieHelpers.callDependencyMap.containsKey(proc)) {
				BoogieHelpers.callDependencyMap.put(proc,
						new HashSet<BoogieProcedure>());
				 /*
				  *  for each procedure we need 
				  *  to consider at least it's own modified
				  *  globals
				 */
				BoogieHelpers.callDependencyMap.get(proc).add(proc);
			}
			BoogieExceptionAnalysis.addUncaughtExceptionsAndModifiesClause(m,
					new HashSet<SootMethod>());
			// TODO: IS THIS SAFE TO DO? Is it true that all non-static
			// procedures should require that __this is not null?
			if (proc.getThisVariable() != null) {
				proc.addRequires(BoogieHelpers.isNotNull(proc.getThisVariable()));
			}
			//undo change to BoogieHelpers.currentProcedure
			BoogieHelpers.currentProcedure = old_;
		} else {
			proc = boogieProcedures.get(m);
		}
		return proc;
	}

	private BoogieProcedure createBoogieProcedure(SootMethod method) {		
		String procedureName = BoogieHelpers.getQualifiedName(method);
		Variable returnVariable = BoogieHelpers.createProcedureReturnVariable(method
				.getReturnType());

		LocationTag locationTag = BoogieHelpers.createLocationTag(method.getTags());
		String signatureString = method.getSignature();
		
		LinkedList<Variable> parameterList = new LinkedList<Variable>();
		for (int i = 0; i < method.getParameterCount(); i++) {
			ParameterRef pref = new ParameterRef(method.getParameterType(i), i);
			parameterList.addLast(BoogieHelpers.createParameterVariable(method,
					pref));
		}

		Variable thisVariable = BoogieHelpers.createProcedureThisVariable(method);
		BoogieProcedure proc = new BoogieProcedure(procedureName, returnVariable, 
				locationTag, signatureString, parameterList, thisVariable);
		return proc;
	}
	
	public Variable lookupStaticField(SootField arg0) {
		if (!publicFields.containsKey(arg0)) {
			Variable v = BoogieVariableFactory.v().createBoogieVariable(
					BoogieHelpers.getQualifiedName(arg0),
					BoogieTypeFactory.lookupBoogieType(arg0.getType()),
					false);
			publicFields.put(arg0,v);
					
			BoogieProgram.v().addGlobalVar(v);
		}
		return publicFields.get(arg0);
	}

	public Variable lookupField(SootField arg0) {
		if (!publicFields.containsKey(arg0)) {
			Variable v = BoogieVariableFactory.v().createBoogieVariable(
					BoogieHelpers.getQualifiedName(arg0),
					BoogieTypeFactory.lookupBoogieFieldType(arg0
							.getType()), false);
			publicFields.put(arg0, v);
			BoogieProgram.v().addGlobalVar(v);
		}
		return publicFields.get(arg0);
	}

	/**
	 * This counter returns consecutive, unique number.
	 * might be placed somewhere else in the future.
	 */
	private Integer uniqueNumber=0;	
	public Integer getUniqueNumber() {
		return this.uniqueNumber++;
	}
	
	/*
	 * Singleton stuff
	 */
	public static GlobalsCache v() {
		if (null==instance) {
			instance = new GlobalsCache();
		}
		return instance;
	}
	
	public static void resetInstance() {
		if (instance != null) {
			instance.boogieProcedures = new HashMap<SootMethod, BoogieProcedure>();
			instance.publicFields = new HashMap<SootField, Variable>();
			instance.typeVariables = new HashMap<RefType, Variable>();
			instance.uniqueNumber = 0;
		}
		BoogieTypeFactory.resetFactory();
		RealConstantFactory.resetFactory();
		StringConstantFactory.resetFactory();
		instance = null;		
	}
	
	private static GlobalsCache instance = null;
	
	private GlobalsCache() {
		
	}
	
	
	/*
	 * TODO: this has to be Sergios code. Please test it again. 
	 * This should not be in this class anyway
	 * =======================================================================================
	 */
	/**
	 * Creates a boogie procedure according to the structure specified in the
	 * EFG
	 */
	/**
	 * 
	 */
	public void createEFGProcedure() {

		Log.debug("Generating EFG Procedure...");
		try {
			// Parse the XML File
			DocumentBuilderFactory docBuilderFactory = DocumentBuilderFactory
					.newInstance();
			DocumentBuilder docBuilder = docBuilderFactory.newDocumentBuilder();
			Document doc = docBuilder.parse(new File(Options.v()
					.getEFG()));
			// Get a new XPath to query our graph
			XPathFactory xPathfactory = XPathFactory.newInstance();
			XPath xpath = xPathfactory.newXPath();

			// Look for the events and map them to the boogie procedures
			NodeList events = (NodeList) xpath.evaluate("/EFG/Events/Event",
					doc, XPathConstants.NODESET);

			// The event handlers
			BoogieProcedure eventList[] = new BoogieProcedure[events
					.getLength()];
			// The init procedures for the handler classes
			Set<BoogieProcedure> initProcedures = new HashSet<BoogieProcedure>(
					events.getLength());
			// boolean array to indicate initial events
			boolean initialEvents[] = new boolean[eventList.length];
			int i;
			for (i = 0; i < events.getLength(); i++) {
				String className = xpath.evaluate("Listeners", events.item(i));
				initialEvents[i] = Boolean.parseBoolean(xpath.evaluate(
						"Initial", events.item(i)));
				boolean found;
				if (className == null || className.isEmpty()) { // The <Event>
																// doesn't have
																// a <Listeners>
																// key
					Log.error("Couldn't locate the Listeners value:"
							+ events.item(i).getTextContent());
					return;
				}
				found = false;
				for (Entry<SootMethod, BoogieProcedure> e : boogieProcedures
						.entrySet()) { // look for the event in my procedures
										// and get a reference
					SootMethod p = e.getKey();
					if (p.getDeclaringClass().getName().equals(className)) {
						if (p.getName().equals("actionPerformed") && !found) { // Assumed
																				// all
																				// handlers
																				// are
																				// ActionListener
							eventList[i] = e.getValue();
							found = true;
						}
					}
					if (p.getName().equals("<init>") // Collect initializers as
														// well
							&& e.getValue().getRootBlock() != null)
						initProcedures.add(e.getValue());
				}
				if (!found) // couldn't find the event handler. PANIC!
				{
					Log.error("Couldn't locate event handler:"
							+ events.item(i).getTextContent());
					return;
				}
			}

			// Load the adjacency matrix
			boolean GraphMatrix[][] = new boolean[eventList.length][eventList.length];
			NodeList rows = (NodeList) xpath.evaluate("/EFG/EventGraph/Row",
					doc, XPathConstants.NODESET);
			for (i = 0; i < rows.getLength(); i++) {
				NodeList columns = (NodeList) xpath.evaluate("E", rows.item(i),
						XPathConstants.NODESET);
				for (int j = 0; j < columns.getLength(); j++)
					GraphMatrix[i][j] = Integer.parseInt(columns.item(j)
							.getTextContent()) == 0 ? false : true;
			}

			// Create the new procedure
			LinkedList<BoogieType> params = new LinkedList<BoogieType>();
			params.add(BoogieBaseTypes.getRefType());
			BoogieProcedure proc = new BoogieProcedure("$EFG_Procedure", null,
					false, false);
			BoogieHelpers.callDependencyMap.put(proc,
					new HashSet<BoogieProcedure>());
			BoogieHelpers.callDependencyMap.get(proc).add(proc); // for each
																	// procedure
																	// we need
																	// to
																	// consider
																	// at least
																	// its own
																	// modified
																	// globals
			// Create an initial block for our procedure
			BoogieProcedureInfo procinfo = getProcedureInfo(proc);
			proc.setBodyRoot(new BasicBlock("$EFG_INIT_"));
			Set<BasicBlock> lastBlocks = proc.getRootBlock()
					.getFinalSuccessors(); // Makes sure all blocks are
											// connected

			// Create a block for abnormal exits (uncaught exceptions)
			BasicBlock abnormalExit = new BasicBlock("$EFG_ABNORMAL_EXIT_");
			abnormalExit.addStatement(new ReturnStatement());
			HashSet<BasicBlock> abnormalExitSucc = new HashSet<BasicBlock>();
			abnormalExitSucc.add(abnormalExit);

			// First, inline all init procedures
			for (BoogieProcedure p : initProcedures) {
				BoogieProcedureInfo pi = getProcedureInfo(p);
				BoogieHelpers.callDependencyMap.get(proc).add(p); // Ensure the
																	// modifies
																	// list is
																	// consistent
				procinfo.getLocalMap().putAll(pi.getLocalMap()); // Add the locals
				p.renameParametersForInlining();
				proc.getTmpLocals().addAll(p.getTmpLocals()); // Add the temp.
																// variables

				for (Variable v : p.getParameterList())
					procinfo.getLocalMap().put(
							new JimpleLocal(v.getName(), UnknownType.v()), v);
				if (p.getThisVariable() != null) {
					procinfo.getLocalMap().put(
							new JimpleLocal(p.getThisVariable().getName(),
									UnknownType.v()), p.getThisVariable());
				}
				Map<BasicBlock, BasicBlock> transMap = new HashMap<BasicBlock, BasicBlock>();
				BasicBlock newBlock = p.getRootBlock().deepClone(p.getName(),
						transMap);
				transMap = Util.reverseMap(transMap);
				for (Expression e : p.getRequires())
					// Assume the requires
					newBlock.addStatement(new AssumeStatement(e), true);
				for (BasicBlock b : lastBlocks)
					// Connect the final blocks from the last procedure
					b.connectToSuccessor(newBlock);
				for (BasicBlock b : getThrowBlocks(newBlock, p, transMap,
						new HashSet<BasicBlock>()))
					b.Successors = abnormalExitSucc; // Connect the exceptions
														// with the abnormal
														// exit
				lastBlocks = newBlock.getFinalSuccessors();
				lastBlocks.remove(abnormalExit);
			}

			// Then, create the structure dictated by the EFG

			BasicBlock efgStart = new BasicBlock("$EFG_START_"); // Initial EFG
																	// block
			for (BasicBlock b : lastBlocks)
				// Connect it to the init section
				b.connectToSuccessor(efgStart);

			// Keep track of the initial block of each inlined event procedure
			BasicBlock eventBlocks[] = new BasicBlock[eventList.length];
			// Also keep track of the final blocks
			@SuppressWarnings("unchecked")
			Set<BasicBlock>[] finalSets = (Set<BasicBlock>[]) new Set[eventList.length];

			for (i = 0; i < eventList.length; i++) { // Clone the procedures
				BoogieProcedure p = eventList[i];
				BoogieHelpers.callDependencyMap.get(proc).add(p); // Ensure the
																	// modifies
																	// list is
																	// consistent
				procinfo.getLocalMap().putAll(getProcedureInfo(p).getLocalMap()); // Add the locals
				p.renameParametersForInlining();
				proc.getTmpLocals().addAll(p.getTmpLocals()); // Add the temp.
																// variables

				// Add the parameters as locals
				for (Variable v : p.getParameterList())
					procinfo.getLocalMap().put(
							new JimpleLocal(v.getName(), UnknownType.v()), v);
				if (p.getThisVariable() != null) {
					procinfo.getLocalMap().put(
							new JimpleLocal(p.getThisVariable().getName(),
									UnknownType.v()), p.getThisVariable());
				}

				eventBlocks[i] = p.getRootBlock().deepClone(
						"Event" + Integer.toString(i) + "_");
				for (Expression e : p.getRequires())
					// Assume the requires at the beginning of the method
					eventBlocks[i].addStatement(new AssumeStatement(e), true);
				finalSets[i] = eventBlocks[i].getFinalSuccessors();
				if (initialEvents[i])
					efgStart.connectToSuccessor(eventBlocks[i]);
			}

			// Create an exit block
			BasicBlock exitBlock = new BasicBlock("$EFG_EXIT_");
			exitBlock.addStatement(new ReturnStatement());
			proc.setExitBlock(exitBlock);

			// Connect the procedure blocks according to the EFG
			for (i = 0; i < GraphMatrix.length; i++)
				for (int j = 0; j < GraphMatrix[i].length; j++)
					for (BasicBlock b : finalSets[i]) {
						if (GraphMatrix[i][j])
							b.connectToSuccessor(eventBlocks[j]);
						b.connectToSuccessor(exitBlock);
					}

			// Sweep the method and inline field accesses
			inlineFieldAccesses(proc.getRootBlock(), new HashSet<BasicBlock>(),
					new HashMap<BoogieProcedure, Variable>());

			// Finally, add the generated procedure to the program
			boogieProcedures.put(null, proc);
			Log.debug("EFG procedure created successfully.");
		} catch (SAXParseException err) {
			Log.error("** XML Parsing error" + ", line " + err.getLineNumber()
					+ ", uri " + err.getSystemId());
			Log.error(" " + err.getMessage());

		} catch (SAXException e) {
			StringWriter errorLog = new StringWriter();
			PrintWriter s = new PrintWriter(errorLog);
			Exception x = e.getException();
			((x == null) ? e : x).printStackTrace(s);
			Log.error(errorLog);

		} catch (Throwable t) {
			StringWriter errorLog = new StringWriter();
			PrintWriter s = new PrintWriter(errorLog);
			t.printStackTrace(s);
			Log.error(errorLog);
		}
	}

	/**
	 * @param b
	 *            The block
	 * @param p
	 *            A procedure
	 * @param transMap
	 *            A map of the clone process (NewBlock -> OldBlock)
	 * @param visited
	 *            A set indicating already visited blocks for the recursion
	 *            termination
	 * @return The list of blocks starting at b that are exception catch blocks
	 *         in procedure p (according to the translation map)
	 */
	private Set<BasicBlock> getThrowBlocks(BasicBlock b, BoogieProcedure p,
			Map<BasicBlock, BasicBlock> transMap, HashSet<BasicBlock> visited) {
		HashSet<BasicBlock> result = new HashSet<BasicBlock>();
		
		if (getProcedureInfo(p).getExceptionBlocks().contains(transMap.get(b))) // If b is an
																// exception
																// block
			result.add(b);
		visited.add(b);
		for (BasicBlock s : b.Successors)
			// Repeat for the successors
			if (!visited.contains(s))
				result.addAll(getThrowBlocks(s, p, transMap, visited));
		return result;
	}

	/**
	 * Replaces get/set procedure calls introduced by the compiler with inlined
	 * assignments. We need this in order to avoid recursive inlining . ==> Also
	 * changes asserts to assumes!
	 * 
	 * @param b
	 *            The block for which get/set procedure calls should be inlined
	 * @param visited
	 *            A set of already visited blocks
	 * @param cache
	 *            A cache of already processed getter/setters to speed things up
	 */
	private void inlineFieldAccesses(BasicBlock b, Set<BasicBlock> visited,
			Map<BoogieProcedure, Variable> cache) {
		if (visited.contains(b))
			return;

		// Replace all access method calls with assignments
		int sindex = 0;
		for (Statement s : b.getStatements()) {
			if (s instanceof InvokeStatement) {
				InvokeStatement is = (InvokeStatement) s;
				BoogieProcedure proc = is.getInvokedProcedure();
				Statement replacement = null;
				if (proc.getName().contains("access")) {
					Expression theField = cache.get(proc);
					if (proc.getParameterList().size() == 1) { // A getter
						if (theField == null)
							for (Statement ps : proc.getRootBlock()
									.getStatements()) // Look for the field
														// access, we assume a
														// single block
							{
								if (ps instanceof AssignStatement) {
									AssignStatement as = (AssignStatement) ps;
									// Look for local := nonparameter
									if (as.getRight() instanceof Variable
											&& !proc.getParameterList()
													.contains(as.getRight())) {
										theField = as.getRight();
										cache.put(proc, (Variable) theField);
										break;
									}
								}
							}
						replacement = BoogieHelpers.createAssignment(is
								.getModifiedVariables().get(0), theField);
					} else if (proc.getParameterList().size() == 2) { // A
																		// setter
						if (theField == null)
							for (Statement ps : proc.getRootBlock()
									.getStatements()) // Look for the field
							{
								if (ps instanceof AssignStatement) {
									AssignStatement as = (AssignStatement) ps;
									// Look for global := local
									if (as.getLeft() instanceof Variable
											&& !getProcedureInfo(proc).getLocalMap().values()
													.contains(as.getLeft())) {
										theField = as.getLeft();
										cache.put(proc, (Variable) theField);
										break;
									}
								}
							}
						replacement = BoogieHelpers.createAssignment(theField, is
								.getArguments().get(1));
					}
					b.getStatements().set(sindex, replacement);
				}
			} else if (s instanceof AssertStatement) // Transform asserts in
														// assumes
				b.getStatements().set(
						sindex,
						new AssumeStatement(((AssertStatement) s)
								.getExpression()));
			sindex++;
		}
		visited.add(b); // Mark the block as visited
		// Repeat recursively for all successors
		for (BasicBlock succ : b.Successors) {
			inlineFieldAccesses(succ, visited, cache);
		}
	}
	



}
