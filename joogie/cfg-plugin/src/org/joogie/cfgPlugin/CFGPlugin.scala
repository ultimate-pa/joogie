/*
 * Joogie, CFG-Plugin
 *
 * Copyright (C) 2013 Philipp Ruemmer
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

package org.joogie.cfgPlugin

import ap.parser._
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction
import ap.terfor.TerForConvenience
import ap.util.LRUCache

import scala.collection.mutable.ArrayBuffer

import Util._

object CFGPlugin {
  private def toPred(f : IFormula) : Predicate = f match {
    case IAtom(p, _) => p
  }

  def apply(cfg : Dag[IFormula],
            effectualNodes : Seq[IFormula],
            ineffectualityFlags : Seq[IFormula],
            minEffectualNodesCovered : Int) =
    new CFGPlugin(cfg map (toPred _),
                  effectualNodes map (toPred _),
                  ineffectualityFlags map (toPred _),
                  minEffectualNodesCovered)

  // Some wrappers to make integration with Java easier

  def mkDagEmpty : Dag[IFormula] = DagEmpty

  def mkDagNode(d : IFormula,
                children : Array[Int],
                next : Dag[IFormula]) : Dag[IFormula] =
    DagNode(d, children.toList, next)
}

class CFGPlugin(cfg : Dag[Predicate],
                effectualNodes : Seq[Predicate],
                ineffectualityFlags : Seq[Predicate],
                minEffectualNodesCovered : Int) extends Plugin {

  private val cfgSeq = cfg.subdagIterator.toVector

//cfg.prettyPrint
//println("effectual: " + effectualNodes.toList)
//println("minEffectualNodesCovered: " + minEffectualNodesCovered)

  // unique entry node
  assert(cfg.elimUnconnectedNodes.size == cfg.size)
  // unique exit node
  assert((0 until (cfgSeq.size - 1)) forall {
            i => !cfgSeq(i).children.isEmpty
          })

  private val relevantPredicates : Set[Predicate] =
    cfg.iterator.toSet ++ ineffectualityFlags

  private val axiomCache =
    new LRUCache[(Set[Predicate], Set[Predicate]),
                 Option[(Conjunction, Conjunction)]](100)

  def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = {
    val knownPosLits =
      (for (atom <- goal.facts.predConj.positiveLits.iterator;
            if (relevantPredicates contains atom.pred))
         yield atom.pred).toSet
    val knownNegLits =
      (for (atom <- goal.facts.predConj.negativeLits.iterator;
            if (relevantPredicates contains atom.pred))
         yield atom.pred).toSet

    axiomCache((knownPosLits, knownNegLits)){
      doGenerateAxioms(goal, knownPosLits, knownNegLits)
    }
  }

  private def doGenerateAxioms(goal : Goal,
                               knownPosLits : Set[Predicate],
                               knownNegLits : Set[Predicate])
                             : Option[(Conjunction, Conjunction)] = {

    // Determine the remaining effectual nodes
    val effectualNodesSet =
      (for ((p, f) <-
              effectualNodes.iterator zip ineffectualityFlags.iterator;
            if (!(knownPosLits contains f))) yield p).toSet

    // Nodes that every considered control path has to pass through
    val fixedNodes =
      (for ((DagNode(p, _, _), i) <- cfgSeq.iterator.zipWithIndex;
            if (knownPosLits contains p)) yield i).toVector

    ////////////////////////////////////////////////////////////////////////////
    // Determine reachable states 

//println("Running plugin")
//println("state: " + goal.facts)

    // Array specifying the nodes that are reachable on control paths
    // passing through the nodes that have been assumed so far
    val reachableNodes = Array.fill(cfgSeq.size)(false)

    // For each dag node, the index of the next-bigger
    // positively assumed node
    val nextFixedIndex = Array.ofDim[Int](cfgSeq.size)

    {
      // Forward sweep
      var nextFixedNode = 0
      var nextFixedNodeIndex : Int = fixedNodes match {
        case Seq() => cfgSeq.size
        case Seq(i, _*) => i
      }
  
      reachableNodes(0) = true
  
      for (i <- 0 until cfgSeq.size) {
        val DagNode(p, children, _) = cfgSeq(i)
  
        if (knownPosLits contains p) {
          if (!reachableNodes(i))
            return Some((Conjunction.FALSE, Conjunction.TRUE))
  
          nextFixedNode = nextFixedNode + 1
          nextFixedNodeIndex =
            if (nextFixedNode < fixedNodes.size)
              fixedNodes(nextFixedNode)
            else
              cfgSeq.size
        } else if (knownNegLits contains p) {
          reachableNodes(i) = false
        }

        nextFixedIndex(i) = nextFixedNodeIndex

        if (reachableNodes(i)) {
          for (c <- children)
            if (i + c <= nextFixedNodeIndex)
              reachableNodes(i + c) = true
        }
      }
    }

    if (!reachableNodes.last)
      return Some((Conjunction.FALSE, Conjunction.TRUE))

    {
      // Backward sweep
      for (i <- (cfgSeq.size - 2) to 0 by -1) {
        val DagNode(p, children, _) = cfgSeq(i)

        if (reachableNodes(i))
          reachableNodes(i) = children exists { c =>
            (i + c <= nextFixedIndex(i)) && reachableNodes(i + c)
          }

        if (knownPosLits contains p) {
          if (!reachableNodes(i))
            return Some((Conjunction.FALSE, Conjunction.TRUE))
        }
      }
    }

    if (!reachableNodes(0))
      return Some((Conjunction.FALSE, Conjunction.TRUE))

//println("reachable: " + (reachableNodes mkString ", "))

    ////////////////////////////////////////////////////////////////////////////
    // Determine number of reachable effectual states

    val maxEffectualBwd, maxEffectualFwd = Array.fill(cfgSeq.size)(0)

    {
      // Forward sweep
      for (i <- 0 until cfgSeq.size) if (reachableNodes(i)) {
        val DagNode(p, children, _) = cfgSeq(i)

        val localMax =
          maxEffectualBwd(i) + (if (effectualNodesSet contains p) 1 else 0)
        maxEffectualBwd(i) = localMax

        val nextFixed = nextFixedIndex(i)
        for (c <- children)
          if (i + c <= nextFixed && reachableNodes(i + c))
            maxEffectualBwd(i + c) = maxEffectualBwd(i + c) max localMax
      }
    }

    {
      // Backward sweep
      for (i <- (cfgSeq.size - 1) to 0 by -1) if (reachableNodes(i)) {
        val DagNode(_, children, _) = cfgSeq(i)

        var localMax = 0

        val nextFixed = nextFixedIndex(i)
        for (c <- children)
          if (i + c <= nextFixed && reachableNodes(i + c))
            localMax = localMax max (
              maxEffectualFwd(i + c) +
              (if (effectualNodesSet contains cfgSeq(i + c).d) 1 else 0))

        maxEffectualFwd(i) = localMax
      }
    }
   
//   println("fwd effectual: " + (maxEffectualFwd mkString ", "))
//   println("bwd effectual: " + (maxEffectualBwd mkString ", "))

    for (i <- 0 until cfgSeq.size)
      if (reachableNodes(i) &&
          maxEffectualBwd(i) + maxEffectualFwd(i) < minEffectualNodesCovered)
        reachableNodes(i) = false

    ////////////////////////////////////////////////////////////////////////////
    // Search for nodes that are visited by all remaining paths

    val inevitableNodes = new ArrayBuffer[Predicate]

    {
      var inevitableCand = 0

      for (i <- 0 until cfgSeq.size) if (reachableNodes(i)) {
        val DagNode(p, children, _) = cfgSeq(i)
  
        if (i == inevitableCand && !(knownPosLits contains p))
          inevitableNodes += p

        val nextFixed = nextFixedIndex(i)
        for (c <- children)
          if (i + c <= nextFixed && reachableNodes(i + c))
            inevitableCand = inevitableCand max (i + c)
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    val unreachableNodes =
      (for ((DagNode(p, _, _), i) <- cfgSeq.iterator.zipWithIndex;
            if (!(knownNegLits contains p) && !reachableNodes(i)))
         yield p).toVector

//println("unreachable nodes: " + unreachableNodes)
//println("inevitable nodes: " + inevitableNodes)

    if (unreachableNodes.isEmpty && inevitableNodes.isEmpty) {
      None
    } else {
      implicit val _ = goal.order
      import TerForConvenience._

      Some((conj(for (p <- unreachableNodes) yield !atom2Conj(p(List()))) &
            conj(for (p <- inevitableNodes) yield p(List())),
            Conjunction.TRUE))
    }
  }

}

