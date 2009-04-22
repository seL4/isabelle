/*
 * Document markup nodes, with connection to Swing tree model
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover

import isabelle.proofdocument.ProofDocument

import sidekick.IAsset
import javax.swing._
import javax.swing.text.Position
import javax.swing.tree._

object MarkupNode {

  def markup2default_node(node: MarkupNode, cmd: Command, doc: ProofDocument) : DefaultMutableTreeNode = {

    implicit def int2pos(offset: Int): Position =
      new Position { def getOffset = offset; override def toString = offset.toString}

    object RelativeAsset extends IAsset {
      override def getIcon : Icon = null
      override def getShortString : String = node.kind
      override def getLongString : String = node.desc
      override def getName : String = node.id
      override def setName (name : String) = ()
      override def setStart(start : Position) = ()
      override def getStart : Position = node.abs_start(doc)
      override def setEnd(end : Position) = ()
      override def getEnd : Position = node.abs_stop(doc)
      override def toString = node.id + ": " + node.kind + "[" + getStart + " - " + getEnd + "]"
    }

    new DefaultMutableTreeNode(RelativeAsset)
  }
}

class MarkupNode (val base : Command, val start : Int, val stop : Int,
                    val id : String, val kind : String, val desc : String) {

  def swing_node(doc: ProofDocument) : DefaultMutableTreeNode = {
    val node = MarkupNode.markup2default_node (this, base, doc)
    for (c <- children) node add c.swing_node(doc)
    node
  }
    
  def abs_start(doc: ProofDocument) = base.start(doc) + start
  def abs_stop(doc: ProofDocument) = base.start(doc) + stop

  var parent : MarkupNode = null
  def orphan = parent == null

  var children : List[MarkupNode] = Nil

  private def add(child : MarkupNode) {
    child parent = this
    children = (child :: children) sort ((a, b) => a.start < b.start)
  }

  private def remove(nodes : List[MarkupNode]) {
    children = children diff nodes
  }

  def dfs : List[MarkupNode] = {
    var all = Nil : List[MarkupNode]
    for (child <- children)
      all = child.dfs ::: all
    all = this :: all
    all
  }

  def leafs: List[MarkupNode] = {
    if (children == Nil) return List(this)
    else return children flatMap (_.leafs)
  }

  def flatten: List[MarkupNode] = {
    var next_x = start
    if(children.length == 0) List(this)
    else {
      val filled_gaps = for {
        child <- children
        markups = if (next_x < child.start) {
          new MarkupNode(base, next_x, child.start, id, kind, "") :: child.flatten
        } else child.flatten
        update = (next_x = child.stop)
        markup <- markups
      } yield markup
      if (next_x < stop) filled_gaps + new MarkupNode(base, next_x, stop, id, kind, "")
      else filled_gaps
    }
  }

  def insert(new_child : MarkupNode) : Unit = {
    if (new_child fitting_into this) {
      for (child <- children) {
        if (new_child fitting_into child)
          child insert new_child
      }
      if (new_child orphan) {
        // new_child did not fit into children of this
        // -> insert new_child between this and its children
        for (child <- children) {
          if (child fitting_into new_child) {
            new_child add child
          }
        }
        this add new_child
        this remove new_child.children
      }
    } else {
      System.err.println("ignored nonfitting markup " + new_child.id + new_child.kind + new_child.desc
                         + "(" +new_child.start + ", "+ new_child.stop + ")")
    }
  }

  // does this fit into node?
  def fitting_into(node : MarkupNode) = node.start <= this.start &&
    node.stop >= this.stop

  override def toString = "([" + start + " - " + stop + "] " + id + "( " + kind + "): " + desc
}
