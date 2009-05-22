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

abstract class MarkupInfo
case class RootInfo extends MarkupInfo
case class OuterInfo(highlight: String) extends MarkupInfo {override def toString = highlight}
case class HighlightInfo(highlight: String) extends MarkupInfo {override def toString = highlight}
case class TypeInfo(type_kind: String) extends MarkupInfo {override def toString = type_kind}
case class RefInfo(file: Option[String], line: Option[Int],
                   command_id: Option[String], offset: Option[Int]) extends MarkupInfo {
  override def toString = (file, line, command_id, offset).toString
}

object MarkupNode {

  def markup2default_node(node: MarkupNode, cmd: Command, doc: ProofDocument) : DefaultMutableTreeNode = {

    implicit def int2pos(offset: Int): Position =
      new Position { def getOffset = offset; override def toString = offset.toString}

    object RelativeAsset extends IAsset {
      override def getIcon : Icon = null
      override def getShortString : String = node.content
      override def getLongString : String = node.info.toString
      override def getName : String = node.id
      override def setName (name : String) = ()
      override def setStart(start : Position) = ()
      override def getStart : Position = node.abs_start(doc)
      override def setEnd(end : Position) = ()
      override def getEnd : Position = node.abs_stop(doc)
      override def toString = node.id + ": " + node.content + "[" + getStart + " - " + getEnd + "]"
    }

    new DefaultMutableTreeNode(RelativeAsset)
  }
}

class MarkupNode (val base: Command, val start: Int, val stop: Int,
                  val children: List[MarkupNode],
                  val id: String, val content: String, val info: MarkupInfo) {

  def swing_node(doc: ProofDocument) : DefaultMutableTreeNode = {
    val node = MarkupNode.markup2default_node (this, base, doc)
    children.map(node add _.swing_node(doc))
    node
  }

  def abs_start(doc: ProofDocument) = base.start(doc) + start
  def abs_stop(doc: ProofDocument) = base.start(doc) + stop

  def set_children(newchildren: List[MarkupNode]): MarkupNode =
    new MarkupNode(base, start, stop, newchildren, id, content, info)

  def add(child : MarkupNode) = set_children ((child :: children) sort ((a, b) => a.start < b.start))

  def remove(nodes : List[MarkupNode]) = set_children(children diff nodes)

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
          new MarkupNode(base, next_x, child.start, Nil, id, content, info) :: child.flatten
        } else child.flatten
        update = (next_x = child.stop)
        markup <- markups
      } yield markup
      if (next_x < stop) filled_gaps + new MarkupNode(base, next_x, stop, Nil, id, content, info)
      else filled_gaps
    }
  }

  def filter(p: (MarkupNode => Boolean)): List[MarkupNode] = {
    val filtered = children.flatMap(_.filter(p))
    if (p(this)) List(this set_children(filtered))
    else filtered
  }

  def +(new_child : MarkupNode) : MarkupNode = {
    if (new_child fitting_into this) {
      var inserted = false
      val new_children = children.map(c => if((new_child fitting_into c) && !inserted) {inserted = true; c + new_child} else c)
      if (!inserted) {
        // new_child did not fit into children of this -> insert new_child between this and its children
        val fitting = children filter(_ fitting_into new_child)
        (this remove fitting) add ((new_child /: fitting) (_ + _))
      }
      else this set_children new_children
    } else {
      error("ignored nonfitting markup " + new_child.id + new_child.content + new_child.info.toString
                         + "(" +new_child.start + ", "+ new_child.stop + ")")
    }
  }

  // does this fit into node?
  def fitting_into(node : MarkupNode) = node.start <= this.start && node.stop >= this.stop

  override def toString = "([" + start + " - " + stop + "] " + id + "( " + content + "): " + info.toString
}
