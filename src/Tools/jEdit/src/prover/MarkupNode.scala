/*
 * Document markup nodes, with connection to Swing tree model
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover

import sidekick.IAsset
import javax.swing._
import javax.swing.text.Position
import javax.swing.tree._

object MarkupNode {

  def markup2default_node(node : MarkupNode) : DefaultMutableTreeNode = {

    class MyPos(val o : Int) extends Position {
      override def getOffset = o
    }

    implicit def int2pos(x : Int) : MyPos = new MyPos(x)

    object RelativeAsset extends IAsset{
      override def getIcon : Icon = null
      override def getShortString : String = node.short
      override def getLongString : String = node.long
      override def getName : String = node.name
      override def setName (name : String) = ()
      override def setStart(start : Position) = ()
      override def getStart : Position = node.base.start + node.start
      override def setEnd(end : Position) = ()
      override def getEnd : Position = node.base.start + node.end
      override def toString = node.name + ": " + node.short
    }

    new DefaultMutableTreeNode(RelativeAsset)
  }
}

class MarkupNode (val base : Command, val start : Int, val end : Int,
                    val name : String, val short : String, val long : String) {

  val swing_node : DefaultMutableTreeNode = MarkupNode.markup2default_node (this)

  var parent : MarkupNode = null
  def orphan = parent == null

  private var children_cell : List[MarkupNode] = Nil
  //track changes in swing_node
  def children = children_cell
  def children_= (cs : List[MarkupNode]) = {
    swing_node.removeAllChildren
    for(c <- cs) swing_node add c.swing_node
    children_cell = cs
  }
  
  private def add(child : MarkupNode) {
    child parent = this
    children_cell = (child :: children) sort ((a, b) => a.start < b.end)

    swing_node add child.swing_node
  }

  private def remove(nodes : List[MarkupNode]) {
    children_cell = children diff nodes

      for(node <- nodes) try {
        swing_node remove node.swing_node
      } catch { case e : IllegalArgumentException =>
        System.err.println(e.toString)
        case e => throw e
      }
  }

  def dfs : List[MarkupNode] = {
    var all = Nil : List[MarkupNode]
    for(child <- children)
      all = child.dfs ::: all
    all = this :: all
    all
  }

  def insert(new_child : MarkupNode) : Unit = {
    if(new_child fitting_into this){
      for(child <- children){
        if(new_child fitting_into child)
          child insert new_child
      }
      if(new_child orphan){
        // new_child did not fit into children of this
        // -> insert new_child between this and its children
        for(child <- children){
          if(child fitting_into new_child) {
            new_child add child
          }
        }
        this add new_child
        this remove new_child.children
      }
    } else {
      System.err.println("ignored nonfitting markup " + new_child.name + new_child.short + new_child.long
                         + "(" +new_child.start + ", "+ new_child.end + ")")
    }
  }

  // does this fit into node?
  def fitting_into(node : MarkupNode) = node.start <= this.start &&
    node.end >= this.end
  
}
