/*
 * RelativeAsset.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package isabelle.prover

import sidekick.IAsset
import javax.swing._
import javax.swing.text.Position
import javax.swing.tree._

class MarkupNode (base : Command, val rel_start : Int, val rel_end : Int,
                    val name : String, val short : String, val long : String)
      extends DefaultMutableTreeNode{

  private class MyPos(val o : Int) extends Position {
    override def getOffset = o
  }

  private def pos(x : Int) : MyPos = new MyPos(x)

  private object RelativeAsset extends IAsset{
    override def getIcon : Icon = null
    override def getShortString : String = short
    override def getLongString : String = long
    override def getName : String = name
    override def setName (name : String) = ()
    override def setStart(start : Position) = ()
    override def getStart : Position = pos(base.start + rel_start)
    override def setEnd(end : Position) = ()
    override def getEnd : Position = pos(base.start + rel_end)
    override def toString = name + ": " + short
  }

  super.setUserObject(RelativeAsset)

  override def add(new_child : MutableTreeNode) = {
    if(new_child.isInstanceOf[MarkupNode]){
      val new_node = new_child.asInstanceOf[MarkupNode]
      if(!equals(new_node) && fitting(new_node)){
        val cs = children()
        while (cs.hasMoreElements){
          val child = cs.nextElement.asInstanceOf[MarkupNode]
          if(child.fitting(new_node)) {
            child.add(new_node)
          }
        }
        if(new_node.getParent == null){
          val cs = children()
          while(cs.hasMoreElements){
            val child = cs.nextElement.asInstanceOf[MarkupNode]
            if(new_node.fitting(child)) {
              remove(child)
              new_node.add(child)
            }
          }
          super.add(new_node)
        }
      } else {
        System.err.println("ignored nonfitting markup " + new_node.name + new_node.short + new_node.long
                           + "(" +new_node.rel_start + ", "+ new_node.rel_end + ")")
      }
    } else {
      super.add(new_child)
    }
  }

  // does node fit into this?
  def fitting(node : MarkupNode) : boolean = {
    return node.rel_start >= this.rel_start && node.rel_end <= this.rel_end
  }
  
}
