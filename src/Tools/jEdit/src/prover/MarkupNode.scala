/*
 * Document markup nodes, with connection to Swing tree model
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover


import javax.swing.tree.DefaultMutableTreeNode

import isabelle.proofdocument.ProofDocument


class MarkupNode(val start: Int, val stop: Int, val content: String, val info: Any,
  val children: List[MarkupNode])
{

  def swing_tree(make_node: MarkupNode => DefaultMutableTreeNode): DefaultMutableTreeNode =
  {
    val node = make_node(this)
    children.foreach(node add _.swing_tree(make_node))
    node
  }

  def set_children(new_children: List[MarkupNode]): MarkupNode =
    new MarkupNode(start, stop, content, info, new_children)

  private def add(child: MarkupNode) =   // FIXME avoid sort?
    set_children ((child :: children) sort ((a, b) => a.start < b.start))

  def remove(nodes: List[MarkupNode]) = set_children(children -- nodes)

  def fits_into(node: MarkupNode): Boolean =
    node.start <= this.start && this.stop <= node.stop

  def + (new_child: MarkupNode): MarkupNode =
  {
    if (new_child fits_into this) {
      var inserted = false
      val new_children =
        children.map(c =>
          if ((new_child fits_into c) && !inserted) {inserted = true; c + new_child}
          else c)
      if (!inserted) {
        // new_child did not fit into children of this
        // -> insert new_child between this and its children
        val fitting = children filter(_ fits_into new_child)
        (this remove fitting) add ((new_child /: fitting) (_ + _))
      }
      else this set_children new_children
    }
    else {
      System.err.println("ignored nonfitting markup: " + new_child)
      this
    }
  }

  def flatten: List[MarkupNode] = {
    var next_x = start
    if (children.isEmpty) List(this)
    else {
      val filled_gaps = for {
        child <- children
        markups =
          if (next_x < child.start) {
            // FIXME proper content!?
            new MarkupNode(next_x, child.start, content, info, Nil) :: child.flatten
          }
          else child.flatten
        update = (next_x = child.stop)
        markup <- markups
      } yield markup
      if (next_x < stop)
        filled_gaps + new MarkupNode(next_x, stop, content, info, Nil) // FIXME proper content!?
      else filled_gaps
    }
  }

  def filter(p: MarkupNode => Boolean): List[MarkupNode] =
  {
    val filtered = children.flatMap(_.filter(p))
    if (p(this)) List(this set_children(filtered))
    else filtered
  }

  override def toString =
    "([" + start + " - " + stop + "] ( " + content + "): " + info.toString
}
