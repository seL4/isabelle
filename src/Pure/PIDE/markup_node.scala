/*  Title:      Pure/PIDE/markup_node.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Text markup nodes.
*/

package isabelle


import javax.swing.tree.DefaultMutableTreeNode



case class Markup_Node(val range: Text.Range, val info: Any)

case class Markup_Tree(val node: Markup_Node, val branches: List[Markup_Tree])
{
  private def add(branch: Markup_Tree) =   // FIXME avoid sort
    copy(branches = (branch :: branches).sortWith((a, b) => a.node.range.start < b.node.range.start))

  private def remove(bs: List[Markup_Tree]) =
    copy(branches = branches.filterNot(bs.contains(_)))

  def + (new_tree: Markup_Tree): Markup_Tree =
  {
    val new_node = new_tree.node
    if (node.range contains new_node.range) {
      var inserted = false
      val new_branches =
        branches.map(branch =>
          if ((branch.node.range contains new_node.range) && !inserted) {
            inserted = true
            branch + new_tree
          }
          else branch)
      if (!inserted) {
        // new_tree did not fit into children of this
        // -> insert between this and its branches
        val fitting = branches filter(new_node.range contains _.node.range)
        (this remove fitting) add ((new_tree /: fitting)(_ + _))
      }
      else copy(branches = new_branches)
    }
    else {
      System.err.println("Ignored nonfitting markup: " + new_node)
      this
    }
  }

  def flatten: List[Markup_Node] =
  {
    var next_x = node.range.start
    if (branches.isEmpty) List(this.node)
    else {
      val filled_gaps =
        for {
          child <- branches
          markups =
            if (next_x < child.node.range.start)
              new Markup_Node(Text.Range(next_x, child.node.range.start), node.info) :: child.flatten
            else child.flatten
          update = (next_x = child.node.range.stop)
          markup <- markups
        } yield markup
      if (next_x < node.range.stop)
        filled_gaps ::: List(new Markup_Node(Text.Range(next_x, node.range.stop), node.info))
      else filled_gaps
    }
  }
}


case class Markup_Text(val markup: List[Markup_Tree], val content: String)
{
  private val root = new Markup_Tree(new Markup_Node(Text.Range(0, content.length), None), markup)  // FIXME !?

  def + (new_tree: Markup_Tree): Markup_Text =
    new Markup_Text((root + new_tree).branches, content)

  def filter(pred: Markup_Node => Boolean): Markup_Text =
  {
    def filt(tree: Markup_Tree): List[Markup_Tree] =
    {
      val branches = tree.branches.flatMap(filt(_))
      if (pred(tree.node)) List(tree.copy(branches = branches))
      else branches
    }
    new Markup_Text(markup.flatMap(filt(_)), content)
  }

  def flatten: List[Markup_Node] = markup.flatMap(_.flatten)

  def swing_tree(swing_node: Markup_Node => DefaultMutableTreeNode): DefaultMutableTreeNode =
  {
    def swing(tree: Markup_Tree): DefaultMutableTreeNode =
    {
      val node = swing_node(tree.node)
      tree.branches foreach ((branch: Markup_Tree) => node.add(swing(branch)))
      node
    }
    swing(root)
  }
}
