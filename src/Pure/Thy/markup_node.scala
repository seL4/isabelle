/*
 * Document markup nodes, with connection to Swing tree model
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle


import javax.swing.tree.DefaultMutableTreeNode



class Markup_Node(val start: Int, val stop: Int, val info: Any)
{
  def fits_into(that: Markup_Node): Boolean =
    that.start <= this.start && this.stop <= that.stop
}


class Markup_Tree(val node: Markup_Node, val branches: List[Markup_Tree])
{
  def set_branches(bs: List[Markup_Tree]): Markup_Tree = new Markup_Tree(node, bs)

  private def add(branch: Markup_Tree) =   // FIXME avoid sort
    set_branches((branch :: branches) sort ((a, b) => a.node.start < b.node.start))

  private def remove(bs: List[Markup_Tree]) = set_branches(branches -- bs)

  def + (new_tree: Markup_Tree): Markup_Tree =
  {
    val new_node = new_tree.node
    if (new_node fits_into node) {
      var inserted = false
      val new_branches =
        branches.map(branch =>
          if ((new_node fits_into branch.node) && !inserted) {
            inserted = true
            branch + new_tree
          }
          else branch)
      if (!inserted) {
        // new_tree did not fit into children of this
        // -> insert between this and its branches
        val fitting = branches filter(_.node fits_into new_node)
        (this remove fitting) add ((new_tree /: fitting)(_ + _))
      }
      else set_branches(new_branches)
    }
    else {
      System.err.println("ignored nonfitting markup: " + new_node)
      this
    }
  }

  def flatten: List[Markup_Node] =
  {
    var next_x = node.start
    if (branches.isEmpty) List(this.node)
    else {
      val filled_gaps =
        for {
          child <- branches
          markups =
            if (next_x < child.node.start)
              new Markup_Node(next_x, child.node.start, node.info) :: child.flatten
            else child.flatten
          update = (next_x = child.node.stop)
          markup <- markups
        } yield markup
      if (next_x < node.stop)
        filled_gaps + new Markup_Node(next_x, node.stop, node.info)
      else filled_gaps
    }
  }
}


class Markup_Text(val markup: List[Markup_Tree], val content: String)
{
  private lazy val root =
    new Markup_Tree(new Markup_Node(0, content.length, None), markup)

  def + (new_tree: Markup_Tree): Markup_Text =
    new Markup_Text((root + new_tree).branches, content)

  def filter(pred: Markup_Node => Boolean): Markup_Text =
  {
    def filt(tree: Markup_Tree): List[Markup_Tree] =
    {
      val branches = tree.branches.flatMap(filt(_))
      if (pred(tree.node)) List(tree.set_branches(branches))
      else branches
    }
    new Markup_Text(markup.flatMap(filt(_)), content)
  }

  def flatten: List[Markup_Node] = markup.flatten(_.flatten)

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
