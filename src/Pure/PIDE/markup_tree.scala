/*  Title:      Pure/PIDE/markup_tree.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Markup trees over nested / non-overlapping text ranges.
*/

package isabelle


import javax.swing.tree.DefaultMutableTreeNode

import scala.collection.immutable.SortedMap
import scala.collection.mutable
import scala.annotation.tailrec


object Markup_Tree
{
  /* branches sorted by quasi-order -- overlapping ranges appear as equivalent */

  object Branches
  {
    type Entry = (Text.Info[Any], Markup_Tree)
    type T = SortedMap[Text.Info[Any], Entry]

    val empty = SortedMap.empty[Text.Info[Any], Entry](new scala.math.Ordering[Text.Info[Any]]
      {
        def compare(x: Text.Info[Any], y: Text.Info[Any]): Int = x.range compare y.range
      })

    def update(branches: T, entry: Entry): T = branches + (entry._1 -> entry)

    def overlapping(range: Text.Range, branches: T): T =
    {
      val start = Text.Info[Any](Text.Range(range.start), Nil)
      val stop = Text.Info[Any](Text.Range(range.stop), Nil)
      branches.get(stop) match {
        case Some(end) if range overlaps end._1.range =>
          update(branches.range(start, stop), end)
        case _ => branches.range(start, stop)
      }
    }
  }

  val empty = new Markup_Tree(Branches.empty)
}


case class Markup_Tree(val branches: Markup_Tree.Branches.T)
{
  import Markup_Tree._

  override def toString =
    branches.toList.map(_._2) match {
      case Nil => "Empty"
      case list => list.mkString("Tree(", ",", ")")
    }

  def + (new_info: Text.Info[Any]): Markup_Tree =
  {
    branches.get(new_info) match {
      case None =>
        new Markup_Tree(Branches.update(branches, new_info -> empty))
      case Some((info, subtree)) =>
        if (info.range != new_info.range && info.contains(new_info))
          new Markup_Tree(Branches.update(branches, info -> (subtree + new_info)))
        else if (new_info.contains(branches.head._1) && new_info.contains(branches.last._1))
          new Markup_Tree(Branches.update(Branches.empty, (new_info -> this)))
        else {
          val body = Branches.overlapping(new_info.range, branches)
          if (body.forall(e => new_info.contains(e._1))) {
            val rest = (branches /: body) { case (bs, (e, _)) => bs - e }
            new Markup_Tree(Branches.update(rest, new_info -> new Markup_Tree(body)))
          }
          else { // FIXME split markup!?
            System.err.println("Ignored overlapping markup information: " + new_info)
            this
          }
        }
    }
  }

  def select[A](root: Text.Info[A])(sel: PartialFunction[Text.Info[Any], A]): Stream[Text.Info[A]] =
  {
    def stream(parent: Text.Info[A], bs: Branches.T): Stream[Text.Info[A]] =
    {
      val substream =
        (for ((_, (info, subtree)) <- Branches.overlapping(parent.range, bs).toStream) yield {
          if (sel.isDefinedAt(info)) {
            val current = Text.Info(info.range.restrict(parent.range), sel(info))
            stream(current, subtree.branches)
          }
          else stream(parent.restrict(info.range), subtree.branches)
        }).flatten

      def padding(last: Text.Offset, s: Stream[Text.Info[A]]): Stream[Text.Info[A]] =
        s match {
          case info #:: rest =>
            val Text.Range(start, stop) = info.range
            if (last < start)
              parent.restrict(Text.Range(last, start)) #:: info #:: padding(stop, rest)
            else info #:: padding(stop, rest)
          case Stream.Empty =>
            if (last < parent.range.stop)
              Stream(parent.restrict(Text.Range(last, parent.range.stop)))
            else Stream.Empty
        }
      if (substream.isEmpty) Stream(parent)
      else padding(parent.range.start, substream)
    }
    stream(root, branches)
  }

  def swing_tree(parent: DefaultMutableTreeNode)
    (swing_node: Text.Info[Any] => DefaultMutableTreeNode)
  {
    for ((_, (info, subtree)) <- branches) {
      val current = swing_node(info)
      subtree.swing_tree(current)(swing_node)
      parent.add(current)
    }
  }
}

