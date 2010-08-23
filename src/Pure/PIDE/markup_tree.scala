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
    type T = SortedMap[Text.Range, Entry]

    val empty = SortedMap.empty[Text.Range, Entry](new scala.math.Ordering[Text.Range]
      {
        def compare(r1: Text.Range, r2: Text.Range): Int = r1 compare r2
      })

    def update(branches: T, entry: Entry): T = branches + (entry._1.range -> entry)

    def overlapping(range: Text.Range, branches: T): T =
    {
      val start = Text.Range(range.start)
      val stop = Text.Range(range.stop)
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
    val new_range = new_info.range
    branches.get(new_range) match {
      case None =>
        new Markup_Tree(Branches.update(branches, new_info -> empty))
      case Some((info, subtree)) =>
        val range = info.range
        if (range != new_range && range.contains(new_range))
          new Markup_Tree(Branches.update(branches, info -> (subtree + new_info)))
        else if (new_range.contains(branches.head._1) && new_range.contains(branches.last._1))
          new Markup_Tree(Branches.update(Branches.empty, (new_info -> this)))
        else {
          val body = Branches.overlapping(new_range, branches)
          if (body.forall(e => new_range.contains(e._1))) {
            val rest = (Branches.empty /: branches)((rest, entry) =>
              if (body.isDefinedAt(entry._1)) rest else rest + entry)
            new Markup_Tree(Branches.update(rest, new_info -> new Markup_Tree(body)))
          }
          else { // FIXME split markup!?
            System.err.println("Ignored overlapping markup information: " + new_info)
            this
          }
        }
    }
  }

  def select[A](root_range: Text.Range)
    (result: PartialFunction[Text.Info[Any], A])(default: A): Stream[Text.Info[A]] =
  {
    def stream(parent: Text.Info[A], bs: Branches.T): Stream[Text.Info[A]] =
    {
      val range = parent.range
      val substream =
        (for ((info_range, (info, subtree)) <- Branches.overlapping(range, bs).toStream) yield {
          if (result.isDefinedAt(info)) {
            val current = Text.Info(info_range.restrict(range), result(info))
            stream(current, subtree.branches)
          }
          else stream(parent.restrict(info_range), subtree.branches)
        }).flatten

      def padding(last: Text.Offset, s: Stream[Text.Info[A]]): Stream[Text.Info[A]] =
        s match {
          case info #:: rest =>
            val Text.Range(start, stop) = info.range
            if (last < start)
              parent.restrict(Text.Range(last, start)) #:: info #:: padding(stop, rest)
            else info #:: padding(stop, rest)
          case Stream.Empty =>
            if (last < range.stop)
              Stream(parent.restrict(Text.Range(last, range.stop)))
            else Stream.Empty
        }
      if (substream.isEmpty) Stream(parent)
      else padding(range.start, substream)
    }
    stream(Text.Info(root_range, default), branches)
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

