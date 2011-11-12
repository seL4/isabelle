/*  Title:      Pure/PIDE/markup_tree.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Markup trees over nested / non-overlapping text ranges.
*/

package isabelle

import java.lang.System
import javax.swing.tree.DefaultMutableTreeNode

import scala.collection.immutable.SortedMap


object Markup_Tree
{
  sealed case class Cumulate[A](info: A, result: PartialFunction[(A, Text.Markup), A])
  sealed case class Select[A](result: PartialFunction[Text.Markup, A])

  val empty: Markup_Tree = new Markup_Tree(Branches.empty)

  sealed case class Entry(range: Text.Range, rev_markup: List[XML.Tree], subtree: Markup_Tree)
  {
    def + (m: XML.Tree): Entry = copy(rev_markup = m :: rev_markup)
    def markup: List[XML.Tree] = rev_markup.reverse
  }

  object Branches
  {
    type T = SortedMap[Text.Range, Entry]
    val empty: T = SortedMap.empty(Text.Range.Ordering)
  }
}


class Markup_Tree private(branches: Markup_Tree.Branches.T)
{
  private def this(branches: Markup_Tree.Branches.T, entry: Markup_Tree.Entry) =
    this(branches + (entry.range -> entry))


  import Markup_Tree._

  override def toString =
    branches.toList.map(_._2) match {
      case Nil => "Empty"
      case list => list.mkString("Tree(", ",", ")")
    }

  private def overlapping(range: Text.Range): Branches.T =
  {
    val start = Text.Range(range.start)
    val stop = Text.Range(range.stop)
    val bs = branches.range(start, stop)
    // FIXME check after Scala 2.8.x
    branches.get(stop) match {
      case Some(end) if range overlaps end.range => bs + (end.range -> end)
      case _ => bs
    }
  }

  def + (new_markup: Text.Markup): Markup_Tree =
  {
    val new_range = new_markup.range
    val new_info = new_markup.info

    branches.get(new_range) match {
      case None =>
        new Markup_Tree(branches, Entry(new_range, List(new_info), empty))
      case Some(entry) =>
        if (entry.range == new_range)
          new Markup_Tree(branches, entry + new_info)
        else if (entry.range.contains(new_range))
          new Markup_Tree(branches, entry.copy(subtree = entry.subtree + new_markup))
        else if (new_range.contains(branches.head._1) && new_range.contains(branches.last._1))
          new Markup_Tree(Branches.empty, Entry(new_range, List(new_info), this))
        else {
          val body = overlapping(new_range)
          if (body.forall(e => new_range.contains(e._1))) {
            val rest = // branches -- body, modulo workarounds for Redblack in Scala 2.8.0 FIXME
              if (body.size > 1)
                (Branches.empty /: branches)((rest, entry) =>
                  if (body.isDefinedAt(entry._1)) rest else rest + entry)
              else branches
            new Markup_Tree(rest, Entry(new_range, List(new_info), new Markup_Tree(body)))
          }
          else { // FIXME split markup!?
            System.err.println("Ignored overlapping markup information: " + new_markup)
            this
          }
        }
    }
  }

  def cumulate[A](root_range: Text.Range)(body: Cumulate[A]): Stream[Text.Info[A]] =
  {
    val root_info = body.info

    def result(x: A, entry: Entry): Option[A] =
    {
      val (y, changed) =
        (entry.markup :\ (x, false))((info, res) =>
          {
            val (y, changed) = res
            val arg = (x, Text.Info(entry.range, info))
            if (body.result.isDefinedAt(arg)) (body.result(arg), true)
            else res
          })
      if (changed) Some(y) else None
    }

    def stream(
      last: Text.Offset,
      stack: List[(Text.Info[A], Stream[(Text.Range, Entry)])]): Stream[Text.Info[A]] =
    {
      stack match {
        case (parent, (range, entry) #:: more) :: rest =>
          val subrange = range.restrict(root_range)
          val subtree = entry.subtree.overlapping(subrange).toStream
          val start = subrange.start

          result(parent.info, entry) match {
            case Some(res) =>
              val next = Text.Info(subrange, res)
              val nexts = stream(start, (next, subtree) :: (parent, more) :: rest)
              if (last < start) parent.restrict(Text.Range(last, start)) #:: nexts
              else nexts
            case None => stream(last, (parent, subtree #::: more) :: rest)
          }

        case (parent, Stream.Empty) :: rest =>
          val stop = parent.range.stop
          val nexts = stream(stop, rest)
          if (last < stop) parent.restrict(Text.Range(last, stop)) #:: nexts
          else nexts

        case Nil =>
          val stop = root_range.stop
          if (last < stop) Stream(Text.Info(Text.Range(last, stop), root_info))
          else Stream.empty
      }
    }
    stream(root_range.start,
      List((Text.Info(root_range, root_info), overlapping(root_range).toStream)))
  }

  def swing_tree(parent: DefaultMutableTreeNode)
    (swing_node: Text.Markup => DefaultMutableTreeNode)
  {
    for ((_, entry) <- branches) {
      var current = parent
      for (info <- entry.markup) {
        val node = swing_node(Text.Info(entry.range, info))
        current.add(node)
        current = node
      }
      entry.subtree.swing_tree(current)(swing_node)
    }
  }
}

