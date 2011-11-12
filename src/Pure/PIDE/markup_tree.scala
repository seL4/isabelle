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
  type Select[A] = PartialFunction[Text.Markup, A]

  val empty: Markup_Tree = new Markup_Tree(Branches.empty)

  object Branches
  {
    type Entry = (Text.Markup, Markup_Tree)
    type T = SortedMap[Text.Range, Entry]

    val empty: T = SortedMap.empty(Text.Range.Ordering)
    def update(branches: T, entry: Entry): T = branches + (entry._1.range -> entry)
    def single(entry: Entry): T = update(empty, entry)
  }
}


class Markup_Tree private(branches: Markup_Tree.Branches.T)
{
  import Markup_Tree._

  override def toString =
    branches.toList.map(_._2) match {
      case Nil => "Empty"
      case list => list.mkString("Tree(", ",", ")")
    }

  private def overlapping(range: Text.Range): Branches.T =  // FIXME special cases!?
  {
    val start = Text.Range(range.start)
    val stop = Text.Range(range.stop)
    val bs = branches.range(start, stop)
    // FIXME check after Scala 2.8.x
    branches.get(stop) match {
      case Some(end) if range overlaps end._1.range => Branches.update(bs, end)
      case _ => bs
    }
  }

  def + (new_info: Text.Markup): Markup_Tree =
  {
    val new_range = new_info.range
    branches.get(new_range) match {
      case None =>
        new Markup_Tree(Branches.update(branches, new_info -> empty))
      case Some((info, subtree)) =>
        val range = info.range
        if (range.contains(new_range))
          new Markup_Tree(Branches.update(branches, info -> (subtree + new_info)))
        else if (new_range.contains(branches.head._1) && new_range.contains(branches.last._1))
          new Markup_Tree(Branches.single(new_info -> this))
        else {
          val body = overlapping(new_range)
          if (body.forall(e => new_range.contains(e._1))) {
            val rest = // branches -- body, modulo workarounds for Redblack in Scala 2.8.0
              if (body.size > 1)
                (Branches.empty /: branches)((rest, entry) =>
                  if (body.isDefinedAt(entry._1)) rest else rest + entry)
              else branches
            new Markup_Tree(Branches.update(rest, new_info -> new Markup_Tree(body)))
          }
          else { // FIXME split markup!?
            System.err.println("Ignored overlapping markup information: " + new_info)
            this
          }
        }
    }
  }

  def cumulate[A](root_range: Text.Range)(body: Cumulate[A]): Stream[Text.Info[A]] =
  {
    val root_info = body.info
    val result = body.result

    def stream(
      last: Text.Offset,
      stack: List[(Text.Info[A], Stream[(Text.Range, Branches.Entry)])]): Stream[Text.Info[A]] =
    {
      stack match {
        case (parent, (range, (info, tree)) #:: more) :: rest =>
          val subrange = range.restrict(root_range)
          val subtree = tree.overlapping(subrange).toStream
          val start = subrange.start

          val arg = (parent.info, info)
          if (result.isDefinedAt(arg)) {
            val next = Text.Info(subrange, result(arg))
            val nexts = stream(start, (next, subtree) :: (parent, more) :: rest)
            if (last < start) parent.restrict(Text.Range(last, start)) #:: nexts
            else nexts
          }
          else stream(last, (parent, subtree #::: more) :: rest)

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

  def select[A](root_range: Text.Range)(result: Select[A]): Stream[Text.Info[Option[A]]] =
  {
    def stream(
      last: Text.Offset,
      stack: List[(Text.Info[Option[A]], Stream[(Text.Range, Branches.Entry)])])
        : Stream[Text.Info[Option[A]]] =
    {
      stack match {
        case (parent, (range, (info, tree)) #:: more) :: rest =>
          val subrange = range.restrict(root_range)
          val subtree = tree.overlapping(subrange).toStream
          val start = subrange.start

          if (result.isDefinedAt(info)) {
            val next = Text.Info[Option[A]](subrange, Some(result(info)))
            val nexts = stream(start, (next, subtree) :: (parent, more) :: rest)
            if (last < start) parent.restrict(Text.Range(last, start)) #:: nexts
            else nexts
          }
          else stream(last, (parent, subtree #::: more) :: rest)

        case (parent, Stream.Empty) :: rest =>
          val stop = parent.range.stop
          val nexts = stream(stop, rest)
          if (last < stop) parent.restrict(Text.Range(last, stop)) #:: nexts
          else nexts

        case Nil =>
          val stop = root_range.stop
          if (last < stop) Stream(Text.Info(Text.Range(last, stop), None))
          else Stream.empty
      }
    }
    stream(root_range.start,
      List((Text.Info(root_range, None), overlapping(root_range).toStream)))
  }

  def swing_tree(parent: DefaultMutableTreeNode)
    (swing_node: Text.Markup => DefaultMutableTreeNode)
  {
    for ((_, (info, subtree)) <- branches) {
      val current = swing_node(info)
      subtree.swing_tree(current)(swing_node)
      parent.add(current)
    }
  }
}

