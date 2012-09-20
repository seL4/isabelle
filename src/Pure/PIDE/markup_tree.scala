/*  Title:      Pure/PIDE/markup_tree.scala
    Module:     PIDE
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Markup trees over nested / non-overlapping text ranges.
*/

package isabelle

import java.lang.System
import javax.swing.tree.DefaultMutableTreeNode

import scala.collection.immutable.SortedMap
import scala.annotation.tailrec


object Markup_Tree
{
  val empty: Markup_Tree = new Markup_Tree(Branches.empty)

  def merge_disjoint(trees: List[Markup_Tree]): Markup_Tree =
    trees match {
      case Nil => empty
      case head :: tail =>
        new Markup_Tree(
          (head.branches /: tail) {
            case (branches, tree) =>
              (branches /: tree.branches) {
                case (bs, (r, entry)) =>
                  require(!bs.isDefinedAt(r))
                  bs + (r -> entry)
              }
          })
    }

  object Entry
  {
    def apply(markup: Text.Markup, subtree: Markup_Tree): Entry =
      Entry(markup.range, List(markup.info), Set(markup.info.markup.name), subtree)

    def apply(range: Text.Range, rev_markups: List[XML.Elem], subtree: Markup_Tree): Entry =
      Entry(range, rev_markups, Set.empty ++ rev_markups.iterator.map(_.markup.name), subtree)
  }

  sealed case class Entry(
    range: Text.Range,
    rev_markup: List[XML.Elem],
    elements: Set[String],
    subtree: Markup_Tree)
  {
    def + (info: XML.Elem): Entry =
      if (elements(info.markup.name)) copy(rev_markup = info :: rev_markup)
      else copy(rev_markup = info :: rev_markup, elements = elements + info.markup.name)

    def markup: List[XML.Elem] = rev_markup.reverse
  }

  object Branches
  {
    type T = SortedMap[Text.Range, Entry]
    val empty: T = SortedMap.empty(Text.Range.Ordering)
  }


  /* XML representation */

  @tailrec private def strip_elems(markups: List[Markup], body: XML.Body): (List[Markup], XML.Body) =
    body match {
      case List(XML.Elem(markup1, body1)) => strip_elems(markup1 :: markups, body1)
      case _ => (markups, body)
    }

  private def make_trees(acc: (Int, List[Markup_Tree]), tree: XML.Tree): (Int, List[Markup_Tree]) =
    {
      val (offset, markup_trees) = acc

      strip_elems(Nil, List(tree)) match {
        case (Nil, body) =>
          (offset + XML.text_length(body), markup_trees)

        case (elems, body) =>
          val (end_offset, subtrees) = ((offset, Nil: List[Markup_Tree]) /: body)(make_trees)
          val range = Text.Range(offset, end_offset)
          val entry = Entry(range, elems.map(XML.Elem(_, Nil)), merge_disjoint(subtrees))
          (end_offset, new Markup_Tree(Branches.empty, entry) :: markup_trees)
      }
    }

  def from_XML(body: XML.Body): Markup_Tree =
    merge_disjoint(((0, Nil: List[Markup_Tree]) /: body)(make_trees)._2)
}


final class Markup_Tree private(private val branches: Markup_Tree.Branches.T)
{
  import Markup_Tree._

  private def this(branches: Markup_Tree.Branches.T, entry: Markup_Tree.Entry) =
    this(branches + (entry.range -> entry))

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

    branches.get(new_range) match {
      case None => new Markup_Tree(branches, Entry(new_markup, empty))
      case Some(entry) =>
        if (entry.range == new_range)
          new Markup_Tree(branches, entry + new_markup.info)
        else if (entry.range.contains(new_range))
          new Markup_Tree(branches, entry.copy(subtree = entry.subtree + new_markup))
        else if (new_range.contains(branches.head._1) && new_range.contains(branches.last._1))
          new Markup_Tree(Branches.empty, Entry(new_markup, this))
        else {
          val body = overlapping(new_range)
          if (body.forall(e => new_range.contains(e._1))) {
            val rest = // branches -- body, modulo workarounds for Redblack in Scala 2.8.0 FIXME
              if (body.size > 1)
                (Branches.empty /: branches)((rest, entry) =>
                  if (body.isDefinedAt(entry._1)) rest else rest + entry)
              else branches
            new Markup_Tree(rest, Entry(new_markup, new Markup_Tree(body)))
          }
          else { // FIXME split markup!?
            System.err.println("Ignored overlapping markup information: " + new_markup +
              body.filter(e => !new_range.contains(e._1)).mkString("\n"))
            this
          }
        }
    }
  }

  def cumulate[A](root_range: Text.Range, root_info: A, result_elements: Option[Set[String]],
    result: PartialFunction[(A, Text.Markup), A]): Stream[Text.Info[A]] =
  {
    def results(x: A, entry: Entry): Option[A] =
      if (result_elements match { case Some(es) => es.exists(entry.elements) case None => true }) {
        val (y, changed) =
          (entry.markup :\ (x, false))((info, res) =>
            {
              val (y, changed) = res
              val arg = (y, Text.Info(entry.range, info))
              if (result.isDefinedAt(arg)) (result(arg), true)
              else res
            })
        if (changed) Some(y) else None
      }
      else None

    def stream(
      last: Text.Offset,
      stack: List[(Text.Info[A], Stream[(Text.Range, Entry)])]): Stream[Text.Info[A]] =
    {
      stack match {
        case (parent, (range, entry) #:: more) :: rest =>
          val subrange = range.restrict(root_range)
          val subtree = entry.subtree.overlapping(subrange).toStream
          val start = subrange.start

          results(parent.info, entry) match {
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

  def swing_tree(parent: DefaultMutableTreeNode,
    swing_node: Text.Info[List[XML.Elem]] => DefaultMutableTreeNode)
  {
    for ((_, entry) <- branches) {
      val node = swing_node(Text.Info(entry.range, entry.markup))
      entry.subtree.swing_tree(node, swing_node)
      parent.add(node)
    }
  }
}

