/*  Title:      Pure/General/linear_set.scala
    Author:     Makarius
    Author:     Fabian Immler, TU Munich

Sets with canonical linear order, or immutable linked-lists.
*/

package isabelle

import scala.collection.SetLike
import scala.collection.generic.{ImmutableSetFactory, CanBuildFrom,
  GenericSetTemplate, GenericCompanion}


object Linear_Set extends ImmutableSetFactory[Linear_Set]
{
  protected case class Rep[A](
    val start: Option[A], val end: Option[A], val nexts: Map[A, A], prevs: Map[A, A])

  private def empty_rep[A] = Rep[A](None, None, Map(), Map())

  private def make[A](start: Option[A], end: Option[A], nexts: Map[A, A], prevs: Map[A, A])
    : Linear_Set[A] = new Linear_Set[A] { override val rep = Rep(start, end, nexts, prevs) }

  implicit def canBuildFrom[A]: CanBuildFrom[Coll, A, Linear_Set[A]] = setCanBuildFrom[A]
  override def empty[A] = new Linear_Set[A]

  class Duplicate[A](x: A) extends Exception
  class Undefined[A](x: A) extends Exception
  class Next_Undefined[A](x: Option[A]) extends Exception
}


class Linear_Set[A]
  extends scala.collection.immutable.Set[A]
  with GenericSetTemplate[A, Linear_Set]
  with SetLike[A, Linear_Set[A]]
{
  override def companion: GenericCompanion[Linear_Set] = Linear_Set


  /* representation */

  protected val rep = Linear_Set.empty_rep[A]


  /* relative addressing */

  // FIXME check definedness??
  def next(elem: A): Option[A] = rep.nexts.get(elem)
  def prev(elem: A): Option[A] = rep.prevs.get(elem)

  def get_after(hook: Option[A]): Option[A] =
    hook match {
      case None => rep.start
      case Some(elem) =>
        if (!contains(elem)) throw new Linear_Set.Undefined(elem)
        next(elem)
    }

  def insert_after(hook: Option[A], elem: A): Linear_Set[A] =
    if (contains(elem)) throw new Linear_Set.Duplicate(elem)
    else
      hook match {
        case None =>
          rep.start match {
            case None => Linear_Set.make(Some(elem), Some(elem), Map(), Map())
            case Some(elem1) =>
              Linear_Set.make(Some(elem), rep.end,
                rep.nexts + (elem -> elem1), rep.prevs + (elem1 -> elem))
          }
        case Some(elem1) =>
          if (!contains(elem1)) throw new Linear_Set.Undefined(elem1)
          else
            rep.nexts.get(elem1) match {
              case None =>
                Linear_Set.make(rep.start, Some(elem),
                  rep.nexts + (elem1 -> elem), rep.prevs + (elem -> elem1))
              case Some(elem2) =>
                Linear_Set.make(rep.start, rep.end,
                  rep.nexts + (elem1 -> elem) + (elem -> elem2),
                  rep.prevs + (elem2 -> elem) + (elem -> elem1))
            }
      }

  def delete_after(hook: Option[A]): Linear_Set[A] =
    hook match {
      case None =>
        rep.start match {
          case None => throw new Linear_Set.Next_Undefined[A](None)
          case Some(elem1) =>
            rep.nexts.get(elem1) match {
              case None => empty
              case Some(elem2) =>
                Linear_Set.make(Some(elem2), rep.end, rep.nexts - elem1, rep.prevs - elem2)
            }
        }
      case Some(elem1) =>
        if (!contains(elem1)) throw new Linear_Set.Undefined(elem1)
        else
          rep.nexts.get(elem1) match {
            case None => throw new Linear_Set.Next_Undefined(Some(elem1))
            case Some(elem2) =>
              rep.nexts.get(elem2) match {
                case None =>
                  Linear_Set.make(rep.start, Some(elem1), rep.nexts - elem1, rep.prevs - elem2)
                case Some(elem3) =>
                  Linear_Set.make(rep.start, rep.end,
                    rep.nexts - elem2 + (elem1 -> elem3),
                    rep.prevs - elem2 + (elem3 -> elem1))
              }
          }
    }

  def append_after(hook: Option[A], elems: Seq[A]): Linear_Set[A] =
    ((hook, this) /: elems) {
      case ((last_elem, set), elem) => (Some(elem), set.insert_after(last_elem, elem))
    }._2

  def delete_between(from: Option[A], to: Option[A]): Linear_Set[A] =
  {
    if (isEmpty) this
    else {
      val next =
        if (from == rep.end) None
        else if (from == None) rep.start
        else from.map(rep.nexts(_))
      if (next == to) this
      else delete_after(from).delete_between(from, to)
    }
  }


  /* Set methods */

  override def stringPrefix = "Linear_Set"

  override def isEmpty: Boolean = !rep.start.isDefined
  override def size: Int = if (isEmpty) 0 else rep.nexts.size + 1

  def contains(elem: A): Boolean =
    !isEmpty && (rep.end.get == elem || rep.nexts.isDefinedAt(elem))

  private def make_iterator(from: Option[A], which: Map[A, A]): Iterator[A] = new Iterator[A] {
    private var next_elem = from
    def hasNext(): Boolean = next_elem.isDefined
    def next(): A =
      next_elem match {
        case Some(elem) =>
          next_elem = which.get(elem)
          elem
        case None => Iterator.empty.next()
      }
  }

  override def iterator: Iterator[A] = make_iterator(rep.start, rep.nexts)

  def iterator(elem: A): Iterator[A] =
    if (contains(elem)) make_iterator(Some(elem), rep.nexts)
    else throw new Linear_Set.Undefined(elem)

  def reverse_iterator(elem: A): Iterator[A] =
    if (contains(elem)) make_iterator(Some(elem), rep.prevs)
    else throw new Linear_Set.Undefined(elem)

  def + (elem: A): Linear_Set[A] = insert_after(rep.end, elem)

  def - (elem: A): Linear_Set[A] =
    if (!contains(elem)) throw new Linear_Set.Undefined(elem)
    else delete_after(prev(elem))
}