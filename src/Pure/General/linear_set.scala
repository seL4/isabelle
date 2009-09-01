/*  Title:      Pure/General/linear_set.scala
    Author:     Makarius

Sets with canonical linear order, or immutable linked-lists.
*/
package isabelle


object Linear_Set
{
  def empty[A]: Linear_Set[A] = new Linear_Set[A]
  def apply[A](elems: A*): Linear_Set[A] =
    (empty[A] /: elems) ((s, elem) => s + elem)

  class Duplicate(s: String) extends Exception(s)
  class Undefined(s: String) extends Exception(s)

  private def make[A](first: Option[A], last: Option[A], b: Map[A, A]): Linear_Set[A] =
    new Linear_Set[A] {
      override val first_elem = first
      override val last_elem = last
      override val body = b
    }
}


class Linear_Set[A] extends scala.collection.immutable.Set[A]
{
  /* representation */

  val first_elem: Option[A] = None
  val last_elem: Option[A] = None
  val body: Map[A, A] = Map.empty


  /* basic methods */

  def next(elem: A) = body.get(elem)
  def prev(elem: A) = body.find(_._2 == elem).map(_._1)
  override def isEmpty: Boolean = !last_elem.isDefined
  def size: Int = if (isEmpty) 0 else body.size + 1

  def empty[B] = Linear_Set.empty[B]

  def contains(elem: A): Boolean =
    !isEmpty && (last_elem.get == elem || body.isDefinedAt(elem))

  private def _insert_after(hook: Option[A], elem: A): Linear_Set[A] =
    if (contains(elem)) throw new Linear_Set.Duplicate(elem.toString)
    else hook match {
      case Some(hook) =>
        if (!contains(hook)) throw new Linear_Set.Undefined(hook.toString)
        else if (body.isDefinedAt(hook))
          Linear_Set.make(first_elem, last_elem, body - hook + (hook -> elem) + (elem -> body(hook)))
        else Linear_Set.make(first_elem, Some(elem), body + (hook -> elem))
      case None =>
        if (isEmpty) Linear_Set.make(Some(elem), Some(elem), Map.empty)
        else Linear_Set.make(Some(elem), last_elem, body + (elem -> first_elem.get))
    }

  def insert_after(hook: Option[A], elems: Seq[A]): Linear_Set[A] =
    elems.reverse.foldLeft (this) ((ls, elem) => ls._insert_after(hook, elem))

  def +(elem: A): Linear_Set[A] = _insert_after(last_elem, elem)

  def delete_after(elem: Option[A]): Linear_Set[A] =
    elem match {
      case Some(elem) =>
        if (!contains(elem)) throw new Linear_Set.Undefined(elem.toString)
        else if (!body.isDefinedAt(elem)) throw new Linear_Set.Undefined(null)
        else if (body(elem) == last_elem.get) Linear_Set.make(first_elem, Some(elem), body - elem)
        else Linear_Set.make(first_elem, last_elem, body - elem - body(elem) + (elem -> body(body(elem))))
      case None =>
        if (isEmpty) throw new Linear_Set.Undefined(null)
        else if (size == 1) empty
        else Linear_Set.make(Some(body(first_elem.get)), last_elem, body - first_elem.get)
    }

  def delete_between(from: Option[A], to: Option[A]): Linear_Set[A] = {
    if(!first_elem.isDefined) this
    else {
      val next = if (from == last_elem) None
                 else if (from == None) first_elem
                 else from.map(body(_))
      if (next == to) this
      else delete_after(from).delete_between(from, to)
    }
  }

  def -(elem: A): Linear_Set[A] =
    if (!contains(elem)) throw new Linear_Set.Undefined(elem.toString)
    else delete_after(body find (p => p._2 == elem) map (p => p._1))

  def elements = new Iterator[A] {
    private var next_elem = first_elem
    def hasNext = next_elem.isDefined
    def next = {
      val elem = next_elem.get
      next_elem = if (body.isDefinedAt(elem)) Some(body(elem)) else None
      elem
    }
  }
}