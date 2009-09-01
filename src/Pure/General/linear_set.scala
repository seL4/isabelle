/*  Title:      Pure/General/linear_set.scala
    Author:     Makarius
    Author:     Fabian Immler TU Munich

Sets with canonical linear order, or immutable linked-lists.
*/
package isabelle


object Linear_Set
{
  private case class Rep[A](
    val first_elem: Option[A], val last_elem: Option[A], val body: Map[A, A])

  private def empty_rep[A] = Rep[A](None, None, Map())

  private def make[A](first_elem: Option[A], last_elem: Option[A], body: Map[A, A]): Linear_Set[A] =
    new Linear_Set[A] { override val rep = Rep(first_elem, last_elem, body) }


  def empty[A]: Linear_Set[A] = new Linear_Set
  def apply[A](elems: A*): Linear_Set[A] = empty[A] ++ elems

  class Duplicate(s: String) extends Exception(s)
  class Undefined(s: String) extends Exception(s)
}


class Linear_Set[A] extends scala.collection.immutable.Set[A]
{
  /* representation */

  protected val rep = Linear_Set.empty_rep[A]


  /* auxiliary operations */

  def next(elem: A) = rep.body.get(elem)
  def prev(elem: A) = rep.body.find(_._2 == elem).map(_._1)   // slow

  private def _insert_after(hook: Option[A], elem: A): Linear_Set[A] =
    if (contains(elem)) throw new Linear_Set.Duplicate(elem.toString)
    else hook match {
      case Some(hook) =>
        if (!contains(hook)) throw new Linear_Set.Undefined(hook.toString)
        else if (rep.body.isDefinedAt(hook))
          Linear_Set.make(rep.first_elem, rep.last_elem,
            rep.body - hook + (hook -> elem) + (elem -> rep.body(hook)))
        else Linear_Set.make(rep.first_elem, Some(elem), rep.body + (hook -> elem))
      case None =>
        if (isEmpty) Linear_Set.make(Some(elem), Some(elem), Map())
        else Linear_Set.make(Some(elem), rep.last_elem, rep.body + (elem -> rep.first_elem.get))
    }

  def insert_after(hook: Option[A], elems: Seq[A]): Linear_Set[A] =
    elems.reverse.foldLeft (this) ((ls, elem) => ls._insert_after(hook, elem))

  def delete_after(elem: Option[A]): Linear_Set[A] =
    elem match {
      case Some(elem) =>
        if (!contains(elem)) throw new Linear_Set.Undefined(elem.toString)
        else if (!rep.body.isDefinedAt(elem)) throw new Linear_Set.Undefined(null)
        else if (rep.body(elem) == rep.last_elem.get)
          Linear_Set.make(rep.first_elem, Some(elem), rep.body - elem)
        else Linear_Set.make(rep.first_elem, rep.last_elem,
          rep.body - elem - rep.body(elem) + (elem -> rep.body(rep.body(elem))))
      case None =>
        if (isEmpty) throw new Linear_Set.Undefined(null)
        else if (size == 1) empty
        else Linear_Set.make(Some(rep.body(rep.first_elem.get)), rep.last_elem, rep.body - rep.first_elem.get)
    }

  def delete_between(from: Option[A], to: Option[A]): Linear_Set[A] = {
    if(!rep.first_elem.isDefined) this
    else {
      val next =
        if (from == rep.last_elem) None
        else if (from == None) rep.first_elem
        else from.map(rep.body(_))
      if (next == to) this
      else delete_after(from).delete_between(from, to)
    }
  }


  /* Set methods */

  override def stringPrefix = "Linear_Set"

  def empty[B]: Linear_Set[B] = Linear_Set.empty

  override def isEmpty: Boolean = !rep.last_elem.isDefined
  def size: Int = if (isEmpty) 0 else rep.body.size + 1

  def elements = new Iterator[A] {
    private var next_elem = rep.first_elem
    def hasNext = next_elem.isDefined
    def next = {
      val elem = next_elem.get
      next_elem = if (rep.body.isDefinedAt(elem)) Some(rep.body(elem)) else None
      elem
    }
  }

  def contains(elem: A): Boolean =
    !isEmpty && (rep.last_elem.get == elem || rep.body.isDefinedAt(elem))

  def + (elem: A): Linear_Set[A] = _insert_after(rep.last_elem, elem)

  override def + (elem1: A, elem2: A, elems: A*): Linear_Set[A] =
    this + elem1 + elem2 ++ elems
  override def ++ (elems: Iterable[A]): Linear_Set[A] = (this /: elems) ((s, elem) => s + elem)
  override def ++ (elems: Iterator[A]): Linear_Set[A] = (this /: elems) ((s, elem) => s + elem)

  def - (elem: A): Linear_Set[A] =
    if (!contains(elem)) throw new Linear_Set.Undefined(elem.toString)
    else delete_after(prev(elem))
}