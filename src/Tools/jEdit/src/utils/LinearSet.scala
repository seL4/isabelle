/*  Title:      LinearSet.scala
    Author:     Makarius

Sets with canonical linear order, or immutable linked-lists.
*/
package isabelle.utils

object LinearSet
{
  def empty[A]: LinearSet[A] = new LinearSet[A]
  def apply[A](elems: A*): LinearSet[A] =
    (empty[A] /: elems) ((s, elem) => s + elem)

  class Duplicate(s: String) extends Exception(s)
  class Undefined(s: String) extends Exception(s)

  private def make[A](first: Option[A], last: Option[A], b: Map[A, A]): LinearSet[A] =
    new LinearSet[A] {
      override val first_elem = first
      override val last_elem = last
      override val body = b
    }
}

class LinearSet[A] extends scala.collection.immutable.Set[A]
{
  /* representation */

  val first_elem: Option[A] = None
  val last_elem: Option[A] = None
  val body: Map[A, A] = Map.empty


  /* basic methods */

  def next(elem: A) = body.get(elem)
  
  override def isEmpty: Boolean = !last_elem.isDefined
  def size: Int = if (isEmpty) 0 else body.size + 1

  def empty[B] = LinearSet.empty[B]

  def contains(elem: A): Boolean =
    !isEmpty && (last_elem.get == elem || body.isDefinedAt(elem))

  def insert_after(hook: Option[A], elem: A): LinearSet[A] =
    if (contains(elem)) throw new LinearSet.Duplicate(elem.toString)
    else hook match {
      case Some(hook) =>
        if (!contains(hook)) throw new LinearSet.Undefined(hook.toString)
        else if (body.isDefinedAt(hook))
          LinearSet.make(first_elem, last_elem, body - hook + (hook -> elem) + (elem -> body(hook)))
        else LinearSet.make(first_elem, Some(elem), body + (hook -> elem))
      case None =>
        if (isEmpty) LinearSet.make(Some(elem), Some(elem), Map.empty)
        else LinearSet.make(Some(elem), last_elem, body + (elem -> first_elem.get))
    }
    
  def +(elem: A): LinearSet[A] = insert_after(last_elem, elem)

  def delete_after(elem: Option[A]): LinearSet[A] =
    elem match {
      case Some(elem) =>
        if (!contains(elem)) throw new LinearSet.Undefined(elem.toString)
        else if (!body.isDefinedAt(elem)) throw new LinearSet.Undefined(null)
        else if (body(elem) == last_elem.get) LinearSet.make(first_elem, Some(elem), body - elem)
        else LinearSet.make(first_elem, last_elem, body - elem - body(elem) + (elem -> body(body(elem))))
      case None =>
        if (isEmpty) throw new LinearSet.Undefined(null)
        else if (size == 1) empty
        else LinearSet.make(Some(body(first_elem.get)), last_elem, body - first_elem.get)
    }
    
  def -(elem: A): LinearSet[A] =
    if (!contains(elem)) throw new LinearSet.Undefined(elem.toString)
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