/*  Title:      linear_set.scala
    Author:     Makarius

Sets with canonical linear order, or immutable linked-lists.
*/

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

  override def isEmpty: Boolean = !last_elem.isDefined
  def size: Int = if (isEmpty) 0 else body.size + 1

  def empty[B] = LinearSet.empty[B]

  def contains(elem: A): Boolean =
    !isEmpty && (last_elem.get == elem || body.isDefinedAt(elem))

  def +(elem: A): LinearSet[A] =
    if (contains(elem)) throw new LinearSet.Duplicate(elem.toString)
    else if (isEmpty) LinearSet.make(Some(elem), Some(elem), Map.empty)
    else LinearSet.make(first_elem, Some(elem), body + (last_elem.get -> elem))

  def -(elem: A): LinearSet[A] =
    if (!contains(elem)) throw new LinearSet.Undefined(elem.toString)
    else error("FIXME")

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