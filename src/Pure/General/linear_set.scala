/*  Title:      Pure/General/linear_set.scala
    Author:     Makarius
    Author:     Fabian Immler, TU Munich

Sets with canonical linear order, or immutable linked-lists.
*/

package isabelle


object Linear_Set
{
  private case class Rep[A](
    val first: Option[A], val last: Option[A], val nexts: Map[A, A], prevs: Map[A, A])

  private def empty_rep[A] = Rep[A](None, None, Map(), Map())

  private def make[A](first: Option[A], last: Option[A], nexts: Map[A, A], prevs: Map[A, A])
    : Linear_Set[A] = new Linear_Set[A] { override val rep = Rep(first, last, nexts, prevs) }

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

  def next(elem: A): Option[A] = rep.nexts.get(elem)
  def prev(elem: A): Option[A] = rep.prevs.get(elem)

  def insert_after(hook: Option[A], elem: A): Linear_Set[A] =
    if (contains(elem)) throw new Linear_Set.Duplicate(elem.toString)
    else
      hook match {
        case None =>
          rep.first match {
            case None => Linear_Set.make(Some(elem), Some(elem), Map(), Map())
            case Some(elem1) =>
              Linear_Set.make(Some(elem), rep.last,
                rep.nexts + (elem -> elem1), rep.prevs + (elem1 -> elem))
          }
        case Some(elem1) =>
          if (!contains(elem1)) throw new Linear_Set.Undefined(elem1.toString)
          else
            rep.nexts.get(elem1) match {
              case None =>
                Linear_Set.make(rep.first, Some(elem),
                  rep.nexts + (elem1 -> elem), rep.prevs + (elem -> elem1))
              case Some(elem2) =>
                Linear_Set.make(rep.first, rep.last,
                  rep.nexts + (elem1 -> elem) + (elem -> elem2),
                  rep.prevs + (elem2 -> elem) + (elem -> elem1))
            }
      }

  def delete_after(hook: Option[A]): Linear_Set[A] =
    hook match {
      case None =>
        rep.first match {
          case None => throw new Linear_Set.Undefined("")
          case Some(elem1) =>
            rep.nexts.get(elem1) match {
              case None => empty
              case Some(elem2) =>
                Linear_Set.make(Some(elem2), rep.last, rep.nexts - elem1, rep.prevs - elem2)
            }
        }
      case Some(elem1) =>
        if (!contains(elem1)) throw new Linear_Set.Undefined(elem1.toString)
        else
          rep.nexts.get(elem1) match {
            case None => throw new Linear_Set.Undefined("")
            case Some(elem2) =>
              rep.nexts.get(elem2) match {
                case None =>
                  Linear_Set.make(rep.first, Some(elem1), rep.nexts - elem1, rep.prevs - elem2)
                case Some(elem3) =>
                  Linear_Set.make(rep.first, rep.last,
                    rep.nexts - elem2 + (elem1 -> elem3),
                    rep.prevs - elem2 + (elem3 -> elem1))
              }
          }
    }

  def append_after(hook: Option[A], elems: Seq[A]): Linear_Set[A] =
    (elems :\ this)((elem: A, ls: Linear_Set[A]) => ls.insert_after(hook, elem))

  def delete_between(from: Option[A], to: Option[A]): Linear_Set[A] =
  {
    if (!rep.first.isDefined) this
    else {
      val next =
        if (from == rep.last) None
        else if (from == None) rep.first
        else from.map(rep.nexts(_))
      if (next == to) this
      else delete_after(from).delete_between(from, to)
    }
  }


  /* Set methods */

  override def stringPrefix = "Linear_Set"

  def empty[B]: Linear_Set[B] = Linear_Set.empty

  override def isEmpty: Boolean = !rep.first.isDefined
  def size: Int = if (isEmpty) 0 else rep.nexts.size + 1

  def elements = new Iterator[A] {
    private var next_elem = rep.first
    def hasNext = next_elem.isDefined
    def next = {
      val elem = next_elem.get
      next_elem = if (rep.nexts.isDefinedAt(elem)) Some(rep.nexts(elem)) else None
      elem
    }
  }

  def contains(elem: A): Boolean =
    !isEmpty && (rep.last.get == elem || rep.nexts.isDefinedAt(elem))

  def + (elem: A): Linear_Set[A] = insert_after(rep.last, elem)

  override def + (elem1: A, elem2: A, elems: A*): Linear_Set[A] =
    this + elem1 + elem2 ++ elems
  override def ++ (elems: Iterable[A]): Linear_Set[A] = (this /: elems) ((s, elem) => s + elem)
  override def ++ (elems: Iterator[A]): Linear_Set[A] = (this /: elems) ((s, elem) => s + elem)

  def - (elem: A): Linear_Set[A] =
    if (!contains(elem)) throw new Linear_Set.Undefined(elem.toString)
    else delete_after(prev(elem))
}