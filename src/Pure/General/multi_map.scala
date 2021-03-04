/*  Title:      Pure/General/multi_map.scala
    Author:     Makarius

Maps with multiple entries per key.
*/

package isabelle

import scala.collection.mutable
import scala.collection.{IterableFactory, MapFactory, MapFactoryDefaults}
import scala.collection.immutable.{Iterable, MapOps}


object Multi_Map extends MapFactory[Multi_Map]
{
  private val empty_val: Multi_Map[Any, Nothing] = new Multi_Map[Any, Nothing](Map.empty)
  def empty[A, B]: Multi_Map[A, B] = empty_val.asInstanceOf[Multi_Map[A, B]]

  def from[A, B](entries: IterableOnce[(A, B)]): Multi_Map[A, B] =
    entries.foldLeft(empty[A, B]) { case (m, (a, b)) => m.insert(a, b) }

  override def newBuilder[A, B]: mutable.Builder[(A, B), Multi_Map[A, B]] = new Builder[A, B]
  private class Builder[A, B] extends mutable.Builder[(A, B), Multi_Map[A, B]]
  {
    private var res = empty[A, B]
    override def clear(): Unit = { res = empty[A, B] }
    override def addOne(p: (A, B)): this.type = { res = res.insert(p._1, p._2); this }
    override def result(): Multi_Map[A, B] = res
  }
}

final class Multi_Map[A, +B] private(protected val rep: Map[A, List[B]])
  extends Iterable[(A, B)]
    with MapOps[A, B, Multi_Map, Multi_Map[A, B]]
    with MapFactoryDefaults[A, B, Multi_Map, Iterable]
{
  /* Multi_Map operations */

  def iterator_list: Iterator[(A, List[B])] = rep.iterator

  def get_list(a: A): List[B] = rep.getOrElse(a, Nil)

  def insert[B1 >: B](a: A, b: B1): Multi_Map[A, B1] =
  {
    val bs = get_list(a)
    if (bs.contains(b)) this
    else new Multi_Map(rep + (a -> (b :: bs)))
  }

  def remove[B1 >: B](a: A, b: B1): Multi_Map[A, B1] =
  {
    val bs = get_list(a)
    if (bs.contains(b)) {
      bs.filterNot(_ == b) match {
        case Nil => new Multi_Map(rep - a)
        case bs1 => new Multi_Map(rep + (a -> bs1))
      }
    }
    else this
  }

  def ++[B1 >: B] (other: Multi_Map[A, B1]): Multi_Map[A, B1] =
    if (this eq other) this
    else if (isEmpty) other
    else
      other.rep.iterator.foldLeft(this.asInstanceOf[Multi_Map[A, B1]]) {
        case (m1, (a, bs)) => bs.foldRight(m1) { case (b, m2) => m2.insert(a, b) }
      }


  /* Map operations */

  override def empty: Multi_Map[A, Nothing] = Multi_Map.empty
  override def isEmpty: Boolean = rep.isEmpty

  override def keySet: Set[A] = rep.keySet

  override def iterator: Iterator[(A, B)] =
    for ((a, bs) <- rep.iterator; b <- bs.iterator) yield (a, b)

  def get(a: A): Option[B] = get_list(a).headOption

  override def updated[B1 >: B](a: A, b: B1): Multi_Map[A, B1] = insert(a, b)

  override def removed(a: A): Multi_Map[A, B] =
    if (rep.isDefinedAt(a)) new Multi_Map(rep - a) else this

  override def mapFactory: MapFactory[Multi_Map] = Multi_Map

  override def toString: String = mkString("Multi_Map(", ", ", ")")
}
