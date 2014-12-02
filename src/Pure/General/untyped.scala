/*  Title:      Pure/General/untyped.scala
    Module:     PIDE
    Author:     Makarius

Untyped, unscoped, unchecked access to JVM objects.
*/

package isabelle


object Untyped
{
  def classes(obj: AnyRef): Iterator[Class[_ <: AnyRef]] = new Iterator[Class[_ <: AnyRef]] {
    private var next_elem: Class[_ <: AnyRef] = obj.getClass
    def hasNext(): Boolean = next_elem != null
    def next(): Class[_ <: AnyRef] = {
      val c = next_elem
      next_elem = c.getSuperclass.asInstanceOf[Class[_ <: AnyRef]]
      c
    }
  }

  def get[A](obj: AnyRef, x: String): A =
    if (obj == null) null.asInstanceOf[A]
    else {
      val iterator =
        for {
          c <- classes(obj)
          field <- c.getDeclaredFields.iterator
          if field.getName == x
        } yield {
          field.setAccessible(true)
          field.get(obj)
        }
      if (iterator.hasNext) iterator.next.asInstanceOf[A]
      else error("No field " + quote(x) + " for " + obj)
    }
}

