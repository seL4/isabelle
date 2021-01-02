/*  Title:      Pure/General/cache.scala
    Author:     Makarius

Cache for partial sharing (weak table).
*/

package isabelle


import java.util.{Collections, WeakHashMap}
import java.lang.ref.WeakReference


class Cache(initial_size: Int = 131071, max_string: Int = 100)
{
  private val table =
    Collections.synchronizedMap(new WeakHashMap[Any, WeakReference[Any]](initial_size))

  def size: Int = table.size

  override def toString: String = "Cache(" + size + ")"

  protected def lookup[A](x: A): Option[A] =
  {
    val ref = table.get(x)
    if (ref == null) None
    else Option(ref.asInstanceOf[WeakReference[A]].get)
  }

  protected def store[A](x: A): A =
  {
    table.put(x, new WeakReference[Any](x))
    x
  }

  protected def cache_string(x: String): String =
  {
    if (x == "") ""
    else if (x == "true") "true"
    else if (x == "false") "false"
    else if (x == "0.0") "0.0"
    else if (Library.is_small_int(x)) Library.signed_string_of_int(Integer.parseInt(x))
    else {
      lookup(x) match {
        case Some(y) => y
        case None =>
          val z = Library.isolate_substring(x)
          if (z.length > max_string) z else store(z)
      }
    }
  }

  // main methods
  def string(x: String): String = synchronized { cache_string(x) }
}
