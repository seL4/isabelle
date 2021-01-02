/*  Title:      Pure/General/cache.scala
    Author:     Makarius

Cache for partial sharing (weak table).
*/

package isabelle


import java.util.{Collections, WeakHashMap, Map => JMap}
import java.lang.ref.WeakReference


object Cache
{
  val default_max_string = 100
  val default_initial_size = 131071

  def make(max_string: Int = default_max_string, initial_size: Int = default_initial_size): Cache =
    new Cache(max_string, initial_size)

  val none: Cache = make(max_string = 0)
}

class Cache(max_string: Int, initial_size: Int)
{
  val no_cache: Boolean = max_string == 0

  private val table: JMap[Any, WeakReference[Any]] =
    if (max_string == 0) null
    else  Collections.synchronizedMap(new WeakHashMap[Any, WeakReference[Any]](initial_size))

  override def toString: String =
    if (no_cache) "Cache.none" else "Cache(size = " + table.size + ")"

  protected def lookup[A](x: A): Option[A] =
  {
    if (table == null) None
    else {
      val ref = table.get(x)
      if (ref == null) None
      else Option(ref.asInstanceOf[WeakReference[A]].get)
    }
  }

  protected def store[A](x: A): A =
  {
    if (table == null || x == null) x
    else {
      table.put(x, new WeakReference[Any](x))
      x
    }
  }

  protected def cache_string(x: String): String =
  {
    if (x == null) null
    else if (x == "") ""
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
  def string(x: String): String =
    if (no_cache) x else synchronized { cache_string(x) }
}
