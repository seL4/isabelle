/*  Title:      Pure/General/untyped.scala
    Author:     Makarius

Untyped, unscoped, unchecked access to JVM objects.
*/

package isabelle


import java.lang.reflect.{Constructor, Method, Field}


object Untyped {
  def constructor[C](c: Class[C], arg_types: Class[_]*): Constructor[C] = {
    val con = c.getDeclaredConstructor(arg_types: _*)
    con.setAccessible(true)
    con
  }

  def the_constructor[C](c: Class[C]): Constructor[C] = {
    c.getDeclaredConstructors().toList match {
      case List(con) =>
        con.setAccessible(true)
        con.asInstanceOf[Constructor[C]]
      case Nil => error("No constructor for " + c)
      case _ => error("Multiple constructors for " + c)
    }
  }

  def method(c: Class[_], name: String, arg_types: Class[_]*): Method = {
    val m = c.getDeclaredMethod(name, arg_types: _*)
    m.setAccessible(true)
    m
  }

  def the_method(c: Class[_], name: String): Method = {
    c.getDeclaredMethods().iterator.filter(m => m.getName == name).toList match {
      case List(m) =>
        m.setAccessible(true)
        m
      case Nil => error("No method " + quote(name) + " for " + c)
      case _ => error("Multiple methods " + quote(name) + " for " + c)
    }
  }

  def classes(c0: Class[_ <: AnyRef]): Iterator[Class[_ <: AnyRef]] = new Iterator[Class[_ <: AnyRef]] {
    private var next_elem: Class[_ <: AnyRef] = c0
    def hasNext: Boolean = next_elem != null
    def next(): Class[_ <: AnyRef] = {
      val c = next_elem
      next_elem = c.getSuperclass.asInstanceOf[Class[_ <: AnyRef]]
      c
    }
  }

  def class_field(c0: Class[_ <: AnyRef], x: String): Field = {
    val iterator =
      for {
        c <- classes(c0)
        field <- c.getDeclaredFields.iterator
        if field.getName == x
      } yield {
        field.setAccessible(true)
        field
      }
    if (iterator.hasNext) iterator.next()
    else error("No field " + quote(x) + " for " + c0)
  }

  def get_static[A](c: Class[_ <: AnyRef], x: String): A =
    class_field(c, x).get(null).asInstanceOf[A]

  def field(obj: AnyRef, x: String): Field = class_field(obj.getClass, x)

  def get[A](obj: AnyRef, x: String): A =
    if (obj == null) null.asInstanceOf[A]
    else field(obj, x).get(obj).asInstanceOf[A]

  def set[A](obj: AnyRef, x: String, y: A): Unit =
    field(obj, x).set(obj, y)
}
