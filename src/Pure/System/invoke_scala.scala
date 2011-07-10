/*  Title:      Pure/System/invoke_scala.scala
    Author:     Makarius

Invoke static methods (String)String via reflection.
*/

package isabelle


import java.lang.reflect.{Method, Modifier}


object Invoke_Scala
{
  private val STRING = Class.forName("java.lang.String")

  def method(class_name: String, method_name: String): String => String =
  {
    val m =
      try { Class.forName(class_name).getMethod(method_name, STRING) }
      catch {
        case _: ClassNotFoundException =>
          error("Class not found: " + quote(class_name))
        case _: NoSuchMethodException =>
          error("No such method: " + quote(class_name + "." + method_name))
      }
    if (!Modifier.isStatic(m.getModifiers)) error("Not at static method: " + m.toString)
    if (m.getReturnType != STRING) error("Bad return type of method: " + m.toString)

    (s: String) => m.invoke(null, s).asInstanceOf[String]
  }
}
