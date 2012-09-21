/*  Title:      Pure/System/invoke_scala.scala
    Author:     Makarius

JVM method invocation service via Isabelle/Scala.
*/

package isabelle


import java.lang.reflect.{Method, Modifier, InvocationTargetException}
import scala.util.matching.Regex


object Invoke_Scala
{
  /* method reflection */

  private val Ext = new Regex("(.*)\\.([^.]*)")
  private val STRING = Class.forName("java.lang.String")

  private def get_method(name: String): String => String =
    name match {
      case Ext(class_name, method_name) =>
        val m =
          try { Class.forName(class_name).getMethod(method_name, STRING) }
          catch {
            case _: ClassNotFoundException | _: NoSuchMethodException =>
              error("No such method: " + quote(name))
          }
        if (!Modifier.isStatic(m.getModifiers)) error("Not at static method: " + m.toString)
        if (m.getReturnType != STRING) error("Bad method return type: " + m.toString)

        (arg: String) => {
          try { m.invoke(null, arg).asInstanceOf[String] }
          catch {
            case e: InvocationTargetException if e.getCause != null =>
              throw e.getCause
          }
        }
      case _ => error("Malformed method name: " + quote(name))
    }


  /* method invocation */

  object Tag extends Enumeration
  {
    val NULL = Value("0")
    val OK = Value("1")
    val ERROR = Value("2")
    val FAIL = Value("3")
    val INTERRUPT = Value("4")
  }

  def method(name: String, arg: String): (Tag.Value, String) =
    Exn.capture { get_method(name) } match {
      case Exn.Res(f) =>
        Exn.capture { f(arg) } match {
          case Exn.Res(null) => (Tag.NULL, "")
          case Exn.Res(res) => (Tag.OK, res)
          case Exn.Exn(_: InterruptedException) => (Tag.INTERRUPT, "")
          case Exn.Exn(e) => (Tag.ERROR, Exn.message(e))
        }
      case Exn.Exn(e) => (Tag.FAIL, Exn.message(e))
    }
}
