/*  Title:      Pure/System/scala.scala
    Author:     Makarius

Support for Scala at runtime.
*/

package isabelle


import java.lang.reflect.{Modifier, InvocationTargetException}
import java.io.{File => JFile, StringWriter, PrintWriter}

import scala.util.matching.Regex
import scala.tools.nsc.GenericRunnerSettings
import scala.tools.nsc.interpreter.IMain


object Scala
{
  /* compiler */

  object Compiler
  {
    def classpath(jar_dirs: List[JFile]): String =
    {
      def find_jars(dir: JFile): List[String] =
        File.find_files(dir, file => file.getName.endsWith(".jar")).
          map(File.absolute_name)

      val class_path =
        for {
          prop <- List("scala.boot.class.path", "java.class.path")
          path = System.getProperty(prop, "") if path != "\"\""
          elem <- space_explode(JFile.pathSeparatorChar, path)
        } yield elem

      (class_path ::: jar_dirs.flatMap(find_jars)).mkString(JFile.pathSeparator)
    }

    type Settings = scala.tools.nsc.Settings

    def settings(
      error: String => Unit = Exn.error,
      jar_dirs: List[JFile] = Nil): Settings =
    {
      val settings = new GenericRunnerSettings(error)
      settings.classpath.value = classpath(jar_dirs)
      settings
    }

    def toplevel(settings: Settings, source: String): List[String] =
    {
      val out = new StringWriter
      val interp = new IMain(settings, new PrintWriter(out))
      val rep = new interp.ReadEvalPrint
      val ok = interp.withLabel("\u0001") { rep.compile(source) }
      out.close

      val Error = """(?s)^\S* error: (.*)$""".r
      val errors =
        space_explode('\u0001', Library.strip_ansi_color(out.toString)).
          collect({ case Error(msg) => Word.capitalize(Library.trim_line(msg)) })

      if (!ok && errors.isEmpty) List("Error") else errors
    }
  }



  /** invoke JVM method via Isabelle/Scala **/

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
    val NULL, OK, ERROR, FAIL, INTERRUPT = Value
  }

  def method(name: String, arg: String): (Tag.Value, String) =
    Exn.capture { get_method(name) } match {
      case Exn.Res(f) =>
        Exn.capture { f(arg) } match {
          case Exn.Res(null) => (Tag.NULL, "")
          case Exn.Res(res) => (Tag.OK, res)
          case Exn.Exn(Exn.Interrupt()) => (Tag.INTERRUPT, "")
          case Exn.Exn(e) => (Tag.ERROR, Exn.message(e))
        }
      case Exn.Exn(e) => (Tag.FAIL, Exn.message(e))
    }
}


/* protocol handler */

class Scala extends Session.Protocol_Handler
{
  private var session: Session = null
  private var futures = Map.empty[String, Future[Unit]]

  override def init(init_session: Session): Unit =
    synchronized { session = init_session }

  override def exit(): Unit = synchronized
  {
    for ((id, future) <- futures) cancel(id, future)
    futures = Map.empty
  }

  private def fulfill(id: String, tag: Scala.Tag.Value, res: String): Unit =
    synchronized
    {
      if (futures.isDefinedAt(id)) {
        session.protocol_command("Scala.fulfill", id, tag.id.toString, res)
        futures -= id
      }
    }

  private def cancel(id: String, future: Future[Unit])
  {
    future.cancel
    fulfill(id, Scala.Tag.INTERRUPT, "")
  }

  private def invoke_scala(msg: Prover.Protocol_Output): Boolean = synchronized
  {
    msg.properties match {
      case Markup.Invoke_Scala(name, id) =>
        futures += (id ->
          Future.fork {
            val (tag, result) = Scala.method(name, msg.text)
            fulfill(id, tag, result)
          })
        true
      case _ => false
    }
  }

  private def cancel_scala(msg: Prover.Protocol_Output): Boolean = synchronized
  {
    msg.properties match {
      case Markup.Cancel_Scala(id) =>
        futures.get(id) match {
          case Some(future) => cancel(id, future)
          case None =>
        }
        true
      case _ => false
    }
  }

  val functions =
    List(
      Markup.Invoke_Scala.name -> invoke_scala,
      Markup.Cancel_Scala.name -> cancel_scala)
}
