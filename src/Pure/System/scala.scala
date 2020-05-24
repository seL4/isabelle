/*  Title:      Pure/System/scala.scala
    Author:     Makarius

Support for Scala at runtime.
*/

package isabelle


import java.io.{File => JFile, StringWriter, PrintWriter}

import scala.tools.nsc.{GenericRunnerSettings, ConsoleWriter, NewLinePrintWriter}
import scala.tools.nsc.interpreter.IMain


object Scala
{
  /** compiler **/

  object Compiler
  {
    lazy val default_context: Context = context()

    def context(
      error: String => Unit = Exn.error,
      jar_dirs: List[JFile] = Nil): Context =
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

      val settings = new GenericRunnerSettings(error)
      settings.classpath.value =
        (class_path ::: jar_dirs.flatMap(find_jars)).mkString(JFile.pathSeparator)

      new Context(settings)
    }

    def default_print_writer: PrintWriter =
      new NewLinePrintWriter(new ConsoleWriter, true)

    class Context private [Compiler](val settings: GenericRunnerSettings)
    {
      override def toString: String = settings.toString

      def interpreter(
        print_writer: PrintWriter = default_print_writer,
        class_loader: ClassLoader = null): IMain =
      {
        new IMain(settings, print_writer)
        {
          override def parentClassLoader: ClassLoader =
            if (class_loader == null) super.parentClassLoader
            else class_loader
        }
      }

      def toplevel(source: String): List[String] =
      {
        val out = new StringWriter
        val interp = interpreter(new PrintWriter(out))
        val rep = new interp.ReadEvalPrint
        val ok = interp.withLabel("\u0001") { rep.compile(source) }
        out.close

        val Error = """(?s)^\S* error: (.*)$""".r
        val errors =
          space_explode('\u0001', Library.strip_ansi_color(out.toString)).
            collect({ case Error(msg) => "Scala error: " + Library.trim_line(msg) })

        if (!ok && errors.isEmpty) List("Error") else errors
      }

      def check(body: String): List[String] =
      {
        try { toplevel("package test\nobject Test { " + body + " }") }
        catch { case ERROR(msg) => List(msg) }
      }
    }
  }

  def check_yxml(body: String): String =
  {
    val errors = Compiler.default_context.check(body)
    locally { import XML.Encode._; YXML.string_of_body(list(string)(errors)) }
  }



  /** invoke Scala functions from ML **/

  /* registered functions */

  sealed case class Fun(name: String, apply: String => String)
  {
    override def toString: String = name
  }

  lazy val functions: List[Fun] =
    Isabelle_System.services.collect { case c: Isabelle_Scala_Functions => c.functions.toList }.flatten


  /* invoke function */

  object Tag extends Enumeration
  {
    val NULL, OK, ERROR, FAIL, INTERRUPT = Value
  }

  def function(name: String, arg: String): (Tag.Value, String) =
    functions.find(fun => fun.name == name) match {
      case Some(fun) =>
        Exn.capture { fun.apply(arg) } match {
          case Exn.Res(null) => (Tag.NULL, "")
          case Exn.Res(res) => (Tag.OK, res)
          case Exn.Exn(Exn.Interrupt()) => (Tag.INTERRUPT, "")
          case Exn.Exn(e) => (Tag.ERROR, Exn.message(e))
        }
      case None => (Tag.FAIL, "Unknown Isabelle/Scala function: " + quote(name))
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
            val (tag, result) = Scala.function(name, msg.text)
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


/* registered functions */

class Isabelle_Scala_Functions(val functions: Scala.Fun*) extends Isabelle_System.Service

class Functions extends Isabelle_Scala_Functions(
  Scala.Fun("echo", identity),
  Scala.Fun("scala_check", Scala.check_yxml),
  Scala.Fun("check_bibtex_database", Bibtex.check_database_yxml))
