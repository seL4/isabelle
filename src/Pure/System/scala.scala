/*  Title:      Pure/System/scala.scala
    Author:     Makarius

Support for Scala at runtime.
*/

package isabelle


import java.io.{File => JFile, StringWriter, PrintWriter}

import scala.tools.nsc.{GenericRunnerSettings, ConsoleWriter, NewLinePrintWriter}
import scala.tools.nsc.interpreter.{IMain, Results}
import scala.tools.nsc.interpreter.shell.ReplReporterImpl

object Scala
{
  /** registered functions **/

  abstract class Fun(val name: String, val thread: Boolean = false)
  {
    override def toString: String = name
    def multi: Boolean = true
    def position: Properties.T = here.position
    def here: Scala_Project.Here
    def invoke(args: List[Bytes]): List[Bytes]
  }

  abstract class Fun_Strings(name: String, thread: Boolean = false)
    extends Fun(name, thread = thread)
  {
    override def invoke(args: List[Bytes]): List[Bytes] =
      apply(args.map(_.text)).map(Bytes.apply)
    def apply(args: List[String]): List[String]
  }

  abstract class Fun_String(name: String, thread: Boolean = false)
    extends Fun_Strings(name, thread = thread)
  {
    override def multi: Boolean = false
    override def apply(args: List[String]): List[String] =
      args match {
        case List(arg) => List(apply(arg))
        case _ => error("Expected single argument for Scala function " + quote(name))
      }
    def apply(arg: String): String
  }

  class Functions(val functions: Fun*) extends Isabelle_System.Service

  lazy val functions: List[Fun] =
    Isabelle_System.make_services(classOf[Functions]).flatMap(_.functions)



  /** demo functions **/

  object Echo extends Fun_String("echo")
  {
    val here = Scala_Project.here
    def apply(arg: String): String = arg
  }

  object Sleep extends Fun_String("sleep")
  {
    val here = Scala_Project.here
    def apply(seconds: String): String =
    {
      val t =
        seconds match {
          case Value.Double(s) => Time.seconds(s)
          case _ => error("Malformed argument: " + quote(seconds))
        }
      val t0 = Time.now()
      t.sleep
      val t1 = Time.now()
      (t1 - t0).toString
    }
  }



  /** compiler **/

  object Compiler
  {
    def context(
      error: String => Unit = Exn.error,
      jar_dirs: List[JFile] = Nil): Context =
    {
      def find_jars(dir: JFile): List[String] =
        File.find_files(dir, file => file.getName.endsWith(".jar")).
          map(File.absolute_name)

      val class_path =
        for {
          prop <- List("isabelle.scala.classpath", "java.class.path")
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
        new IMain(settings, new ReplReporterImpl(settings, print_writer))
        {
          override def parentClassLoader: ClassLoader =
            if (class_loader == null) super.parentClassLoader
            else class_loader
        }
      }

      def toplevel(interpret: Boolean, source: String): List[String] =
      {
        val out = new StringWriter
        val interp = interpreter(new PrintWriter(out))
        val marker = '\u000b'
        val ok =
          interp.withLabel(marker.toString) {
            if (interpret) interp.interpret(source) == Results.Success
            else (new interp.ReadEvalPrint).compile(source)
          }
        out.close()

        val Error = """(?s)^\S* error: (.*)$""".r
        val errors =
          space_explode(marker, Library.strip_ansi_color(out.toString)).
            collect({ case Error(msg) => "Scala error: " + Library.trim_line(msg) })

        if (!ok && errors.isEmpty) List("Error") else errors
      }
    }
  }

  object Toplevel extends Fun_String("scala_toplevel")
  {
    val here = Scala_Project.here
    def apply(arg: String): String =
    {
      val (interpret, source) =
        YXML.parse_body(arg) match {
          case Nil => (false, "")
          case List(XML.Text(source)) => (false, source)
          case body => import XML.Decode._; pair(bool, string)(body)
        }
      val errors =
        try { Compiler.context().toplevel(interpret, source) }
        catch { case ERROR(msg) => List(msg) }
      locally { import XML.Encode._; YXML.string_of_body(list(string)(errors)) }
    }
  }



  /** invoke Scala functions from ML **/

  /* invoke function */

  object Tag extends Enumeration
  {
    val NULL, OK, ERROR, FAIL, INTERRUPT = Value
  }

  def function_thread(name: String): Boolean =
    functions.find(fun => fun.name == name) match {
      case Some(fun) => fun.thread
      case None => false
    }

  def function_body(name: String, args: List[Bytes]): (Tag.Value, List[Bytes]) =
    functions.find(fun => fun.name == name) match {
      case Some(fun) =>
        Exn.capture { fun.invoke(args) } match {
          case Exn.Res(null) => (Tag.NULL, Nil)
          case Exn.Res(res) => (Tag.OK, res)
          case Exn.Exn(Exn.Interrupt()) => (Tag.INTERRUPT, Nil)
          case Exn.Exn(e) => (Tag.ERROR, List(Bytes(Exn.message(e))))
        }
      case None => (Tag.FAIL, List(Bytes("Unknown Isabelle/Scala function: " + quote(name))))
    }


  /* protocol handler */

  class Handler extends Session.Protocol_Handler
  {
    private var session: Session = null
    private var futures = Map.empty[String, Future[Unit]]

    override def init(session: Session): Unit =
      synchronized { this.session = session }

    override def exit(): Unit = synchronized
    {
      for ((id, future) <- futures) cancel(id, future)
      futures = Map.empty
    }

    private def result(id: String, tag: Scala.Tag.Value, res: List[Bytes]): Unit =
      synchronized
      {
        if (futures.isDefinedAt(id)) {
          session.protocol_command_raw("Scala.result", Bytes(id) :: Bytes(tag.id.toString) :: res)
          futures -= id
        }
      }

    private def cancel(id: String, future: Future[Unit]): Unit =
    {
      future.cancel()
      result(id, Scala.Tag.INTERRUPT, Nil)
    }

    private def invoke_scala(msg: Prover.Protocol_Output): Boolean = synchronized
    {
      msg.properties match {
        case Markup.Invoke_Scala(name, id) =>
          def body: Unit =
          {
            val (tag, res) = Scala.function_body(name, msg.chunks)
            result(id, tag, res)
          }
          val future =
            if (Scala.function_thread(name)) {
              Future.thread(name = Isabelle_Thread.make_name(base = "invoke_scala"))(body)
            }
            else Future.fork(body)
          futures += (id -> future)
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

    override val functions =
      List(
        Markup.Invoke_Scala.name -> invoke_scala,
        Markup.Cancel_Scala.name -> cancel_scala)
  }
}

class Scala_Functions extends Scala.Functions(
  Scala.Echo,
  Scala.Sleep,
  Scala.Toplevel,
  Doc.Doc_Names,
  Bash.Process,
  Bibtex.Check_Database,
  Isabelle_System.Make_Directory,
  Isabelle_System.Copy_Dir,
  Isabelle_System.Copy_File,
  Isabelle_System.Copy_File_Base,
  Isabelle_System.Rm_Tree,
  Isabelle_System.Download,
  Isabelle_System.Isabelle_Id,
  Isabelle_Tool.Isabelle_Tools,
  isabelle.atp.SystemOnTPTP.List_Systems,
  isabelle.atp.SystemOnTPTP.Run_System)
