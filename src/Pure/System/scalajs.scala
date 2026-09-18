/*  Title:      Pure/System/scalajs.scala
    Author:     Fabian Huch

Support for compiling Scala to JavaScript.
*/

package isabelle

import scala.language.unsafeNulls

import java.io.{File => JFile}

import scala.annotation.tailrec
import scala.jdk.CollectionConverters._
import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits.global
import scala.scalajs.js
import scala.scalajs.js.JSConverters._

import org.scalajs.dom
import org.scalajs.logging
import org.scalajs.linker.{PathIRContainer, StandardImpl, PathOutputDirectory}
import org.scalajs.linker.interface.{Report, StandardConfig, ModuleInitializer, ModuleKind}

import dotty.tools.dotc.Driver
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.interfaces.Diagnostic
import dotty.tools.dotc.reporting


object Scalajs {
  /** compilation **/

  final case class Module(name: String, class_name: String, main: String = "main") {
    def js_path: Path = Path.basic(name).ext("js")
  }

  object Message {
    enum Phase { case compilation, linking }
    enum Kind { case error, warning, info, debug, other }

    def compilation(kind: Kind, text: String): Message = Message(Phase.compilation, kind, text)

    def linking(level: logging.Level, text: String): Message = {
      val kind =
        level match {
          case logging.Level.Error => Kind.error
          case logging.Level.Warn => Kind.warning
          case logging.Level.Info => Kind.info
          case logging.Level.Debug => Kind.debug
        }
      Message(Phase.linking, kind, text)
    }
  }

  sealed case class Message(phase: Message.Phase, kind: Message.Kind, text: String) {
    def is_error: Boolean = kind == Message.Kind.error
    override def toString: String = text

    def output(progress: Progress): Unit = kind match {
      case Message.Kind.error => progress.echo_error_message(text)
      case Message.Kind.warning => progress.echo_warning(text)
      case Message.Kind.info => progress.echo(text)
      case Message.Kind.debug => progress.echo(text, verbose = true)
      case Message.Kind.other =>
    }
  }

  sealed case class Result(
    messages: List[Message] = Nil,
    report: Option[Report] = None,
    outputs: List[Path] = Nil
  ) {
    val errors: List[String] = messages.flatMap(msg => if (msg.is_error) Some(msg.text) else None)
    def ok: Boolean = errors.isEmpty
    override def toString: String =
      if (ok) "Result(outputs=" + outputs.map(_.absolute).mkString(", ") + ")" else "Result(error)"
  }

  def compile(
    sources: List[JFile],
    modules: List[Module],
    output_dir: Path,
    more_settings: List[String] = Nil,
    classpath: Classpath = Classpath()
  ): Result = {
    if (!sources.exists(s => File.is_scala(s.file_name))) Result()
    else Isabelle_System.with_tmp_dir("scalajs") { dir =>
      val ir_dir = Isabelle_System.make_directory(dir + Path.basic("ir")).java_path.nn

      val settings =
        Word.explode(Isabelle_System.getenv_strict("ISABELLE_SCALAC_OPTIONS")) ::: more_settings :::
          List("-d", ir_dir.toString, "-bootclasspath", classpath.platform_path, "-scalajs")

      val msgs = new mutable.ListBuffer[Message]()
      val reporter =
        new reporting.AbstractReporter {
          def doReport(diagnostic: reporting.Diagnostic)(using Context): Unit = {
            val kind =
              diagnostic.level() match {
                case Diagnostic.ERROR => Message.Kind.error
                case Diagnostic.WARNING => Message.Kind.warning
                case Diagnostic.INFO => Message.Kind.info
                case _ => Message.Kind.other
              }
            msgs += Message.compilation(kind, messageAndPos(diagnostic))
          }
        }

      val args = settings ::: "--" :: sources.map(_.toString)
      val result = new Driver().process(args.toArray, reporter, null)

      if (result.hasErrors) Result(msgs.toList)
      else {
        val linker = StandardImpl.linker(StandardConfig().withModuleKind(ModuleKind.ESModule))
        val cache = StandardImpl.irFileCache().newCache

        val logger =
          new logging.Logger {
            def trace(t: => Throwable): Unit = {
              msgs += Message(Message.Phase.linking, Message.Kind.error, Exn.trace(t))
            }
            def log(level: logging.Level, message: => String): Unit = {
              msgs += Message.linking(level, message)
            }
          }

        val js_dir = Isabelle_System.make_directory(dir + Path.basic("js"))
        val output = PathOutputDirectory(js_dir.java_path.nn)

        val initializers =
          for (m <- modules)
          yield ModuleInitializer.mainMethod(m.class_name, m.main).withModuleID(m.name)

        val futures =
          for {
            containers <- PathIRContainer.fromClasspath(ir_dir :: classpath.jars.map(_.toPath.nn))
            ir_files <- cache.cached(containers._1)
            result <- linker.link(ir_files, initializers, output, logger)
          } yield result

        val report =
         Exn.capture { Await.result(futures, scala.concurrent.duration.Duration.Inf) } match {
           case Exn.Res(res) => Some(res)
           case Exn.Exn(t) =>
             msgs += Message(Message.Phase.linking, Message.Kind.error, Exn.trace(t))
             None
         }

        val results =
          for (name <- File.read_dir(js_dir) if name.endsWith(".js"))
          yield {
            Isabelle_System.copy_file(js_dir + Path.basic(name), output_dir)
            output_dir + Path.basic(name)
          }
        Result(msgs.toList, report, results)
      }
    }
  }


  /** json conversions **/

  object JSON {
    def apply(json: isabelle.JSON.T): js.Any =
      json match {
        case x: String => x
        case x: Double => x
        case x: Long => x.toDouble
        case x: Int => x
        case x: Boolean => x
        case null => null
        case xs: List[isabelle.JSON.T] => xs.map(apply).toJSArray
        case isabelle.JSON.Object(obj) => Object(obj)
        case x => error("Bad JSON value: " + x.toString)
      }

    def unapply(json: Any): Option[isabelle.JSON.T] =
      json match {
        case x: String => Some(x)
        case x: Double => Some(x)
        case x: Int => Some(x)
        case x: Boolean => Some(x)
        case null => Some(null)
        case xs: js.Array[_] =>
          val arr = xs.map(unapply)
          if (arr.forall(_.isDefined)) Some(arr.map(_.get).toList) else None
        case Object(m) => Some(m)
        case _ => None
      }

    object Object {
      def apply(json: isabelle.JSON.Object.T): js.Object =
        js.Dynamic.literal(json.toList.map((k, v) => k -> JSON(v)): _*)

      def unapply(json: js.Object): Option[isabelle.JSON.Object.T] = {
        val entries = js.Object.entries(json).map(t => t._1 -> JSON.unapply(t._2))
        if (entries.forall(_._2.isDefined)) Some(entries.map((k, v) => k -> v.get).toMap) else None
      }
    }
  }


  /** registered functions **/

  sealed abstract class JS_Fun {
    val invoke: PartialFunction[List[Any], Unit]
    final val function = Functions.register(this)
  }

  abstract class Fun_Any extends JS_Fun {
    def apply(arg: Any): Unit
    final val invoke = { case arg :: Nil => apply(arg) }
  }

  abstract class Fun_Unit extends JS_Fun {
    def apply(): Unit
    final val invoke = { case Nil => apply() }
  }

  abstract class Fun_JSON extends JS_Fun {
    def apply(a: isabelle.JSON.T): Unit
    final val invoke = { case JSON(json) :: Nil => apply(json) }
  }

  abstract class Fun[A] extends JS_Fun {
    def apply(a: A): Unit
    final val invoke = { case a :: Nil => apply(a.asInstanceOf[A]) }
  }

  abstract class Fun2[A, B] extends JS_Fun {
    def apply(a: A, b: B): Unit
    final val invoke = { case a :: b :: Nil => apply(a.asInstanceOf[A], b.asInstanceOf[B]) }
  }

  abstract class Fun3[A, B, C] extends JS_Fun {
    def apply(a: A, b: B, c: C): Unit
    final val invoke = { 
      case a :: b :: c :: Nil => apply(a.asInstanceOf[A], b.asInstanceOf[B], c.asInstanceOf[C])
    }
  }

  object Functions {
    private val functions = mutable.Map.empty[String, js.Function1[js.Array[Any], Unit]]
    if (Platform.is_scalajs) js.Dynamic.global.window.isabelle_functions = functions

    def lookup(name: String): String = JS.function("window.isabelle_functions", quote(name))

    def register(fun: JS_Fun): Function = {
      if (Platform.is_scalajs) {
        functions.update(fun.class_name,
          { args =>
            fun.invoke.applyOrElse(args.toList,
              _ => error("Function invocation with invalid JS arguments"))
          })
      }
      new Function(fun.class_name)
    }
  }

  class Function private[Scalajs](val name: String) {
    override def toString: String = name
    def apply(args: JS.Source*): JS.Source = JS.function(Functions.lookup(name), JS.array(args: _*))
  }


  /** DOM operations **/

  object DOM {
    /* DOM update via XML.Body diff */

    private def update_attributes(elem: dom.Element, props: Properties.T): Unit = {
      val seen =
        (for ((key, value) <- props) yield {
          if (elem.attributes.get(key).forall(_.value != value)) elem.setAttribute(key, value)
          key
        }).toSet
      elem.attributes.keys.filterNot(seen).foreach(elem.removeAttribute)

      elem match {
        case input: dom.HTMLInputElement =>
          if (input.value != input.defaultValue) input.value = input.defaultValue
          if (input.checked != input.defaultChecked) input.checked = input.defaultChecked

        case option: dom.HTMLOptionElement =>
          if (option.selected != option.defaultSelected) option.selected = option.defaultSelected

        case textarea: dom.HTMLTextAreaElement =>
          if (textarea.value != textarea.defaultValue) textarea.value = textarea.defaultValue

        case media: dom.HTMLMediaElement =>
          if (media.playbackRate != media.defaultPlaybackRate) {
            media.playbackRate = media.defaultPlaybackRate
          }

        case _ =>
      }
    }

    private def create(tree: XML.Tree): dom.Node =
      tree match {
        case XML.Text(s) => dom.document.createTextNode(s)

        case XML.Elem(Markup(Markup.RAW_HTML, _), body) =>
          val raw =
            Library.string_builder() { s => XML.traverse_text(body, (), (_, raw) => s.append(raw)) }
          val elem = dom.document.createElement("raw-html")
          elem.innerHTML = raw
          elem

        case XML.Elem(markup, body) =>
          val elem = dom.document.createElement(markup.name)
          update_attributes(elem, markup.properties)
          body.foreach(child => elem.appendChild(create(child)))
          elem
      }

    private def update_children(parent: dom.Node, body: XML.Body): Unit = {
      @tailrec def update(children: List[dom.Node], trees: List[XML.Tree]): Unit =
        (children, trees) match {
          case (Nil, trees) => trees.map(create).foreach(parent.appendChild)
          case (children, Nil) => children.foreach(parent.removeChild)
          case (child :: children, tree :: trees) =>
            (child, tree) match {
              case (text: dom.Text, XML.Text(s)) => text.data = s
              case (elem: dom.Element, XML.Elem(markup, body))
                   if Word.lowercase(elem.tagName) == markup.name =>
                update_attributes(elem, markup.properties)
                update_children(elem, body)
              case (_, tree) => parent.replaceChild(create(tree), child)
            }
            update(children, trees)
        }

      update(parent.childNodes.toList, body)
    }

    def update(body: XML.Body): Unit = update_children(dom.document.body, body)


    /* handlers */

    final class Handler(val handle: scala.PartialFunction[dom.Event, Unit])

    class Event_Handler(register: js.Function1[dom.Event, Unit] => Unit) {
      private var handlers: List[Handler] = Nil
      register(e => handlers.foreach(_.handle.lift(e)))

      def += (h: Handler): Unit = { handlers = Library.update(h)(handlers) }
      def -= (h: Handler): Unit = { handlers = Library.remove(h)(handlers) }
    }

    val onresize = new Event_Handler(handler => dom.window.onresize = handler)
    val onload = new Event_Handler(handler => dom.window.onload = handler)
  }
}
