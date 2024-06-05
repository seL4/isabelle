/*  Title:      Pure/System/web_app.scala
    Author:     Fabian Huch, TU Muenchen

Technical layer for web apps using server-side rendering with HTML forms.
 */
package isabelle


import scala.annotation.tailrec
import scala.collection.immutable.SortedMap


object Web_App {
  /* form html elements */

  object More_HTML {
    import HTML._

    def css(s: String): Attribute = new Attribute("style", s)
    def name(n: String): Attribute = new Attribute("name", n)
    def value(v: String): Attribute = new Attribute("value", v)
    def placeholder(p: String): Attribute = new Attribute("placeholder", p)

    val fieldset = new Operator("fieldset")
    val button = new Operator("button")

    def legend(txt: String): XML.Elem = XML.Elem(Markup("legend", Nil), text(txt))
    def input(typ: String): XML.Elem = XML.Elem(Markup("input", List("type" -> typ)), Nil)
    def hidden(k: Params.Key, v: String): XML.Elem =
      id(k.print)(name(k.print)(value(v)(input("hidden"))))

    def textfield(i: Params.Key, p: String, v: String): XML.Elem =
      id(i.print)(name(i.print)(value(v)(placeholder(p)(input("text")))))

    def browse(i: Params.Key, accept: List[String]): XML.Elem =
      id(i.print)(name(i.print)(input("file"))) + ("accept" -> accept.mkString(","))

    def label(`for`: Params.Key, txt: String): XML.Elem =
      XML.Elem(Markup("label", List("for" -> `for`.print)), text(txt))

    def option(k: String, v: String): XML.Elem = value(k)(XML.elem("option", text(v)))

    def optgroup(txt: String, opts: XML.Body): XML.Elem =
      XML.Elem(Markup("optgroup", List("label" -> txt)), opts)

    def select(i: Params.Key, opts: XML.Body): XML.Elem =
      id(i.print)(name(i.print)(XML.elem("select", opts)))

    def textarea(i: Params.Key, v: String): XML.Elem =
      id(i.print)(name(i.print)(value(v)(XML.elem("textarea", text(v + "\n")))))

    def radio(i: Params.Key, v: Params.Key, values: List[(Params.Key, String)]): XML.Elem = {
      def to_option(k: Params.Key): XML.Elem = {
        val elem = id(i.print + k)(name(i.print)(value(k.print)(input("radio"))))
        if (v == k) elem + ("checked" -> "checked") else elem
      }

      span(values.map { case (k, v) => span(List(label(i + k, v), to_option(k))) })
    }

    def selection(i: Params.Key, selected: Option[String], opts: XML.Body): XML.Elem = {
      def sel(elem: XML.Tree): XML.Tree = {
        selected match {
          case Some(value) =>
            val Value = new Properties.String("value")
            elem match {
              case XML.Elem(Markup("optgroup", props), body) =>
                XML.Elem(Markup("optgroup", props), body.map(sel))
              case e@XML.Elem(Markup("option", Value(v)), _) if v == value =>
                e + ("selected" -> "selected")
              case e => e
            }
          case None => elem
        }
      }

      def is_empty_group(elem: XML.Tree): Boolean = elem match {
        case XML.Elem(Markup("optgroup", _), body) if body.isEmpty => true
        case _ => false
      }

      val default = if (selected.isEmpty) List(option("", "") + ("hidden" -> "hidden")) else Nil
      select(i, default ::: opts.filterNot(is_empty_group).map(sel))
    }

    def api_button(call: String, label: String): XML.Elem =
      button(text(label)) + ("formaction" -> call) + ("type" -> "submit")

    def submit_form(endpoint: String, body: XML.Body): XML.Elem = {
      val default_button = css("display: none")(input("submit") + ("formaction" -> endpoint))
      val attrs =
        List("method" -> "post", "target" -> "iframe", "enctype" -> "multipart/form-data")
      XML.Elem(Markup("form", attrs), default_button :: body)
    }
  }


  /* form http handling */

  object Multi_Part {
    abstract class Data(name: String)
    case class Param(name: String, value: String) extends Data(name)
    case class File(name: String, file_name: String, content: Bytes) extends Data(name)

    def parse(body: Bytes): List[Data] = {
      /* Seq for text with embedded bytes */
      case class Seq(text: String, bytes: Bytes) {
        def split_one(sep: String): Option[(Seq, Seq)] = {
          val text_i = text.indexOf(sep)
          if (text_i >= 0 && sep.nonEmpty) {
            val (before_text, at_text) = text.splitAt(text_i)
            val after_text = at_text.substring(sep.length)

            // text might be shorter than bytes because of misinterpreted characters
            var found = false
            var bytes_i = 0
            while (!found && bytes_i < bytes.length) {
              var sep_ok = true
              var sep_i = 0
              while (sep_ok && sep_i < sep.length) {
                if (bytes.charAt(bytes_i + sep_i) == sep.charAt(sep_i)) {
                  sep_i += 1
                } else {
                  bytes_i += 1
                  sep_ok = false
                }
              }
              if (sep_ok) found = true
            }

            val before_bytes = bytes.subSequence(0, bytes_i)
            val after_bytes = bytes.subSequence(bytes_i + sep.length, bytes.length)

            Some(Seq(before_text, before_bytes), Seq(after_text, after_bytes))
          } else None
        }
      }

      val s = Seq(body.text, body)

      def perhaps_unprefix(pfx: String, s: Seq): Seq =
        Library.try_unprefix(pfx, s.text) match {
          case Some(text) => Seq(text, s.bytes.subSequence(pfx.length, s.bytes.length))
          case None => s
        }

      val Separator = """--(.*)""".r

      s.split_one(HTTP.NEWLINE) match {
        case Some(Seq(Separator(sep), _), rest) =>
          val Param = """Content-Disposition: form-data; name="([^"]+)"""".r
          val File = """Content-Disposition: form-data; name="([^"]+)"; filename="([^"]+)"""".r

          def parts(body: Seq): Option[List[Data]] =
            for {
              (first_line, more) <- body.split_one(HTTP.NEWLINE)
              more1 = perhaps_unprefix(HTTP.NEWLINE, more)
              (value, rest) <- more1.split_one(HTTP.NEWLINE + "--" + sep)
              rest1 = perhaps_unprefix(HTTP.NEWLINE, rest)
            } yield first_line.text match {
              case Param(name) =>
                Multi_Part.Param(name, Line.normalize(value.text)) :: parts(rest1).getOrElse(Nil)
              case File(name, file_name) =>
                value.split_one(HTTP.NEWLINE + HTTP.NEWLINE) match {
                  case Some(_, content) =>
                    Multi_Part.File(name, file_name, content.bytes) :: parts(rest1).getOrElse(Nil)
                  case _ => parts(rest1).getOrElse(Nil)
                }
              case _ => Nil
            }

          parts(rest).getOrElse(Nil)
        case _ => Nil
      }
    }
  }


  /* request parameters as structured data */

  object Params {
    def key(s: String): Key = Key(List(Key.elem(s)))

    object Key {
      sealed trait Elem { def print: String }

      class Nested_Elem private[Key](val rep: String) extends Elem {
        override def equals(that: Any): Boolean =
          that match {
            case other: Nested_Elem => rep == other.rep
            case _ => false
          }
        override def hashCode(): Int = rep.hashCode

        def print: String = rep
        override def toString: String = print
      }

      class List_Elem private[Key](val rep: Int) extends Elem {
        override def equals(that: Any): Boolean =
          that match {
            case other: List_Elem => rep == other.rep
            case _ => false
          }
        override def hashCode(): Int = rep.hashCode

        def print: String = rep.toString
        override def toString: String = print
      }

      def elem(s: String): Elem =
        if (s.contains('/')) error("Illegal separator in " + quote(s))
        else {
          for {
            c <- s
            if Symbol.is_ascii_blank(c)
          } error("Illegal blank character " + c.toInt + " in " + quote(s))
          s match {
            case Value.Int(i) => new List_Elem(i)
            case s => new Nested_Elem(s)
          }
        }

      def elem(i: Int): List_Elem = if (i < 0) error("Illegal list element") else new List_Elem(i)

      def is_blank(es: List[Elem]): Boolean = es.length <= 1 && es.forall(_.print.isBlank)
      def apply(es: List[Elem]): Key = if (is_blank(es)) error("Empty key") else new Key(es)

      def explode(s: String): Key = Key(space_explode('/', s).map(elem))


      /* ordering */

      object Ordering extends scala.math.Ordering[Key] {
        def compare(key1: Key, key2: Key): Int = key1.print.compareTo(key2.print)
      }
    }

    class Key(private val rep: List[Key.Elem]) {
      def +(elem: Key.Elem): Key = Key(rep :+ elem)
      def +(i: Int): Key = this + Key.elem(i)
      def +(s: String): Key = this + Key.elem(s)
      def +(key: Key) = Key(rep ++ key.rep)

      def num: Option[Int] =
        rep match {
          case (e: Key.List_Elem) :: _ => Some(e.rep)
          case _ => None
        }

      def get(key: Key): Option[Key] =
        if (!rep.startsWith(key.rep)) None
        else {
          val rest = rep.drop(key.rep.length)
          if (Key.is_blank(rest)) None
          else Some(Key(rest))
        }

      def print = rep.map(_.print).mkString("/")

      override def toString: String = print
      override def equals(that: Any): Boolean =
        that match {
          case other: Key => rep == other.rep
          case _ => false
        }
      override def hashCode(): Int = rep.hashCode()
    }

    def indexed[A, B](key: Key, xs: List[A], f: (Key, A) => B): List[B] =
      for ((x, i) <- xs.zipWithIndex) yield f(key + i, x)


    object Data {
      def from_multipart(parts: List[Multi_Part.Data]): Data = {
        val files = parts.collect { case f: Multi_Part.File => f }
        val params =
          parts.collect { case Multi_Part.Param(name, value) => Key.explode(name) -> value }
        val file_params = files.map(file => Key.explode(file.name) -> file.file_name)
        val file_files = files.map(file => Key.explode(file.name) -> file.content)

        new Data(
          SortedMap.from(params ++ file_params)(Key.Ordering),
          SortedMap.from(file_files)(Key.Ordering))
      }
    }

    class Data private(params: SortedMap[Key, String], files: SortedMap[Key, Bytes]) {
      override def toString: String = "Data(" + params.toString() + "," + files.toString() + ")"

      def get(key: Key): Option[String] = params.get(key)
      def apply(key: Key): String = get(key).getOrElse("")
      def list(key: Key): List[Key] =
        (for {
          key1 <- params.keys.toList
          key2 <- key1.get(key)
          i <- key2.num
        } yield key + i).distinct

      def file(key: Key): Option[Bytes] = files.get(key)
    }
  }


  /* API with backend base path, and application url (e.g. for frontend links). */

  case class Paths(
    frontend: Url,
    api_base: Path,
    serve_frontend: Boolean = false,
    landing: Path = Path.current
  ) {
    def api_path(path: Path, external: Boolean = true): Path =
      (if (serve_frontend) Path.explode("backend") else Path.current) +
        (if (external) api_base else Path.current) + path

    def route(path: Path, params: Properties.T = Nil): String = {
      def param(p: Properties.Entry): String = Url.encode(p._1) + "=" + Url.encode(p._2)
      if (params.isEmpty) path.implode else path.implode + "?" + params.map(param).mkString("&")
    }

    def api_route(path: Path, params: Properties.T = Nil, external: Boolean = true): String =
      "/" + route(api_path(path, external = external), params)

    def frontend_url(path: Path, params: Properties.T = Nil): Url =
      frontend.resolve(route(path, params))
  }

  abstract class Server[A](
    paths: Paths,
    port: Int = 0,
    verbose: Boolean = false,
    progress: Progress = new Progress(),
  ) {
    def render(model: A): XML.Body
    val error_model: A
    val endpoints: List[API_Endpoint]
    val head: XML.Body


    /* public-facing endpoints */

    sealed abstract class Endpoint(path: Path, method: String = "GET")
      extends HTTP.Service(path.implode, method) {

      def reply(request: HTTP.Request): HTTP.Response

      def html(head: XML.Elem, body: XML.Elem): HTTP.Response =
        HTTP.Response.html(
          cat_lines(
            List(
              HTML.header,
              HTML.output(head, hidden = true, structural = true),
              HTML.output(body, hidden = true, structural = true),
              HTML.footer)))

      final def apply(request: HTTP.Request): Option[HTTP.Response] =
        Exn.capture(reply(request)) match {
          case Exn.Res(res) => Some(res)
          case Exn.Exn(exn) =>
            val id = UUID.random_string()
            progress.echo_error_message("Internal error <" + id + ">: " + exn)
            error("Internal server error. ID: " + id)
        }
    }

    class UI(path: Path) extends Endpoint(path, "GET") {
      def reply(request: HTTP.Request): HTTP.Response = {
        progress.echo_if(verbose, "GET ui")

        val on_load = """
(function() {
  window.addEventListener('message', (event) => {
    if (Number.isInteger(event.data)) {
      this.style.height=event.data + 'px'
    }
  })
}).call(this)"""

        val set_src = """
const base = '""" + paths.frontend.toString.replace("/", "\\/") + """'
document.getElementById('iframe').src = base + '""" + paths.api_route(path).replace("/", "\\/") + """' + window.location.search"""

        html(
          XML.elem("head", HTML.head_meta :: head),
          XML.Elem(Markup("body", List("style" -> "height: fit-content")), List(
            XML.Elem(
              Markup(
                "iframe",
                List(
                  "id" -> "iframe",
                  "name" -> "iframe",
                  "style" -> "border-style: none; width: 100%",
                  "onload" -> on_load)),
              HTML.text("content")),
            HTML.script(set_src))))
      }
    }

    sealed abstract class API_Endpoint(path: Path, method: String = "GET")
      extends Endpoint(paths.api_path(path, external = false), method) {

      def html_content(content: XML.Body, auto_reload: Boolean = false): HTTP.Response = {
        val auto_reload_script = HTML.script("""
var state = null
function heartbeat() {
  fetch(window.location, { method: "HEAD" }).then((http_res) => {
    if (http_res.status === 200) {
      const new_state = http_res.headers.get("Content-Digest")
      if (state === null) state = new_state
      else if (state !== new_state) window.location.reload()
    }
    setTimeout(heartbeat, 1000)
  })
}
heartbeat()""")

        val resize_script = HTML.script("""
function post_height() {
  const scroll_bar_height = window.innerHeight - document.documentElement.clientHeight
  parent.postMessage(document.documentElement.scrollHeight + scroll_bar_height, '*')
}
window.addEventListener("resize", (event) => { post_height() })
""")

        val head1 = (if (auto_reload) List(auto_reload_script) else Nil) ::: resize_script :: head

        html(
          XML.elem("head", HTML.head_meta :: head1),
          XML.Elem(Markup("body", List("onLoad" -> "post_height()")), content))
      }
    }

    private def query_params(request: HTTP.Request): Properties.T = {
      def decode(s: String): Option[Properties.Entry] =
        s match {
          case Properties.Eq(k, v) => Some(Url.decode(k) -> Url.decode(v))
          case _ => None
        }

      Library.try_unprefix(request.query, request.uri_name).toList.flatMap(params =>
        space_explode('&', params).flatMap(decode))
    }


    /* endpoint types */

    class Get(val path: Path, description: String, get: Properties.T => Option[A])
      extends API_Endpoint(path) {

      def reply(request: HTTP.Request): HTTP.Response = {
        progress.echo_if(verbose, "GET " + description)

        val params = query_params(request)
        progress.echo_if(verbose, "params: " + params.toString())

        val model =
          get(params) match {
            case Some(model) => model
            case None =>
              progress.echo_if(verbose, "Parsing failed")
              error_model
          }

        html_content(render(model), auto_reload = true)
      }
    }

    class Get_File(path: Path, description: String, download: Properties.T => Option[Path])
      extends API_Endpoint(path) {

      def reply(request: HTTP.Request): HTTP.Response = {
        progress.echo_if(verbose, "DOWNLOAD " + description)

        val params = query_params(request)
        progress.echo_if(verbose, "params: " + params.toString())

        download(params) match {
          case Some(path) => HTTP.Response.content(HTTP.Content.read(path))
          case None =>
            progress.echo_if(verbose, "Fetching file path failed")
            html_content(render(error_model))
        }
      }
    }

    class Post(path: Path, description: String, post: Params.Data => Option[A])
      extends API_Endpoint(path, method = "POST") {

      def reply(request: HTTP.Request): HTTP.Response = {
        progress.echo_if(verbose, "POST " + description)

        val parts = Multi_Part.parse(request.input)
        val params = Params.Data.from_multipart(parts)
        progress.echo_if(verbose, "params: " + params.toString)

        val model =
          post(params) match {
            case Some(model) => model
            case None =>
              progress.echo_if(verbose, "Parsing failed")
              error_model
          }

        html_content(render(model))
      }
    }


    /* server */

    private def ui_endpoints =
      if (paths.serve_frontend) endpoints.collect { case page: Get => new UI(page.path) } else Nil

    private lazy val server =
      HTTP.server(port = port, name = "", services = endpoints ::: ui_endpoints)

    def run(): Unit = {
      start()

      @tailrec
      def loop(): Unit = {
        Thread.sleep(Long.MaxValue)
        loop()
      }

      Isabelle_Thread.interrupt_handler(_ => server.stop()) { loop() }
    }

    def start(): Unit = {
      server.start()
      progress.echo("Server started on " + paths.frontend_url(paths.landing))
    }

    def stop(): Unit = {
      server.stop()
      progress.echo("Server stopped")
    }
  }
}