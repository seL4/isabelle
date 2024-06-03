/*  Title:      Pure/General/http.scala
    Author:     Makarius

HTTP client and server support.
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.Files
import java.net.{InetSocketAddress, URI, HttpURLConnection}
import java.util.HexFormat
import com.sun.net.httpserver.{HttpExchange, HttpHandler, HttpServer}


object HTTP {
  /** content **/

  object Content {
    val mime_type_bytes: String = "application/octet-stream"
    val mime_type_text: String = "text/plain; charset=utf-8"
    val mime_type_html: String = "text/html; charset=utf-8"

    val default_mime_type: String = mime_type_bytes
    val default_encoding: String = UTF8.charset.name

    def apply(
        bytes: Bytes,
        file_name: String = "",
        mime_type: String = default_mime_type,
        encoding: String = default_encoding,
        elapsed_time: Time = Time.zero): Content =
      new Content(bytes, file_name, mime_type, encoding, elapsed_time)

    def read(file: JFile): Content = {
      val bytes = Bytes.read(file)
      val file_name = file.getName
      val mime_type = Option(Files.probeContentType(file.toPath)).getOrElse(default_mime_type)
      apply(bytes, file_name = file_name, mime_type = mime_type)
    }

    def read(path: Path): Content = read(path.file)
  }

  class Content private(
    val bytes: Bytes,
    val file_name: String,
    val mime_type: String,
    val encoding: String,
    val elapsed_time: Time
  ) {
    def text: String = new String(bytes.array, encoding)
    def json: JSON.T = JSON.parse(text)
  }



  /** client **/

  val NEWLINE: String = "\r\n"

  object Client {
    val default_timeout: Time = Time.seconds(180)

    def open_connection(
      url: Url,
      timeout: Time = default_timeout,
      user_agent: String = ""
    ): HttpURLConnection = {
      url.open_connection() match {
        case connection: HttpURLConnection =>
          if (0 < timeout.ms && timeout.ms <= Int.MaxValue) {
            val ms = timeout.ms.toInt
            connection.setConnectTimeout(ms)
            connection.setReadTimeout(ms)
          }
          proper_string(user_agent).foreach(s => connection.setRequestProperty("User-Agent", s))
          connection
        case _ => error("Bad URL (not HTTP): " + quote(url.toString))
      }
    }

    def get_content(connection: HttpURLConnection): Content = {
      val Charset = """.*\bcharset="?([\S^"]+)"?.*""".r

      val start = Time.now()
      using(connection.getInputStream) { stream =>
        val bytes = Bytes.read_stream(stream, hint = connection.getContentLength)
        val stop = Time.now()

        val file_name = Url.file_name(Url(connection.getURL.toURI))
        val mime_type = Option(connection.getContentType).getOrElse(Content.default_mime_type)
        val encoding =
          (connection.getContentEncoding, mime_type) match {
            case (enc, _) if enc != null => enc
            case (_, Charset(enc)) => enc
            case _ => Content.default_encoding
          }
        Content(bytes, file_name = file_name, mime_type = mime_type,
          encoding = encoding, elapsed_time = stop - start)
      }
    }

    def get(url: Url, timeout: Time = default_timeout, user_agent: String = ""): Content =
      get_content(open_connection(url, timeout = timeout, user_agent = user_agent))

    def post(
      url: Url,
      parameters: List[(String, Any)],
      timeout: Time = default_timeout,
      user_agent: String = ""
    ): Content = {
      val connection = open_connection(url, timeout = timeout, user_agent = user_agent)
      connection.setRequestMethod("POST")
      connection.setDoOutput(true)

      val boundary = UUID.random_string()
      connection.setRequestProperty(
        "Content-Type", "multipart/form-data; boundary=" + quote(boundary))

      using(connection.getOutputStream) { out =>
        def output(s: String): Unit = out.write(UTF8.bytes(s))
        def output_newline(n: Int = 1): Unit = (1 to n).foreach(_ => output(NEWLINE))
        def output_boundary(end: Boolean = false): Unit =
          output("--" + boundary + (if (end) "--" else "") + NEWLINE)
        def output_name(name: String): Unit =
          output("Content-Disposition: form-data; name=" + quote(name))
        def output_value(value: Any): Unit = {
          output_newline(2)
          output(value.toString)
        }
        def output_content(content: Content): Unit = {
          proper_string(content.file_name).foreach(s => output("; filename=" + quote(s)))
          output_newline()
          proper_string(content.mime_type).foreach(s => output("Content-Type: " + s))
          output_newline(2)
          content.bytes.write_stream(out)
        }

        output_newline(2)

        for { (name, value) <- parameters } {
          output_boundary()
          output_name(name)
          value match {
            case content: Content => output_content(content)
            case file: JFile => output_content(Content.read(file))
            case path: Path => output_content(Content.read(path))
            case _ => output_value(value)
          }
          output_newline()
        }
        output_boundary(end = true)
        out.flush()
      }

      get_content(connection)
    }
  }



  /** server **/

  /* request */

  def url_path(names: String*): String =
    names.iterator.flatMap(a => if (a.isEmpty) None else Some("/" + a)).mkString

  class Request private[HTTP](
    val server_name: String,
    val service_name: String,
    val uri: URI,
    val input: Bytes
  ) {
    def home: String = url_path(server_name, service_name)
    def root: String = home + "/"
    def query: String = home + "?"

    def toplevel: Boolean = uri_name == home || uri_name == root

    val uri_name: String = uri.toString

    def uri_path: Option[Path] =
      for {
        s <- Option(uri.getPath).flatMap(Library.try_unprefix(root, _))
        if Path.is_wellformed(s)
        p = Path.explode(s) if p.all_basic
      } yield p

    def decode_query: Option[String] =
      Library.try_unprefix(query, uri_name).map(Url.decode)

    def decode_properties: Properties.T =
      space_explode('&', input.text).map(
        {
          case Properties.Eq(a, b) => Url.decode(a) -> Url.decode(b)
          case s => error("Malformed key-value pair in HTTP/POST: " + quote(s))
        })
  }


  /* response */

  object Response {
    def apply(
        bytes: Bytes = Bytes.empty,
        content_type: String = Content.mime_type_bytes): Response =
      new Response(bytes, content_type)

    val empty: Response = apply()
    def text(s: String): Response = apply(Bytes(s), Content.mime_type_text)
    def html(s: String): Response = apply(Bytes(s), Content.mime_type_html)

    def content(content: Content): Response = apply(content.bytes, content.mime_type)
    def read(file: JFile): Response = content(Content.read(file))
    def read(path: Path): Response = content(Content.read(path))
  }

  class Response private[HTTP](val output: Bytes, val content_type: String) {
    override def toString: String = output.toString

    def write(http: HttpExchange, code: Int, is_head: Boolean = false): Unit = {
      http.getResponseHeaders.set("Content-Type", content_type)
      if (is_head) {
        val encoded_digest = Base64.encode(HexFormat.of().parseHex(SHA1.digest(output).toString))
        http.getResponseHeaders.set("Content-Digest", "sha=:" + encoded_digest + ":")
      }
      http.sendResponseHeaders(code, if (is_head) -1 else output.length.toLong)
      if (!is_head) using(http.getResponseBody)(output.write_stream)
    }
  }


  /* service */

  abstract class Service(val name: String, method: String = "GET") {
    override def toString: String = name

    def apply(request: Request): Option[Response]

    def context(server_name: String): String =
      proper_string(url_path(server_name, name)).getOrElse("/")

    def handler(server_name: String): HttpHandler = { (http: HttpExchange) =>
      val uri = http.getRequestURI
      val input = using(http.getRequestBody)(Bytes.read_stream(_))
      val is_head = http.getRequestMethod == "HEAD" && method == "GET"
      if (http.getRequestMethod == method || is_head) {
        val request = new Request(server_name, name, uri, input)
        Exn.result(apply(request)) match {
          case Exn.Res(Some(response)) =>
            response.write(http, 200, is_head)
          case Exn.Res(None) =>
            Response.empty.write(http, 404, is_head)
          case Exn.Exn(ERROR(msg)) =>
            Response.text(Output.error_message_text(msg)).write(http, 500, is_head)
          case Exn.Exn(exn) => throw exn
        }
      }
      else Response.empty.write(http, 400)
    }
  }


  /* server */

  class Server private[HTTP](val name: String, val http_server: HttpServer) {
    def += (service: Service): Unit =
      http_server.createContext(service.context(name), service.handler(name))
    def -= (service: Service): Unit =
      http_server.removeContext(service.context(name))

    def start(): Unit = http_server.start()
    def stop(): Unit = http_server.stop(0)

    def address: InetSocketAddress = http_server.getAddress

    def url: String = "http://" + address.getHostName + ":" + address.getPort + url_path(name)
    override def toString: String = url
  }

  def server(
    port: Int = 0,
    name: String = UUID.random_string(),
    services: List[Service] = isabelle_services
  ): Server = {
    val http_server = HttpServer.create(new InetSocketAddress(isabelle.Server.localhost, port), 0)
    http_server.setExecutor(null)

    val server = new Server(name, http_server)
    for (service <- services) server += service
    server
  }



  /** Isabelle services **/

  def isabelle_services: List[Service] =
    List(Welcome_Service, Fonts_Service, PDFjs_Service, Docs_Service)


  /* welcome */

  object Welcome_Service extends Welcome()

  class Welcome(name: String = "") extends Service(name) {
    def apply(request: Request): Option[Response] =
      if (request.toplevel) {
        Some(Response.text("Welcome to " + Isabelle_System.identification()))
      }
      else None
  }


  /* fonts */

  object Fonts_Service extends Fonts()

  class Fonts(name: String = "fonts") extends Service(name) {
    private lazy val html_fonts: List[Isabelle_Fonts.Entry] =
      Isabelle_Fonts.fonts(hidden = true)

    def apply(request: Request): Option[Response] =
      if (request.toplevel) {
        Some(Response.text(cat_lines(html_fonts.map(entry => entry.path.file_name))))
      }
      else {
        request.uri_path.flatMap(path =>
          html_fonts.collectFirst(
            { case entry if path == entry.path.base => Response(entry.bytes) }
          ))
      }
  }


  /* pdfjs */

  object PDFjs_Service extends PDFjs()

  class PDFjs(name: String = "pdfjs") extends Service(name) {
    def apply(request: Request): Option[Response] =
      for {
        p <- request.uri_path
        path = Path.explode("$ISABELLE_PDFJS_HOME") + p if path.is_file
        s = p.implode if s.startsWith("build/") || s.startsWith("web/")
      } yield Response.read(path)
  }


  /* docs */

  object Docs_Service extends Docs()

  class Docs(name: String = "docs") extends PDFjs(name) {
    private val doc_contents = isabelle.Doc.main_contents()

    // example: .../docs/web/viewer.html?file=system.pdf
    def doc_request(request: Request): Option[Response] =
      for {
        p <- request.uri_path if p.is_pdf
        s = p.implode if s.startsWith("web/")
        name = p.base.split_ext._1.implode
        doc <- doc_contents.docs.find(_.name == name)
      } yield Response.read(doc.path)

    override def apply(request: Request): Option[Response] =
      doc_request(request) orElse super.apply(request)
  }
}
