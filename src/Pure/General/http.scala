/*  Title:      Pure/General/http.scala
    Author:     Makarius

HTTP client and server support.
*/

package isabelle


import java.io.{File => JFile}
import java.net.{InetSocketAddress, URI, URL, URLConnection, HttpURLConnection}
import com.sun.net.httpserver.{HttpExchange, HttpHandler, HttpServer}


object HTTP
{
  /** content **/

  val mime_type_bytes: String = "application/octet-stream"
  val mime_type_text: String = "text/plain; charset=utf-8"
  val mime_type_html: String = "text/html; charset=utf-8"

  val default_mime_type: String = mime_type_bytes
  val default_encoding: String = UTF8.charset_name

  sealed case class Content(
    bytes: Bytes,
    file_name: String = "",
    mime_type: String = default_mime_type,
    encoding: String = default_encoding,
    elapsed_time: Time = Time.zero)
  {
    def text: String = new String(bytes.array, encoding)
  }

  def read_content(file: JFile): Content =
  {
    val bytes = Bytes.read(file)
    val file_name = file.getName
    val mime_type =
      Option(URLConnection.guessContentTypeFromName(file_name)).getOrElse(default_mime_type)
    Content(bytes, file_name = file_name, mime_type = mime_type)
  }

  def read_content(path: Path): Content = read_content(path.file)



  /** client **/

  val NEWLINE: String = "\r\n"

  object Client
  {
    val default_timeout: Time = Time.seconds(180)

    def open_connection(url: URL,
      timeout: Time = default_timeout,
      user_agent: String = ""): HttpURLConnection =
    {
      url.openConnection match {
        case connection: HttpURLConnection =>
          if (0 < timeout.ms && timeout.ms <= Integer.MAX_VALUE) {
            val ms = timeout.ms.toInt
            connection.setConnectTimeout(ms)
            connection.setReadTimeout(ms)
          }
          proper_string(user_agent).foreach(s => connection.setRequestProperty("User-Agent", s))
          connection
        case _ => error("Bad URL (not HTTP): " + quote(url.toString))
      }
    }

    def get_content(connection: HttpURLConnection): Content =
    {
      val Charset = """.*\bcharset="?([\S^"]+)"?.*""".r

      val start = Time.now()
      using(connection.getInputStream)(stream =>
      {
        val bytes = Bytes.read_stream(stream, hint = connection.getContentLength)
        val stop = Time.now()

        val file_name = Url.file_name(connection.getURL)
        val mime_type = Option(connection.getContentType).getOrElse(default_mime_type)
        val encoding =
          (connection.getContentEncoding, mime_type) match {
            case (enc, _) if enc != null => enc
            case (_, Charset(enc)) => enc
            case _ => default_encoding
          }
        Content(bytes, file_name = file_name, mime_type = mime_type,
          encoding = encoding, elapsed_time = stop - start)
      })
    }

    def get(url: URL, timeout: Time = default_timeout, user_agent: String = ""): Content =
      get_content(open_connection(url, timeout = timeout, user_agent = user_agent))

    def post(url: URL, parameters: List[(String, Any)],
      timeout: Time = default_timeout,
      user_agent: String = ""): Content =
    {
      val connection = open_connection(url, timeout = timeout, user_agent = user_agent)
      connection.setRequestMethod("POST")
      connection.setDoOutput(true)

      val boundary = UUID.random_string()
      connection.setRequestProperty(
        "Content-Type", "multipart/form-data; boundary=" + quote(boundary))

      using(connection.getOutputStream)(out =>
      {
        def output(s: String): Unit = out.write(UTF8.bytes(s))
        def output_newline(n: Int = 1): Unit = (1 to n).foreach(_ => output(NEWLINE))
        def output_boundary(end: Boolean = false): Unit =
          output("--" + boundary + (if (end) "--" else "") + NEWLINE)
        def output_name(name: String): Unit =
          output("Content-Disposition: form-data; name=" + quote(name))
        def output_value(value: Any): Unit =
        {
          output_newline(2)
          output(value.toString)
        }
        def output_content(content: Content): Unit =
        {
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
            case file: JFile => output_content(read_content(file))
            case path: Path => output_content(read_content(path))
            case _ => output_value(value)
          }
          output_newline()
        }
        output_boundary(end = true)
        out.flush()
      })

      get_content(connection)
    }
  }



  /** server **/

  /* response */

  object Response
  {
    def apply(
        bytes: Bytes = Bytes.empty,
        content_type: String = mime_type_bytes): Response =
      new Response(bytes, content_type)

    val empty: Response = apply()
    def text(s: String): Response = apply(Bytes(s), mime_type_text)
    def html(s: String): Response = apply(Bytes(s), mime_type_html)
  }

  class Response private[HTTP](val bytes: Bytes, val content_type: String)
  {
    override def toString: String = bytes.toString
  }


  /* exchange */

  class Exchange private[HTTP](val http_exchange: HttpExchange)
  {
    def request_method: String = http_exchange.getRequestMethod
    def request_uri: URI = http_exchange.getRequestURI

    def read_request(): Bytes =
      using(http_exchange.getRequestBody)(Bytes.read_stream(_))

    def write_response(code: Int, response: Response): Unit =
    {
      http_exchange.getResponseHeaders.set("Content-Type", response.content_type)
      http_exchange.sendResponseHeaders(code, response.bytes.length.toLong)
      using(http_exchange.getResponseBody)(response.bytes.write_stream)
    }
  }


  /* handler for request method */

  sealed case class Arg(method: String, uri: URI, request: Bytes)
  {
    def decode_properties: Properties.T =
      space_explode('&', request.text).map(s =>
        space_explode('=', s) match {
          case List(a, b) => Url.decode(a) -> Url.decode(b)
          case _ => error("Malformed key-value pair in HTTP/POST: " + quote(s))
        })
  }

  object Handler
  {
    def apply(root: String, body: Exchange => Unit): Handler =
      new Handler(root, (x: HttpExchange) => body(new Exchange(x)))

    def method(name: String, root: String, body: Arg => Option[Response]): Handler =
      apply(root, http =>
        {
          val request = http.read_request()
          if (http.request_method == name) {
            val arg = Arg(name, http.request_uri, request)
            Exn.capture(body(arg)) match {
              case Exn.Res(Some(response)) =>
                http.write_response(200, response)
              case Exn.Res(None) =>
                http.write_response(404, Response.empty)
              case Exn.Exn(ERROR(msg)) =>
                http.write_response(500, Response.text(Output.error_message_text(msg)))
              case Exn.Exn(exn) => throw exn
            }
          }
          else http.write_response(400, Response.empty)
        })

    def get(root: String, body: Arg => Option[Response]): Handler = method("GET", root, body)
    def post(root: String, body: Arg => Option[Response]): Handler = method("POST", root, body)
  }

  class Handler private(val root: String, val handler: HttpHandler)
  {
    override def toString: String = root
  }


  /* server */

  class Server private[HTTP](val http_server: HttpServer)
  {
    def += (handler: Handler): Unit = http_server.createContext(handler.root, handler.handler)
    def -= (handler: Handler): Unit = http_server.removeContext(handler.root)

    def start(): Unit = http_server.start()
    def stop(): Unit = http_server.stop(0)

    def address: InetSocketAddress = http_server.getAddress
    def url: String = "http://" + address.getHostName + ":" + address.getPort
    override def toString: String = url
  }

  def server(handlers: List[Handler] = isabelle_resources): Server =
  {
    val http_server = HttpServer.create(new InetSocketAddress(isabelle.Server.localhost, 0), 0)
    http_server.setExecutor(null)

    val server = new Server(http_server)
    for (handler <- handlers) server += handler
    server
  }



  /** Isabelle resources **/

  lazy val isabelle_resources: List[Handler] =
    List(welcome(), fonts())


  /* welcome */

  def welcome(root: String = "/"): Handler =
    Handler.get(root, arg =>
      if (arg.uri.toString == root) {
        val id = Isabelle_System.isabelle_id()
        Some(Response.text("Welcome to Isabelle/" + id + Isabelle_System.isabelle_heading()))
      }
      else None)


  /* fonts */

  private lazy val html_fonts: List[Isabelle_Fonts.Entry] =
    Isabelle_Fonts.fonts(hidden = true)

  def fonts(root: String = "/fonts"): Handler =
    Handler.get(root, arg =>
      {
        val uri_name = arg.uri.toString
        if (uri_name == root) {
          Some(Response.text(cat_lines(html_fonts.map(entry => entry.path.file_name))))
        }
        else {
          html_fonts.collectFirst(
            { case entry if uri_name == root + "/" + entry.path.file_name => Response(entry.bytes) })
        }
      })
}
