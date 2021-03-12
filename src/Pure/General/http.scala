/*  Title:      Pure/General/http.scala
    Author:     Makarius

HTTP server support.
*/

package isabelle


import java.net.{InetSocketAddress, URI, URL}
import com.sun.net.httpserver.{HttpExchange, HttpHandler, HttpServer}


object HTTP
{
  /** content **/

  val default_mime_type: String = "application/octet-stream"

  sealed case class Content(bytes: Bytes, mime_type: String = default_mime_type)
  {
    def text: String = bytes.text
  }



  /** client **/

  object Client
  {
    def get(url: URL): Content =
    {
      val connection = url.openConnection
      using(connection.getInputStream)(stream =>
      {
        val length = connection.getContentLength
        val mime_type = Option(connection.getContentType).getOrElse(default_mime_type)
        val bytes = Bytes.read_stream(stream, hint = length)
        Content(bytes, mime_type = mime_type)
      })
    }
  }



  /** server **/

  /* response */

  object Response
  {
    def apply(
        bytes: Bytes = Bytes.empty,
        content_type: String = "application/octet-stream"): Response =
      new Response(bytes, content_type)

    val empty: Response = apply()
    def text(s: String): Response = apply(Bytes(s), "text/plain; charset=utf-8")
    def html(s: String): Response = apply(Bytes(s), "text/html; charset=utf-8")
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
      http_exchange.getResponseHeaders().set("Content-Type", response.content_type)
      http_exchange.sendResponseHeaders(code, response.bytes.length.toLong)
      using(http_exchange.getResponseBody)(response.bytes.write_stream(_))
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
      new Handler(root,
        new HttpHandler { def handle(x: HttpExchange): Unit = body(new Exchange(x)) })

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

    def start(): Unit = http_server.start
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
    List(welcome, fonts())


  /* welcome */

  val welcome: Handler =
    Handler.get("/", arg =>
      if (arg.uri.toString == "/") {
        val id = Isabelle_System.isabelle_id()
        Some(Response.text("Welcome to Isabelle/" + id + ": " + Distribution.version))
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
