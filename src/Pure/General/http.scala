/*  Title:      Pure/General/http.scala
    Author:     Makarius

HTTP server support.
*/

package isabelle


import java.net.{InetAddress, InetSocketAddress, URI}
import com.sun.net.httpserver.{HttpExchange, HttpHandler, HttpServer}


object HTTP
{
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

    def write_response(code: Int, response: Response)
    {
      http_exchange.getResponseHeaders().set("Content-Type", response.content_type)
      http_exchange.sendResponseHeaders(code, response.bytes.length.toLong)
      using(http_exchange.getResponseBody)(response.bytes.write_stream(_))
    }
  }


  /* handler */

  class Handler private[HTTP](val path: String, val handler: HttpHandler)
  {
    override def toString: String = path
  }

  def handler(path: String, body: Exchange => Unit): Handler =
    new Handler(path, new HttpHandler { def handle(x: HttpExchange) { body(new Exchange(x)) } })

  def get(path: String, body: URI => Option[Response]): Handler =
    handler(path, http =>
      {
        http.read_request()
        if (http.request_method == "GET")
          body(http.request_uri) match {
            case None => http.write_response(404, Response.empty)
            case Some(response) => http.write_response(200, response)
          }
        else http.write_response(400, Response.empty)
      })


  /* server */

  class Server private[HTTP](val http_server: HttpServer)
  {
    def += (handler: Handler) { http_server.createContext(handler.path, handler.handler) }
    def -= (handler: Handler) { http_server.removeContext(handler.path) }

    def start: Unit = http_server.start
    def stop: Unit = http_server.stop(0)

    def address: InetSocketAddress = http_server.getAddress
    def url: String = "http://" + address.getHostName + ":" + address.getPort
    override def toString: String = url
  }

  def server(handlers: Handler*): Server =
  {
    val localhost = InetAddress.getByName("127.0.0.1")
    val http_server = HttpServer.create(new InetSocketAddress(localhost, 0), 0)
    http_server.setExecutor(null)

    val server = new Server(http_server)
    for (handler <- handlers) server += handler
    server
  }
}
