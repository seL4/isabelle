/*  Title:      Pure/General/http.scala
    Author:     Makarius

HTTP server support.
*/

package isabelle


import java.net.{InetAddress, InetSocketAddress}
import com.sun.net.httpserver.{HttpExchange, HttpHandler, HttpServer}


object HTTP
{
  /* handler */

  class Handler private[HTTP](val path: String, val handler: HttpHandler)
  {
    override def toString: String = path
  }

  def handler(path: String, body: HttpExchange => Unit): Handler =
    new Handler(path, new HttpHandler { def handle(x: HttpExchange) { body(x) } })


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
