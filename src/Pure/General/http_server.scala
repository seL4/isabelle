/*  Title:      Pure/General/http_server.scala
    Author:     Makarius

Minimal HTTP server.
*/

package isabelle


import java.net.{InetAddress, InetSocketAddress}
import com.sun.net.httpserver.{HttpExchange, HttpHandler, HttpServer}


object HTTP_Server
{
  class Handler private[HTTP_Server](val path: String, val handler: HttpHandler)
  {
    override def toString: String = path
  }

  def handler(path: String)(body: HttpExchange => Unit): Handler =
    new Handler(path, new HttpHandler { def handle(x: HttpExchange) { body(x) } })

  def apply(handlers: Handler*): HTTP_Server =
  {
    val localhost = InetAddress.getByName("127.0.0.1")

    val server = HttpServer.create(new InetSocketAddress(localhost, 0), 0)
    server.setExecutor(null)

    val http_server = new HTTP_Server(server)
    for (handler <- handlers) http_server += handler
    http_server
  }
}

class HTTP_Server private(val server: HttpServer)
{
  def += (handler: HTTP_Server.Handler) { server.createContext(handler.path, handler.handler) }
  def -= (handler: HTTP_Server.Handler) { server.removeContext(handler.path) }

  def start: Unit = server.start
  def stop: Unit = server.stop(0)

  def address: InetSocketAddress = server.getAddress
  def url: String = "http://" + address.getHostName + ":" + address.getPort
  override def toString: String = url
}
