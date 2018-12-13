/*  Title:      Pure/System/system_channel.scala
    Author:     Makarius

Socket-based system channel for inter-process communication.
*/

package isabelle


import java.io.{InputStream, OutputStream}
import java.net.{ServerSocket, InetAddress}


object System_Channel
{
  def apply(): System_Channel = new System_Channel
}

class System_Channel private
{
  private val server = new ServerSocket(0, 50, Server.localhost)

  val server_name: String = Server.print_address(server.getLocalPort)
  override def toString: String = server_name

  def rendezvous(): (OutputStream, InputStream) =
  {
    val socket = server.accept
    (socket.getOutputStream, socket.getInputStream)
  }

  def accepted() { server.close }
}
