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

  val address: String = Server.print_address(server.getLocalPort)
  val password: String = UUID.random().toString

  override def toString: String = address

  def shutdown(): Unit = server.close()

  def rendezvous(): (OutputStream, InputStream) =
  {
    val socket = server.accept
    try {
      val out_stream = socket.getOutputStream
      val in_stream = socket.getInputStream

      if (Byte_Message.read_line(in_stream).map(_.text) == Some(password)) (out_stream, in_stream)
      else {
        out_stream.close()
        in_stream.close()
        error("Failed to connect system channel: bad password")
      }
    }
    finally { shutdown() }
  }
}
