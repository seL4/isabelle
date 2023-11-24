/*  Title:      Pure/System/system_channel.scala
    Author:     Makarius

Socket-based system channel for inter-process communication.
*/

package isabelle


import java.io.{InputStream, OutputStream}
import java.net.{InetAddress, InetSocketAddress, ProtocolFamily, ServerSocket, SocketAddress, StandardProtocolFamily, UnixDomainSocketAddress}
import java.nio.channels.{ServerSocketChannel, Channels}


object System_Channel {
  def apply(unix_domain: Boolean = Platform.is_unix): System_Channel =
    if (unix_domain) new Unix else new Inet

  class Inet extends System_Channel(StandardProtocolFamily.INET) {
    server.bind(new InetSocketAddress(Server.localhost, 0), 50)

    override def address: String =
      Server.print_address(server.getLocalAddress.asInstanceOf[InetSocketAddress].getPort)
  }

  class Unix extends System_Channel(StandardProtocolFamily.UNIX) {
    private val socket_file = Isabelle_System.tmp_file("socket", initialized = false)
    private val socket_file_name = socket_file.getPath

    server.bind(UnixDomainSocketAddress.of(socket_file_name))

    override def address: String = socket_file_name
    override def shutdown(): Unit = {
      super.shutdown()
      socket_file.delete
    }
  }
}

abstract class System_Channel private(protocol_family: ProtocolFamily) {
  protected val server: ServerSocketChannel = ServerSocketChannel.open(protocol_family)

  def address: String
  lazy val password: String = UUID.random().toString

  override def toString: String = address

  def shutdown(): Unit = server.close()

  def rendezvous(): (OutputStream, InputStream) = {
    val socket = server.accept
    try {
      val out_stream = Channels.newOutputStream(socket)
      val in_stream = Channels.newInputStream(socket)

      Byte_Message.read_line(in_stream) match {
        case Some(bs) if bs.text == password => (out_stream, in_stream)
        case _ =>
          out_stream.close()
          in_stream.close()
          error("Failed to connect system channel: bad password")
      }
    }
    finally { shutdown() }
  }
}
