/*  Title:      Pure/System/system_channel.scala
    Author:     Makarius

Portable system channel for inter-process communication, based on
named pipes or sockets.
*/

package isabelle


import java.io.{InputStream, OutputStream, File, FileInputStream, FileOutputStream, IOException}
import java.net.{ServerSocket, InetAddress}


object System_Channel
{
  def apply(): System_Channel = new Fifo_Channel
}

abstract class System_Channel
{
  def isabelle_args: List[String]
  def rendezvous(): (OutputStream, InputStream)
  def accepted(): Unit
}


/** named pipes **/

object Fifo_Channel
{
  private val next_fifo = new Counter
}

class Fifo_Channel extends System_Channel
{
  private def mk_fifo(): String =
  {
    val i = Fifo_Channel.next_fifo()
    val script =
      "FIFO=\"/tmp/isabelle-fifo-${PPID}-$$" + i + "\"\n" +
      "echo -n \"$FIFO\"\n" +
      "mkfifo -m 600 \"$FIFO\"\n"
    val (out, err, rc) = Isabelle_System.bash(script)
    if (rc == 0) out else error(err.trim)
  }

  private def rm_fifo(fifo: String): Boolean =
    Isabelle_System.platform_file(
      Path.explode(if (Platform.is_windows) fifo + ".lnk" else fifo)).delete

  private def fifo_input_stream(fifo: String): InputStream =
  {
    if (Platform.is_windows) { // Cygwin fifo as Windows/Java input stream
      val proc =
        Isabelle_System.execute(false,
          Isabelle_System.standard_path(Path.explode("~~/lib/scripts/raw_dump")), fifo, "-")
      proc.getOutputStream.close
      proc.getErrorStream.close
      proc.getInputStream
    }
    else new FileInputStream(fifo)
  }

  private def fifo_output_stream(fifo: String): OutputStream =
  {
    if (Platform.is_windows) { // Cygwin fifo as Windows/Java output stream
      val proc =
        Isabelle_System.execute(false,
          Isabelle_System.standard_path(Path.explode("~~/lib/scripts/raw_dump")), "-", fifo)
      proc.getInputStream.close
      proc.getErrorStream.close
      val out = proc.getOutputStream
      new OutputStream {
        override def close() { out.close(); proc.waitFor() }
        override def flush() { out.flush() }
        override def write(b: Array[Byte]) { out.write(b) }
        override def write(b: Array[Byte], off: Int, len: Int) { out.write(b, off, len) }
        override def write(b: Int) { out.write(b) }
      }
    }
    else new FileOutputStream(fifo)
  }


  private val fifo1 = mk_fifo()
  private val fifo2 = mk_fifo()

  val isabelle_args: List[String] = List ("-W", fifo1 + ":" + fifo2)

  def rendezvous(): (OutputStream, InputStream) =
  {
    val output_stream = fifo_output_stream(fifo1)
    val input_stream = fifo_input_stream(fifo2)
    (output_stream, input_stream)
  }

  def accepted() { rm_fifo(fifo1); rm_fifo(fifo2) }
}


/** sockets **/

class Socket_Channel extends System_Channel
{
  private val server = new ServerSocket(0, 2, InetAddress.getByName("127.0.0.1"))

  def isabelle_args: List[String] = List("-T", "127.0.0.1:" + server.getLocalPort)

  def rendezvous(): (OutputStream, InputStream) =
  {
    val socket = server.accept
    (socket.getOutputStream, socket.getInputStream)
  }

  def accepted() { server.close }
}
