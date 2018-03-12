/*  Title:      Pure/System/tty_loop.scala
    Author:     Makarius

Line-oriented TTY loop.
*/

package isabelle


import java.io.{IOException, Writer, Reader, InputStreamReader, BufferedReader}


class TTY_Loop(writer: Writer, reader: Reader, interrupt: Option[() => Unit] = None)
{
  private val console_output = Future.thread[Unit]("console_output") {
    try {
      var result = new StringBuilder(100)
      var finished = false
      while (!finished) {
        var c = -1
        var done = false
        while (!done && (result.length == 0 || reader.ready)) {
          c = reader.read
          if (c >= 0) result.append(c.asInstanceOf[Char])
          else done = true
        }
        if (result.length > 0) {
          System.out.print(result.toString)
          System.out.flush()
          result.length = 0
        }
        else {
          reader.close()
          finished = true
        }
      }
    }
    catch { case e: IOException => case Exn.Interrupt() => }
  }

  private val console_input = Future.thread[Unit]("console_input") {
    val console_reader = new BufferedReader(new InputStreamReader(System.in))
    def body
    {
      try {
        var finished = false
        while (!finished) {
          console_reader.readLine() match {
            case null =>
              writer.close()
              finished = true
            case line =>
              writer.write(line)
              writer.write("\n")
              writer.flush()
          }
        }
      }
      catch { case e: IOException => case Exn.Interrupt() => }
    }
    interrupt match {
      case None => body
      case Some(int) => POSIX_Interrupt.handler { int() } { body }
    }
  }

  def join { console_output.join; console_input.join }

  def cancel { console_input.cancel }
}
