/*  Title:      Pure/System/tty_loop.scala
    Author:     Makarius

Line-oriented TTY loop.
*/

package isabelle


import java.io.{IOException, BufferedReader, BufferedWriter, InputStreamReader}


class TTY_Loop(
  process_writer: BufferedWriter,
  process_reader: BufferedReader,
  process_interrupt: Option[() => Unit] = None)
{
  private val console_output = Future.thread[Unit]("console_output") {
    try {
      var result = new StringBuilder(100)
      var finished = false
      while (!finished) {
        var c = -1
        var done = false
        while (!done && (result.length == 0 || process_reader.ready)) {
          c = process_reader.read
          if (c >= 0) result.append(c.asInstanceOf[Char])
          else done = true
        }
        if (result.length > 0) {
          System.out.print(result.toString)
          System.out.flush()
          result.length = 0
        }
        else {
          process_reader.close()
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
              process_writer.close()
              finished = true
            case line =>
              process_writer.write(line)
              process_writer.write("\n")
              process_writer.flush()
          }
        }
      }
      catch { case e: IOException => case Exn.Interrupt() => }
    }
    process_interrupt match {
      case None => body
      case Some(interrupt) =>
        POSIX_Interrupt.handler { interrupt() } { body }
    }
  }

  def join { console_output.join; console_input.join }

  def cancel { console_input.cancel }
}
