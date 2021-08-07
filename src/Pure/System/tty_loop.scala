/*  Title:      Pure/System/tty_loop.scala
    Author:     Makarius

Line-oriented TTY loop.
*/

package isabelle


import java.io.{IOException, Writer, Reader, InputStreamReader, BufferedReader}


class TTY_Loop(
  writer: Writer,
  reader: Reader,
  writer_lock: AnyRef = new Object)
{
  private val console_output = Future.thread[Unit]("console_output", uninterruptible = true) {
    try {
      val result = new StringBuilder(100)
      var finished = false
      while (!finished) {
        var c = -1
        var done = false
        while (!done && (result.isEmpty || reader.ready)) {
          c = reader.read
          if (c >= 0) result.append(c.asInstanceOf[Char])
          else done = true
        }
        if (result.nonEmpty) {
          System.out.print(result.toString)
          System.out.flush()
          result.clear()
        }
        else {
          reader.close()
          finished = true
        }
      }
    }
    catch { case e: IOException => case Exn.Interrupt() => }
  }

  private val console_input = Future.thread[Unit]("console_input", uninterruptible = true) {
    val console_reader = new BufferedReader(new InputStreamReader(System.in))
    try {
      var finished = false
      while (!finished) {
        console_reader.readLine() match {
          case null =>
            writer.close()
            finished = true
          case line =>
            writer_lock.synchronized {
              writer.write(line)
              writer.write("\n")
              writer.flush()
            }
        }
      }
    }
    catch { case e: IOException => case Exn.Interrupt() => }
  }

  def join(): Unit = { console_output.join; console_input.join }

  def cancel(): Unit = console_input.cancel()
}
