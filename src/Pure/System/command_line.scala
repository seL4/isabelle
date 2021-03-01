/*  Title:      Pure/System/command_line.scala
    Author:     Makarius

Support for Isabelle/Scala command line tools.
*/

package isabelle


object Command_Line
{
  object Chunks
  {
    private def chunks(list: List[String]): List[List[String]] =
      list.indexWhere(_ == "\n") match {
        case -1 => List(list)
        case i =>
          val (chunk, rest) = list.splitAt(i)
          chunk :: chunks(rest.tail)
      }
    def unapplySeq(list: List[String]): Option[List[List[String]]] = Some(chunks(list))
  }

  var debug = false

  def tool(body: => Unit): Unit =
  {
    val thread =
      Isabelle_Thread.fork(name = "command_line", inherit_locals = true) {
        val rc =
          try { body; 0 }
          catch {
            case exn: Throwable =>
              Output.error_message(Exn.message(exn) + (if (debug) "\n" + Exn.trace(exn) else ""))
              Exn.return_code(exn, 2)
          }
        sys.exit(rc)
      }
    thread.join
  }

  def ML_tool(body: List[String]): String =
    "Command_Line.tool (fn () => (" + body.mkString("; ") + "));"
}
