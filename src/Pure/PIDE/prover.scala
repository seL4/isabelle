/*  Title:      Pure/PIDE/prover.scala
    Author:     Makarius

General prover operations.
*/

package isabelle


object Prover
{
  /* messages */

  sealed abstract class Message

  class Input(val name: String, val args: List[String]) extends Message
  {
    override def toString: String =
      XML.Elem(Markup(Markup.PROVER_COMMAND, List((Markup.NAME, name))),
        args.map(s =>
          List(XML.Text("\n"), XML.elem(Markup.PROVER_ARG, YXML.parse_body(s)))).flatten).toString
  }

  class Output(val message: XML.Elem) extends Message
  {
    def kind: String = message.markup.name
    def properties: Properties.T = message.markup.properties
    def body: XML.Body = message.body

    def is_init = kind == Markup.INIT
    def is_exit = kind == Markup.EXIT
    def is_stdout = kind == Markup.STDOUT
    def is_stderr = kind == Markup.STDERR
    def is_system = kind == Markup.SYSTEM
    def is_status = kind == Markup.STATUS
    def is_report = kind == Markup.REPORT
    def is_syslog = is_init || is_exit || is_system || is_stderr

    override def toString: String =
    {
      val res =
        if (is_status || is_report) message.body.map(_.toString).mkString
        else Pretty.string_of(message.body)
      if (properties.isEmpty)
        kind.toString + " [[" + res + "]]"
      else
        kind.toString + " " +
          (for ((x, y) <- properties) yield x + "=" + y).mkString("{", ",", "}") + " [[" + res + "]]"
    }
  }

  class Protocol_Output(props: Properties.T, val bytes: Bytes)
    extends Output(XML.Elem(Markup(Markup.PROTOCOL, props), Nil))
  {
    lazy val text: String = bytes.toString
  }
}

