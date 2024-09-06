/*  Title:      Pure/PIDE/protocol_message.scala
    Author:     Makarius

Auxiliary operations on protocol messages.
*/

package isabelle


object Protocol_Message {
  /* message markers */

  object Marker {
    def apply(a: String): Marker =
      new Marker { override def name: String = a }

    def test(line: String): Boolean = line.startsWith("\f")
  }

  abstract class Marker private {
    def name: String
    val prefix: String = "\f" + name + " = "

    def apply(text: String): String = prefix + Library.encode_lines(text)
    def apply(props: Properties.T): String = apply(YXML.string_of_body(XML.Encode.properties(props)))

    def test(line: String): Boolean = line.startsWith(prefix)
    def test_yxml(line: String): Boolean = test(line) && YXML.detect(line)

    def unapply(line: String): Option[String] =
      Library.try_unprefix(prefix, line).map(Library.decode_lines)

    override def toString: String = "Marker(" + quote(name) + ")"
  }


  /* inlined reports */

  private val report_elements = Markup.Elements(Markup.REPORT, Markup.NO_REPORT)
  private val no_report_elements = Markup.Elements(Markup.NO_REPORT)

  def clean_reports(body: XML.Body): XML.Body =
    XML.filter_elements(body, remove = report_elements)

  def expose_no_reports(body: XML.Body): XML.Body =
    XML.filter_elements(body, expose = no_report_elements)

  def reports(props: Properties.T, body: XML.Body): List[XML.Elem] =
    body flatMap {
      case XML.Wrapped_Elem(Markup(Markup.REPORT, ps), body, ts) =>
        List(XML.Wrapped_Elem(Markup(Markup.REPORT, props ::: ps), body, ts))
      case XML.Elem(Markup(Markup.REPORT, ps), ts) =>
        List(XML.Elem(Markup(Markup.REPORT, props ::: ps), ts))
      case XML.Wrapped_Elem_Body(ts) => reports(props, ts)
      case XML.Elem(_, ts) => reports(props, ts)
      case XML.Text(_) => Nil
    }


  /* clean output */

  def clean_output(msg: String): String =
    try { XML.content(clean_reports(YXML.parse_body(YXML.Source(msg)))) }
    catch { case ERROR(_) => msg }
}
