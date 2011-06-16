/*  Title:      Tools/jEdit/src/token_markup.scala
    Author:     Makarius

Outer syntax token markup.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.syntax.{Token => JToken, TokenMarker, TokenHandler, ParserRuleSet}
import javax.swing.text.Segment


object Token_Markup
{
  /* extended jEdit syntax styles */

  private val plain_range: Int = JToken.ID_COUNT
  private def check_range(i: Int) { require(0 <= i && i < plain_range) }

  def subscript(i: Byte): Byte = { check_range(i); (i + plain_range).toByte }
  def superscript(i: Byte): Byte = { check_range(i); (i + 2 * plain_range).toByte }
  val hidden: Byte = (3 * plain_range).toByte


  /* token marker */

  private val isabelle_rules = new ParserRuleSet("isabelle", "MAIN")

  private class Line_Context(val context: Scan.Context)
    extends TokenMarker.LineContext(isabelle_rules, null)
  {
    override def hashCode: Int = context.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Line_Context => context == other.context
        case _ => false
      }
  }

  def token_marker(session: Session, buffer: Buffer): TokenMarker =
    new TokenMarker {
      override def markTokens(context: TokenMarker.LineContext,
          handler: TokenHandler, line: Segment): TokenMarker.LineContext =
      {
        Isabelle.swing_buffer_lock(buffer) {
          val syntax = session.current_syntax()

          val ctxt =
            context match {
              case c: Line_Context => c.context
              case _ => Scan.Finished
            }

          val (tokens, ctxt1) = syntax.scan_context(line, ctxt)
          val context1 = new Line_Context(ctxt1)

          var offset = 0
          for (token <- tokens) {
            val style = Isabelle_Markup.token_markup(syntax, token)
            val length = token.source.length
            handler.handleToken(line, style, offset, length, context1)
            offset += length
          }
          handler.handleToken(line, JToken.END, line.count, 0, context1)
          handler.setLineContext(context1)
          context1
        }
      }
    }
}

