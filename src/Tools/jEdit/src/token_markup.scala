/*  Title:      Tools/jEdit/src/token_markup.scala
    Author:     Makarius

Outer syntax token markup.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.Mode
import org.gjt.sp.jedit.syntax.{Token => JEditToken, TokenMarker, TokenHandler,
  ParserRuleSet, ModeProvider, XModeHandler}

import javax.swing.text.Segment


object Token_Markup
{
  /* extended syntax styles */

  private val plain_range: Int = JEditToken.ID_COUNT
  private def check_range(i: Int) { require(0 <= i && i < plain_range) }

  def subscript(i: Byte): Byte = { check_range(i); (i + plain_range).toByte }
  def superscript(i: Byte): Byte = { check_range(i); (i + 2 * plain_range).toByte }
  def bold(i: Byte): Byte = { check_range(i); (i + 3 * plain_range).toByte }
  val hidden: Byte = (4 * plain_range).toByte

  private def extended_styles(symbols: Symbol.Interpretation, text: CharSequence)
    : Map[Text.Offset, Byte => Byte] =
  {
    if (Isabelle.extended_styles) {
      // FIXME \\<^bsub> \\<^esub> \\<^bsup> \\<^esup>
      def ctrl_style(sym: String): Option[Byte => Byte] =
        if (symbols.is_subscript_decoded(sym)) Some(subscript(_))
        else if (symbols.is_superscript_decoded(sym)) Some(superscript(_))
        else if (symbols.is_bold_decoded(sym)) Some(bold(_))
        else None

      var result = Map[Text.Offset, Byte => Byte]()
      def mark(start: Text.Offset, stop: Text.Offset, style: Byte => Byte)
      {
        for (i <- start until stop) result += (i -> style)
      }
      var offset = 0
      var ctrl = ""
      for (sym <- Symbol.iterator(text).map(_.toString)) {
        if (ctrl_style(sym).isDefined) ctrl = sym
        else if (ctrl != "") {
          if (symbols.is_controllable(sym)) {
            mark(offset - ctrl.length, offset, _ => hidden)
            mark(offset, offset + sym.length, ctrl_style(ctrl).get)
          }
          ctrl = ""
        }
        offset += sym.length
      }
      result
    }
    else Map.empty
  }


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

  class Marker extends TokenMarker
  {
    override def markTokens(context: TokenMarker.LineContext,
        handler: TokenHandler, line: Segment): TokenMarker.LineContext =
    {
      val symbols = Isabelle.system.symbols
      val syntax = Isabelle.session.current_syntax()

      val ctxt =
        context match {
          case c: Line_Context => c.context
          case _ => Scan.Finished
        }
      val (tokens, ctxt1) = syntax.scan_context(line, ctxt)
      val context1 = new Line_Context(ctxt1)

      val extended = extended_styles(symbols, line)

      var offset = 0
      for (token <- tokens) {
        val style = Isabelle_Markup.token_markup(syntax, token)
        val length = token.source.length
        val end_offset = offset + length
        if ((offset until end_offset) exists extended.isDefinedAt) {
          for (i <- offset until end_offset) {
            val style1 =
              extended.get(i) match {
                case None => style
                case Some(ext) => ext(style)
              }
            handler.handleToken(line, style1, i, 1, context1)
          }
        }
        else handler.handleToken(line, style, offset, length, context1)
        offset += length
      }
      handler.handleToken(line, JEditToken.END, line.count, 0, context1)

      val context2 = context1.intern
      handler.setLineContext(context2)
      context2
    }
  }


  /* mode provider */

  class Mode_Provider(orig_provider: ModeProvider) extends ModeProvider
  {
    for (mode <- orig_provider.getModes) addMode(mode)

    val isabelle_token_marker = new Token_Markup.Marker

    override def loadMode(mode: Mode, xmh: XModeHandler)
    {
      super.loadMode(mode, xmh)
      if (mode.getName == "isabelle")
        mode.setTokenMarker(isabelle_token_marker)
    }
  }
}

