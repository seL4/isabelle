/*  Title:      Tools/jEdit/src/token_markup.scala
    Author:     Makarius

Outer syntax token markup.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Font, Color}
import java.awt.font.{TextAttribute, TransformAttribute}
import java.awt.geom.AffineTransform

import org.gjt.sp.util.SyntaxUtilities
import org.gjt.sp.jedit.Mode
import org.gjt.sp.jedit.syntax.{Token => JEditToken, TokenMarker, TokenHandler,
  ParserRuleSet, ModeProvider, XModeHandler, SyntaxStyle}

import javax.swing.text.Segment


object Token_Markup
{
  /* extended syntax styles */

  private val plain_range: Int = JEditToken.ID_COUNT
  private val full_range = 6 * plain_range + 1
  private def check_range(i: Int) { require(0 <= i && i < plain_range) }

  def subscript(i: Byte): Byte = { check_range(i); (i + plain_range).toByte }
  def superscript(i: Byte): Byte = { check_range(i); (i + 2 * plain_range).toByte }
  def bold(i: Byte): Byte = { check_range(i); (i + 3 * plain_range).toByte }
  def user_font(idx: Int, i: Byte): Byte = { check_range(i); (i + (4 + idx) * plain_range).toByte }
  val hidden: Byte = (6 * plain_range).toByte

  private def font_style(style: SyntaxStyle, f: Font => Font): SyntaxStyle =
    new SyntaxStyle(style.getForegroundColor, style.getBackgroundColor, f(style.getFont))

  private def script_style(style: SyntaxStyle, i: Int): SyntaxStyle =
  {
    import scala.collection.JavaConversions._
    font_style(style, font =>
      style.getFont.deriveFont(Map(TextAttribute.SUPERSCRIPT -> new java.lang.Integer(i))))
  }

  private def bold_style(style: SyntaxStyle): SyntaxStyle =
    font_style(style, _.deriveFont(Font.BOLD))

  private def hidden_font(font: Font): Font =
  {
    import scala.collection.JavaConversions._
    val base_font = new Font(font.getFamily, 0, 1)
    val transform =
      new TransformAttribute(AffineTransform.getScaleInstance(1.0, font.getSize.toDouble))
    base_font.deriveFont(Map(TextAttribute.TRANSFORM -> transform))
  }

  class Style_Extender(symbols: Symbol.Interpretation) extends SyntaxUtilities.StyleExtender
  {
    if (symbols.font_names.length > 2)
      error("Too many user symbol fonts (max 2 permitted): " + symbols.font_names.mkString(", "))

    override def extendStyles(styles: Array[SyntaxStyle]): Array[SyntaxStyle] =
    {
      val new_styles = new Array[SyntaxStyle](full_range)
      for (i <- 0 until plain_range) {
        val style = styles(i)
        new_styles(i) = style
        new_styles(subscript(i.toByte)) = script_style(style, -1)
        new_styles(superscript(i.toByte)) = script_style(style, 1)
        new_styles(bold(i.toByte)) = bold_style(style)
        for ((family, idx) <- symbols.font_index) {
          // FIXME adjust size
          new_styles(user_font(idx, i.toByte)) =
            font_style(style, font => new Font(family, font.getStyle, font.getSize))
        }
      }
      new_styles(hidden) = new SyntaxStyle(Color.white, null, hidden_font(styles(0).getFont))
      new_styles
    }
  }

  def extended_styles(symbols: Symbol.Interpretation, text: CharSequence)
    : Map[Text.Offset, Byte => Byte] =
  {
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
    for (sym <- Symbol.iterator_string(text)) {
      if (ctrl_style(sym).isDefined) ctrl = sym
      else if (ctrl != "") {
        if (symbols.is_controllable(sym) && sym != "\"" && !symbols.fonts.isDefinedAt(sym)) {
          mark(offset - ctrl.length, offset, _ => hidden)
          mark(offset, offset + sym.length, ctrl_style(ctrl).get)
        }
        ctrl = ""
      }
      symbols.lookup_font(sym) match {
        case Some(idx) => mark(offset, offset + sym.length, user_font(idx, _))
        case _ =>
      }
      offset += sym.length
    }
    result
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

