/*  Title:      Tools/jEdit/src/syntax_style.scala
    Author:     Makarius

Support for extended syntax styles: subscript, superscript, bold, user fonts.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Font, Color}
import java.awt.font.TextAttribute
import java.awt.geom.AffineTransform

import org.gjt.sp.util.SyntaxUtilities
import org.gjt.sp.jedit.syntax.{Token => JEditToken, SyntaxStyle}
import org.gjt.sp.jedit.textarea.TextArea


object Syntax_Style
{
  /* extended syntax styles */

  private val plain_range: Int = JEditToken.ID_COUNT
  private def check_range(i: Int) { require(0 <= i && i < plain_range, "bad syntax style range") }

  def subscript(i: Byte): Byte = { check_range(i); (i + plain_range).toByte }
  def superscript(i: Byte): Byte = { check_range(i); (i + 2 * plain_range).toByte }
  def bold(i: Byte): Byte = { check_range(i); (i + 3 * plain_range).toByte }
  def user_font(idx: Int, i: Byte): Byte = { check_range(i); (i + (4 + idx) * plain_range).toByte }
  val hidden: Byte = (6 * plain_range).toByte
  val control: Byte = (hidden + JEditToken.DIGIT).toByte

  private def font_style(style: SyntaxStyle, f: Font => Font): SyntaxStyle =
    new SyntaxStyle(style.getForegroundColor, style.getBackgroundColor, f(style.getFont))

  private def script_style(style: SyntaxStyle, i: Int): SyntaxStyle =
  {
    font_style(style, font0 =>
      {
        val font1 =
          font0.deriveFont(java.util.Map.of(TextAttribute.SUPERSCRIPT, java.lang.Integer.valueOf(i)))

        def shift(y: Float): Font =
          GUI.transform_font(font1, AffineTransform.getTranslateInstance(0.0, y.toDouble))

        val m0 = GUI.line_metrics(font0)
        val m1 = GUI.line_metrics(font1)
        val a = m1.getAscent - m0.getAscent
        val b = (m1.getDescent + m1.getLeading) - (m0.getDescent + m0.getLeading)
        if (a > 0.0f) shift(a)
        else if (b > 0.0f) shift(- b)
        else font1
      })
  }

  private def bold_style(style: SyntaxStyle): SyntaxStyle =
    font_style(style, font => font.deriveFont(if (font.isBold) Font.PLAIN else Font.BOLD))

  val hidden_color: Color = new Color(255, 255, 255, 0)

  object Extender extends SyntaxUtilities.StyleExtender
  {
    val max_user_fonts = 2
    if (Symbol.font_names.length > max_user_fonts)
      error("Too many user symbol fonts (" + max_user_fonts + " permitted): " +
        Symbol.font_names.mkString(", "))

    override def extendStyles(styles: Array[SyntaxStyle]): Array[SyntaxStyle] =
    {
      val style0 = styles(0)
      val font0 = style0.getFont

      val new_styles = Array.fill[SyntaxStyle](java.lang.Byte.MAX_VALUE)(styles(0))
      for (i <- 0 until plain_range) {
        val style = styles(i)
        new_styles(i) = style
        new_styles(subscript(i.toByte)) = script_style(style, -1)
        new_styles(superscript(i.toByte)) = script_style(style, 1)
        new_styles(bold(i.toByte)) = bold_style(style)
        for (idx <- 0 until max_user_fonts)
          new_styles(user_font(idx, i.toByte)) = style
        for ((family, idx) <- Symbol.font_index)
          new_styles(user_font(idx, i.toByte)) = font_style(style, GUI.imitate_font(_, family))
      }
      new_styles(hidden) =
        new SyntaxStyle(hidden_color, null,
          GUI.transform_font(new Font(font0.getFamily, 0, 1),
            AffineTransform.getScaleInstance(2.0, font0.getSize.toDouble)))
      new_styles(control) =
        new SyntaxStyle(style0.getForegroundColor, style0.getBackgroundColor,
          { val font_style =
              (if (font0.isItalic) 0 else Font.ITALIC) |
              (if (font0.isBold) 0 else Font.BOLD)
            new Font(font0.getFamily, font_style, font0.getSize) })
      new_styles
    }
  }

  private def control_style(sym: String): Option[Byte => Byte] =
    if (sym == Symbol.sub_decoded) Some(subscript)
    else if (sym == Symbol.sup_decoded) Some(superscript)
    else if (sym == Symbol.bold_decoded) Some(bold)
    else None

  def extended(text: CharSequence): Map[Text.Offset, Byte => Byte] =
  {
    var result = Map[Text.Offset, Byte => Byte]()
    def mark(start: Text.Offset, stop: Text.Offset, style: Byte => Byte)
    {
      for (i <- start until stop) result += (i -> style)
    }

    var offset = 0
    var control_sym = ""
    for (sym <- Symbol.iterator(text)) {
      val end_offset = offset + sym.length

      if (control_style(sym).isDefined) control_sym = sym
      else if (control_sym != "") {
        if (Symbol.is_controllable(sym) && !Symbol.fonts.isDefinedAt(sym)) {
          mark(offset - control_sym.length, offset, _ => hidden)
          mark(offset, end_offset, control_style(control_sym).get)
        }
        control_sym = ""
      }

      if (Symbol.is_control_encoded(sym)) {
        val a = offset + Symbol.control_prefix.length
        val b = end_offset - Symbol.control_suffix.length
        mark(offset, a, _ => hidden)
        mark(a, b, _ => control)
        mark(b, end_offset, _ => hidden)
      }

      Symbol.lookup_font(sym) match {
        case Some(idx) => mark(offset, end_offset, user_font(idx, _))
        case _ =>
      }

      offset = end_offset
    }

    result
  }


  /* editing support for control symbols */

  def edit_control_style(text_area: TextArea, control_sym: String)
  {
    GUI_Thread.assert {}

    val buffer = text_area.getBuffer

    val control_decoded = Isabelle_Encoding.perhaps_decode(buffer, control_sym)

    def update_style(text: String): String =
    {
      val result = new StringBuilder
      for (sym <- Symbol.iterator(text) if !HTML.is_control(sym)) {
        if (Symbol.is_controllable(sym)) result ++= control_decoded
        result ++= sym
      }
      result.toString
    }

    text_area.getSelection.foreach(sel => {
      val before = JEdit_Lib.point_range(buffer, sel.getStart - 1)
      JEdit_Lib.get_text(buffer, before) match {
        case Some(s) if HTML.is_control(s) =>
          text_area.extendSelection(before.start, before.stop)
        case _ =>
      }
    })

    text_area.getSelection.toList match {
      case Nil =>
        text_area.setSelectedText(control_decoded)
      case sels =>
        JEdit_Lib.buffer_edit(buffer) {
          sels.foreach(sel =>
            text_area.setSelectedText(sel, update_style(text_area.getSelectedText(sel))))
        }
    }
  }
}
