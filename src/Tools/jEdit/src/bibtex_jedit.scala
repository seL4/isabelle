/*  Title:      Tools/jEdit/src/bibtex_jedit.scala
    Author:     Makarius

BibTeX support in Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._


import scala.collection.mutable

import java.awt.event.{ActionListener, ActionEvent}

import javax.swing.text.Segment
import javax.swing.tree.DefaultMutableTreeNode
import javax.swing.{JMenu, JMenuItem}

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}
import org.gjt.sp.jedit.syntax.{Token => JEditToken, TokenMarker, TokenHandler, ParserRuleSet}

import sidekick.{SideKickParser, SideKickParsedData}


object Bibtex_JEdit
{
  /** buffer model **/

  /* file type */

  def check(buffer: Buffer): Boolean =
    JEdit_Lib.buffer_name(buffer).endsWith(".bib")


  /* parse entries */

  def parse_buffer_entries(buffer: Buffer): List[(String, Text.Offset)] =
  {
    val chunks =
      try { Bibtex.parse(JEdit_Lib.buffer_text(buffer)) }
      catch { case ERROR(msg) => Output.warning(msg); Nil }

    val result = new mutable.ListBuffer[(String, Text.Offset)]
    var offset = 0
    for (chunk <- chunks) {
      if (chunk.name != "" && !chunk.is_command) result += ((chunk.name, offset))
      offset += chunk.source.length
    }
    result.toList
  }


  /* retrieve entries */

  def entries_iterator(): Iterator[(String, Buffer, Text.Offset)] =
    for {
      buffer <- JEdit_Lib.jedit_buffers()
      model <- PIDE.document_model(buffer).iterator
      (name, offset) <- model.bibtex_entries.iterator
    } yield (name, buffer, offset)


  /* completion */

  def complete(name: String): List[String] =
  {
    val name1 = name.toLowerCase
    (for ((entry, _, _) <- entries_iterator() if entry.toLowerCase.containsSlice(name1))
      yield entry).toList
  }

  def completion(
    history: Completion.History,
    text_area: JEditTextArea,
    rendering: Rendering): Option[Completion.Result] =
  {
    for {
      Text.Info(r, name) <- rendering.citation(JEdit_Lib.before_caret_range(text_area, rendering))
      original <- JEdit_Lib.try_get_text(text_area.getBuffer, r)
      orig = Library.perhaps_unquote(original)
      entries = complete(name).filter(_ != orig)
      if entries.nonEmpty
      items =
        entries.map({
          case entry =>
            val full_name = Long_Name.qualify(Markup.CITATION, entry)
            val description = List(entry, "(BibTeX entry)")
            val replacement = quote(entry)
          Completion.Item(r, original, full_name, description, replacement, 0, false)
        }).sorted(history.ordering).take(PIDE.options.int("completion_limit"))
    } yield Completion.Result(r, original, false, items)
  }



  /** context menu **/

  def context_menu(text_area0: JEditTextArea): List[JMenuItem] =
  {
    text_area0 match {
      case text_area: TextArea =>
        text_area.getBuffer match {
          case buffer: Buffer
          if (check(buffer) && buffer.isEditable) =>
            val menu = new JMenu("BibTeX entries")
            for (entry <- Bibtex.entries) {
              val item = new JMenuItem(entry.kind)
              item.addActionListener(new ActionListener {
                def actionPerformed(evt: ActionEvent): Unit =
                  Isabelle.insert_line_padding(text_area, entry.template)
              })
              menu.add(item)
            }
            List(menu)
          case _ => Nil
        }
      case _ => Nil
    }
  }



  /** token markup **/

  /* token style */

  private def token_style(context: String, token: Bibtex.Token): Byte =
    token.kind match {
      case Bibtex.Token.Kind.COMMAND => JEditToken.KEYWORD2
      case Bibtex.Token.Kind.ENTRY => JEditToken.KEYWORD1
      case Bibtex.Token.Kind.KEYWORD => JEditToken.OPERATOR
      case Bibtex.Token.Kind.NAT => JEditToken.LITERAL2
      case Bibtex.Token.Kind.STRING => JEditToken.LITERAL1
      case Bibtex.Token.Kind.NAME => JEditToken.LABEL
      case Bibtex.Token.Kind.IDENT =>
        if (Bibtex.is_month(token.source)) JEditToken.LITERAL3
        else
          Bibtex.get_entry(context) match {
            case Some(entry) if entry.is_required(token.source) => JEditToken.KEYWORD3
            case Some(entry) if entry.is_optional(token.source) => JEditToken.KEYWORD4
            case _ => JEditToken.DIGIT
          }
      case Bibtex.Token.Kind.SPACE => JEditToken.NULL
      case Bibtex.Token.Kind.COMMENT => JEditToken.COMMENT1
      case Bibtex.Token.Kind.ERROR => JEditToken.INVALID
    }


  /* line context */

  private val context_rules = new ParserRuleSet("bibtex", "MAIN")

  private class Line_Context(val context: Option[Bibtex.Line_Context])
    extends TokenMarker.LineContext(context_rules, null)
  {
    override def hashCode: Int = context.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Line_Context => context == other.context
        case _ => false
      }
  }


  /* token marker */

  class Token_Marker extends TokenMarker
  {
    override def markTokens(context: TokenMarker.LineContext,
        handler: TokenHandler, raw_line: Segment): TokenMarker.LineContext =
    {
      val line_ctxt =
        context match {
          case c: Line_Context => c.context
          case _ => Some(Bibtex.Ignored)
        }
      val line = if (raw_line == null) new Segment else raw_line

      def no_markup =
      {
        val styled_token = (JEditToken.NULL, line.subSequence(0, line.count).toString)
        (List(styled_token), new Line_Context(None))
      }

      val context1 =
      {
        val (styled_tokens, context1) =
          line_ctxt match {
            case Some(ctxt) =>
              try {
                val (chunks, ctxt1) = Bibtex.parse_line(line, ctxt)
                val styled_tokens =
                  for { chunk <- chunks; tok <- chunk.tokens }
                  yield (token_style(chunk.kind, tok), tok.source)
                (styled_tokens, new Line_Context(Some(ctxt1)))
              }
              catch { case ERROR(msg) => Output.warning(msg); no_markup }
            case None => no_markup
          }

        var offset = 0
        for ((style, token) <- styled_tokens) {
          val length = token.length
          val end_offset = offset + length

          if ((offset until end_offset).exists(i => line.charAt(i) == '\t')) {
            for (i <- offset until end_offset)
              handler.handleToken(line, style, i, 1, context1)
          }
          else handler.handleToken(line, style, offset, length, context1)

          offset += length
        }
        handler.handleToken(line, JEditToken.END, line.count, 0, context1)
        context1
      }
      val context2 = context1.intern
      handler.setLineContext(context2)
      context2
    }
  }



  /** Sidekick parser **/

  class Sidekick_Parser extends SideKickParser("bibtex")
  {
    override def supportsCompletion = false

    private class Asset(label: String, label_html: String, range: Text.Range, source: String)
      extends Isabelle_Sidekick.Asset(label, range) {
        override def getShortString: String = label_html
        override def getLongString: String = source
      }

    def parse(buffer: Buffer, error_source: errorlist.DefaultErrorSource): SideKickParsedData =
    {
      val data = Isabelle_Sidekick.root_data(buffer)

      try {
        var offset = 0
        for (chunk <- Bibtex.parse(JEdit_Lib.buffer_text(buffer))) {
          val kind = chunk.kind
          val name = chunk.name
          val source = chunk.source
          if (kind != "") {
            val label = kind + (if (name == "") "" else " " + name)
            val label_html =
              "<html><b>" + HTML.encode(kind) + "</b>" +
              (if (name == "") "" else " " + HTML.encode(name)) + "</html>"
            val range = Text.Range(offset, offset + source.length)
            val asset = new Asset(label, label_html, range, source)
            data.root.add(new DefaultMutableTreeNode(asset))
          }
          offset += source.length
        }
        data
      }
      catch { case ERROR(msg) => Output.warning(msg); null }
    }
  }
}

