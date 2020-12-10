/*  Title:      Tools/jEdit/src/jedit_rendering.scala
    Author:     Makarius

Isabelle/jEdit-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle.jedit


import isabelle._

import java.awt.Color
import javax.swing.Icon

import org.gjt.sp.jedit.syntax.{Token => JEditToken}
import org.gjt.sp.jedit.jEdit

import scala.collection.immutable.SortedMap


object JEdit_Rendering
{
  /* make rendering */

  def apply(snapshot: Document.Snapshot, model: Document_Model, options: Options): JEdit_Rendering =
    new JEdit_Rendering(snapshot, model, options)

  def text(snapshot: Document.Snapshot, formatted_body: XML.Body,
    results: Command.Results = Command.Results.empty): (String, JEdit_Rendering) =
  {
    val command = Command.rich_text(Document_ID.make(), results, formatted_body)
    val snippet = snapshot.command_snippet(command)
    val model = File_Model.empty(PIDE.session)
    val rendering = apply(snippet, model, PIDE.options.value)
    (command.source, rendering)
  }


  /* popup window bounds */

  def popup_bounds: Double = (PIDE.options.real("jedit_popup_bounds") max 0.2) min 0.8


  /* Isabelle/Isar token markup */

  private val command_style: Map[String, Byte] =
  {
    import JEditToken._
    Map[String, Byte](
      Keyword.THY_END -> KEYWORD2,
      Keyword.PRF_ASM -> KEYWORD3,
      Keyword.PRF_ASM_GOAL -> KEYWORD3
    ).withDefaultValue(KEYWORD1)
  }

  private val token_style: Map[Token.Kind.Value, Byte] =
  {
    import JEditToken._
    Map[Token.Kind.Value, Byte](
      Token.Kind.KEYWORD -> KEYWORD2,
      Token.Kind.IDENT -> NULL,
      Token.Kind.LONG_IDENT -> NULL,
      Token.Kind.SYM_IDENT -> NULL,
      Token.Kind.VAR -> NULL,
      Token.Kind.TYPE_IDENT -> NULL,
      Token.Kind.TYPE_VAR -> NULL,
      Token.Kind.NAT -> NULL,
      Token.Kind.FLOAT -> NULL,
      Token.Kind.SPACE -> NULL,
      Token.Kind.STRING -> LITERAL1,
      Token.Kind.ALT_STRING -> LITERAL2,
      Token.Kind.VERBATIM -> COMMENT3,
      Token.Kind.CARTOUCHE -> COMMENT3,
      Token.Kind.INFORMAL_COMMENT -> COMMENT1,
      Token.Kind.FORMAL_COMMENT -> COMMENT1,
      Token.Kind.ERROR -> INVALID
    ).withDefaultValue(NULL)
  }

  def token_markup(syntax: Outer_Syntax, token: Token): Byte =
    if (token.is_command) command_style(syntax.keywords.kinds.getOrElse(token.content, ""))
    else if (token.is_delimiter) JEditToken.OPERATOR
    else token_style(token.kind)


  /* Isabelle/ML token markup */

  private val ml_token_style: Map[ML_Lex.Kind.Value, Byte] =
  {
    import JEditToken._
    Map[ML_Lex.Kind.Value, Byte](
      ML_Lex.Kind.KEYWORD -> NULL,
      ML_Lex.Kind.IDENT -> NULL,
      ML_Lex.Kind.LONG_IDENT -> NULL,
      ML_Lex.Kind.TYPE_VAR -> NULL,
      ML_Lex.Kind.WORD -> DIGIT,
      ML_Lex.Kind.INT -> DIGIT,
      ML_Lex.Kind.REAL -> DIGIT,
      ML_Lex.Kind.CHAR -> LITERAL2,
      ML_Lex.Kind.STRING -> LITERAL1,
      ML_Lex.Kind.SPACE -> NULL,
      ML_Lex.Kind.INFORMAL_COMMENT -> COMMENT1,
      ML_Lex.Kind.FORMAL_COMMENT -> COMMENT1,
      ML_Lex.Kind.ANTIQ -> NULL,
      ML_Lex.Kind.ANTIQ_START -> LITERAL4,
      ML_Lex.Kind.ANTIQ_STOP -> LITERAL4,
      ML_Lex.Kind.ANTIQ_OTHER -> NULL,
      ML_Lex.Kind.ANTIQ_STRING -> NULL,
      ML_Lex.Kind.ANTIQ_ALT_STRING -> NULL,
      ML_Lex.Kind.ANTIQ_CARTOUCHE -> NULL,
      ML_Lex.Kind.ERROR -> INVALID
    ).withDefaultValue(NULL)
  }

  def ml_token_markup(token: ML_Lex.Token): Byte =
    if (!token.is_keyword) ml_token_style(token.kind)
    else if (token.is_delimiter) JEditToken.OPERATOR
    else if (ML_Lex.keywords2(token.source)) JEditToken.KEYWORD2
    else if (ML_Lex.keywords3(token.source)) JEditToken.KEYWORD3
    else JEditToken.KEYWORD1


  /* markup elements */

  private val indentation_elements =
    Markup.Elements(Markup.Command_Indent.name)

  private val breakpoint_elements = Markup.Elements(Markup.ML_BREAKPOINT)

  private val highlight_elements =
    Markup.Elements(Markup.EXPRESSION, Markup.CITATION, Markup.LANGUAGE, Markup.ML_TYPING,
      Markup.TOKEN_RANGE, Markup.ENTITY, Markup.PATH, Markup.DOC, Markup.URL,
      Markup.SORTING, Markup.TYPING, Markup.CLASS_PARAMETER, Markup.FREE, Markup.SKOLEM,
      Markup.BOUND, Markup.VAR, Markup.TFREE, Markup.TVAR, Markup.ML_BREAKPOINT,
      Markup.MARKDOWN_PARAGRAPH, Markup.MARKDOWN_ITEM, Markup.Markdown_List.name)

  private val hyperlink_elements =
    Markup.Elements(Markup.ENTITY, Markup.PATH, Markup.EXPORT_PATH, Markup.DOC, Markup.URL,
      Markup.POSITION, Markup.CITATION)

  private val gutter_elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING, Markup.LEGACY, Markup.ERROR)

  private val squiggly_elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING, Markup.LEGACY, Markup.ERROR)

  private val line_background_elements =
    Markup.Elements(Markup.WRITELN_MESSAGE, Markup.STATE_MESSAGE, Markup.INFORMATION_MESSAGE,
      Markup.TRACING_MESSAGE, Markup.WARNING_MESSAGE, Markup.LEGACY_MESSAGE,
      Markup.ERROR_MESSAGE)

  private val separator_elements =
    Markup.Elements(Markup.SEPARATOR)

  private val bullet_elements =
    Markup.Elements(Markup.BULLET, Markup.ML_BREAKPOINT)

  private val fold_depth_elements =
    Markup.Elements(Markup.TEXT_FOLD, Markup.GOAL, Markup.SUBGOAL)
}


class JEdit_Rendering(snapshot: Document.Snapshot, model: Document_Model, options: Options)
  extends Rendering(snapshot, options, PIDE.session)
{
  override def get_text(range: Text.Range): Option[String] = model.get_text(range)


  /* colors */

  def color(s: String): Color =
    if (s == "main_color") main_color
    else Color_Value(options.string(s))

  def color(c: Rendering.Color.Value): Color = _rendering_colors(c)

  lazy val _rendering_colors: Map[Rendering.Color.Value, Color] =
    Rendering.Color.values.iterator.map(c => c -> color(c.toString + "_color")).toMap

  val main_color = jEdit.getColorProperty("view.fgColor")

  val outdated_color = color("outdated_color")
  val bullet_color = color("bullet_color")
  val tooltip_color = color("tooltip_color")
  val spell_checker_color = color("spell_checker_color")
  val entity_ref_color = color("entity_ref_color")
  val breakpoint_disabled_color = color("breakpoint_disabled_color")
  val breakpoint_enabled_color = color("breakpoint_enabled_color")
  val caret_debugger_color = color("caret_debugger_color")
  val highlight_color = color("highlight_color")
  val hyperlink_color = color("hyperlink_color")
  val active_hover_color = color("active_hover_color")
  val caret_invisible_color = color("caret_invisible_color")
  val completion_color = color("completion_color")
  val search_color = color("search_color")


  /* indentation */

  def indentation(range: Text.Range): Int =
    snapshot.select(range, JEdit_Rendering.indentation_elements, _ =>
      {
        case Text.Info(_, XML.Elem(Markup.Command_Indent(i), _)) => Some(i)
        case _ => None
      }).headOption.map(_.info).getOrElse(0)


  /* breakpoints */

  def breakpoint(range: Text.Range): Option[(Command, Long)] =
    if (snapshot.is_outdated) None
    else
      snapshot.select(range, JEdit_Rendering.breakpoint_elements, command_states =>
        {
          case Text.Info(_, Protocol.ML_Breakpoint(breakpoint)) =>
            command_states match {
              case st :: _ => Some((st.command, breakpoint))
              case _ => None
            }
          case _ => None
        }).headOption.map(_.info)


  /* caret focus */

  def entity_ref(range: Text.Range, focus: Set[Long]): List[Text.Info[Color]] =
    snapshot.select(range, Rendering.caret_focus_elements, _ =>
      {
        case Text.Info(_, XML.Elem(Markup(Markup.ENTITY, Markup.Entity.Ref(i)), _)) if focus(i) =>
          Some(entity_ref_color)
        case _ => None
      })


  /* highlighted area */

  def highlight(range: Text.Range): Option[Text.Info[Color]] =
    snapshot.select(range, JEdit_Rendering.highlight_elements, _ =>
      {
        case info => Some(Text.Info(snapshot.convert(info.range), highlight_color))
      }).headOption.map(_.info)


  /* hyperlinks */

  def hyperlink(range: Text.Range): Option[Text.Info[PIDE.editor.Hyperlink]] =
  {
    snapshot.cumulate[Vector[Text.Info[PIDE.editor.Hyperlink]]](
      range, Vector.empty, JEdit_Rendering.hyperlink_elements, _ =>
        {
          case (links, Text.Info(info_range, XML.Elem(Markup.Path(name), _))) =>
            val file = perhaps_append_file(snapshot.node_name, name)
            val link = PIDE.editor.hyperlink_file(true, file)
            Some(links :+ Text.Info(snapshot.convert(info_range), link))

          case (links, Text.Info(info_range, XML.Elem(Markup.Export_Path(name), _))) =>
            val link = PIDE.editor.hyperlink_file(true, Isabelle_Export.vfs_prefix + name)
            Some(links :+ Text.Info(snapshot.convert(info_range), link))

          case (links, Text.Info(info_range, XML.Elem(Markup.Doc(name), _))) =>
            PIDE.editor.hyperlink_doc(name).map(link =>
              (links :+ Text.Info(snapshot.convert(info_range), link)))

          case (links, Text.Info(info_range, XML.Elem(Markup.Url(name), _))) =>
            val link = PIDE.editor.hyperlink_url(name)
            Some(links :+ Text.Info(snapshot.convert(info_range), link))

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.ENTITY, props), _))) =>
            val opt_link = PIDE.editor.hyperlink_def_position(true, snapshot, props)
            opt_link.map(link => links :+ Text.Info(snapshot.convert(info_range), link))

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.POSITION, props), _))) =>
            val opt_link = PIDE.editor.hyperlink_position(true, snapshot, props)
            opt_link.map(link => links :+ Text.Info(snapshot.convert(info_range), link))

          case (links, Text.Info(info_range, XML.Elem(Markup.Citation(name), _))) =>
            val opt_link =
              Document_Model.bibtex_entries_iterator().collectFirst(
                { case Text.Info(entry_range, (entry, model)) if entry == name =>
                    PIDE.editor.hyperlink_model(true, model, entry_range.start) })
            opt_link.map(link => links :+ Text.Info(snapshot.convert(info_range), link))

          case _ => None
        }) match { case Text.Info(_, _ :+ info) :: _ => Some(info) case _ => None }
  }


  /* active elements */

  def active(range: Text.Range): Option[Text.Info[XML.Elem]] =
    snapshot.select(range, Rendering.active_elements, command_states =>
      {
        case Text.Info(info_range, elem) =>
          if (elem.name == Markup.DIALOG) {
            elem match {
              case Protocol.Dialog(_, serial, _)
              if !command_states.exists(st => st.results.defined(serial)) =>
                Some(Text.Info(snapshot.convert(info_range), elem))
              case _ => None
            }
          }
          else Some(Text.Info(snapshot.convert(info_range), elem))
      }).headOption.map(_.info)


  /* tooltips */

  def tooltip_margin: Int = options.int("jedit_tooltip_margin")
  override def timing_threshold: Double = options.real("jedit_timing_threshold")

  def tooltip(range: Text.Range, control: Boolean): Option[Text.Info[XML.Body]] =
  {
    val elements = if (control) Rendering.tooltip_elements else Rendering.tooltip_message_elements
    tooltips(elements, range).map(info => info.map(Pretty.fbreaks))
  }

  lazy val tooltip_close_icon: Icon = JEdit_Lib.load_icon(options.string("tooltip_close_icon"))
  lazy val tooltip_detach_icon: Icon = JEdit_Lib.load_icon(options.string("tooltip_detach_icon"))


  /* gutter */

  private def gutter_message_pri(msg: XML.Tree): Int =
    if (Protocol.is_error(msg)) Rendering.error_pri
    else if (Protocol.is_legacy(msg)) Rendering.legacy_pri
    else if (Protocol.is_warning(msg)) Rendering.warning_pri
    else if (Protocol.is_information(msg)) Rendering.information_pri
    else 0

  private lazy val gutter_message_content = Map(
    Rendering.information_pri ->
      (JEdit_Lib.load_icon(options.string("gutter_information_icon")),
        color(Rendering.Color.information_message)),
    Rendering.warning_pri ->
      (JEdit_Lib.load_icon(options.string("gutter_warning_icon")),
        color(Rendering.Color.warning_message)),
    Rendering.legacy_pri ->
      (JEdit_Lib.load_icon(options.string("gutter_legacy_icon")),
        color(Rendering.Color.legacy_message)),
    Rendering.error_pri ->
      (JEdit_Lib.load_icon(options.string("gutter_error_icon")),
        color(Rendering.Color.error_message)))

  def gutter_content(range: Text.Range): Option[(Icon, Color)] =
  {
    val pris =
      snapshot.cumulate[Int](range, 0, JEdit_Rendering.gutter_elements, _ =>
        {
          case (pri, Text.Info(_, elem)) => Some(pri max gutter_message_pri(elem))
          case _ => None
        }).map(_.info)

    gutter_message_content.get((0 /: pris)(_ max _))
  }


  /* message output */

  def squiggly_underline(range: Text.Range): List[Text.Info[Rendering.Color.Value]] =
    message_underline_color(JEdit_Rendering.squiggly_elements, range)

  def line_background(range: Text.Range): Option[(Rendering.Color.Value, Boolean)] =
  {
    val results =
      snapshot.cumulate[Int](range, 0, JEdit_Rendering.line_background_elements, _ =>
        {
          case (pri, Text.Info(_, elem)) => Some(pri max Rendering.message_pri(elem.name))
        })
    val pri = (0 /: results) { case (p1, Text.Info(_, p2)) => p1 max p2 }

    Rendering.message_background_color.get(pri).map(message_color =>
      {
        val is_separator =
          snapshot.cumulate[Boolean](range, false, JEdit_Rendering.separator_elements, _ =>
            {
              case _ => Some(true)
            }).exists(_.info)
        (message_color, is_separator)
      })
  }


  /* text color */

  def text_color(range: Text.Range, current_color: Color): List[Text.Info[Color]] =
  {
    if (current_color == Syntax_Style.hidden_color) List(Text.Info(range, current_color))
    else
      snapshot.cumulate(range, current_color, Rendering.text_color_elements, _ =>
        {
          case (_, Text.Info(_, elem)) => Rendering.text_color.get(elem.name).map(color)
        })
  }


  /* virtual bullets */

  def bullet(range: Text.Range): List[Text.Info[Color]] =
    snapshot.select(range, JEdit_Rendering.bullet_elements, _ =>
      {
        case Text.Info(_, Protocol.ML_Breakpoint(breakpoint)) =>
          PIDE.session.debugger.active_breakpoint_state(breakpoint).map(b =>
            if (b) breakpoint_enabled_color else breakpoint_disabled_color)
        case _ => Some(bullet_color)
      })


  /* text folds */

  def fold_depth(range: Text.Range): List[Text.Info[Int]] =
    snapshot.cumulate[Int](range, 0, JEdit_Rendering.fold_depth_elements, _ =>
      {
        case (depth, _) => Some(depth + 1)
      })
}
