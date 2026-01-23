/*  Title:      Tools/jEdit/src/jedit_rendering.scala
    Author:     Makarius

Isabelle/jEdit-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle.jedit


import isabelle._

import java.awt.Color
import javax.swing.{Icon, UIManager}

import org.gjt.sp.jedit.syntax.{Token => JEditToken}
import org.gjt.sp.jedit.jEdit


object JEdit_Rendering {
  /* make rendering */

  def make(
    snapshot: Document.Snapshot,
    rich_texts: List[Rich_Text.Formatted] = Nil,
    results: Command.Results = Command.Results.empty
  ): JEdit_Rendering = {
    val snapshot1 =
      if (rich_texts.isEmpty) snapshot
      else snapshot.snippet(rich_texts.map(_.command(results)), Document.Blobs.empty)
    val model = File_Model.init(PIDE.session)
    new JEdit_Rendering(snapshot1, model, PIDE.options)
  }


  /* popup window bounds */

  def popup_bounds: Double = (PIDE.options.real("jedit_popup_bounds") max 0.2) min 0.8


  /* Isabelle/Isar token markup */

  private val command_style: Map[String, Byte] = {
    import JEditToken._
    Map[String, Byte](
      Keyword.THY_END -> KEYWORD2,
      Keyword.PRF_ASM -> KEYWORD3,
      Keyword.PRF_ASM_GOAL -> KEYWORD3
    ).withDefaultValue(KEYWORD1)
  }

  private val token_style: Map[Token.Kind.Value, Byte] = {
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
      Token.Kind.CARTOUCHE -> COMMENT3,
      Token.Kind.CONTROL -> COMMENT3,
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

  private val ml_token_style: Map[ML_Lex.Kind.Value, Byte] = {
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
    Markup.Elements(Markup.NOTATION, Markup.EXPRESSION, Markup.LANGUAGE, Markup.COMMAND_SPAN,
      Markup.ML_TYPING, Markup.TOKEN_RANGE, Markup.ENTITY, Markup.PATH, Markup.DOC, Markup.URL,
      Markup.SORTING, Markup.TYPING, Markup.CLASS_PARAMETER, Markup.FREE, Markup.SKOLEM,
      Markup.BOUND, Markup.VAR, Markup.TFREE, Markup.TVAR, Markup.ML_BREAKPOINT,
      Markup.MARKDOWN_PARAGRAPH, Markup.MARKDOWN_ITEM, Markup.Markdown_List.name)

  private val hyperlink_elements =
    Markup.Elements(Markup.ENTITY, Markup.PATH, Markup.EXPORT_PATH, Markup.DOC, Markup.URL,
      Markup.POSITION)

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
extends Rendering(snapshot, options, PIDE.session) {
  override def get_text(range: Text.Range): Option[String] = model.get_text(range)


  /* colors */

  def color(name: String): Color =
    if (name == "main_color") main_color
    else Color_Value.option(options, name)

  def color(c: Rendering.Color.Value): Color = _rendering_colors(c)

  lazy val _rendering_colors: Map[Rendering.Color.Value, Color] =
    Rendering.Color.values.iterator.map(c => c -> color(c.toString + "_color")).toMap

  val main_color = jEdit.getColorProperty("view.fgColor")

  val outdated_color = color("outdated_color")
  val bullet_color = color("bullet_color")
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

  lazy val tooltip_foreground_color: Color =
    Option(UIManager.getColor("ToolTip.foreground")).getOrElse(GUI.default_foreground_color())

  lazy val tooltip_background_color: Color =
    Option(UIManager.getColor("ToolTip.background")).getOrElse(GUI.default_background_color())


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

  def entity_ref(range: Text.Range, focus: Rendering.Focus): List[Text.Info[Color]] =
    snapshot.select(range, Rendering.entity_elements, _ =>
      {
        case Text.Info(_, XML.Elem(Markup.Entity.Ref(i), _)) if focus(i) =>
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
    hyperlinks(range).lastOption

  def hyperlinks(range: Text.Range): List[Text.Info[PIDE.editor.Hyperlink]] =
    make_hyperlinks(range, elements = JEdit_Rendering.hyperlink_elements) {
      case Markup(Markup.ENTITY, props) =>
        PIDE.editor.hyperlink_def_position(snapshot, props, focus = true)
      case Markup(Markup.POSITION, props) =>
        PIDE.editor.hyperlink_position(snapshot, props, focus = true)
      case Markup.Path(name) =>
        val file = perhaps_append_file(snapshot.node_name, name)
        Some(PIDE.editor.hyperlink_file(file, focus = true))
      case Markup.Export_Path(name) =>
        val file = Isabelle_Export.vfs_prefix + name
        Some(PIDE.editor.hyperlink_file(file, focus = true))
      case Markup.Doc(name) => PIDE.editor.hyperlink_doc(name)
      case Markup.Url(name) => Some(PIDE.editor.hyperlink_url(name))
      case _ => None
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

  def tooltip(range: Text.Range, control: Boolean): Option[Text.Info[List[XML.Elem]]] =
    tooltips(if (control) Rendering.tooltip_elements else Rendering.tooltip_message_elements,
      range)

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

  def gutter_content(range: Text.Range): Option[(Icon, Color)] = {
    val pris =
      snapshot.cumulate[Int](range, 0, JEdit_Rendering.gutter_elements, _ =>
        {
          case (pri, Text.Info(_, elem)) => Some(pri max gutter_message_pri(elem))
        }).map(_.info)

    gutter_message_content.get(pris.foldLeft(0)(_ max _))
  }


  /* message output */

  def squiggly_underline(range: Text.Range): List[Text.Info[Rendering.Color.Value]] =
    message_underline_color(JEdit_Rendering.squiggly_elements, range)

  def line_background(range: Text.Range): Option[Rendering.Color.Value] =
    Rendering.message_background_color.get(
      snapshot.cumulate[Int](range, 0, JEdit_Rendering.line_background_elements, _ => {
        case (pri, Text.Info(_, elem)) => Some(pri max Rendering.message_pri(elem.name))
      }).foldLeft(0) { case (p1, Text.Info(_, p2)) => p1 max p2 })

  def line_separator(range: Text.Range): Boolean =
    snapshot.cumulate[Boolean](range, false, JEdit_Rendering.separator_elements, _ => {
      case _ => Some(true)
    }).exists(_.info)


  /* text color */

  def text_color(range: Text.Range, current_color: Color): List[Text.Info[Color]] = {
    if (current_color == Syntax_Style.hidden_color) List(Text.Info(range, current_color))
    else
      snapshot.cumulate(range, current_color, Rendering.text_color_elements, _ =>
        {
          case (_, Text.Info(_, elem)) => Rendering.get_text_color(elem.markup).map(color)
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
