/*  Title:      Tools/jEdit/src/rendering.scala
    Author:     Makarius

Isabelle-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle.jedit


import isabelle._

import java.awt.Color
import javax.swing.Icon

import org.gjt.sp.jedit.syntax.{Token => JEditToken}
import org.gjt.sp.jedit.{jEdit, GUIUtilities}

import scala.collection.immutable.SortedMap


object Rendering
{
  def apply(snapshot: Document.Snapshot, options: Options): Rendering =
    new Rendering(snapshot, options)


  /* message priorities */

  private val writeln_pri = 1
  private val tracing_pri = 2
  private val warning_pri = 3
  private val legacy_pri = 4
  private val error_pri = 5

  private val message_pri = Map(
    Markup.WRITELN -> writeln_pri, Markup.WRITELN_MESSAGE -> writeln_pri,
    Markup.TRACING -> tracing_pri, Markup.TRACING_MESSAGE -> tracing_pri,
    Markup.WARNING -> warning_pri, Markup.WARNING_MESSAGE -> warning_pri,
    Markup.ERROR -> error_pri, Markup.ERROR_MESSAGE -> error_pri)


  /* icons */

  private def load_icon(name: String): Icon =
  {
    val icon = GUIUtilities.loadIcon(name)
    if (icon.getIconWidth < 0 || icon.getIconHeight < 0) error("Bad icon: " + name)
    else icon
  }

  private val gutter_icons = Map(
    warning_pri -> load_icon("16x16/status/dialog-information.png"),
    legacy_pri -> load_icon("16x16/status/dialog-warning.png"),
    error_pri -> load_icon("16x16/status/dialog-error.png"))

  val tooltip_close_icon = load_icon("16x16/actions/document-close.png")
  val tooltip_detach_icon = load_icon("16x16/actions/window-new.png")


  /* jEdit font */

  def font_family(): String = jEdit.getProperty("view.font")

  def font_size(scale: String): Float =
    (jEdit.getIntegerProperty("view.fontsize", 16) * PIDE.options.real(scale)).toFloat


  /* token markup -- text styles */

  private val command_style: Map[String, Byte] =
  {
    import JEditToken._
    Map[String, Byte](
      Keyword.THY_END -> KEYWORD2,
      Keyword.THY_SCRIPT -> LABEL,
      Keyword.PRF_SCRIPT -> DIGIT,
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
      Token.Kind.STRING -> LITERAL1,
      Token.Kind.ALT_STRING -> LITERAL2,
      Token.Kind.VERBATIM -> COMMENT3,
      Token.Kind.SPACE -> NULL,
      Token.Kind.COMMENT -> COMMENT1,
      Token.Kind.ERROR -> INVALID
    ).withDefaultValue(NULL)
  }

  def token_markup(syntax: Outer_Syntax, token: Token): Byte =
    if (token.is_command) command_style(syntax.keyword_kind(token.content).getOrElse(""))
    else if (token.is_operator) JEditToken.OPERATOR
    else token_style(token.kind)
}


class Rendering private(val snapshot: Document.Snapshot, val options: Options)
{
  /* colors */

  def color_value(s: String): Color = Color_Value(options.string(s))

  val outdated_color = color_value("outdated_color")
  val unprocessed_color = color_value("unprocessed_color")
  val unprocessed1_color = color_value("unprocessed1_color")
  val running_color = color_value("running_color")
  val running1_color = color_value("running1_color")
  val light_color = color_value("light_color")
  val tooltip_color = color_value("tooltip_color")
  val writeln_color = color_value("writeln_color")
  val warning_color = color_value("warning_color")
  val error_color = color_value("error_color")
  val error1_color = color_value("error1_color")
  val writeln_message_color = color_value("writeln_message_color")
  val tracing_message_color = color_value("tracing_message_color")
  val warning_message_color = color_value("warning_message_color")
  val error_message_color = color_value("error_message_color")
  val bad_color = color_value("bad_color")
  val intensify_color = color_value("intensify_color")
  val quoted_color = color_value("quoted_color")
  val highlight_color = color_value("highlight_color")
  val hyperlink_color = color_value("hyperlink_color")
  val active_color = color_value("active_color")
  val active_hover_color = color_value("active_hover_color")
  val active_result_color = color_value("active_result_color")
  val keyword1_color = color_value("keyword1_color")
  val keyword2_color = color_value("keyword2_color")

  val tfree_color = color_value("tfree_color")
  val tvar_color = color_value("tvar_color")
  val free_color = color_value("free_color")
  val skolem_color = color_value("skolem_color")
  val bound_color = color_value("bound_color")
  val var_color = color_value("var_color")
  val inner_numeral_color = color_value("inner_numeral_color")
  val inner_quoted_color = color_value("inner_quoted_color")
  val inner_comment_color = color_value("inner_comment_color")
  val antiquotation_color = color_value("antiquotation_color")
  val dynamic_color = color_value("dynamic_color")


  /* command overview */

  val overview_limit = options.int("jedit_text_overview_limit")

  private val overview_include = Protocol.command_status_markup + Markup.WARNING + Markup.ERROR

  def overview_color(range: Text.Range): Option[Color] =
  {
    if (snapshot.is_outdated) None
    else {
      val results =
        snapshot.cumulate_markup[(Protocol.Status, Int)](
          range, (Protocol.Status.init, 0), Some(overview_include), _ =>
          {
            case ((status, pri), Text.Info(_, XML.Elem(markup, _)))
            if overview_include(markup.name) =>
              if (markup.name == Markup.WARNING || markup.name == Markup.ERROR)
                (status, pri max Rendering.message_pri(markup.name))
              else (Protocol.command_status(status, markup), pri)
          })
      if (results.isEmpty) None
      else {
        val (status, pri) =
          ((Protocol.Status.init, 0) /: results) {
            case ((s1, p1), Text.Info(_, (s2, p2))) => (s1 + s2, p1 max p2) }

        if (status.is_running) Some(running_color)
        else if (pri == Rendering.warning_pri) Some(warning_color)
        else if (pri == Rendering.error_pri) Some(error_color)
        else if (status.is_unprocessed) Some(unprocessed_color)
        else if (status.is_failed) Some(error_color)
        else None
      }
    }
  }


  /* markup selectors */

  private val highlight_include =
    Set(Markup.SORT, Markup.TYP, Markup.TERM, Markup.PROP, Markup.ML_TYPING, Markup.TOKEN_RANGE,
      Markup.ENTITY, Markup.PATH, Markup.SORTING, Markup.TYPING, Markup.FREE, Markup.SKOLEM,
      Markup.BOUND, Markup.VAR, Markup.TFREE, Markup.TVAR, Markup.ML_SOURCE, Markup.DOCUMENT_SOURCE)

  def highlight(range: Text.Range): Option[Text.Info[Color]] =
  {
    snapshot.select_markup(range, Some(highlight_include), _ =>
        {
          case Text.Info(info_range, XML.Elem(Markup(name, _), _)) if highlight_include(name) =>
            Text.Info(snapshot.convert(info_range), highlight_color)
        }) match { case Text.Info(_, info) #:: _ => Some(info) case _ => None }
  }


  private val hyperlink_include = Set(Markup.ENTITY, Markup.PATH)

  def hyperlink(range: Text.Range): Option[Text.Info[Hyperlink]] =
  {
    snapshot.cumulate_markup[List[Text.Info[Hyperlink]]](range, Nil, Some(hyperlink_include), _ =>
        {
          case (links, Text.Info(info_range, XML.Elem(Markup.Path(name), _)))
          if Path.is_ok(name) =>
            val jedit_file = PIDE.thy_load.append(snapshot.node_name.dir, Path.explode(name))
            Text.Info(snapshot.convert(info_range), Hyperlink(jedit_file, 0, 0)) :: links

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.ENTITY, props), _)))
          if !props.exists(
            { case (Markup.KIND, Markup.ML_OPEN) => true
              case (Markup.KIND, Markup.ML_STRUCT) => true
              case _ => false }) =>

            props match {
              case Position.Def_Line_File(line, name) if Path.is_ok(name) =>
                Isabelle_System.source_file(Path.explode(name)) match {
                  case Some(path) =>
                    val jedit_file = Isabelle_System.platform_path(path)
                    Text.Info(snapshot.convert(info_range), Hyperlink(jedit_file, line, 0)) :: links
                  case None => links
                }

              case Position.Def_Id_Offset(id, offset) =>
                snapshot.state.find_command(snapshot.version, id) match {
                  case Some((node, command)) =>
                    val sources =
                      node.commands.iterator.takeWhile(_ != command).map(_.source) ++
                        Iterator.single(command.source(Text.Range(0, command.decode(offset))))
                    val (line, column) = ((1, 1) /: sources)(Symbol.advance_line_column)
                    Text.Info(snapshot.convert(info_range),
                      Hyperlink(command.node_name.node, line, column)) :: links
                  case None => links
                }

              case _ => links
            }
        }) match { case Text.Info(_, info :: _) #:: _ => Some(info) case _ => None }
  }


  private val active_include =
    Set(Markup.BROWSER, Markup.GRAPHVIEW, Markup.SENDBACK, Markup.DIALOG)

  def active(range: Text.Range): Option[Text.Info[XML.Elem]] =
    snapshot.select_markup(range, Some(active_include), command_state =>
        {
          case Text.Info(info_range, elem @ Protocol.Dialog(_, serial, _))
          if !command_state.results.defined(serial) =>
            Text.Info(snapshot.convert(info_range), elem)
          case Text.Info(info_range, elem @ XML.Elem(Markup(name, _), _))
          if name == Markup.BROWSER || name == Markup.GRAPHVIEW || name == Markup.SENDBACK =>
            Text.Info(snapshot.convert(info_range), elem)
        }) match { case Text.Info(_, info) #:: _ => Some(info) case _ => None }


  def command_results(range: Text.Range): Command.Results =
  {
    val results =
      snapshot.select_markup[Command.Results](range, None, command_state =>
        { case _ => command_state.results }).map(_.info)
    (Command.Results.empty /: results)(_ ++ _)
  }

  def tooltip_message(range: Text.Range): XML.Body =
  {
    val msgs =
      Command.Results.merge(
        snapshot.cumulate_markup[Command.Results](range, Command.Results.empty,
          Some(Set(Markup.WRITELN, Markup.WARNING, Markup.ERROR, Markup.BAD)), _ =>
          {
            case (msgs, Text.Info(_, XML.Elem(Markup(name, props @ Markup.Serial(serial)), body)))
            if name == Markup.WRITELN ||
                name == Markup.WARNING ||
                name == Markup.ERROR =>
              msgs + (serial -> XML.Elem(Markup(Markup.message(name), props), body))
            case (msgs, Text.Info(_, msg @ XML.Elem(Markup(Markup.BAD, _), body)))
            if !body.isEmpty => msgs + (Document.new_id() -> msg)
          }).map(_.info))
    Pretty.separate(msgs.entries.map(_._2).toList)
  }


  private val tooltips: Map[String, String] =
    Map(
      Markup.SORT -> "sort",
      Markup.TYP -> "type",
      Markup.TERM -> "term",
      Markup.PROP -> "proposition",
      Markup.TOKEN_RANGE -> "inner syntax token",
      Markup.FREE -> "free variable",
      Markup.SKOLEM -> "skolem variable",
      Markup.BOUND -> "bound variable",
      Markup.VAR -> "schematic variable",
      Markup.TFREE -> "free type variable",
      Markup.TVAR -> "schematic type variable",
      Markup.ML_SOURCE -> "ML source",
      Markup.DOCUMENT_SOURCE -> "document source")

  private val tooltip_elements =
    Set(Markup.ENTITY, Markup.SORTING, Markup.TYPING, Markup.ML_TYPING, Markup.PATH) ++
      tooltips.keys

  private def pretty_typing(kind: String, body: XML.Body): XML.Tree =
    Pretty.block(XML.Text(kind) :: Pretty.Break(1) :: body)

  def tooltip(range: Text.Range): XML.Body =
  {
    def add(prev: Text.Info[List[(Boolean, XML.Tree)]], r: Text.Range, p: (Boolean, XML.Tree)) =
      if (prev.range == r) Text.Info(r, p :: prev.info) else Text.Info(r, List(p))

    val tips =
      snapshot.cumulate_markup[Text.Info[(List[(Boolean, XML.Tree)])]](
        range, Text.Info(range, Nil), Some(tooltip_elements), _ =>
        {
          case (prev, Text.Info(r, XML.Elem(Markup.Entity(kind, name), _))) =>
            val kind1 = space_explode('_', kind).mkString(" ")
            add(prev, r, (true, XML.Text(kind1 + " " + quote(name))))
          case (prev, Text.Info(r, XML.Elem(Markup.Path(name), _)))
          if Path.is_ok(name) =>
            val jedit_file = PIDE.thy_load.append(snapshot.node_name.dir, Path.explode(name))
            add(prev, r, (true, XML.Text("file " + quote(jedit_file))))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), body)))
          if name == Markup.SORTING || name == Markup.TYPING =>
            add(prev, r, (true, pretty_typing("::", body)))
          case (prev, Text.Info(r, XML.Elem(Markup(Markup.ML_TYPING, _), body))) =>
            add(prev, r, (false, pretty_typing("ML:", body)))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), _)))
          if tooltips.isDefinedAt(name) => add(prev, r, (true, XML.Text(tooltips(name))))
        }).toList.flatMap(_.info.info)

    val all_tips =
      (tips.filter(_._1) ++ tips.filter(!_._1).lastOption.toList).map(_._2)
    Library.separate(Pretty.FBreak, all_tips.toList)
  }

  val tooltip_margin: Int = options.int("jedit_tooltip_margin")
  val tooltip_bounds: Double = (options.real("jedit_tooltip_bounds") max 0.2) min 0.8


  def gutter_message(range: Text.Range): Option[Icon] =
  {
    val results =
      snapshot.cumulate_markup[Int](range, 0, Some(Set(Markup.WARNING, Markup.ERROR)), _ =>
        {
          case (pri, Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), body))) =>
            body match {
              case List(XML.Elem(Markup(Markup.LEGACY, _), _)) =>
                pri max Rendering.legacy_pri
              case _ => pri max Rendering.warning_pri
            }
          case (pri, Text.Info(_, XML.Elem(Markup(Markup.ERROR, _), _))) =>
            pri max Rendering.error_pri
        })
    val pri = (0 /: results) { case (p1, Text.Info(_, p2)) => p1 max p2 }
    Rendering.gutter_icons.get(pri)
  }


  private val squiggly_colors = Map(
    Rendering.writeln_pri -> writeln_color,
    Rendering.warning_pri -> warning_color,
    Rendering.error_pri -> error_color)

  def squiggly_underline(range: Text.Range): Stream[Text.Info[Color]] =
  {
    val results =
      snapshot.cumulate_markup[Int](range, 0,
        Some(Set(Markup.WRITELN, Markup.WARNING, Markup.ERROR)), _ =>
        {
          case (pri, Text.Info(_, XML.Elem(Markup(name, _), _)))
          if name == Markup.WRITELN ||
            name == Markup.WARNING ||
            name == Markup.ERROR => pri max Rendering.message_pri(name)
        })
    for {
      Text.Info(r, pri) <- results
      color <- squiggly_colors.get(pri)
    } yield Text.Info(r, color)
  }


  private val messages_include =
    Set(Markup.WRITELN_MESSAGE, Markup.TRACING_MESSAGE, Markup.WARNING_MESSAGE, Markup.ERROR_MESSAGE)

  private val message_colors = Map(
    Rendering.writeln_pri -> writeln_message_color,
    Rendering.tracing_pri -> tracing_message_color,
    Rendering.warning_pri -> warning_message_color,
    Rendering.error_pri -> error_message_color)

  def line_background(range: Text.Range): Option[(Color, Boolean)] =
  {
    val results =
      snapshot.cumulate_markup[Int](range, 0, Some(messages_include), _ =>
        {
          case (pri, Text.Info(_, XML.Elem(Markup(name, _), _)))
          if name == Markup.WRITELN_MESSAGE ||
            name == Markup.TRACING_MESSAGE ||
            name == Markup.WARNING_MESSAGE ||
            name == Markup.ERROR_MESSAGE => pri max Rendering.message_pri(name)
        })
    val pri = (0 /: results) { case (p1, Text.Info(_, p2)) => p1 max p2 }

    val is_separator = pri > 0 &&
      snapshot.cumulate_markup[Boolean](range, false, Some(Set(Markup.SEPARATOR)), _ =>
        {
          case (_, Text.Info(_, XML.Elem(Markup(Markup.SEPARATOR, _), _))) => true
        }).exists(_.info)

    message_colors.get(pri).map((_, is_separator))
  }


  def output_messages(st: Command.State): List[XML.Tree] =
  {
    st.results.entries.map(_._2).filterNot(Protocol.is_result(_)).toList
  }


  private val background1_include =
    Protocol.command_status_markup + Markup.WRITELN_MESSAGE + Markup.TRACING_MESSAGE +
      Markup.WARNING_MESSAGE + Markup.ERROR_MESSAGE + Markup.BAD + Markup.INTENSIFY ++
      active_include

  def background1(range: Text.Range): Stream[Text.Info[Color]] =
  {
    if (snapshot.is_outdated) Stream(Text.Info(range, outdated_color))
    else
      for {
        Text.Info(r, result) <-
          snapshot.cumulate_markup[(Option[Protocol.Status], Option[Color])](
            range, (Some(Protocol.Status.init), None), Some(background1_include), command_state =>
            {
              case (((Some(status), color), Text.Info(_, XML.Elem(markup, _))))
              if (Protocol.command_status_markup(markup.name)) =>
                (Some(Protocol.command_status(status, markup)), color)
              case (_, Text.Info(_, XML.Elem(Markup(Markup.BAD, _), _))) =>
                (None, Some(bad_color))
              case (_, Text.Info(_, XML.Elem(Markup(Markup.INTENSIFY, _), _))) =>
                (None, Some(intensify_color))
              case (acc, Text.Info(_, elem @ XML.Elem(Markup(Markup.DIALOG, _), _))) =>
                // FIXME pattern match problem in scala-2.9.2 (!??)
                elem match {
                  case Protocol.Dialog(_, serial, result) =>
                    command_state.results.get(serial) match {
                      case Some(Protocol.Dialog_Result(res)) if res == result =>
                        (None, Some(active_result_color))
                      case _ =>
                        (None, Some(active_color))
                    }
                  case _ => acc
                }
              case (_, Text.Info(_, XML.Elem(markup, _))) if active_include(markup.name) =>
                (None, Some(active_color))
            })
        color <-
          (result match {
            case (Some(status), opt_color) =>
              if (status.is_unprocessed) Some(unprocessed1_color)
              else if (status.is_running) Some(running1_color)
              else opt_color
            case (_, opt_color) => opt_color
          })
      } yield Text.Info(r, color)
  }


  def background2(range: Text.Range): Stream[Text.Info[Color]] =
    snapshot.select_markup(range, Some(Set(Markup.TOKEN_RANGE)), _ =>
      {
        case Text.Info(_, XML.Elem(Markup(Markup.TOKEN_RANGE, _), _)) => light_color
      })


  def foreground(range: Text.Range): Stream[Text.Info[Color]] =
    snapshot.select_markup(range, Some(Set(Markup.STRING, Markup.ALTSTRING, Markup.VERBATIM)), _ =>
      {
        case Text.Info(_, XML.Elem(Markup(Markup.STRING, _), _)) => quoted_color
        case Text.Info(_, XML.Elem(Markup(Markup.ALTSTRING, _), _)) => quoted_color
        case Text.Info(_, XML.Elem(Markup(Markup.VERBATIM, _), _)) => quoted_color
      })


  private val text_colors: Map[String, Color] = Map(
      Markup.KEYWORD1 -> keyword1_color,
      Markup.KEYWORD2 -> keyword2_color,
      Markup.STRING -> Color.BLACK,
      Markup.ALTSTRING -> Color.BLACK,
      Markup.VERBATIM -> Color.BLACK,
      Markup.LITERAL -> keyword1_color,
      Markup.DELIMITER -> Color.BLACK,
      Markup.TFREE -> tfree_color,
      Markup.TVAR -> tvar_color,
      Markup.FREE -> free_color,
      Markup.SKOLEM -> skolem_color,
      Markup.BOUND -> bound_color,
      Markup.VAR -> var_color,
      Markup.INNER_STRING -> inner_quoted_color,
      Markup.INNER_COMMENT -> inner_comment_color,
      Markup.DYNAMIC_FACT -> dynamic_color,
      Markup.ML_KEYWORD -> keyword1_color,
      Markup.ML_DELIMITER -> Color.BLACK,
      Markup.ML_NUMERAL -> inner_numeral_color,
      Markup.ML_CHAR -> inner_quoted_color,
      Markup.ML_STRING -> inner_quoted_color,
      Markup.ML_COMMENT -> inner_comment_color,
      Markup.ANTIQ -> antiquotation_color)

  private val text_color_elements = Set.empty[String] ++ text_colors.keys

  def text_color(range: Text.Range, color: Color)
      : Stream[Text.Info[Color]] =
  {
    if (color == Token_Markup.hidden_color) Stream(Text.Info(range, color))
    else
      snapshot.cumulate_markup(range, color, Some(text_color_elements), _ =>
        {
          case (_, Text.Info(_, XML.Elem(Markup(m, _), _)))
          if text_colors.isDefinedAt(m) => text_colors(m)
        })
  }


  /* nested text structure -- folds */

  private val fold_depth_include = Set(Markup.TEXT_FOLD, Markup.GOAL, Markup.SUBGOAL)

  def fold_depth(range: Text.Range): Stream[Text.Info[Int]] =
    snapshot.cumulate_markup[Int](range, 0, Some(fold_depth_include), _ =>
      {
        case (depth, Text.Info(_, XML.Elem(Markup(name, _), _)))
        if fold_depth_include(name) => depth + 1
      })
}
