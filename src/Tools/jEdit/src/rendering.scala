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
import org.gjt.sp.jedit.{jEdit, View}

import scala.collection.immutable.SortedMap


object Rendering
{
  def apply(snapshot: Document.Snapshot, options: Options): Rendering =
    new Rendering(snapshot, options)


  /* message priorities */

  private val writeln_pri = 1
  private val information_pri = 2
  private val tracing_pri = 3
  private val warning_pri = 4
  private val legacy_pri = 5
  private val error_pri = 6

  private val message_pri = Map(
    Markup.WRITELN -> writeln_pri, Markup.WRITELN_MESSAGE -> writeln_pri,
    Markup.TRACING -> tracing_pri, Markup.TRACING_MESSAGE -> tracing_pri,
    Markup.WARNING -> warning_pri, Markup.WARNING_MESSAGE -> warning_pri,
    Markup.ERROR -> error_pri, Markup.ERROR_MESSAGE -> error_pri)


  /* jEdit font */

  def font_family(): String = jEdit.getProperty("view.font")

  private def view_font_size(): Int = jEdit.getIntegerProperty("view.fontsize", 16)
  private val font_size0 = 5
  private val font_size1 = 250

  def font_size(scale: String): Float =
    (view_font_size() * PIDE.options.real(scale)).toFloat max font_size0 min font_size1

  def font_size_change(view: View, change: Int => Int)
  {
    val size = change(view_font_size()) max font_size0 min font_size1
    jEdit.setIntegerProperty("view.fontsize", size)
    jEdit.propertiesChanged()
    jEdit.saveSettings()
    view.getStatus.setMessageAndClear("Text font size: " + size)
  }


  /* popup window bounds */

  def popup_bounds: Double = (PIDE.options.real("jedit_popup_bounds") max 0.2) min 0.8


  /* token markup -- text styles */

  private val command_style: Map[String, Byte] =
  {
    import JEditToken._
    Map[String, Byte](
      Keyword.THY_END -> KEYWORD2,
      Keyword.THY_SCRIPT -> LABEL,
      Keyword.QED_SCRIPT -> DIGIT,
      Keyword.PRF_SCRIPT -> DIGIT,
      Keyword.PRF_ASM -> KEYWORD3,
      Keyword.PRF_ASM_GOAL -> KEYWORD3,
      Keyword.PRF_ASM_GOAL_SCRIPT -> DIGIT
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
      Token.Kind.CARTOUCHE -> COMMENT4,
      Token.Kind.SPACE -> NULL,
      Token.Kind.COMMENT -> COMMENT1,
      Token.Kind.ERROR -> INVALID
    ).withDefaultValue(NULL)
  }

  def token_markup(syntax: Outer_Syntax, token: Token): Byte =
    if (token.is_command) command_style(syntax.keyword_kind(token.content).getOrElse(""))
    else if (token.is_operator) JEditToken.OPERATOR
    else token_style(token.kind)

  private val ml_token_style: Map[ML_Lex.Kind.Value, Byte] =
  {
    import JEditToken._
    Map[ML_Lex.Kind.Value, Byte](
      ML_Lex.Kind.KEYWORD -> KEYWORD1,
      ML_Lex.Kind.IDENT -> NULL,
      ML_Lex.Kind.LONG_IDENT -> NULL,
      ML_Lex.Kind.TYPE_VAR -> NULL,
      ML_Lex.Kind.WORD -> NULL,
      ML_Lex.Kind.INT -> NULL,
      ML_Lex.Kind.REAL -> NULL,
      ML_Lex.Kind.CHAR -> LITERAL2,
      ML_Lex.Kind.STRING -> LITERAL1,
      ML_Lex.Kind.SPACE -> NULL,
      ML_Lex.Kind.COMMENT -> COMMENT1,
      ML_Lex.Kind.ERROR -> INVALID
    ).withDefaultValue(NULL)
  }

  def ml_token_markup(token: ML_Lex.Token): Byte =
    if (token.is_operator) JEditToken.OPERATOR
    else ml_token_style(token.kind)
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
  val bullet_color = color_value("bullet_color")
  val tooltip_color = color_value("tooltip_color")
  val writeln_color = color_value("writeln_color")
  val information_color = color_value("information_color")
  val warning_color = color_value("warning_color")
  val error_color = color_value("error_color")
  val error1_color = color_value("error1_color")
  val writeln_message_color = color_value("writeln_message_color")
  val information_message_color = color_value("information_message_color")
  val tracing_message_color = color_value("tracing_message_color")
  val warning_message_color = color_value("warning_message_color")
  val error_message_color = color_value("error_message_color")
  val bad_color = color_value("bad_color")
  val intensify_color = color_value("intensify_color")
  val quoted_color = color_value("quoted_color")
  val antiquoted_color = color_value("antiquoted_color")
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
  val inner_cartouche_color = color_value("inner_cartouche_color")
  val inner_comment_color = color_value("inner_comment_color")
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
            case ((status, pri), Text.Info(_, elem)) =>
              if (elem.name == Markup.WARNING || elem.name == Markup.ERROR)
                Some((status, pri max Rendering.message_pri(elem.name)))
              else if (overview_include(elem.name))
                Some((Protocol.command_status(status, elem.markup), pri))
              else None
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
      Markup.ENTITY, Markup.PATH, Markup.URL, Markup.SORTING, Markup.TYPING, Markup.FREE,
      Markup.SKOLEM, Markup.BOUND, Markup.VAR, Markup.TFREE, Markup.TVAR, Markup.ML_SOURCE,
      Markup.DOCUMENT_SOURCE)

  def highlight(range: Text.Range): Option[Text.Info[Color]] =
  {
    snapshot.select_markup(range, Some(highlight_include), _ =>
        {
          case Text.Info(info_range, elem) =>
            if (highlight_include(elem.name))
              Some(Text.Info(snapshot.convert(info_range), highlight_color))
            else None
        }) match { case Text.Info(_, info) :: _ => Some(info) case _ => None }
  }


  private val hyperlink_include = Set(Markup.ENTITY, Markup.PATH, Markup.URL)

  def hyperlink(range: Text.Range): Option[Text.Info[PIDE.editor.Hyperlink]] =
  {
    snapshot.cumulate_markup[List[Text.Info[PIDE.editor.Hyperlink]]](
      range, Nil, Some(hyperlink_include), _ =>
        {
          case (links, Text.Info(info_range, XML.Elem(Markup.Path(name), _)))
          if Path.is_ok(name) =>
            val jedit_file = PIDE.thy_load.append(snapshot.node_name.master_dir, Path.explode(name))
            val link = PIDE.editor.hyperlink_file(jedit_file)
            Some(Text.Info(snapshot.convert(info_range), link) :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup.Url(name), _))) =>
            val link = PIDE.editor.hyperlink_url(name)
            Some(Text.Info(snapshot.convert(info_range), link) :: links)

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
                    val link = PIDE.editor.hyperlink_file(jedit_file, line)
                    Some(Text.Info(snapshot.convert(info_range), link) :: links)
                  case None => None
                }

              case Position.Def_Id_Offset(id, offset) =>
                snapshot.state.find_command(snapshot.version, id) match {
                  case Some((node, command)) =>
                    PIDE.editor.hyperlink_command(snapshot, command, offset)
                      .map(link => (Text.Info(snapshot.convert(info_range), link) :: links))
                  case None => None
                }

              case _ => None
            }

          case _ => None
        }) match { case Text.Info(_, info :: _) :: _ => Some(info) case _ => None }
  }


  private val active_include =
    Set(Markup.BROWSER, Markup.GRAPHVIEW, Markup.SENDBACK, Markup.DIALOG, Markup.SIMP_TRACE)

  def active(range: Text.Range): Option[Text.Info[XML.Elem]] =
    snapshot.select_markup(range, Some(active_include), command_state =>
        {
          case Text.Info(info_range, elem @ Protocol.Dialog(_, serial, _))
          if !command_state.results.defined(serial) =>
            Some(Text.Info(snapshot.convert(info_range), elem))
          case Text.Info(info_range, elem) =>
            if (elem.name == Markup.BROWSER ||
                elem.name == Markup.GRAPHVIEW ||
                elem.name == Markup.SENDBACK ||
                elem.name == Markup.SIMP_TRACE)
              Some(Text.Info(snapshot.convert(info_range), elem))
            else None
        }) match { case Text.Info(_, info) :: _ => Some(info) case _ => None }


  def command_results(range: Text.Range): Command.Results =
  {
    val results =
      snapshot.select_markup[Command.Results](range, None, command_state =>
        { case _ => Some(command_state.results) }).map(_.info)
    (Command.Results.empty /: results)(_ ++ _)
  }

  def tooltip_message(range: Text.Range): Option[Text.Info[XML.Body]] =
  {
    val results =
      snapshot.cumulate_markup[List[Text.Info[Command.Results.Entry]]](range, Nil,
        Some(Set(Markup.WRITELN, Markup.WARNING, Markup.ERROR, Markup.BAD)), _ =>
        {
          case (msgs, Text.Info(info_range,
            XML.Elem(Markup(name, props @ Markup.Serial(serial)), body)))
          if name == Markup.WRITELN || name == Markup.WARNING || name == Markup.ERROR =>
            val entry: Command.Results.Entry =
              (serial -> XML.Elem(Markup(Markup.message(name), props), body))
            Some(Text.Info(snapshot.convert(info_range), entry) :: msgs)

          case (msgs, Text.Info(info_range, msg @ XML.Elem(Markup(Markup.BAD, _), body)))
          if !body.isEmpty =>
            val entry: Command.Results.Entry = (Document_ID.make(), msg)
            Some(Text.Info(snapshot.convert(info_range), entry) :: msgs)

          case _ => None
        }).flatMap(_.info)
    if (results.isEmpty) None
    else {
      val r = Text.Range(results.head.range.start, results.last.range.stop)
      val msgs = Command.Results.make(results.map(_.info))
      Some(Text.Info(r, Pretty.separate(msgs.entries.map(_._2).toList)))
    }
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
    Set(Markup.TIMING, Markup.ENTITY, Markup.SORTING, Markup.TYPING,
      Markup.ML_TYPING, Markup.PATH, Markup.URL) ++ tooltips.keys

  private def pretty_typing(kind: String, body: XML.Body): XML.Tree =
    Pretty.block(XML.Text(kind) :: Pretty.Break(1) :: body)

  private val timing_threshold: Double = options.real("jedit_timing_threshold")

  def tooltip(range: Text.Range): Option[Text.Info[XML.Body]] =
  {
    def add(prev: Text.Info[(Timing, List[(Boolean, XML.Tree)])],
      r0: Text.Range, p: (Boolean, XML.Tree)): Text.Info[(Timing, List[(Boolean, XML.Tree)])] =
    {
      val r = snapshot.convert(r0)
      val (t, info) = prev.info
      if (prev.range == r) Text.Info(r, (t, p :: info)) else Text.Info(r, (t, List(p)))
    }

    val results =
      snapshot.cumulate_markup[Text.Info[(Timing, List[(Boolean, XML.Tree)])]](
        range, Text.Info(range, (Timing.zero, Nil)), Some(tooltip_elements), _ =>
        {
          case (Text.Info(r, (t1, info)), Text.Info(_, XML.Elem(Markup.Timing(t2), _))) =>
            Some(Text.Info(r, (t1 + t2, info)))
          case (prev, Text.Info(r, XML.Elem(Markup.Entity(kind, name), _))) =>
            val kind1 = space_explode('_', kind).mkString(" ")
            val txt1 = kind1 + " " + quote(name)
            val t = prev.info._1
            val txt2 =
              if (kind == Markup.COMMAND && t.elapsed.seconds >= timing_threshold)
                "\n" + t.message
              else ""
            Some(add(prev, r, (true, XML.Text(txt1 + txt2))))
          case (prev, Text.Info(r, XML.Elem(Markup.Path(name), _)))
          if Path.is_ok(name) =>
            val jedit_file = PIDE.thy_load.append(snapshot.node_name.master_dir, Path.explode(name))
            Some(add(prev, r, (true, XML.Text("file " + quote(jedit_file)))))
          case (prev, Text.Info(r, XML.Elem(Markup.Url(name), _))) =>
            Some(add(prev, r, (true, XML.Text("URL " + quote(name)))))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), body)))
          if name == Markup.SORTING || name == Markup.TYPING =>
            Some(add(prev, r, (true, pretty_typing("::", body))))
          case (prev, Text.Info(r, XML.Elem(Markup(Markup.ML_TYPING, _), body))) =>
            Some(add(prev, r, (false, pretty_typing("ML:", body))))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), _))) =>
            if (tooltips.isDefinedAt(name))
              Some(add(prev, r, (true, XML.Text(tooltips(name)))))
            else None
        }).map(_.info)

    results.map(_.info).flatMap(_._2) match {
      case Nil => None
      case tips =>
        val r = Text.Range(results.head.range.start, results.last.range.stop)
        val all_tips = (tips.filter(_._1) ++ tips.filter(!_._1).lastOption.toList).map(_._2)
        Some(Text.Info(r, Library.separate(Pretty.FBreak, all_tips)))
    }
  }

  val tooltip_margin: Int = options.int("jedit_tooltip_margin")

  lazy val tooltip_close_icon = JEdit_Lib.load_icon(options.string("tooltip_close_icon"))
  lazy val tooltip_detach_icon = JEdit_Lib.load_icon(options.string("tooltip_detach_icon"))


  private lazy val gutter_icons = Map(
    Rendering.information_pri -> JEdit_Lib.load_icon(options.string("gutter_information_icon")),
    Rendering.warning_pri -> JEdit_Lib.load_icon(options.string("gutter_warning_icon")),
    Rendering.legacy_pri -> JEdit_Lib.load_icon(options.string("gutter_legacy_icon")),
    Rendering.error_pri -> JEdit_Lib.load_icon(options.string("gutter_error_icon")))

  private val gutter_elements = Set(Markup.WRITELN, Markup.WARNING, Markup.ERROR)

  def gutter_message(range: Text.Range): Option[Icon] =
  {
    val results =
      snapshot.cumulate_markup[Int](range, 0, Some(gutter_elements), _ =>
        {
          case (pri, Text.Info(_, XML.Elem(Markup(Markup.WRITELN, _),
              List(XML.Elem(Markup(Markup.INFORMATION, _), _))))) =>
            Some(pri max Rendering.information_pri)
          case (pri, Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), body))) =>
            body match {
              case List(XML.Elem(Markup(Markup.LEGACY, _), _)) =>
                Some(pri max Rendering.legacy_pri)
              case _ =>
                Some(pri max Rendering.warning_pri)
            }
          case (pri, Text.Info(_, XML.Elem(Markup(Markup.ERROR, _), _))) =>
            Some(pri max Rendering.error_pri)
          case _ => None
        })
    val pri = (0 /: results) { case (p1, Text.Info(_, p2)) => p1 max p2 }
    gutter_icons.get(pri)
  }


  private val squiggly_colors = Map(
    Rendering.writeln_pri -> writeln_color,
    Rendering.information_pri -> information_color,
    Rendering.warning_pri -> warning_color,
    Rendering.error_pri -> error_color)

  private val squiggly_include = Set(Markup.WRITELN, Markup.WARNING, Markup.ERROR)

  def squiggly_underline(range: Text.Range): List[Text.Info[Color]] =
  {
    val results =
      snapshot.cumulate_markup[Int](range, 0, Some(squiggly_include), _ =>
        {
          case (pri, Text.Info(_, elem)) =>
            if (Protocol.is_information(elem))
              Some(pri max Rendering.information_pri)
            else if (squiggly_include.contains(elem.name))
              Some(pri max Rendering.message_pri(elem.name))
            else None
        })
    for {
      Text.Info(r, pri) <- results
      color <- squiggly_colors.get(pri)
    } yield Text.Info(r, color)
  }


  private val message_colors = Map(
    Rendering.writeln_pri -> writeln_message_color,
    Rendering.information_pri -> information_message_color,
    Rendering.tracing_pri -> tracing_message_color,
    Rendering.warning_pri -> warning_message_color,
    Rendering.error_pri -> error_message_color)

  private val line_background_elements =
    Set(Markup.WRITELN_MESSAGE, Markup.TRACING_MESSAGE, Markup.WARNING_MESSAGE,
      Markup.ERROR_MESSAGE, Markup.INFORMATION)

  def line_background(range: Text.Range): Option[(Color, Boolean)] =
  {
    val results =
      snapshot.cumulate_markup[Int](range, 0, Some(line_background_elements), _ =>
        {
          case (pri, Text.Info(_, elem)) =>
            val name = elem.name
            if (name == Markup.INFORMATION)
              Some(pri max Rendering.information_pri)
            else if (name == Markup.WRITELN_MESSAGE || name == Markup.TRACING_MESSAGE ||
                elem.name == Markup.WARNING_MESSAGE || name == Markup.ERROR_MESSAGE)
              Some(pri max Rendering.message_pri(name))
            else None
        })
    val pri = (0 /: results) { case (p1, Text.Info(_, p2)) => p1 max p2 }

    val is_separator = pri > 0 &&
      snapshot.cumulate_markup[Boolean](range, false, Some(Set(Markup.SEPARATOR)), _ =>
        {
          case (_, Text.Info(_, elem)) =>
            if (elem.name == Markup.SEPARATOR) Some(true) else None
        }).exists(_.info)

    message_colors.get(pri).map((_, is_separator))
  }


  def output_messages(st: Command.State): List[XML.Tree] =
    st.results.entries.map(_._2).filterNot(Protocol.is_result(_)).toList


  private val background1_include =
    Protocol.command_status_markup + Markup.WRITELN_MESSAGE + Markup.TRACING_MESSAGE +
      Markup.WARNING_MESSAGE + Markup.ERROR_MESSAGE + Markup.BAD + Markup.INTENSIFY ++
      active_include

  def background1(range: Text.Range): List[Text.Info[Color]] =
  {
    if (snapshot.is_outdated) List(Text.Info(range, outdated_color))
    else
      for {
        Text.Info(r, result) <-
          snapshot.cumulate_markup[(Option[Protocol.Status], Option[Color])](
            range, (Some(Protocol.Status.init), None), Some(background1_include), command_state =>
            {
              case (((Some(status), color), Text.Info(_, XML.Elem(markup, _))))
              if (Protocol.command_status_markup(markup.name)) =>
                Some((Some(Protocol.command_status(status, markup)), color))
              case (_, Text.Info(_, XML.Elem(Markup(Markup.BAD, _), _))) =>
                Some((None, Some(bad_color)))
              case (_, Text.Info(_, XML.Elem(Markup(Markup.INTENSIFY, _), _))) =>
                Some((None, Some(intensify_color)))
              case (acc, Text.Info(_, Protocol.Dialog(_, serial, result))) =>
                command_state.results.get(serial) match {
                  case Some(Protocol.Dialog_Result(res)) if res == result =>
                    Some((None, Some(active_result_color)))
                  case _ =>
                    Some((None, Some(active_color)))
                }
              case (_, Text.Info(_, elem)) =>
                if (active_include(elem.name)) Some((None, Some(active_color)))
                else None
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


  def background2(range: Text.Range): List[Text.Info[Color]] =
    snapshot.select_markup(range, Some(Set(Markup.TOKEN_RANGE)), _ =>
      {
        case Text.Info(_, elem) =>
          if (elem.name == Markup.TOKEN_RANGE) Some(light_color) else None
      })


  def bullet(range: Text.Range): List[Text.Info[Color]] =
    snapshot.select_markup(range, Some(Set(Markup.BULLET)), _ =>
      {
        case Text.Info(_, elem) =>
          if (elem.name == Markup.BULLET) Some(bullet_color) else None
      })


  private val foreground_include =
    Set(Markup.STRING, Markup.ALTSTRING, Markup.VERBATIM, Markup.ANTIQ)

  def foreground(range: Text.Range): List[Text.Info[Color]] =
    snapshot.select_markup(range, Some(foreground_include), _ =>
      {
        case Text.Info(_, elem) =>
          if (elem.name == Markup.ANTIQ) Some(antiquoted_color)
          else if (foreground_include.contains(elem.name)) Some(quoted_color)
          else None
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
      Markup.INNER_CARTOUCHE -> inner_cartouche_color,
      Markup.INNER_COMMENT -> inner_comment_color,
      Markup.DYNAMIC_FACT -> dynamic_color,
      Markup.ML_KEYWORD -> keyword1_color,
      Markup.ML_DELIMITER -> Color.BLACK,
      Markup.ML_NUMERAL -> inner_numeral_color,
      Markup.ML_CHAR -> inner_quoted_color,
      Markup.ML_STRING -> inner_quoted_color,
      Markup.ML_COMMENT -> inner_comment_color)

  private val text_color_elements = text_colors.keySet

  def text_color(range: Text.Range, color: Color): List[Text.Info[Color]] =
  {
    if (color == Token_Markup.hidden_color) List(Text.Info(range, color))
    else
      snapshot.cumulate_markup(range, color, Some(text_color_elements), _ =>
        {
          case (_, Text.Info(_, elem)) => text_colors.get(elem.name)
        })
  }


  /* nested text structure -- folds */

  private val fold_depth_include = Set(Markup.TEXT_FOLD, Markup.GOAL, Markup.SUBGOAL)

  def fold_depth(range: Text.Range): List[Text.Info[Int]] =
    snapshot.cumulate_markup[Int](range, 0, Some(fold_depth_include), _ =>
      {
        case (depth, Text.Info(_, elem)) =>
          if (fold_depth_include(elem.name)) Some(depth + 1) else None
      })
}
