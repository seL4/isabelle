/*  Title:      Tools/jEdit/src/isabelle_rendering.scala
    Author:     Makarius

Isabelle specific physical rendering and markup selection.
*/

package isabelle.jedit


import isabelle._

import java.awt.Color
import javax.swing.Icon
import java.io.{File => JFile}

import org.gjt.sp.jedit.syntax.{Token => JEditToken}
import org.gjt.sp.jedit.GUIUtilities
import org.gjt.sp.util.Log

import scala.collection.immutable.SortedMap


object Isabelle_Rendering
{
  def apply(snapshot: Document.Snapshot, options: Options): Isabelle_Rendering =
    new Isabelle_Rendering(snapshot, options)


  /* message priorities */

  private val writeln_pri = 1
  private val tracing_pri = 2
  private val warning_pri = 3
  private val legacy_pri = 4
  private val error_pri = 5

  private val message_pri = Map(
    Isabelle_Markup.WRITELN -> writeln_pri, Isabelle_Markup.WRITELN_MESSAGE -> writeln_pri,
    Isabelle_Markup.TRACING -> tracing_pri, Isabelle_Markup.TRACING_MESSAGE -> tracing_pri,
    Isabelle_Markup.WARNING -> warning_pri, Isabelle_Markup.WARNING_MESSAGE -> warning_pri,
    Isabelle_Markup.ERROR -> error_pri, Isabelle_Markup.ERROR_MESSAGE -> error_pri)


  /* icons */

  private def load_icon(name: String): Icon =
  {
    val icon = GUIUtilities.loadIcon(name)
    if (icon.getIconWidth < 0 || icon.getIconHeight < 0)
      Log.log(Log.ERROR, icon, "Bad icon: " + name)
    icon
  }

  private val gutter_icons = Map(
    warning_pri -> load_icon("16x16/status/dialog-information.png"),
    legacy_pri -> load_icon("16x16/status/dialog-warning.png"),
    error_pri -> load_icon("16x16/status/dialog-error.png"))


  /* token markup -- text styles */

  private val command_style: Map[String, Byte] =
  {
    import JEditToken._
    Map[String, Byte](
      Keyword.THY_END -> KEYWORD2,
      Keyword.THY_SCRIPT -> LABEL,
      Keyword.PRF_SCRIPT -> LABEL,
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


class Isabelle_Rendering private(val snapshot: Document.Snapshot, val options: Options)
{
  /* colors */

  def color_value(s: String): Color = Color_Value(options.string(s))

  val outdated_color = color_value("outdated_color")
  val unprocessed_color = color_value("unprocessed_color")
  val unprocessed1_color = color_value("unprocessed1_color")
  val running_color = color_value("running_color")
  val running1_color = color_value("running1_color")
  val light_color = color_value("light_color")
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

  def overview_color(range: Text.Range): Option[Color] =
  {
    if (snapshot.is_outdated) None
    else {
      val results =
        snapshot.cumulate_markup[(Protocol.Status, Int)](
          range, (Protocol.Status.init, 0),
          Some(Protocol.command_status_markup + Isabelle_Markup.WARNING + Isabelle_Markup.ERROR),
          {
            case ((status, pri), Text.Info(_, XML.Elem(markup, _))) =>
              if (markup.name == Isabelle_Markup.WARNING || markup.name == Isabelle_Markup.ERROR)
                (status, pri max Isabelle_Rendering.message_pri(markup.name))
              else (Protocol.command_status(status, markup), pri)
          })
      if (results.isEmpty) None
      else {
        val (status, pri) =
          ((Protocol.Status.init, 0) /: results) {
            case ((s1, p1), Text.Info(_, (s2, p2))) => (s1 + s2, p1 max p2) }

        if (pri == Isabelle_Rendering.warning_pri) Some(warning_color)
        else if (pri == Isabelle_Rendering.error_pri) Some(error_color)
        else if (status.is_unprocessed) Some(unprocessed_color)
        else if (status.is_running) Some(running_color)
        else if (status.is_failed) Some(error_color)
        else None
      }
    }
  }


  /* markup selectors */

  private val highlight_include =
    Set(Isabelle_Markup.SORT, Isabelle_Markup.TYP, Isabelle_Markup.TERM, Isabelle_Markup.PROP,
      Isabelle_Markup.ML_TYPING, Isabelle_Markup.TOKEN_RANGE, Isabelle_Markup.ENTITY,
      Isabelle_Markup.PATH, Isabelle_Markup.TYPING, Isabelle_Markup.FREE, Isabelle_Markup.SKOLEM,
      Isabelle_Markup.BOUND, Isabelle_Markup.VAR, Isabelle_Markup.TFREE, Isabelle_Markup.TVAR,
      Isabelle_Markup.ML_SOURCE, Isabelle_Markup.DOCUMENT_SOURCE)

  def highlight(range: Text.Range): Option[Text.Info[Color]] =
  {
    snapshot.select_markup(range, Some(highlight_include),
        {
          case Text.Info(info_range, XML.Elem(Markup(name, _), _)) if highlight_include(name) =>
            Text.Info(snapshot.convert(info_range), highlight_color)
        }) match { case Text.Info(_, info) #:: _ => Some(info) case _ => None }
  }


  private val hyperlink_include = Set(Isabelle_Markup.ENTITY, Isabelle_Markup.PATH)

  def hyperlink(range: Text.Range): Option[Text.Info[Hyperlink]] =
  {
    snapshot.cumulate_markup[List[Text.Info[Hyperlink]]](range, Nil, Some(hyperlink_include),
        {
          case (links, Text.Info(info_range, XML.Elem(Isabelle_Markup.Path(name), _)))
          if Path.is_ok(name) =>
            val jedit_file = Isabelle.thy_load.append(snapshot.node_name.dir, Path.explode(name))
            Text.Info(snapshot.convert(info_range), Hyperlink(jedit_file, 0, 0)) :: links

          case (links, Text.Info(info_range, XML.Elem(Markup(Isabelle_Markup.ENTITY, props), _)))
          if (props.find(
            { case (Markup.KIND, Isabelle_Markup.ML_OPEN) => true
              case (Markup.KIND, Isabelle_Markup.ML_STRUCT) => true
              case _ => false }).isEmpty) =>

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


  private def tooltip_text(msg: XML.Tree): String =
    Pretty.string_of(List(msg), margin = options.int("jedit_tooltip_margin"))

  def tooltip_message(range: Text.Range): Option[String] =
  {
    val msgs =
      snapshot.cumulate_markup[SortedMap[Long, String]](range, SortedMap.empty,
        Some(Set(Isabelle_Markup.WRITELN, Isabelle_Markup.WARNING, Isabelle_Markup.ERROR,
          Isabelle_Markup.BAD)),
        {
          case (msgs, Text.Info(_, msg @
              XML.Elem(Markup(markup, Isabelle_Markup.Serial(serial)), _)))
          if markup == Isabelle_Markup.WRITELN ||
              markup == Isabelle_Markup.WARNING ||
              markup == Isabelle_Markup.ERROR =>
            msgs + (serial -> tooltip_text(msg))
          case (msgs, Text.Info(_, msg @ XML.Elem(Markup(Isabelle_Markup.BAD, _), body)))
          if !body.isEmpty => msgs + (Document.new_id() -> tooltip_text(msg))
        }).toList.flatMap(_.info)
    if (msgs.isEmpty) None else Some(cat_lines(msgs.iterator.map(_._2)))
  }


  private val tooltips: Map[String, String] =
    Map(
      Isabelle_Markup.SORT -> "sort",
      Isabelle_Markup.TYP -> "type",
      Isabelle_Markup.TERM -> "term",
      Isabelle_Markup.PROP -> "proposition",
      Isabelle_Markup.TOKEN_RANGE -> "inner syntax token",
      Isabelle_Markup.FREE -> "free variable",
      Isabelle_Markup.SKOLEM -> "skolem variable",
      Isabelle_Markup.BOUND -> "bound variable",
      Isabelle_Markup.VAR -> "schematic variable",
      Isabelle_Markup.TFREE -> "free type variable",
      Isabelle_Markup.TVAR -> "schematic type variable",
      Isabelle_Markup.ML_SOURCE -> "ML source",
      Isabelle_Markup.DOCUMENT_SOURCE -> "document source")

  private val tooltip_elements =
    Set(Isabelle_Markup.ENTITY, Isabelle_Markup.TYPING, Isabelle_Markup.ML_TYPING,
      Isabelle_Markup.PATH) ++ tooltips.keys

  private def string_of_typing(kind: String, body: XML.Body): String =
    Pretty.string_of(List(Pretty.block(XML.Text(kind) :: Pretty.Break(1) :: body)),
      margin = options.int("jedit_tooltip_margin"))

  def tooltip(range: Text.Range): Option[String] =
  {
    def add(prev: Text.Info[List[(Boolean, String)]], r: Text.Range, p: (Boolean, String)) =
      if (prev.range == r) Text.Info(r, p :: prev.info) else Text.Info(r, List(p))

    val tips =
      snapshot.cumulate_markup[Text.Info[(List[(Boolean, String)])]](
        range, Text.Info(range, Nil), Some(tooltip_elements),
        {
          case (prev, Text.Info(r, XML.Elem(Isabelle_Markup.Entity(kind, name), _))) =>
            val kind1 = space_explode('_', kind).mkString(" ")
            add(prev, r, (true, kind1 + " " + quote(name)))
          case (prev, Text.Info(r, XML.Elem(Isabelle_Markup.Path(name), _)))
          if Path.is_ok(name) =>
            val jedit_file = Isabelle.thy_load.append(snapshot.node_name.dir, Path.explode(name))
            add(prev, r, (true, "file " + quote(jedit_file)))
          case (prev, Text.Info(r, XML.Elem(Markup(Isabelle_Markup.TYPING, _), body))) =>
            add(prev, r, (true, string_of_typing("::", body)))
          case (prev, Text.Info(r, XML.Elem(Markup(Isabelle_Markup.ML_TYPING, _), body))) =>
            add(prev, r, (false, string_of_typing("ML:", body)))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), _)))
          if tooltips.isDefinedAt(name) => add(prev, r, (true, tooltips(name)))
        }).toList.flatMap(_.info.info)

    val all_tips =
      (tips.filter(_._1) ++ tips.filter(!_._1).lastOption.toList).map(_._2)
    if (all_tips.isEmpty) None else Some(cat_lines(all_tips))
  }


  def gutter_message(range: Text.Range): Option[Icon] =
  {
    val results =
      snapshot.cumulate_markup[Int](range, 0,
        Some(Set(Isabelle_Markup.WARNING, Isabelle_Markup.ERROR)),
        {
          case (pri, Text.Info(_, XML.Elem(Markup(Isabelle_Markup.WARNING, _), body))) =>
            body match {
              case List(XML.Elem(Markup(Isabelle_Markup.LEGACY, _), _)) =>
                pri max Isabelle_Rendering.legacy_pri
              case _ => pri max Isabelle_Rendering.warning_pri
            }
          case (pri, Text.Info(_, XML.Elem(Markup(Isabelle_Markup.ERROR, _), _))) =>
            pri max Isabelle_Rendering.error_pri
        })
    val pri = (0 /: results) { case (p1, Text.Info(_, p2)) => p1 max p2 }
    Isabelle_Rendering.gutter_icons.get(pri)
  }


  private val squiggly_colors = Map(
    Isabelle_Rendering.writeln_pri -> writeln_color,
    Isabelle_Rendering.warning_pri -> warning_color,
    Isabelle_Rendering.error_pri -> error_color)

  def squiggly_underline(range: Text.Range): Stream[Text.Info[Color]] =
  {
    val results =
      snapshot.cumulate_markup[Int](range, 0,
        Some(Set(Isabelle_Markup.WRITELN, Isabelle_Markup.WARNING, Isabelle_Markup.ERROR)),
        {
          case (pri, Text.Info(_, XML.Elem(Markup(name, _), _)))
          if name == Isabelle_Markup.WRITELN ||
            name == Isabelle_Markup.WARNING ||
            name == Isabelle_Markup.ERROR => pri max Isabelle_Rendering.message_pri(name)
        })
    for {
      Text.Info(r, pri) <- results
      color <- squiggly_colors.get(pri)
    } yield Text.Info(r, color)
  }


  private val message_colors = Map(
    Isabelle_Rendering.writeln_pri -> writeln_message_color,
    Isabelle_Rendering.tracing_pri -> tracing_message_color,
    Isabelle_Rendering.warning_pri -> warning_message_color,
    Isabelle_Rendering.error_pri -> error_message_color)

  def line_background(range: Text.Range): Option[(Color, Boolean)] =
  {
    val messages =
      Set(Isabelle_Markup.WRITELN_MESSAGE, Isabelle_Markup.TRACING_MESSAGE,
        Isabelle_Markup.WARNING_MESSAGE, Isabelle_Markup.ERROR_MESSAGE)
    val results =
      snapshot.cumulate_markup[Int](range, 0, Some(messages),
        {
          case (pri, Text.Info(_, XML.Elem(Markup(name, _), _)))
          if name == Isabelle_Markup.WRITELN_MESSAGE ||
            name == Isabelle_Markup.TRACING_MESSAGE ||
            name == Isabelle_Markup.WARNING_MESSAGE ||
            name == Isabelle_Markup.ERROR_MESSAGE => pri max Isabelle_Rendering.message_pri(name)
        })
    val pri = (0 /: results) { case (p1, Text.Info(_, p2)) => p1 max p2 }

    val is_separator = pri > 0 &&
      snapshot.cumulate_markup[Boolean](range, false, Some(Set(Isabelle_Markup.SEPARATOR)),
        {
          case (_, Text.Info(_, XML.Elem(Markup(Isabelle_Markup.SEPARATOR, _), _))) => true
        }).exists(_.info)

    message_colors.get(pri).map((_, is_separator))
  }

  def background1(range: Text.Range): Stream[Text.Info[Color]] =
  {
    if (snapshot.is_outdated) Stream(Text.Info(range, outdated_color))
    else
      for {
        Text.Info(r, result) <-
          snapshot.cumulate_markup[(Option[Protocol.Status], Option[Color])](
            range, (Some(Protocol.Status.init), None),
            Some(Protocol.command_status_markup + Isabelle_Markup.WRITELN_MESSAGE +
              Isabelle_Markup.TRACING_MESSAGE + Isabelle_Markup.WARNING_MESSAGE +
              Isabelle_Markup.ERROR_MESSAGE + Isabelle_Markup.BAD + Isabelle_Markup.INTENSIFY),
            {
              case (((Some(status), color), Text.Info(_, XML.Elem(markup, _))))
              if (Protocol.command_status_markup(markup.name)) =>
                (Some(Protocol.command_status(status, markup)), color)
              case (_, Text.Info(_, XML.Elem(Markup(Isabelle_Markup.BAD, _), _))) =>
                (None, Some(bad_color))
              case (_, Text.Info(_, XML.Elem(Markup(Isabelle_Markup.INTENSIFY, _), _))) =>
                (None, Some(intensify_color))
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
    snapshot.select_markup(range,
      Some(Set(Isabelle_Markup.TOKEN_RANGE)),
      {
        case Text.Info(_, XML.Elem(Markup(Isabelle_Markup.TOKEN_RANGE, _), _)) => light_color
      })


  def foreground(range: Text.Range): Stream[Text.Info[Color]] =
    snapshot.select_markup(range,
      Some(Set(Isabelle_Markup.STRING, Isabelle_Markup.ALTSTRING, Isabelle_Markup.VERBATIM)),
      {
        case Text.Info(_, XML.Elem(Markup(Isabelle_Markup.STRING, _), _)) => quoted_color
        case Text.Info(_, XML.Elem(Markup(Isabelle_Markup.ALTSTRING, _), _)) => quoted_color
        case Text.Info(_, XML.Elem(Markup(Isabelle_Markup.VERBATIM, _), _)) => quoted_color
      })


  private val text_colors: Map[String, Color] = Map(
      Isabelle_Markup.STRING -> Color.BLACK,
      Isabelle_Markup.ALTSTRING -> Color.BLACK,
      Isabelle_Markup.VERBATIM -> Color.BLACK,
      Isabelle_Markup.LITERAL -> keyword1_color,
      Isabelle_Markup.DELIMITER -> Color.BLACK,
      Isabelle_Markup.TFREE -> tfree_color,
      Isabelle_Markup.TVAR -> tvar_color,
      Isabelle_Markup.FREE -> free_color,
      Isabelle_Markup.SKOLEM -> skolem_color,
      Isabelle_Markup.BOUND -> bound_color,
      Isabelle_Markup.VAR -> var_color,
      Isabelle_Markup.INNER_STRING -> inner_quoted_color,
      Isabelle_Markup.INNER_COMMENT -> inner_comment_color,
      Isabelle_Markup.DYNAMIC_FACT -> dynamic_color,
      Isabelle_Markup.ML_KEYWORD -> keyword1_color,
      Isabelle_Markup.ML_DELIMITER -> Color.BLACK,
      Isabelle_Markup.ML_NUMERAL -> inner_numeral_color,
      Isabelle_Markup.ML_CHAR -> inner_quoted_color,
      Isabelle_Markup.ML_STRING -> inner_quoted_color,
      Isabelle_Markup.ML_COMMENT -> inner_comment_color,
      Isabelle_Markup.ANTIQ -> antiquotation_color)

  private val text_color_elements = Set.empty[String] ++ text_colors.keys

  def text_color(range: Text.Range, color: Color)
      : Stream[Text.Info[Color]] =
  {
    snapshot.cumulate_markup(range, color, Some(text_color_elements),
      {
        case (_, Text.Info(_, XML.Elem(Markup(m, _), _)))
        if text_colors.isDefinedAt(m) => text_colors(m)
      })
  }
}
