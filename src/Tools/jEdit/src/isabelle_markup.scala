/*  Title:      Tools/jEdit/src/isabelle_markup.scala
    Author:     Makarius

Isabelle specific physical rendering and markup selection.
*/

package isabelle.jedit


import isabelle._

import java.awt.Color

import org.lobobrowser.util.gui.ColorFactory
import org.gjt.sp.jedit.syntax.{Token => JEditToken}


object Isabelle_Markup
{
  /* physical rendering */

  // see http://www.w3schools.com/css/css_colornames.asp

  def get_color(s: String): Color = ColorFactory.getInstance.getColor(s)

  val outdated_color = new Color(238, 227, 227)
  val running_color = new Color(97, 0, 97)
  val running1_color = new Color(97, 0, 97, 100)
  val unprocessed_color = new Color(255, 160, 160)
  val unprocessed1_color = new Color(255, 160, 160, 50)

  val light_color = new Color(240, 240, 240)
  val regular_color = new Color(192, 192, 192)
  val warning_color = new Color(255, 140, 0)
  val error_color = new Color(178, 34, 34)
  val error1_color = new Color(178, 34, 34, 50)
  val bad_color = new Color(255, 106, 106, 100)
  val hilite_color = new Color(255, 204, 102, 100)

  val quoted_color = new Color(139, 139, 139, 25)
  val subexp_color = new Color(80, 80, 80, 50)

  val keyword1_color = get_color("#006699")
  val keyword2_color = get_color("#009966")

  class Icon(val priority: Int, val icon: javax.swing.Icon)
  {
    def >= (that: Icon): Boolean = this.priority >= that.priority
  }
  val warning_icon = new Icon(1, Isabelle.load_icon("16x16/status/dialog-information.png"))
  val legacy_icon = new Icon(2, Isabelle.load_icon("16x16/status/dialog-warning.png"))
  val error_icon = new Icon(3, Isabelle.load_icon("16x16/status/dialog-error.png"))


  /* command status */

  def status_color(snapshot: Document.Snapshot, command: Command): Option[Color] =
  {
    val state = snapshot.command_state(command)
    if (snapshot.is_outdated) Some(outdated_color)
    else
      Isar_Document.command_status(state.status) match {
        case Isar_Document.Forked(i) if i > 0 => Some(running1_color)
        case Isar_Document.Unprocessed => Some(unprocessed1_color)
        case _ => None
      }
  }

  def overview_color(snapshot: Document.Snapshot, command: Command): Option[Color] =
  {
    val state = snapshot.command_state(command)
    if (snapshot.is_outdated) None
    else
      Isar_Document.command_status(state.status) match {
        case Isar_Document.Forked(i) => if (i > 0) Some(running_color) else None
        case Isar_Document.Unprocessed => Some(unprocessed_color)
        case Isar_Document.Failed => Some(error_color)
        case Isar_Document.Finished =>
          if (state.results.exists(r => Isar_Document.is_error(r._2))) Some(error_color)
          else if (state.results.exists(r => Isar_Document.is_warning(r._2))) Some(warning_color)
          else None
      }
  }


  /* markup selectors */

  val message: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.WRITELN, _), _)) => regular_color
    case Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), _)) => warning_color
    case Text.Info(_, XML.Elem(Markup(Markup.ERROR, _), _)) => error_color
  }

  val popup: Markup_Tree.Select[String] =
  {
    case Text.Info(_, msg @ XML.Elem(Markup(markup, _), _))
    if markup == Markup.WRITELN || markup == Markup.WARNING || markup == Markup.ERROR =>
      Pretty.string_of(List(msg), margin = Isabelle.Int_Property("tooltip-margin"))
  }

  val gutter_message: Markup_Tree.Select[Icon] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), body)) =>
      body match {
        case List(XML.Elem(Markup(Markup.LEGACY, _), _)) => legacy_icon
        case _ => warning_icon
      }
    case Text.Info(_, XML.Elem(Markup(Markup.ERROR, _), _)) => error_icon
  }

  val background1: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.BAD, _), _)) => bad_color
    case Text.Info(_, XML.Elem(Markup(Markup.HILITE, _), _)) => hilite_color
  }

  val background2: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.TOKEN_RANGE, _), _)) => light_color
  }

  val foreground: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.STRING, _), _)) => quoted_color
    case Text.Info(_, XML.Elem(Markup(Markup.ALTSTRING, _), _)) => quoted_color
    case Text.Info(_, XML.Elem(Markup(Markup.VERBATIM, _), _)) => quoted_color
  }

  private val text_entity_colors: Map[String, Color] =
    Map(Markup.CLASS -> get_color("red"))

  private val text_colors: Map[String, Color] =
    Map(
      Markup.STRING -> get_color("black"),
      Markup.ALTSTRING -> get_color("black"),
      Markup.VERBATIM -> get_color("black"),
      Markup.LITERAL -> keyword1_color,
      Markup.DELIMITER -> get_color("black"),
      Markup.TFREE -> get_color("#A020F0"),
      Markup.TVAR -> get_color("#A020F0"),
      Markup.FREE -> get_color("blue"),
      Markup.SKOLEM -> get_color("#D2691E"),
      Markup.BOUND -> get_color("green"),
      Markup.VAR -> get_color("#00009B"),
      Markup.INNER_STRING -> get_color("#D2691E"),
      Markup.INNER_COMMENT -> get_color("#8B0000"),
      Markup.DYNAMIC_FACT -> get_color("#7BA428"),
      Markup.ML_KEYWORD -> keyword1_color,
      Markup.ML_DELIMITER -> get_color("black"),
      Markup.ML_NUMERAL -> get_color("red"),
      Markup.ML_CHAR -> get_color("#D2691E"),
      Markup.ML_STRING -> get_color("#D2691E"),
      Markup.ML_COMMENT -> get_color("#8B0000"),
      Markup.ML_MALFORMED -> get_color("#FF6A6A"),
      Markup.ANTIQ -> get_color("blue"))

  val text_color: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup.Entity(kind, _), _))
    if text_entity_colors.isDefinedAt(kind) => text_entity_colors(kind)
    case Text.Info(_, XML.Elem(Markup(m, _), _))
    if text_colors.isDefinedAt(m) => text_colors(m)
  }

  private val tooltips: Map[String, String] =
    Map(
      Markup.SORT -> "sort",
      Markup.TYP -> "type",
      Markup.TERM -> "term",
      Markup.PROP -> "proposition",
      Markup.TOKEN_RANGE -> "inner syntax token",
      Markup.FREE -> "free variable (globally fixed)",
      Markup.SKOLEM -> "skolem variable (locally fixed)",
      Markup.BOUND -> "bound variable (internally fixed)",
      Markup.VAR -> "schematic variable",
      Markup.TFREE -> "free type variable",
      Markup.TVAR -> "schematic type variable",
      Markup.ML_SOURCE -> "ML source",
      Markup.DOC_SOURCE -> "document source")

  private def string_of_typing(kind: String, body: XML.Body): String =
    Pretty.string_of(List(Pretty.block(XML.Text(kind) :: Pretty.Break(1) :: body)),
      margin = Isabelle.Int_Property("tooltip-margin"))

  val tooltip: Markup_Tree.Select[String] =
  {
    case Text.Info(_, XML.Elem(Markup.Entity(kind, name), _)) => kind + " " + quote(name)
    case Text.Info(_, XML.Elem(Markup(Markup.TYPING, _), body)) => string_of_typing("::", body)
    case Text.Info(_, XML.Elem(Markup(Markup.ML_TYPING, _), body)) => string_of_typing("ML:", body)
    case Text.Info(_, XML.Elem(Markup(name, _), _))
    if tooltips.isDefinedAt(name) => tooltips(name)
  }

  private val subexp_include =
    Set(Markup.SORT, Markup.TYP, Markup.TERM, Markup.PROP, Markup.ML_TYPING, Markup.TOKEN_RANGE,
      Markup.ENTITY, Markup.FREE, Markup.SKOLEM, Markup.BOUND, Markup.VAR,
      Markup.TFREE, Markup.TVAR, Markup.ML_SOURCE, Markup.DOC_SOURCE)

  val subexp: Markup_Tree.Select[(Text.Range, Color)] =
  {
    case Text.Info(range, XML.Elem(Markup(name, _), _)) if subexp_include(name) =>
      (range, subexp_color)
  }


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
      Token.Kind.UNPARSED -> INVALID
    ).withDefaultValue(NULL)
  }

  def token_markup(syntax: Outer_Syntax, token: Token): Byte =
    if (token.is_command) command_style(syntax.keyword_kind(token.content).getOrElse(""))
    else if (token.is_operator) JEditToken.OPERATOR
    else token_style(token.kind)
}
