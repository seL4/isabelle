/*  Title:      Tools/jEdit/src/jedit/isabelle_markup.scala
    Author:     Makarius

Isabelle specific physical rendering and markup selection.
*/

package isabelle.jedit


import isabelle._

import java.awt.Color

import org.gjt.sp.jedit.syntax.Token


object Isabelle_Markup
{
  /* physical rendering */

  val outdated_color = new Color(240, 240, 240)
  val unfinished_color = new Color(255, 228, 225)

  val light_color = new Color(240, 240, 240)
  val regular_color = new Color(192, 192, 192)
  val warning_color = new Color(255, 168, 0)
  val error_color = new Color(178, 34, 34)
  val bad_color = new Color(255, 106, 106, 100)

  class Icon(val priority: Int, val icon: javax.swing.Icon)
  {
    def >= (that: Icon): Boolean = this.priority >= that.priority
  }
  val warning_icon = new Icon(1, Isabelle.load_icon("16x16/status/dialog-warning.png"))
  val error_icon = new Icon(2, Isabelle.load_icon("16x16/status/dialog-error.png"))


  /* command status */

  def status_color(snapshot: Document.Snapshot, command: Command): Option[Color] =
  {
    val state = snapshot.state(command)
    if (snapshot.is_outdated) Some(outdated_color)
    else
      Isar_Document.command_status(state.status) match {
        case Isar_Document.Forked(i) if i > 0 => Some(unfinished_color)
        case Isar_Document.Unprocessed => Some(unfinished_color)
        case _ => None
      }
  }

  def overview_color(snapshot: Document.Snapshot, command: Command): Option[Color] =
  {
    val state = snapshot.state(command)
    if (snapshot.is_outdated) None
    else
      Isar_Document.command_status(state.status) match {
        case Isar_Document.Forked(i) => if (i > 0) Some(unfinished_color) else None
        case Isar_Document.Unprocessed => Some(unfinished_color)
        case Isar_Document.Failed => Some(error_color)
        case Isar_Document.Finished =>
          if (state.results.exists(r => Isar_Document.is_error(r._2))) Some(error_color)
          else if (state.results.exists(r => Isar_Document.is_warning(r._2))) Some(warning_color)
          else None
      }
  }


  /* markup selectors */

  private val subexp_include =
    Set(Markup.SORT, Markup.TYP, Markup.TERM, Markup.PROP, Markup.ML_TYPING)

  val subexp: Markup_Tree.Select[(Text.Range, Color)] =
  {
    case Text.Info(range, XML.Elem(Markup(name, _), _)) if subexp_include(name) =>
      (range, Color.black)
  }

  val message: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.WRITELN, _), _)) => regular_color
    case Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), _)) => warning_color
    case Text.Info(_, XML.Elem(Markup(Markup.ERROR, _), _)) => error_color
  }

  val gutter_message: Markup_Tree.Select[Icon] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), _)) => warning_icon
    case Text.Info(_, XML.Elem(Markup(Markup.ERROR, _), _)) => error_icon
  }

  val background: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.BAD, _), _)) => bad_color
  }

  val box: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.TOKEN_RANGE, _), _)) => light_color
  }

  val tooltip: Markup_Tree.Select[String] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.ML_TYPING, _), body)) =>
      Pretty.string_of(List(Pretty.block(XML.Text("ML:") :: Pretty.Break(1) :: body)), margin = 40)
    case Text.Info(_, XML.Elem(Markup(Markup.SORT, _), _)) => "sort"
    case Text.Info(_, XML.Elem(Markup(Markup.TYP, _), _)) => "type"
    case Text.Info(_, XML.Elem(Markup(Markup.TERM, _), _)) => "term"
    case Text.Info(_, XML.Elem(Markup(Markup.PROP, _), _)) => "proposition"
  }


  /* token markup -- text styles */

  private val command_style: Map[String, Byte] =
  {
    import Token._
    Map[String, Byte](
      Keyword.THY_END -> KEYWORD2,
      Keyword.THY_SCRIPT -> LABEL,
      Keyword.PRF_SCRIPT -> LABEL,
      Keyword.PRF_ASM -> KEYWORD3,
      Keyword.PRF_ASM_GOAL -> KEYWORD3
    ).withDefaultValue(KEYWORD1)
  }

  private val token_style: Map[String, Byte] =
  {
    import Token._
    Map[String, Byte](
      // logical entities
      Markup.TCLASS -> NULL,
      Markup.TYCON -> NULL,
      Markup.FIXED_DECL -> FUNCTION,
      Markup.FIXED -> NULL,
      Markup.CONST_DECL -> FUNCTION,
      Markup.CONST -> NULL,
      Markup.FACT_DECL -> FUNCTION,
      Markup.FACT -> NULL,
      Markup.DYNAMIC_FACT -> LABEL,
      Markup.LOCAL_FACT_DECL -> FUNCTION,
      Markup.LOCAL_FACT -> NULL,
      // inner syntax
      Markup.TFREE -> NULL,
      Markup.FREE -> NULL,
      Markup.TVAR -> NULL,
      Markup.SKOLEM -> NULL,
      Markup.BOUND -> NULL,
      Markup.VAR -> NULL,
      Markup.NUM -> DIGIT,
      Markup.FLOAT -> DIGIT,
      Markup.XNUM -> DIGIT,
      Markup.XSTR -> LITERAL4,
      Markup.LITERAL -> OPERATOR,
      Markup.INNER_COMMENT -> COMMENT1,
      Markup.SORT -> NULL,
      Markup.TYP -> NULL,
      Markup.TERM -> NULL,
      Markup.PROP -> NULL,
      Markup.ATTRIBUTE -> NULL,
      Markup.METHOD -> NULL,
      // ML syntax
      Markup.ML_KEYWORD -> KEYWORD1,
      Markup.ML_DELIMITER -> OPERATOR,
      Markup.ML_IDENT -> NULL,
      Markup.ML_TVAR -> NULL,
      Markup.ML_NUMERAL -> DIGIT,
      Markup.ML_CHAR -> LITERAL1,
      Markup.ML_STRING -> LITERAL1,
      Markup.ML_COMMENT -> COMMENT1,
      Markup.ML_MALFORMED -> INVALID,
      // embedded source text
      Markup.ML_SOURCE -> COMMENT3,
      Markup.DOC_SOURCE -> COMMENT3,
      Markup.ANTIQ -> COMMENT4,
      Markup.ML_ANTIQ -> COMMENT4,
      Markup.DOC_ANTIQ -> COMMENT4,
      // outer syntax
      Markup.KEYWORD -> KEYWORD2,
      Markup.OPERATOR -> OPERATOR,
      Markup.COMMAND -> KEYWORD1,
      Markup.IDENT -> NULL,
      Markup.VERBATIM -> COMMENT3,
      Markup.COMMENT -> COMMENT1,
      Markup.CONTROL -> COMMENT3,
      Markup.MALFORMED -> INVALID,
      Markup.STRING -> LITERAL3,
      Markup.ALTSTRING -> LITERAL1
    ).withDefaultValue(NULL)
  }

  def tokens(syntax: Outer_Syntax): Markup_Tree.Select[Byte] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.COMMAND, List((Markup.NAME, name))), _))
    if syntax.keyword_kind(name).isDefined => command_style(syntax.keyword_kind(name).get)

    case Text.Info(_, XML.Elem(Markup(name, _), _))
    if token_style(name) != Token.NULL => token_style(name)
  }
}
