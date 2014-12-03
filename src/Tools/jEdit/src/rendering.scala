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


  /* popup window bounds */

  def popup_bounds: Double = (PIDE.options.real("jedit_popup_bounds") max 0.2) min 0.8


  /* Isabelle/Isar token markup */

  private val command_style: Map[String, Byte] =
  {
    import JEditToken._
    Map[String, Byte](
      Keyword.THY_END -> KEYWORD2,
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
      Token.Kind.SPACE -> NULL,
      Token.Kind.STRING -> LITERAL1,
      Token.Kind.ALT_STRING -> LITERAL2,
      Token.Kind.VERBATIM -> COMMENT3,
      Token.Kind.CARTOUCHE -> COMMENT4,
      Token.Kind.COMMENT -> COMMENT1,
      Token.Kind.ERROR -> INVALID
    ).withDefaultValue(NULL)
  }

  def token_markup(syntax: Outer_Syntax, token: Token): Byte =
    if (token.is_command) command_style(syntax.keywords.command_kind(token.content).getOrElse(""))
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
      ML_Lex.Kind.COMMENT -> COMMENT1,
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

  private val semantic_completion_elements =
    Markup.Elements(Markup.COMPLETION, Markup.NO_COMPLETION)

  private val language_context_elements =
    Markup.Elements(Markup.STRING, Markup.ALT_STRING, Markup.VERBATIM,
      Markup.CARTOUCHE, Markup.COMMENT, Markup.LANGUAGE,
      Markup.ML_STRING, Markup.ML_COMMENT)

  private val language_elements = Markup.Elements(Markup.LANGUAGE)

  private val citation_elements = Markup.Elements(Markup.CITATION)

  private val highlight_elements =
    Markup.Elements(Markup.EXPRESSION, Markup.CITATION, Markup.LANGUAGE, Markup.ML_TYPING,
      Markup.TOKEN_RANGE, Markup.ENTITY, Markup.PATH, Markup.URL, Markup.SORTING,
      Markup.TYPING, Markup.FREE, Markup.SKOLEM, Markup.BOUND,
      Markup.VAR, Markup.TFREE, Markup.TVAR)

  private val hyperlink_elements =
    Markup.Elements(Markup.ENTITY, Markup.PATH, Markup.POSITION, Markup.CITATION, Markup.URL)

  private val active_elements =
    Markup.Elements(Markup.DIALOG, Markup.BROWSER, Markup.GRAPHVIEW,
      Markup.SENDBACK, Markup.SIMP_TRACE_PANEL)

  private val tooltip_message_elements =
    Markup.Elements(Markup.WRITELN, Markup.WARNING, Markup.ERROR, Markup.BAD)

  private val tooltip_descriptions =
    Map(
      Markup.EXPRESSION -> "expression",
      Markup.CITATION -> "citation",
      Markup.TOKEN_RANGE -> "inner syntax token",
      Markup.FREE -> "free variable",
      Markup.SKOLEM -> "skolem variable",
      Markup.BOUND -> "bound variable",
      Markup.VAR -> "schematic variable",
      Markup.TFREE -> "free type variable",
      Markup.TVAR -> "schematic type variable")

  private val tooltip_elements =
    Markup.Elements(Markup.LANGUAGE, Markup.TIMING, Markup.ENTITY, Markup.SORTING,
      Markup.TYPING, Markup.ML_TYPING, Markup.PATH, Markup.URL) ++
    Markup.Elements(tooltip_descriptions.keySet)

  private val gutter_elements =
    Markup.Elements(Markup.WRITELN, Markup.WARNING, Markup.ERROR)

  private val squiggly_elements =
    Markup.Elements(Markup.WRITELN, Markup.WARNING, Markup.ERROR)

  private val line_background_elements =
    Markup.Elements(Markup.WRITELN_MESSAGE, Markup.TRACING_MESSAGE,
      Markup.WARNING_MESSAGE, Markup.ERROR_MESSAGE,
      Markup.INFORMATION)

  private val separator_elements =
    Markup.Elements(Markup.SEPARATOR)

  private val background_elements =
    Protocol.proper_status_elements + Markup.WRITELN_MESSAGE +
      Markup.TRACING_MESSAGE + Markup.WARNING_MESSAGE +
      Markup.ERROR_MESSAGE + Markup.BAD + Markup.INTENSIFY ++
      active_elements

  private val foreground_elements =
    Markup.Elements(Markup.STRING, Markup.ALT_STRING, Markup.VERBATIM,
      Markup.CARTOUCHE, Markup.ANTIQUOTED)

  private val bullet_elements =
    Markup.Elements(Markup.BULLET)

  private val fold_depth_elements =
    Markup.Elements(Markup.TEXT_FOLD, Markup.GOAL, Markup.SUBGOAL)
}


class Rendering private(val snapshot: Document.Snapshot, val options: Options)
{
  override def toString: String = "Rendering(" + snapshot.toString + ")"


  /* colors */

  def color_value(s: String): Color = Color_Value(options.string(s))

  val outdated_color = color_value("outdated_color")
  val unprocessed_color = color_value("unprocessed_color")
  val unprocessed1_color = color_value("unprocessed1_color")
  val running_color = color_value("running_color")
  val running1_color = color_value("running1_color")
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
  val spell_checker_color = color_value("spell_checker_color")
  val bad_color = color_value("bad_color")
  val intensify_color = color_value("intensify_color")
  val quoted_color = color_value("quoted_color")
  val antiquoted_color = color_value("antiquoted_color")
  val antiquote_color = color_value("antiquote_color")
  val highlight_color = color_value("highlight_color")
  val hyperlink_color = color_value("hyperlink_color")
  val active_color = color_value("active_color")
  val active_hover_color = color_value("active_hover_color")
  val active_result_color = color_value("active_result_color")
  val keyword1_color = color_value("keyword1_color")
  val keyword2_color = color_value("keyword2_color")
  val keyword3_color = color_value("keyword3_color")
  val quasi_keyword_color = color_value("quasi_keyword_color")
  val improper_color = color_value("improper_color")
  val operator_color = color_value("operator_color")
  val caret_invisible_color = color_value("caret_invisible_color")
  val completion_color = color_value("completion_color")
  val search_color = color_value("search_color")

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


  /* completion */

  def semantic_completion(range: Text.Range): Option[Text.Info[Completion.Semantic]] =
    if (snapshot.is_outdated) None
    else {
      snapshot.select(range, Rendering.semantic_completion_elements, _ =>
        {
          case Completion.Semantic.Info(info) => Some(info)
          case _ => None
        }).headOption.map(_.info)
    }

  def language_context(range: Text.Range): Option[Completion.Language_Context] =
    snapshot.select(range, Rendering.language_context_elements, _ =>
      {
        case Text.Info(_, XML.Elem(Markup.Language(language, symbols, antiquotes, delimited), _)) =>
          if (delimited) Some(Completion.Language_Context(language, symbols, antiquotes))
          else None
        case Text.Info(_, elem)
        if elem.name == Markup.ML_STRING || elem.name == Markup.ML_COMMENT =>
          Some(Completion.Language_Context.ML_inner)
        case Text.Info(_, _) =>
          Some(Completion.Language_Context.inner)
      }).headOption.map(_.info)

  def language_path(range: Text.Range): Option[Text.Range] =
    snapshot.select(range, Rendering.language_elements, _ =>
      {
        case Text.Info(info_range, XML.Elem(Markup.Language(Markup.Language.PATH, _, _, _), _)) =>
          Some(snapshot.convert(info_range))
        case _ => None
      }).headOption.map(_.info)

  def citation(range: Text.Range): Option[Text.Info[String]] =
    snapshot.select(range, Rendering.citation_elements, _ =>
      {
        case Text.Info(info_range, XML.Elem(Markup.Citation(name), _)) =>
          Some(Text.Info(snapshot.convert(info_range), name))
        case _ => None
      }).headOption.map(_.info)


  /* spell checker */

  private lazy val spell_checker_elements =
    Markup.Elements(space_explode(',', options.string("spell_checker_elements")): _*)

  def spell_checker_ranges(range: Text.Range): List[Text.Range] =
    snapshot.select(range, spell_checker_elements, _ => _ => Some(())).map(_.range)

  def spell_checker_point(range: Text.Range): Option[Text.Range] =
    snapshot.select(range, spell_checker_elements, _ =>
      {
        case info => Some(snapshot.convert(info.range))
      }).headOption.map(_.info)


  /* command status overview */

  def overview_limit: Int = options.int("jedit_text_overview_limit")

  def overview_color(range: Text.Range): Option[Color] =
  {
    if (snapshot.is_outdated) None
    else {
      val results =
        snapshot.cumulate[List[Markup]](range, Nil, Protocol.liberal_status_elements, _ =>
          {
            case (status, Text.Info(_, elem)) => Some(elem.markup :: status)
          }, status = true)
      if (results.isEmpty) None
      else {
        val status = Protocol.Status.make(results.iterator.flatMap(_.info))

        if (status.is_running) Some(running_color)
        else if (status.is_failed) Some(error_color)
        else if (status.is_warned) Some(warning_color)
        else if (status.is_unprocessed) Some(unprocessed_color)
        else None
      }
    }
  }


  /* highlighted area */

  def highlight(range: Text.Range): Option[Text.Info[Color]] =
    snapshot.select(range, Rendering.highlight_elements, _ =>
      {
        case info => Some(Text.Info(snapshot.convert(info.range), highlight_color))
      }).headOption.map(_.info)


  /* hyperlinks */

  private def jedit_file(name: String): String =
    if (Path.is_valid(name))
      PIDE.resources.append(snapshot.node_name.master_dir, Path.explode(name))
    else name

  def hyperlink(range: Text.Range): Option[Text.Info[PIDE.editor.Hyperlink]] =
  {
    snapshot.cumulate[Vector[Text.Info[PIDE.editor.Hyperlink]]](
      range, Vector.empty, Rendering.hyperlink_elements, _ =>
        {
          case (links, Text.Info(info_range, XML.Elem(Markup.Path(name), _))) =>
            val link = PIDE.editor.hyperlink_file(jedit_file(name))
            Some(links :+ Text.Info(snapshot.convert(info_range), link))

          case (links, Text.Info(info_range, XML.Elem(Markup.Url(name), _))) =>
            val link = PIDE.editor.hyperlink_url(name)
            Some(links :+ Text.Info(snapshot.convert(info_range), link))

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.ENTITY, props), _)))
          if !props.exists(
            { case (Markup.KIND, Markup.ML_OPEN) => true
              case (Markup.KIND, Markup.ML_STRUCTURE) => true
              case _ => false }) =>
            val opt_link =
              props match {
                case Position.Def_Line_File(line, name) =>
                  val offset = Position.Def_Offset.unapply(props) getOrElse 0
                  PIDE.editor.hyperlink_source_file(name, line, offset)
                case Position.Def_Id_Offset0(id, offset) =>
                  PIDE.editor.hyperlink_command_id(snapshot, id, offset)
                case _ => None
              }
            opt_link.map(link => (links :+ Text.Info(snapshot.convert(info_range), link)))

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.POSITION, props), _))) =>
            val opt_link =
              props match {
                case Position.Line_File(line, name) =>
                  val offset = Position.Offset.unapply(props) getOrElse 0
                  PIDE.editor.hyperlink_source_file(name, line, offset)
                case Position.Id_Offset0(id, offset) =>
                  PIDE.editor.hyperlink_command_id(snapshot, id, offset)
                case _ => None
              }
            opt_link.map(link => (links :+ Text.Info(snapshot.convert(info_range), link)))

          case (links, Text.Info(info_range, XML.Elem(Markup.Citation(name), _))) =>
            val opt_link =
              Bibtex_JEdit.entries_iterator.collectFirst(
                { case (a, buffer, offset) if a == name =>
                    PIDE.editor.hyperlink_buffer(buffer, offset) })
            opt_link.map(link => (links :+ Text.Info(snapshot.convert(info_range), link)))

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

  def command_results(range: Text.Range): Command.Results =
    Command.State.merge_results(
      snapshot.select[List[Command.State]](range, Markup.Elements.full, command_states =>
        { case _ => Some(command_states) }).flatMap(_.info))


  /* tooltip messages */

  def tooltip_message(range: Text.Range): Option[Text.Info[XML.Body]] =
  {
    val results =
      snapshot.cumulate[List[Text.Info[Command.Results.Entry]]](
        range, Nil, Rendering.tooltip_message_elements, _ =>
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
      Some(Text.Info(r, Pretty.separate(msgs.iterator.map(_._2).toList)))
    }
  }


  /* tooltips */

  private def pretty_typing(kind: String, body: XML.Body): XML.Tree =
    Pretty.block(XML.Text(kind) :: Pretty.Break(1) :: body)

  private def timing_threshold: Double = options.real("jedit_timing_threshold")

  def tooltip(range: Text.Range): Option[Text.Info[XML.Body]] =
  {
    def add(prev: Text.Info[(Timing, Vector[(Boolean, XML.Tree)])],
      r0: Text.Range, p: (Boolean, XML.Tree)): Text.Info[(Timing, Vector[(Boolean, XML.Tree)])] =
    {
      val r = snapshot.convert(r0)
      val (t, info) = prev.info
      if (prev.range == r)
        Text.Info(r, (t, info :+ p))
      else Text.Info(r, (t, Vector(p)))
    }

    val results =
      snapshot.cumulate[Text.Info[(Timing, Vector[(Boolean, XML.Tree)])]](
        range, Text.Info(range, (Timing.zero, Vector.empty)), Rendering.tooltip_elements, _ =>
        {
          case (Text.Info(r, (t1, info)), Text.Info(_, XML.Elem(Markup.Timing(t2), _))) =>
            Some(Text.Info(r, (t1 + t2, info)))
          case (prev, Text.Info(r, XML.Elem(Markup.Entity(kind, name), _))) =>
            val kind1 = Word.implode(Word.explode('_', kind))
            val txt1 =
              if (name == "") kind1
              else kind1 + " " + quote(name)
            val t = prev.info._1
            val txt2 =
              if (kind == Markup.COMMAND && t.elapsed.seconds >= timing_threshold)
                "\n" + t.message
              else ""
            Some(add(prev, r, (true, XML.Text(txt1 + txt2))))
          case (prev, Text.Info(r, XML.Elem(Markup.Path(name), _))) =>
            val file = jedit_file(name)
            val text =
              if (name == file) "file " + quote(file)
              else "path " + quote(name) + "\nfile " + quote(file)
            Some(add(prev, r, (true, XML.Text(text))))
          case (prev, Text.Info(r, XML.Elem(Markup.Url(name), _))) =>
            Some(add(prev, r, (true, XML.Text("URL " + quote(name)))))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), body)))
          if name == Markup.SORTING || name == Markup.TYPING =>
            Some(add(prev, r, (true, pretty_typing("::", body))))
          case (prev, Text.Info(r, XML.Elem(Markup(Markup.ML_TYPING, _), body))) =>
            Some(add(prev, r, (false, pretty_typing("ML:", body))))
          case (prev, Text.Info(r, XML.Elem(Markup.Language(language, _, _, _), _))) =>
            Some(add(prev, r, (true, XML.Text("language: " + language))))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), _))) =>
            Rendering.tooltip_descriptions.get(name).
              map(descr => add(prev, r, (true, XML.Text(descr))))
        }).map(_.info)

    results.map(_.info).flatMap(res => res._2.toList) match {
      case Nil => None
      case tips =>
        val r = Text.Range(results.head.range.start, results.last.range.stop)
        val all_tips = (tips.filter(_._1) ++ tips.filter(!_._1).lastOption.toList).map(_._2)
        Some(Text.Info(r, Library.separate(Pretty.FBreak, all_tips)))
    }
  }

  def tooltip_margin: Int = options.int("jedit_tooltip_margin")

  lazy val tooltip_close_icon = JEdit_Lib.load_icon(options.string("tooltip_close_icon"))
  lazy val tooltip_detach_icon = JEdit_Lib.load_icon(options.string("tooltip_detach_icon"))


  /* gutter */

  private def gutter_message_pri(msg: XML.Tree): Int =
    if (Protocol.is_error(msg)) Rendering.error_pri
    else if (Protocol.is_legacy(msg)) Rendering.legacy_pri
    else if (Protocol.is_warning(msg)) Rendering.warning_pri
    else if (Protocol.is_information(msg)) Rendering.information_pri
    else 0

  private lazy val gutter_icons = Map(
    Rendering.information_pri -> JEdit_Lib.load_icon(options.string("gutter_information_icon")),
    Rendering.warning_pri -> JEdit_Lib.load_icon(options.string("gutter_warning_icon")),
    Rendering.legacy_pri -> JEdit_Lib.load_icon(options.string("gutter_legacy_icon")),
    Rendering.error_pri -> JEdit_Lib.load_icon(options.string("gutter_error_icon")))

  def gutter_icon(range: Text.Range): Option[Icon] =
  {
    val pris =
      snapshot.cumulate[Int](range, 0, Rendering.gutter_elements, _ =>
        {
          case (pri, Text.Info(_, msg @ XML.Elem(Markup(_, Markup.Serial(serial)), _))) =>
            Some(pri max gutter_message_pri(msg))
          case _ => None
        }).map(_.info)

    gutter_icons.get((0 /: pris)(_ max _))
  }


  /* squiggly underline */

  private lazy val squiggly_colors = Map(
    Rendering.writeln_pri -> writeln_color,
    Rendering.information_pri -> information_color,
    Rendering.warning_pri -> warning_color,
    Rendering.error_pri -> error_color)

  def squiggly_underline(range: Text.Range): List[Text.Info[Color]] =
  {
    val results =
      snapshot.cumulate[Int](range, 0, Rendering.squiggly_elements, _ =>
        {
          case (pri, Text.Info(_, elem)) =>
            if (Protocol.is_information(elem))
              Some(pri max Rendering.information_pri)
            else
              Some(pri max Rendering.message_pri(elem.name))
        })
    for {
      Text.Info(r, pri) <- results
      color <- squiggly_colors.get(pri)
    } yield Text.Info(r, color)
  }


  /* message output */

  private lazy val message_colors = Map(
    Rendering.writeln_pri -> writeln_message_color,
    Rendering.information_pri -> information_message_color,
    Rendering.tracing_pri -> tracing_message_color,
    Rendering.warning_pri -> warning_message_color,
    Rendering.error_pri -> error_message_color)

  def line_background(range: Text.Range): Option[(Color, Boolean)] =
  {
    val results =
      snapshot.cumulate[Int](range, 0, Rendering.line_background_elements, _ =>
        {
          case (pri, Text.Info(_, elem)) =>
            if (elem.name == Markup.INFORMATION)
              Some(pri max Rendering.information_pri)
            else
              Some(pri max Rendering.message_pri(elem.name))
        })
    val pri = (0 /: results) { case (p1, Text.Info(_, p2)) => p1 max p2 }

    val is_separator =
      pri > 0 &&
      snapshot.cumulate[Boolean](range, false, Rendering.separator_elements, _ =>
        {
          case _ => Some(true)
        }).exists(_.info)

    message_colors.get(pri).map((_, is_separator))
  }

  def output_messages(results: Command.Results): List[XML.Tree] =
  {
    val (states, other) =
      results.iterator.map(_._2).filterNot(Protocol.is_result(_)).toList
        .partition(Protocol.is_state(_))
    states ::: other
  }


  /* text background */

  def background(range: Text.Range): List[Text.Info[Color]] =
  {
    if (snapshot.is_outdated && snapshot.is_loaded) List(Text.Info(range, outdated_color))
    else
      for {
        Text.Info(r, result) <-
          snapshot.cumulate[(List[Markup], Option[Color])](
            range, (List(Markup.Empty), None), Rendering.background_elements,
            command_states =>
              {
                case (((status, color), Text.Info(_, XML.Elem(markup, _))))
                if !status.isEmpty && Protocol.proper_status_elements(markup.name) =>
                  Some((markup :: status, color))
                case (_, Text.Info(_, XML.Elem(Markup(Markup.BAD, _), _))) =>
                  Some((Nil, Some(bad_color)))
                case (_, Text.Info(_, XML.Elem(Markup(Markup.INTENSIFY, _), _))) =>
                  Some((Nil, Some(intensify_color)))
                case (acc, Text.Info(_, Protocol.Dialog(_, serial, result))) =>
                  command_states.collectFirst(
                    { case st if st.results.defined(serial) => st.results.get(serial).get }) match
                  {
                    case Some(Protocol.Dialog_Result(res)) if res == result =>
                      Some((Nil, Some(active_result_color)))
                    case _ =>
                      Some((Nil, Some(active_color)))
                  }
                case (_, Text.Info(_, elem)) =>
                  if (Rendering.active_elements(elem.name)) Some((Nil, Some(active_color)))
                  else None
              })
        color <-
          (result match {
            case (markups, opt_color) if !markups.isEmpty =>
              val status = Protocol.Status.make(markups.iterator)
              if (status.is_unprocessed) Some(unprocessed1_color)
              else if (status.is_running) Some(running1_color)
              else opt_color
            case (_, opt_color) => opt_color
          })
      } yield Text.Info(r, color)
  }


  /* text foreground */

  def foreground(range: Text.Range): List[Text.Info[Color]] =
    snapshot.select(range, Rendering.foreground_elements, _ =>
      {
        case Text.Info(_, elem) =>
          if (elem.name == Markup.ANTIQUOTED) Some(antiquoted_color) else Some(quoted_color)
      })


  /* text color */

  private lazy val text_colors: Map[String, Color] = Map(
      Markup.KEYWORD1 -> keyword1_color,
      Markup.KEYWORD2 -> keyword2_color,
      Markup.KEYWORD3 -> keyword3_color,
      Markup.QUASI_KEYWORD -> quasi_keyword_color,
      Markup.IMPROPER -> improper_color,
      Markup.OPERATOR -> operator_color,
      Markup.STRING -> Color.BLACK,
      Markup.ALT_STRING -> Color.BLACK,
      Markup.VERBATIM -> Color.BLACK,
      Markup.CARTOUCHE -> Color.BLACK,
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
      Markup.ANTIQUOTE -> antiquote_color,
      Markup.ML_KEYWORD1 -> keyword1_color,
      Markup.ML_KEYWORD2 -> keyword2_color,
      Markup.ML_KEYWORD3 -> keyword3_color,
      Markup.ML_DELIMITER -> Color.BLACK,
      Markup.ML_NUMERAL -> inner_numeral_color,
      Markup.ML_CHAR -> inner_quoted_color,
      Markup.ML_STRING -> inner_quoted_color,
      Markup.ML_COMMENT -> inner_comment_color,
      Markup.SML_STRING -> inner_quoted_color,
      Markup.SML_COMMENT -> inner_comment_color)

  private lazy val text_color_elements =
    Markup.Elements(text_colors.keySet)

  def text_color(range: Text.Range, color: Color): List[Text.Info[Color]] =
  {
    if (color == Token_Markup.hidden_color) List(Text.Info(range, color))
    else
      snapshot.cumulate(range, color, text_color_elements, _ =>
        {
          case (_, Text.Info(_, elem)) => text_colors.get(elem.name)
        })
  }


  /* virtual bullets */

  def bullet(range: Text.Range): List[Text.Info[Color]] =
    snapshot.select(range, Rendering.bullet_elements, _ => _ => Some(bullet_color))


  /* text folds */

  def fold_depth(range: Text.Range): List[Text.Info[Int]] =
    snapshot.cumulate[Int](range, 0, Rendering.fold_depth_elements, _ =>
      {
        case (depth, _) => Some(depth + 1)
      })
}
