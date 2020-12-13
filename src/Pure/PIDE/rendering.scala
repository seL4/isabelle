/*  Title:      Pure/PIDE/rendering.scala
    Author:     Makarius

Isabelle-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.FileSystems

import scala.collection.immutable.SortedMap



object Rendering
{
  /* color */

  object Color extends Enumeration
  {
    // background
    val unprocessed1, running1, canceled, bad, intensify, entity, active, active_result,
      markdown_bullet1, markdown_bullet2, markdown_bullet3, markdown_bullet4 = Value
    val background_colors: ValueSet = values

    // foreground
    val quoted, antiquoted = Value
    val foreground_colors: ValueSet = values -- background_colors

    // message underline
    val writeln, information, warning, legacy, error = Value
    val message_underline_colors: ValueSet = values -- background_colors -- foreground_colors

    // message background
    val writeln_message, information_message, tracing_message,
      warning_message, legacy_message, error_message = Value
    val message_background_colors: ValueSet =
      values -- background_colors -- foreground_colors -- message_underline_colors

    // text
    val main, keyword1, keyword2, keyword3, quasi_keyword, improper, operator,
      tfree, tvar, free, skolem, bound, `var`, inner_numeral, inner_quoted,
      inner_cartouche, comment1, comment2, comment3, dynamic, class_parameter,
      antiquote, raw_text, plain_text = Value
    val text_colors: ValueSet =
      values -- background_colors -- foreground_colors -- message_underline_colors --
      message_background_colors

    // text overview
    val unprocessed, running = Value
    val text_overview_colors = Set(unprocessed, running, error, warning)
  }


  /* output messages */

  val state_pri = 1
  val writeln_pri = 2
  val information_pri = 3
  val tracing_pri = 4
  val warning_pri = 5
  val legacy_pri = 6
  val error_pri = 7

  val message_pri = Map(
    Markup.STATE -> state_pri,
    Markup.STATE_MESSAGE -> state_pri,
    Markup.WRITELN -> writeln_pri,
    Markup.WRITELN_MESSAGE -> writeln_pri,
    Markup.INFORMATION -> information_pri,
    Markup.INFORMATION_MESSAGE -> information_pri,
    Markup.TRACING -> tracing_pri,
    Markup.TRACING_MESSAGE -> tracing_pri,
    Markup.WARNING -> warning_pri,
    Markup.WARNING_MESSAGE -> warning_pri,
    Markup.LEGACY -> legacy_pri,
    Markup.LEGACY_MESSAGE -> legacy_pri,
    Markup.ERROR -> error_pri,
    Markup.ERROR_MESSAGE -> error_pri
  ).withDefaultValue(0)

  val message_underline_color = Map(
    writeln_pri -> Color.writeln,
    information_pri -> Color.information,
    warning_pri -> Color.warning,
    legacy_pri -> Color.legacy,
    error_pri -> Color.error)

  val message_background_color = Map(
    writeln_pri -> Color.writeln_message,
    information_pri -> Color.information_message,
    tracing_pri -> Color.tracing_message,
    warning_pri -> Color.warning_message,
    legacy_pri -> Color.legacy_message,
    error_pri -> Color.error_message)

  def output_messages(results: Command.Results): List[XML.Elem] =
  {
    val (states, other) =
      results.iterator.map(_._2).filterNot(Protocol.is_result).toList
        .partition(Protocol.is_state)
    states ::: other
  }


  /* text color */

  val text_color = Map(
    Markup.KEYWORD1 -> Color.keyword1,
    Markup.KEYWORD2 -> Color.keyword2,
    Markup.KEYWORD3 -> Color.keyword3,
    Markup.QUASI_KEYWORD -> Color.quasi_keyword,
    Markup.IMPROPER -> Color.improper,
    Markup.OPERATOR -> Color.operator,
    Markup.STRING -> Color.main,
    Markup.ALT_STRING -> Color.main,
    Markup.VERBATIM -> Color.main,
    Markup.CARTOUCHE -> Color.main,
    Markup.LITERAL -> Color.keyword1,
    Markup.DELIMITER -> Color.main,
    Markup.TFREE -> Color.tfree,
    Markup.TVAR -> Color.tvar,
    Markup.FREE -> Color.free,
    Markup.SKOLEM -> Color.skolem,
    Markup.BOUND -> Color.bound,
    Markup.VAR -> Color.`var`,
    Markup.INNER_STRING -> Color.inner_quoted,
    Markup.INNER_CARTOUCHE -> Color.inner_cartouche,
    Markup.DYNAMIC_FACT -> Color.dynamic,
    Markup.CLASS_PARAMETER -> Color.class_parameter,
    Markup.ANTIQUOTE -> Color.antiquote,
    Markup.RAW_TEXT -> Color.raw_text,
    Markup.PLAIN_TEXT -> Color.plain_text,
    Markup.ML_KEYWORD1 -> Color.keyword1,
    Markup.ML_KEYWORD2 -> Color.keyword2,
    Markup.ML_KEYWORD3 -> Color.keyword3,
    Markup.ML_DELIMITER -> Color.main,
    Markup.ML_NUMERAL -> Color.inner_numeral,
    Markup.ML_CHAR -> Color.inner_quoted,
    Markup.ML_STRING -> Color.inner_quoted,
    Markup.ML_COMMENT -> Color.comment1,
    Markup.COMMENT -> Color.comment1,
    Markup.COMMENT1 -> Color.comment1,
    Markup.COMMENT2 -> Color.comment2,
    Markup.COMMENT3 -> Color.comment3)

  val foreground =
    Map(
      Markup.STRING -> Color.quoted,
      Markup.ALT_STRING -> Color.quoted,
      Markup.VERBATIM -> Color.quoted,
      Markup.CARTOUCHE -> Color.quoted,
      Markup.ANTIQUOTED -> Color.antiquoted)


  /* tooltips */

  val tooltip_descriptions =
    Map(
      Markup.CITATION -> "citation",
      Markup.TOKEN_RANGE -> "inner syntax token",
      Markup.FREE -> "free variable",
      Markup.SKOLEM -> "skolem variable",
      Markup.BOUND -> "bound variable",
      Markup.VAR -> "schematic variable",
      Markup.TFREE -> "free type variable",
      Markup.TVAR -> "schematic type variable")


  /* entity focus */

  object Focus
  {
    def apply(ids: Set[Long]): Focus = new Focus(ids)
    val empty: Focus = apply(Set.empty)
    def make(args: List[Text.Info[Focus]]): Focus =
      (empty /: args)({ case (focus1, Text.Info(_, focus2)) => focus1 ++ focus2 })
  }

  sealed class Focus private[Rendering](protected val rep: Set[Long])
  {
    def defined: Boolean = rep.nonEmpty
    def apply(id: Long): Boolean = rep.contains(id)
    def + (id: Long): Focus = if (rep.contains(id)) this else new Focus(rep + id)
    def ++ (other: Focus): Focus =
      if (this eq other) this
      else if (rep.isEmpty) other
      else (this /: other.rep.iterator)(_ + _)
    override def toString: String = rep.mkString("Focus(", ",", ")")
  }


  /* markup elements */

  val position_elements =
    Markup.Elements(Markup.BINDING, Markup.ENTITY, Markup.REPORT, Markup.POSITION)

  val semantic_completion_elements =
    Markup.Elements(Markup.COMPLETION, Markup.NO_COMPLETION)

  val language_context_elements =
    Markup.Elements(Markup.STRING, Markup.ALT_STRING, Markup.VERBATIM,
      Markup.CARTOUCHE, Markup.COMMENT, Markup.LANGUAGE,
      Markup.ML_STRING, Markup.ML_COMMENT)

  val language_elements = Markup.Elements(Markup.LANGUAGE)

  val citation_elements = Markup.Elements(Markup.CITATION)

  val active_elements =
    Markup.Elements(Markup.DIALOG, Markup.BROWSER, Markup.GRAPHVIEW, Markup.THEORY_EXPORTS,
      Markup.SENDBACK, Markup.JEDIT_ACTION, Markup.SIMP_TRACE_PANEL)

  val background_elements =
    Document_Status.Command_Status.proper_elements + Markup.WRITELN_MESSAGE +
      Markup.STATE_MESSAGE + Markup.INFORMATION_MESSAGE +
      Markup.TRACING_MESSAGE + Markup.WARNING_MESSAGE +
      Markup.LEGACY_MESSAGE + Markup.ERROR_MESSAGE +
      Markup.BAD + Markup.INTENSIFY + Markup.ENTITY +
      Markup.Markdown_Bullet.name ++ active_elements

  val foreground_elements = Markup.Elements(foreground.keySet)

  val text_color_elements = Markup.Elements(text_color.keySet)

  val tooltip_elements =
    Markup.Elements(Markup.LANGUAGE, Markup.EXPRESSION, Markup.TIMING, Markup.ENTITY,
      Markup.SORTING, Markup.TYPING, Markup.CLASS_PARAMETER, Markup.ML_TYPING,
      Markup.ML_BREAKPOINT, Markup.PATH, Markup.DOC, Markup.URL,
      Markup.MARKDOWN_PARAGRAPH, Markup.MARKDOWN_ITEM, Markup.Markdown_List.name) ++
      Markup.Elements(tooltip_descriptions.keySet)

  val tooltip_message_elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING, Markup.LEGACY, Markup.ERROR,
      Markup.BAD)

  val message_elements = Markup.Elements(message_pri.keySet)
  val warning_elements = Markup.Elements(Markup.WARNING, Markup.LEGACY)
  val error_elements = Markup.Elements(Markup.ERROR)

  val entity_elements = Markup.Elements(Markup.ENTITY)

  val antiquoted_elements = Markup.Elements(Markup.ANTIQUOTED)

  val meta_data_elements =
    Markup.Elements(Markup.META_TITLE, Markup.META_CREATOR, Markup.META_CONTRIBUTOR,
      Markup.META_DATE, Markup.META_DESCRIPTION, Markup.META_LICENSE)

  val document_tag_elements =
    Markup.Elements(Markup.Document_Tag.ELEMENT)

  val markdown_elements =
    Markup.Elements(Markup.MARKDOWN_PARAGRAPH, Markup.MARKDOWN_ITEM, Markup.Markdown_List.name,
      Markup.Markdown_Bullet.name)
}

class Rendering(
  val snapshot: Document.Snapshot,
  val options: Options,
  val session: Session)
{
  override def toString: String = "Rendering(" + snapshot.toString + ")"

  def get_text(range: Text.Range): Option[String] = None


  /* caret */

  def before_caret_range(caret: Text.Offset): Text.Range =
  {
    val former_caret = snapshot.revert(caret)
    snapshot.convert(Text.Range(former_caret - 1, former_caret))
  }


  /* completion */

  def semantic_completion(completed_range: Option[Text.Range], caret_range: Text.Range)
      : Option[Text.Info[Completion.Semantic]] =
    if (snapshot.is_outdated) None
    else {
      snapshot.select(caret_range, Rendering.semantic_completion_elements, _ =>
        {
          case Completion.Semantic.Info(info) =>
            completed_range match {
              case Some(range0) if range0.contains(info.range) && range0 != info.range => None
              case _ => Some(info)
            }
          case _ => None
        }).headOption.map(_.info)
    }

  def semantic_completion_result(
    history: Completion.History,
    unicode: Boolean,
    completed_range: Option[Text.Range],
    caret_range: Text.Range): (Boolean, Option[Completion.Result]) =
  {
    semantic_completion(completed_range, caret_range) match {
      case Some(Text.Info(_, Completion.No_Completion)) => (true, None)
      case Some(Text.Info(range, names: Completion.Names)) =>
        get_text(range) match {
          case Some(original) => (false, names.complete(range, history, unicode, original))
          case None => (false, None)
        }
      case None => (false, None)
    }
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

  def citations(range: Text.Range): List[Text.Info[String]] =
    snapshot.select(range, Rendering.citation_elements, _ =>
      {
        case Text.Info(info_range, XML.Elem(Markup.Citation(name), _)) =>
          Some(Text.Info(snapshot.convert(info_range), name))
        case _ => None
      }).map(_.info)


  /* file-system path completion */

  def language_path(range: Text.Range): Option[Text.Info[Boolean]] =
    snapshot.select(range, Rendering.language_elements, _ =>
      {
        case Text.Info(info_range, XML.Elem(Markup.Language.Path(delimited), _)) =>
          Some((delimited, snapshot.convert(info_range)))
        case _ => None
      }).headOption.map({ case Text.Info(_, (delimited, range)) => Text.Info(range, delimited) })

  def path_completion(caret: Text.Offset): Option[Completion.Result] =
  {
    def complete(text: String): List[(String, List[String])] =
    {
      try {
        val path = Path.explode(text)
        val (dir, base_name) =
          if (text == "" || text.endsWith("/")) (path, "")
          else (path.dir, path.file_name)

        val directory = new JFile(session.resources.append(snapshot.node_name, dir))
        val files = directory.listFiles
        if (files == null) Nil
        else {
          val ignore =
            space_explode(':', options.string("completion_path_ignore")).
              map(s => FileSystems.getDefault.getPathMatcher("glob:" + s))
          (for {
            file <- files.iterator

            name = file.getName
            if name.startsWith(base_name)
            path_name = new JFile(name).toPath
            if !ignore.exists(matcher => matcher.matches(path_name))

            text1 = (dir + Path.basic(name)).implode_short
            if text != text1

            is_dir = new JFile(directory, name).isDirectory
            replacement = text1 + (if (is_dir) "/" else "")
            descr = List(text1, if (is_dir) "(directory)" else "(file)")
          } yield (replacement, descr)).take(options.int("completion_limit")).toList
        }
      }
      catch { case ERROR(_) => Nil }
    }

    def is_wrapped(s: String): Boolean =
      s.startsWith("\"") && s.endsWith("\"") ||
      s.startsWith(Symbol.open_decoded) && s.endsWith(Symbol.close_decoded)

    for {
      Text.Info(r1, delimited) <- language_path(before_caret_range(caret))
      s1 <- get_text(r1)
      (r2, s2) <-
        if (is_wrapped(s1)) {
          Some((Text.Range(r1.start + 1, r1.stop - 1), s1.substring(1, s1.length - 1)))
        }
        else if (delimited) Some((r1, s1))
        else None
      if Path.is_valid(s2)
      paths = complete(s2)
      if paths.nonEmpty
      items = paths.map(p => Completion.Item(r2, s2, "", p._2, p._1, 0, false))
    } yield Completion.Result(r2, s2, false, items)
  }


  /* spell checker */

  private lazy val spell_checker_include =
    Markup.Elements(space_explode(',', options.string("spell_checker_include")): _*)

  private lazy val spell_checker_elements =
    spell_checker_include ++
      Markup.Elements(space_explode(',', options.string("spell_checker_exclude")): _*)

  def spell_checker(range: Text.Range): List[Text.Info[Text.Range]] =
  {
    val result =
      snapshot.select(range, spell_checker_elements, _ =>
        {
          case info =>
            Some(
              if (spell_checker_include(info.info.name))
                Some(snapshot.convert(info.range))
              else None)
        })
    for (Text.Info(range, Some(range1)) <- result)
      yield Text.Info(range, range1)
  }

  def spell_checker_point(range: Text.Range): Option[Text.Range] =
    spell_checker(range).headOption.map(_.info)


  /* text background */

  def background(elements: Markup.Elements, range: Text.Range, focus: Rendering.Focus)
    : List[Text.Info[Rendering.Color.Value]] =
  {
    for {
      Text.Info(r, result) <-
        snapshot.cumulate[(List[Markup], Option[Rendering.Color.Value])](
          range, (List(Markup.Empty), None), elements,
          command_states =>
            {
              case (((markups, color), Text.Info(_, XML.Elem(markup, _))))
              if markups.nonEmpty && Document_Status.Command_Status.proper_elements(markup.name) =>
                Some((markup :: markups, color))
              case (_, Text.Info(_, XML.Elem(Markup(Markup.BAD, _), _))) =>
                Some((Nil, Some(Rendering.Color.bad)))
              case (_, Text.Info(_, XML.Elem(Markup(Markup.INTENSIFY, _), _))) =>
                Some((Nil, Some(Rendering.Color.intensify)))
              case (_, Text.Info(_, XML.Elem(Markup.Entity.Id(i), _))) if focus(i) =>
                Some((Nil, Some(Rendering.Color.entity)))
              case (_, Text.Info(_, XML.Elem(Markup.Markdown_Bullet(depth), _))) =>
                val color =
                  depth % 4 match {
                    case 1 => Rendering.Color.markdown_bullet1
                    case 2 => Rendering.Color.markdown_bullet2
                    case 3 => Rendering.Color.markdown_bullet3
                    case _ => Rendering.Color.markdown_bullet4
                  }
                Some((Nil, Some(color)))
              case (acc, Text.Info(_, Protocol.Dialog(_, serial, result))) =>
                command_states.collectFirst(
                  { case st if st.results.defined(serial) => st.results.get(serial).get }) match
                {
                  case Some(Protocol.Dialog_Result(res)) if res == result =>
                    Some((Nil, Some(Rendering.Color.active_result)))
                  case _ =>
                    Some((Nil, Some(Rendering.Color.active)))
                }
              case (_, Text.Info(_, elem)) =>
                if (Rendering.active_elements(elem.name))
                  Some((Nil, Some(Rendering.Color.active)))
                else None
            })
      color <-
        (result match {
          case (markups, opt_color) if markups.nonEmpty =>
            val status = Document_Status.Command_Status.make(markups.iterator)
            if (status.is_unprocessed) Some(Rendering.Color.unprocessed1)
            else if (status.is_running) Some(Rendering.Color.running1)
            else if (status.is_canceled) Some(Rendering.Color.canceled)
            else opt_color
          case (_, opt_color) => opt_color
        })
    } yield Text.Info(r, color)
  }


  /* text foreground */

  def foreground(range: Text.Range): List[Text.Info[Rendering.Color.Value]] =
    snapshot.select(range, Rendering.foreground_elements, _ =>
      {
        case info => Some(Rendering.foreground(info.info.name))
      })


  /* entity focus */

  def entity_focus_defs(range: Text.Range): Rendering.Focus =
    Rendering.Focus.make(
      snapshot.cumulate(range, Rendering.Focus.empty, Rendering.entity_elements, _ =>
        {
          case (focus, Text.Info(_, XML.Elem(Markup.Entity.Def(i), _))) => Some(focus + i)
          case _ => None
        }))

  def entity_focus(range: Text.Range, visible_defs: Rendering.Focus): Rendering.Focus =
    Rendering.Focus.make(
      snapshot.cumulate(range, Rendering.Focus.empty, Rendering.entity_elements, _ =>
        {
          case (focus, Text.Info(_, XML.Elem(Markup.Entity.Ref(i), _)))
          if visible_defs(i) => Some(focus + i)
          case _ => None
        }))


  /* caret focus */

  def caret_focus(caret_range: Text.Range, visible_range: Text.Range): Rendering.Focus =
  {
    val focus = entity_focus_defs(caret_range)
    if (focus.defined) focus
    else entity_focus(caret_range, entity_focus_defs(visible_range))
  }

  def caret_focus_ranges(caret_range: Text.Range, visible_range: Text.Range): List[Text.Range] =
  {
    val focus_defs = caret_focus(caret_range, visible_range)
    if (focus_defs.defined) {
      snapshot.cumulate[Boolean](visible_range, false, Rendering.entity_elements, _ =>
        {
          case (_, Text.Info(_, XML.Elem(Markup.Entity.Id(i), _)))
          if focus_defs(i) => Some(true)
          case _ => None
        }).flatMap(info => if (info.info) Some(info.range) else None)
    }
    else Nil
  }


  /* messages */

  def message_underline_color(elements: Markup.Elements, range: Text.Range)
    : List[Text.Info[Rendering.Color.Value]] =
  {
    val results =
      snapshot.cumulate[Int](range, 0, elements, _ =>
        {
          case (pri, Text.Info(_, elem)) => Some(pri max Rendering.message_pri(elem.name))
        })
    for {
      Text.Info(r, pri) <- results
      color <- Rendering.message_underline_color.get(pri)
    } yield Text.Info(r, color)
  }

  def text_messages(range: Text.Range): List[Text.Info[XML.Elem]] =
  {
    val results =
      snapshot.cumulate[Vector[Command.Results.Entry]](
        range, Vector.empty, Rendering.message_elements, command_states =>
          {
            case (res, Text.Info(_, elem)) =>
              Command.State.get_result_proper(command_states, elem.markup.properties)
                .map(res :+ _)
            case _ => None
          })

    var seen_serials = Set.empty[Long]
    def seen(i: Long): Boolean =
    {
      val b = seen_serials(i)
      seen_serials += i
      b
    }
    for {
      Text.Info(range, entries) <- results
      (i, elem) <- entries if !seen(i)
    } yield Text.Info(range, elem)
  }


  /* tooltips */

  def timing_threshold: Double = 0.0

  private sealed case class Tooltip_Info(
    range: Text.Range,
    timing: Timing = Timing.zero,
    messages: List[(Long, XML.Tree)] = Nil,
    rev_infos: List[(Boolean, XML.Tree)] = Nil)
  {
    def + (t: Timing): Tooltip_Info = copy(timing = timing + t)
    def + (r0: Text.Range, serial: Long, tree: XML.Tree): Tooltip_Info =
    {
      val r = snapshot.convert(r0)
      if (range == r) copy(messages = (serial -> tree) :: messages)
      else copy(range = r, messages = List(serial -> tree))
    }
    def + (r0: Text.Range, important: Boolean, tree: XML.Tree): Tooltip_Info =
    {
      val r = snapshot.convert(r0)
      if (range == r) copy(rev_infos = (important -> tree) :: rev_infos)
      else copy (range = r, rev_infos = List(important -> tree))
    }

    def timing_info(tree: XML.Tree): Option[XML.Tree] =
      tree match {
        case XML.Elem(Markup(Markup.TIMING, _), _) =>
          if (timing.elapsed.seconds >= timing_threshold) Some(XML.Text(timing.message)) else None
        case _ => Some(tree)
      }
    def infos(important: Boolean): List[XML.Tree] =
      for {
        (is_important, tree) <- rev_infos.reverse if is_important == important
        tree1 <- timing_info(tree)
      } yield tree1
  }

  def perhaps_append_file(node_name: Document.Node.Name, name: String): String =
    if (Path.is_valid(name)) session.resources.append(node_name, Path.explode(name)) else name

  def tooltips(elements: Markup.Elements, range: Text.Range): Option[Text.Info[List[XML.Tree]]] =
  {
    val results =
      snapshot.cumulate[Tooltip_Info](range, Tooltip_Info(range), elements, command_states =>
        {
          case (info, Text.Info(_, XML.Elem(Markup.Timing(t), _))) => Some(info + t)

          case (info, Text.Info(r0, msg @ XML.Elem(Markup(Markup.BAD, Markup.Serial(i)), body)))
          if body.nonEmpty => Some(info + (r0, i, msg))

          case (info, Text.Info(r0, XML.Elem(Markup(name, props), _)))
          if Rendering.tooltip_message_elements(name) =>
            for ((i, tree) <- Command.State.get_result_proper(command_states, props))
            yield (info + (r0, i, tree))

          case (info, Text.Info(r0, XML.Elem(Markup.Entity(kind, name), _)))
          if kind != "" && kind != Markup.ML_DEF =>
            val kind1 = Word.implode(Word.explode('_', kind))
            val txt1 =
              if (name == "") kind1
              else if (kind1 == "") quote(name)
              else kind1 + " " + quote(name)
            val info1 = info + (r0, true, XML.Text(txt1))
            Some(if (kind == Markup.COMMAND) info1 + (r0, true, XML.elem(Markup.TIMING)) else info1)

          case (info, Text.Info(r0, XML.Elem(Markup.Path(name), _))) =>
            val file = perhaps_append_file(snapshot.node_name, name)
            val text =
              if (name == file) "file " + quote(file)
              else "path " + quote(name) + "\nfile " + quote(file)
            Some(info + (r0, true, XML.Text(text)))

          case (info, Text.Info(r0, XML.Elem(Markup.Doc(name), _))) =>
            val text = "doc " + quote(name)
            Some(info + (r0, true, XML.Text(text)))

          case (info, Text.Info(r0, XML.Elem(Markup.Url(name), _))) =>
            Some(info + (r0, true, XML.Text("URL " + quote(name))))

          case (info, Text.Info(r0, XML.Elem(Markup(name, _), body)))
          if name == Markup.SORTING || name == Markup.TYPING =>
            Some(info + (r0, true, Pretty.block(XML.Text("::") :: Pretty.brk(1) :: body)))

          case (info, Text.Info(r0, XML.Elem(Markup(Markup.CLASS_PARAMETER, _), body))) =>
            Some(info + (r0, true, Pretty.block(0, body)))

          case (info, Text.Info(r0, XML.Elem(Markup(Markup.ML_TYPING, _), body))) =>
            Some(info + (r0, false, Pretty.block(XML.Text("ML:") :: Pretty.brk(1) :: body)))

          case (info, Text.Info(r0, Protocol.ML_Breakpoint(breakpoint))) =>
              val text =
                if (session.debugger.breakpoint_state(breakpoint)) "breakpoint (enabled)"
                else "breakpoint (disabled)"
              Some(info + (r0, true, XML.Text(text)))
          case (info, Text.Info(r0, XML.Elem(Markup.Language(language, _, _, _), _))) =>
            val lang = Word.implode(Word.explode('_', language))
            Some(info + (r0, true, XML.Text("language: " + lang)))

          case (info, Text.Info(r0, XML.Elem(Markup.Expression(kind), _))) =>
            val descr = if (kind == "") "expression" else "expression: " + kind
            Some(info + (r0, true, XML.Text(descr)))

          case (info, Text.Info(r0, XML.Elem(Markup(Markup.MARKDOWN_PARAGRAPH, _), _))) =>
            Some(info + (r0, true, XML.Text("Markdown: paragraph")))
          case (info, Text.Info(r0, XML.Elem(Markup(Markup.MARKDOWN_ITEM, _), _))) =>
            Some(info + (r0, true, XML.Text("Markdown: item")))
          case (info, Text.Info(r0, XML.Elem(Markup.Markdown_List(kind), _))) =>
            Some(info + (r0, true, XML.Text("Markdown: " + kind)))

          case (info, Text.Info(r0, XML.Elem(Markup(name, _), _))) =>
            Rendering.tooltip_descriptions.get(name).map(desc => info + (r0, true, XML.Text(desc)))
        }).map(_.info)

    if (results.isEmpty) None
    else {
      val r = Text.Range(results.head.range.start, results.last.range.stop)
      val all_tips =
        (SortedMap.empty[Long, XML.Tree] /: results.flatMap(_.messages))(_ + _)
          .iterator.map(_._2).toList :::
        results.flatMap(res => res.infos(true)) :::
        results.flatMap(res => res.infos(false)).lastOption.toList
      if (all_tips.isEmpty) None else Some(Text.Info(r, all_tips))
    }
  }


  /* messages */

  def warnings(range: Text.Range): List[Text.Markup] =
    snapshot.select(range, Rendering.warning_elements, _ => Some(_)).map(_.info)

  def errors(range: Text.Range): List[Text.Markup] =
    snapshot.select(range, Rendering.error_elements, _ => Some(_)).map(_.info)


  /* command status overview */

  def overview_color(range: Text.Range): Option[Rendering.Color.Value] =
  {
    if (snapshot.is_outdated) None
    else {
      val results =
        snapshot.cumulate[List[Markup]](range, Nil, Document_Status.Command_Status.liberal_elements,
          _ =>
            {
              case (status, Text.Info(_, elem)) => Some(elem.markup :: status)
            }, status = true)
      if (results.isEmpty) None
      else {
        val status = Document_Status.Command_Status.make(results.iterator.flatMap(_.info))

        if (status.is_running) Some(Rendering.Color.running)
        else if (status.is_failed) Some(Rendering.Color.error)
        else if (status.is_warned) Some(Rendering.Color.warning)
        else if (status.is_unprocessed) Some(Rendering.Color.unprocessed)
        else None
      }
    }
  }


  /* antiquoted text */

  def antiquoted(range: Text.Range): Option[Text.Range] =
    snapshot.cumulate[Option[Text.Range]](range, None, Rendering.antiquoted_elements, _ =>
      {
        case (res, info) => if (res.isEmpty) Some(Some(info.range)) else None
      }).headOption.flatMap(_.info)


  /* meta data */

  def meta_data(range: Text.Range): Properties.T =
  {
    val results =
      snapshot.cumulate[Properties.T](range, Nil, Rendering.meta_data_elements, _ =>
        {
          case (res, Text.Info(_, elem)) =>
            val plain_text = XML.content(elem)
            Some((elem.name -> plain_text) :: res)
        })
    Library.distinct(results.flatMap(_.info.reverse))
  }


  /* document tags */

  def document_tags(range: Text.Range): List[String] =
  {
    val results =
      snapshot.cumulate[List[String]](range, Nil, Rendering.document_tag_elements, _ =>
        {
          case (res, Text.Info(_, XML.Elem(Markup.Document_Tag(name), _))) => Some(name :: res)
          case _ => None
        })
    Library.distinct(results.flatMap(_.info.reverse))
  }
}
