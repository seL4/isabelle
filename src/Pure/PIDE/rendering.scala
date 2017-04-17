/*  Title:      Pure/PIDE/rendering.scala
    Author:     Makarius

Isabelle-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle


object Rendering
{
  /* color */

  object Color extends Enumeration
  {
    // background
    val unprocessed1 = Value("unprocessed1")
    val running1 = Value("running1")
    val bad = Value("bad")
    val intensify = Value("intensify")
    val entity = Value("entity")
    val active = Value("active")
    val active_result = Value("active_result")
    val markdown_item1 = Value("markdown_item1")
    val markdown_item2 = Value("markdown_item2")
    val markdown_item3 = Value("markdown_item3")
    val markdown_item4 = Value("markdown_item4")
    val background_colors = values

    // foreground
    val quoted = Value("quoted")
    val antiquoted = Value("antiquoted")
    val foreground_colors = values -- background_colors

    // message underline
    val writeln = Value("writeln")
    val information = Value("information")
    val warning = Value("warning")
    val legacy = Value("legacy")
    val error = Value("error")
    val message_underline_colors = values -- background_colors -- foreground_colors

    // message background
    val writeln_message = Value("writeln_message")
    val information_message = Value("information_message")
    val tracing_message = Value("tracing_message")
    val warning_message = Value("warning_message")
    val legacy_message = Value("legacy_message")
    val error_message = Value("error_message")
    val message_background_colors =
      values -- background_colors -- foreground_colors -- message_underline_colors

    // text
    val main = Value("main")
    val keyword1 = Value("keyword1")
    val keyword2 = Value("keyword2")
    val keyword3 = Value("keyword3")
    val quasi_keyword = Value("quasi_keyword")
    val improper = Value("improper")
    val operator = Value("operator")
    val tfree = Value("tfree")
    val tvar = Value("tvar")
    val free = Value("free")
    val skolem = Value("skolem")
    val bound = Value("bound")
    val var_ = Value("var")
    val inner_numeral = Value("inner_numeral")
    val inner_quoted = Value("inner_quoted")
    val inner_cartouche = Value("inner_cartouche")
    val inner_comment = Value("inner_comment")
    val dynamic = Value("dynamic")
    val class_parameter = Value("class_parameter")
    val antiquote = Value("antiquote")
    val text_colors =
      values -- background_colors -- foreground_colors -- message_underline_colors --
      message_background_colors
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

  def output_messages(results: Command.Results): List[XML.Tree] =
  {
    val (states, other) =
      results.iterator.map(_._2).filterNot(Protocol.is_result(_)).toList
        .partition(Protocol.is_state(_))
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
    Markup.VAR -> Color.var_,
    Markup.INNER_STRING -> Color.inner_quoted,
    Markup.INNER_CARTOUCHE -> Color.inner_cartouche,
    Markup.INNER_COMMENT -> Color.inner_comment,
    Markup.DYNAMIC_FACT -> Color.dynamic,
    Markup.CLASS_PARAMETER -> Color.class_parameter,
    Markup.ANTIQUOTE -> Color.antiquote,
    Markup.ML_KEYWORD1 -> Color.keyword1,
    Markup.ML_KEYWORD2 -> Color.keyword2,
    Markup.ML_KEYWORD3 -> Color.keyword3,
    Markup.ML_DELIMITER -> Color.main,
    Markup.ML_NUMERAL -> Color.inner_numeral,
    Markup.ML_CHAR -> Color.inner_quoted,
    Markup.ML_STRING -> Color.inner_quoted,
    Markup.ML_COMMENT -> Color.inner_comment,
    Markup.SML_STRING -> Color.inner_quoted,
    Markup.SML_COMMENT -> Color.inner_comment)


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


  /* markup elements */

  val active_elements =
    Markup.Elements(Markup.DIALOG, Markup.BROWSER, Markup.GRAPHVIEW,
      Markup.SENDBACK, Markup.JEDIT_ACTION, Markup.SIMP_TRACE_PANEL)

  val background_elements =
    Protocol.proper_status_elements + Markup.WRITELN_MESSAGE +
      Markup.STATE_MESSAGE + Markup.INFORMATION_MESSAGE +
      Markup.TRACING_MESSAGE + Markup.WARNING_MESSAGE +
      Markup.LEGACY_MESSAGE + Markup.ERROR_MESSAGE +
      Markup.BAD + Markup.INTENSIFY + Markup.ENTITY +
      Markup.Markdown_Item.name ++ active_elements

  val foreground_elements =
    Markup.Elements(Markup.STRING, Markup.ALT_STRING, Markup.VERBATIM,
      Markup.CARTOUCHE, Markup.ANTIQUOTED)

  val semantic_completion_elements =
    Markup.Elements(Markup.COMPLETION, Markup.NO_COMPLETION)

  val tooltip_elements =
    Markup.Elements(Markup.LANGUAGE, Markup.EXPRESSION, Markup.TIMING, Markup.ENTITY,
      Markup.SORTING, Markup.TYPING, Markup.CLASS_PARAMETER, Markup.ML_TYPING,
      Markup.ML_BREAKPOINT, Markup.PATH, Markup.DOC, Markup.URL, Markup.MARKDOWN_PARAGRAPH,
      Markup.Markdown_List.name) ++ Markup.Elements(tooltip_descriptions.keySet)

  val tooltip_message_elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING, Markup.LEGACY, Markup.ERROR,
      Markup.BAD)

  val caret_focus_elements = Markup.Elements(Markup.ENTITY)

  val text_color_elements = Markup.Elements(text_color.keySet)
}

abstract class Rendering(
  val snapshot: Document.Snapshot,
  val options: Options,
  val session: Session)
{
  override def toString: String = "Rendering(" + snapshot.toString + ")"


  /* completion */

  def semantic_completion(completed_range: Option[Text.Range], range: Text.Range)
      : Option[Text.Info[Completion.Semantic]] =
    if (snapshot.is_outdated) None
    else {
      snapshot.select(range, Rendering.semantic_completion_elements, _ =>
        {
          case Completion.Semantic.Info(info) =>
            completed_range match {
              case Some(range0) if range0.contains(info.range) && range0 != info.range => None
              case _ => Some(info)
            }
          case _ => None
        }).headOption.map(_.info)
    }


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


  /* text background */

  def background(elements: Markup.Elements, range: Text.Range, focus: Set[Long])
    : List[Text.Info[Rendering.Color.Value]] =
  {
    for {
      Text.Info(r, result) <-
        snapshot.cumulate[(List[Markup], Option[Rendering.Color.Value])](
          range, (List(Markup.Empty), None), Rendering.background_elements,
          command_states =>
            {
              case (((markups, color), Text.Info(_, XML.Elem(markup, _))))
              if markups.nonEmpty && Protocol.proper_status_elements(markup.name) =>
                Some((markup :: markups, color))
              case (_, Text.Info(_, XML.Elem(Markup(Markup.BAD, _), _))) =>
                Some((Nil, Some(Rendering.Color.bad)))
              case (_, Text.Info(_, XML.Elem(Markup(Markup.INTENSIFY, _), _))) =>
                Some((Nil, Some(Rendering.Color.intensify)))
              case (_, Text.Info(_, XML.Elem(Markup(Markup.ENTITY, props), _))) =>
                props match {
                  case Markup.Entity.Def(i) if focus(i) => Some((Nil, Some(Rendering.Color.entity)))
                  case Markup.Entity.Ref(i) if focus(i) => Some((Nil, Some(Rendering.Color.entity)))
                  case _ => None
                }
              case (_, Text.Info(_, XML.Elem(Markup.Markdown_Item(depth), _))) =>
                val color =
                  depth % 4 match {
                    case 1 => Rendering.Color.markdown_item1
                    case 2 => Rendering.Color.markdown_item2
                    case 3 => Rendering.Color.markdown_item3
                    case _ => Rendering.Color.markdown_item4
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
            val status = Protocol.Status.make(markups.iterator)
            if (status.is_unprocessed) Some(Rendering.Color.unprocessed1)
            else if (status.is_running) Some(Rendering.Color.running1)
            else opt_color
          case (_, opt_color) => opt_color
        })
    } yield Text.Info(r, color)
  }


  /* text foreground */

  def foreground(range: Text.Range): List[Text.Info[Rendering.Color.Value]] =
    snapshot.select(range, Rendering.foreground_elements, _ =>
      {
        case Text.Info(_, elem) =>
          if (elem.name == Markup.ANTIQUOTED) Some(Rendering.Color.antiquoted)
          else Some(Rendering.Color.quoted)
      })


  /* caret focus */

  private def entity_focus(range: Text.Range,
    check: (Boolean, Long) => Boolean = (is_def: Boolean, i: Long) => is_def): Set[Long] =
  {
    val results =
      snapshot.cumulate[Set[Long]](range, Set.empty, Rendering.caret_focus_elements, _ =>
          {
            case (serials, Text.Info(_, XML.Elem(Markup(Markup.ENTITY, props), _))) =>
              props match {
                case Markup.Entity.Def(i) if check(true, i) => Some(serials + i)
                case Markup.Entity.Ref(i) if check(false, i) => Some(serials + i)
                case _ => None
              }
            case _ => None
          })
    (Set.empty[Long] /: results){ case (s1, Text.Info(_, s2)) => s1 ++ s2 }
  }

  def caret_focus(caret_range: Text.Range, visible_range: Text.Range): Set[Long] =
  {
    val focus_defs = entity_focus(caret_range)
    if (focus_defs.nonEmpty) focus_defs
    else {
      val visible_defs = entity_focus(visible_range)
      entity_focus(caret_range, (is_def: Boolean, i: Long) => !is_def && visible_defs.contains(i))
    }
  }

  def caret_focus_ranges(caret_range: Text.Range, visible_range: Text.Range): List[Text.Range] =
  {
    val focus = caret_focus(caret_range, visible_range)
    if (focus.nonEmpty) {
      val results =
        snapshot.cumulate[Boolean](visible_range, false, Rendering.caret_focus_elements, _ =>
          {
            case (_, Text.Info(_, XML.Elem(Markup(Markup.ENTITY, props), _))) =>
              props match {
                case Markup.Entity.Def(i) if focus(i) => Some(true)
                case Markup.Entity.Ref(i) if focus(i) => Some(true)
                case _ => None
              }
          })
      for (info <- results if info.info) yield info.range
    }
    else Nil
  }


  /* message underline color */

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


  /* tooltips */

  def timing_threshold: Double

  private sealed case class Tooltip_Info(
    range: Text.Range,
    timing: Timing = Timing.zero,
    messages: List[Command.Results.Entry] = Nil,
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
    def infos(important: Boolean): List[XML.Tree] =
      rev_infos.filter(p => p._1 == important).reverse.map(_._2)
  }

  def perhaps_append_file(node_name: Document.Node.Name, name: String): String =
    if (Path.is_valid(name)) session.resources.append(node_name, Path.explode(name)) else name

  def tooltips(elements: Markup.Elements, range: Text.Range): Option[Text.Info[List[XML.Tree]]] =
  {
    val results =
      snapshot.cumulate[Tooltip_Info](range, Tooltip_Info(range), elements, _ =>
        {
          case (info, Text.Info(_, XML.Elem(Markup.Timing(t), _))) => Some(info + t)

          case (info, Text.Info(r0, XML.Elem(Markup(name, props @ Markup.Serial(serial)), body)))
          if Rendering.tooltip_message_elements(name) && body.nonEmpty =>
            Some(info + (r0, serial, XML.Elem(Markup(Markup.message(name), props), body)))

          case (info, Text.Info(r0, XML.Elem(Markup.Entity(kind, name), _)))
          if kind != "" && kind != Markup.ML_DEF =>
            val kind1 = Word.implode(Word.explode('_', kind))
            val txt1 =
              if (name == "") kind1
              else if (kind1 == "") quote(name)
              else kind1 + " " + quote(name)
            val txt2 =
              if (kind == Markup.COMMAND && info.timing.elapsed.seconds >= timing_threshold)
                "\n" + info.timing.message
              else ""
            Some(info + (r0, true, XML.Text(txt1 + txt2)))

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
          case (info, Text.Info(r0, XML.Elem(Markup.Markdown_List(kind), _))) =>
            Some(info + (r0, true, XML.Text("Markdown: " + kind)))

          case (info, Text.Info(r0, XML.Elem(Markup(name, _), _))) =>
            Rendering.tooltip_descriptions.get(name).map(desc => info + (r0, true, XML.Text(desc)))
        }).map(_.info)

    if (results.isEmpty) None
    else {
      val r = Text.Range(results.head.range.start, results.last.range.stop)
      val all_tips =
        Command.Results.make(results.flatMap(_.messages)).iterator.map(_._2).toList :::
        results.flatMap(res => res.infos(true)) :::
        results.flatMap(res => res.infos(false)).lastOption.toList
      if (all_tips.isEmpty) None else Some(Text.Info(r, all_tips))
    }
  }
}
