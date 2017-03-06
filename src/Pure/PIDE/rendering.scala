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
    val background = values

    // foreground
    val quoted = Value("quoted")
    val antiquoted = Value("antiquoted")
    val foreground = values -- background

    // message underline
    val writeln = Value("writeln")
    val information = Value("information")
    val warning = Value("warning")
    val legacy = Value("legacy")
    val error = Value("error")
    val message_underline = values -- background -- foreground

    // message background

    val writeln_message = Value("writeln_message")
    val information_message = Value("information_message")
    val tracing_message = Value("tracing_message")
    val warning_message = Value("warning_message")
    val legacy_message = Value("legacy_message")
    val error_message = Value("error_message")
    val message_background = values -- background -- foreground -- message_underline
  }


  /* message priorities */

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
    Markup.ERROR_MESSAGE -> error_pri)

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


  /* markup elements */

  val active_elements =
    Markup.Elements(Markup.DIALOG, Markup.BROWSER, Markup.GRAPHVIEW,
      Markup.SENDBACK, Markup.JEDIT_ACTION, Markup.SIMP_TRACE_PANEL)

  private val background_elements =
    Protocol.proper_status_elements + Markup.WRITELN_MESSAGE +
      Markup.STATE_MESSAGE + Markup.INFORMATION_MESSAGE +
      Markup.TRACING_MESSAGE + Markup.WARNING_MESSAGE +
      Markup.LEGACY_MESSAGE + Markup.ERROR_MESSAGE +
      Markup.BAD + Markup.INTENSIFY + Markup.ENTITY +
      Markup.Markdown_Item.name ++ active_elements

  private val foreground_elements =
    Markup.Elements(Markup.STRING, Markup.ALT_STRING, Markup.VERBATIM,
      Markup.CARTOUCHE, Markup.ANTIQUOTED)

  private val semantic_completion_elements =
    Markup.Elements(Markup.COMPLETION, Markup.NO_COMPLETION)

  private val tooltip_descriptions =
    Map(
      Markup.CITATION -> "citation",
      Markup.TOKEN_RANGE -> "inner syntax token",
      Markup.FREE -> "free variable",
      Markup.SKOLEM -> "skolem variable",
      Markup.BOUND -> "bound variable",
      Markup.VAR -> "schematic variable",
      Markup.TFREE -> "free type variable",
      Markup.TVAR -> "schematic type variable")

  private val tooltip_elements =
    Markup.Elements(Markup.LANGUAGE, Markup.EXPRESSION, Markup.TIMING, Markup.ENTITY,
      Markup.SORTING, Markup.TYPING, Markup.CLASS_PARAMETER, Markup.ML_TYPING,
      Markup.ML_BREAKPOINT, Markup.PATH, Markup.DOC, Markup.URL, Markup.MARKDOWN_PARAGRAPH,
      Markup.Markdown_List.name) ++ Markup.Elements(tooltip_descriptions.keySet)

  private def pretty_typing(kind: String, body: XML.Body): XML.Tree =
    Pretty.block(XML.Text(kind) :: Pretty.brk(1) :: body)

  val caret_focus_elements = Markup.Elements(Markup.ENTITY)
}

abstract class Rendering(
  val snapshot: Document.Snapshot,
  val options: Options,
  val resources: Resources)
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


  /* tooltips */

  def timing_threshold: Double

  def tooltips(range: Text.Range): Option[Text.Info[List[XML.Tree]]] =
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

          case (prev, Text.Info(r, XML.Elem(Markup.Entity(kind, name), _)))
          if kind != "" && kind != Markup.ML_DEF =>
            val kind1 = Word.implode(Word.explode('_', kind))
            val txt1 =
              if (name == "") kind1
              else if (kind1 == "") quote(name)
              else kind1 + " " + quote(name)
            val t = prev.info._1
            val txt2 =
              if (kind == Markup.COMMAND && t.elapsed.seconds >= timing_threshold)
                "\n" + t.message
              else ""
            Some(add(prev, r, (true, XML.Text(txt1 + txt2))))

          case (prev, Text.Info(r, XML.Elem(Markup.Path(name), _))) =>
            val file = resources.append_file(snapshot.node_name.master_dir, name)
            val text =
              if (name == file) "file " + quote(file)
              else "path " + quote(name) + "\nfile " + quote(file)
            Some(add(prev, r, (true, XML.Text(text))))

          case (prev, Text.Info(r, XML.Elem(Markup.Doc(name), _))) =>
            val text = "doc " + quote(name)
            Some(add(prev, r, (true, XML.Text(text))))

          case (prev, Text.Info(r, XML.Elem(Markup.Url(name), _))) =>
            Some(add(prev, r, (true, XML.Text("URL " + quote(name)))))

          case (prev, Text.Info(r, XML.Elem(Markup(name, _), body)))
          if name == Markup.SORTING || name == Markup.TYPING =>
            Some(add(prev, r, (true, Rendering.pretty_typing("::", body))))

          case (prev, Text.Info(r, XML.Elem(Markup(Markup.CLASS_PARAMETER, _), body))) =>
            Some(add(prev, r, (true, Pretty.block(0, body))))

          case (prev, Text.Info(r, XML.Elem(Markup(Markup.ML_TYPING, _), body))) =>
            Some(add(prev, r, (false, Rendering.pretty_typing("ML:", body))))

          case (prev, Text.Info(r, Protocol.ML_Breakpoint(breakpoint))) =>
            val text =
              if (Debugger.breakpoint_state(breakpoint)) "breakpoint (enabled)"
              else "breakpoint (disabled)"
            Some(add(prev, r, (true, XML.Text(text))))

          case (prev, Text.Info(r, XML.Elem(Markup.Language(language, _, _, _), _))) =>
            val lang = Word.implode(Word.explode('_', language))
            Some(add(prev, r, (true, XML.Text("language: " + lang))))

          case (prev, Text.Info(r, XML.Elem(Markup.Expression(kind), _))) =>
            val descr = if (kind == "") "expression" else "expression: " + kind
            Some(add(prev, r, (true, XML.Text(descr))))

          case (prev, Text.Info(r, XML.Elem(Markup(Markup.MARKDOWN_PARAGRAPH, _), _))) =>
            Some(add(prev, r, (true, XML.Text("Markdown: paragraph"))))
          case (prev, Text.Info(r, XML.Elem(Markup.Markdown_List(kind), _))) =>
            Some(add(prev, r, (true, XML.Text("Markdown: " + kind))))

          case (prev, Text.Info(r, XML.Elem(Markup(name, _), _))) =>
            Rendering.tooltip_descriptions.get(name).
              map(descr => add(prev, r, (true, XML.Text(descr))))
        }).map(_.info)

    results.map(_.info).flatMap(res => res._2.toList) match {
      case Nil => None
      case tips =>
        val r = Text.Range(results.head.range.start, results.last.range.stop)
        val all_tips = (tips.filter(_._1) ++ tips.filter(!_._1).lastOption.toList).map(_._2)
        Some(Text.Info(r, all_tips))
    }
  }


  /* text background */

  def background(range: Text.Range, focus: Set[Long]): List[Text.Info[Rendering.Color.Value]] =
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
                  depth match {
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

  def message_underline_color(
    elements: Markup.Elements, range: Text.Range): List[Text.Info[Rendering.Color.Value]] =
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
}
