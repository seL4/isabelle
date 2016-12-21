/*  Title:      Pure/PIDE/rendering.scala
    Author:     Makarius

Isabelle-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle


object Rendering
{
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
}

abstract class Rendering(
  val snapshot: Document.Snapshot,
  val options: Options,
  val resources: Resources)
{
  override def toString: String = "Rendering(" + snapshot.toString + ")"


  /* tooltips */

  def tooltip_margin: Int
  def timing_threshold: Double

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

          case (prev, Text.Info(r, XML.Elem(Markup.Entity(kind, name), _)))
          if kind != "" &&
            kind != Markup.ML_DEF &&
            kind != Markup.ML_OPEN &&
            kind != Markup.ML_STRUCTURE =>
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
        Some(Text.Info(r, Library.separate(Pretty.fbrk, all_tips)))
    }
  }
}
