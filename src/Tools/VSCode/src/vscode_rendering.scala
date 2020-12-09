/*  Title:      Tools/VSCode/src/vscode_rendering.scala
    Author:     Makarius

Isabelle/VSCode-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.annotation.tailrec


object VSCode_Rendering
{
  /* decorations */

  private def color_decorations(prefix: String, types: Set[Rendering.Color.Value],
    colors: List[Text.Info[Rendering.Color.Value]]): List[VSCode_Model.Decoration] =
  {
    val color_ranges =
      (Map.empty[Rendering.Color.Value, List[Text.Range]] /: colors) {
        case (m, Text.Info(range, c)) => m + (c -> (range :: m.getOrElse(c, Nil)))
      }
    types.toList.map(c =>
      VSCode_Model.Decoration.ranges(prefix + c.toString, color_ranges.getOrElse(c, Nil).reverse))
  }

  private val background_colors =
    Rendering.Color.background_colors - Rendering.Color.active - Rendering.Color.active_result -
      Rendering.Color.entity

  private val dotted_colors =
    Set(Rendering.Color.writeln, Rendering.Color.information, Rendering.Color.warning)


  /* diagnostic messages */

  private val message_severity =
    Map(
      Markup.LEGACY -> LSP.DiagnosticSeverity.Warning,
      Markup.ERROR -> LSP.DiagnosticSeverity.Error)


  /* markup elements */

  private val diagnostics_elements =
    Markup.Elements(Markup.LEGACY, Markup.ERROR)

  private val background_elements =
    Rendering.background_elements - Markup.ENTITY -- Rendering.active_elements

  private val dotted_elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING)

  val tooltip_elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING, Markup.BAD) ++
    Rendering.tooltip_elements

  private val hyperlink_elements =
    Markup.Elements(Markup.ENTITY, Markup.PATH, Markup.POSITION, Markup.CITATION)
}

class VSCode_Rendering(snapshot: Document.Snapshot, val model: VSCode_Model)
  extends Rendering(snapshot, model.resources.options, model.session)
{
  rendering =>

  def resources: VSCode_Resources = model.resources

  override def get_text(range: Text.Range): Option[String] = model.get_text(range)


  /* bibtex */

  def bibtex_entries_iterator(): Iterator[Text.Info[(String, VSCode_Model)]] =
    Bibtex.entries_iterator(resources.get_models)

  def bibtex_completion(history: Completion.History, caret: Text.Offset): Option[Completion.Result] =
    Bibtex.completion(history, rendering, caret, resources.get_models)


  /* completion */

  def completion(caret_pos: Line.Position, caret: Text.Offset): List[LSP.CompletionItem] =
  {
    val doc = model.content.doc
    val line = caret_pos.line
    doc.offset(Line.Position(line)) match {
      case None => Nil
      case Some(line_start) =>
        val history = Completion.History.empty
        val caret_range = before_caret_range(caret)

        val syntax = model.syntax()
        val syntax_completion =
          syntax.complete(history, unicode = false, explicit = true,
            line_start, doc.lines(line).text, caret - line_start,
            language_context(caret_range) getOrElse syntax.language_context)

        val (no_completion, semantic_completion) =
          rendering.semantic_completion_result(
            history, false, syntax_completion.map(_.range), caret_range)

        if (no_completion) Nil
        else {
          val results =
            Completion.Result.merge(history,
              semantic_completion,
              syntax_completion,
              VSCode_Spell_Checker.completion(rendering, caret),
              path_completion(caret),
              bibtex_completion(history, caret))
          val items =
            results match {
              case None => Nil
              case Some(result) =>
                result.items.map(item =>
                  LSP.CompletionItem(
                    label = item.replacement,
                    detail = Some(item.description.mkString(" ")),
                    range = Some(doc.range(item.range))))
            }
          items ::: VSCode_Spell_Checker.menu_items(rendering, caret)
        }
    }
  }


  /* diagnostics */

  def diagnostics: List[Text.Info[Command.Results]] =
    snapshot.cumulate[Command.Results](
      model.content.text_range, Command.Results.empty, VSCode_Rendering.diagnostics_elements,
        command_states =>
          {
            case (res, Text.Info(_, msg @ XML.Elem(Markup(Markup.BAD, Markup.Serial(i)), body)))
            if body.nonEmpty => Some(res + (i -> msg))

            case (res, Text.Info(_, msg)) =>
              Command.State.get_result_proper(command_states, msg.markup.properties).map(res + _)

            case _ => None
          }).filterNot(info => info.info.is_empty)

  def diagnostics_output(results: List[Text.Info[Command.Results]]): List[LSP.Diagnostic] =
  {
    (for {
      Text.Info(text_range, res) <- results.iterator
      range = model.content.doc.range(text_range)
      (_, XML.Elem(Markup(name, _), body)) <- res.iterator
    } yield {
      val message = resources.output_pretty_message(body)
      val severity = VSCode_Rendering.message_severity.get(name)
      LSP.Diagnostic(range, message, severity = severity)
    }).toList
  }


  /* text color */

  def text_color(range: Text.Range): List[Text.Info[Rendering.Color.Value]] =
  {
    snapshot.select(range, Rendering.text_color_elements, _ =>
      {
        case Text.Info(_, XML.Elem(Markup(name, props), _)) =>
          if (name != Markup.IMPROPER && props.contains((Markup.KIND, Markup.COMMAND))) None
          else Rendering.text_color.get(name)
      })
  }


  /* text overview color */

  private sealed case class Color_Info(
    color: Rendering.Color.Value, offset: Text.Offset, end_offset: Text.Offset, end_line: Int)

  def text_overview_color: List[Text.Info[Rendering.Color.Value]] =
  {
    @tailrec def loop(offset: Text.Offset, line: Int, lines: List[Line], colors: List[Color_Info])
      : List[Text.Info[Rendering.Color.Value]] =
    {
      if (lines.nonEmpty) {
        val end_offset = offset + lines.head.text.length
        val colors1 =
          (overview_color(Text.Range(offset, end_offset)), colors) match {
            case (Some(color), old :: rest) if color == old.color && line == old.end_line =>
              old.copy(end_offset = end_offset, end_line = line + 1) :: rest
            case (Some(color), _) =>
              Color_Info(color, offset, end_offset, line + 1) :: colors
            case (None, _) => colors
          }
        loop(end_offset + 1, line + 1, lines.tail, colors1)
      }
      else {
        colors.reverse.map(info =>
          Text.Info(Text.Range(info.offset, info.end_offset), info.color))
      }
    }
    loop(0, 0, model.content.doc.lines, Nil)
  }


  /* dotted underline */

  def dotted(range: Text.Range): List[Text.Info[Rendering.Color.Value]] =
    message_underline_color(VSCode_Rendering.dotted_elements, range)


  /* decorations */

  def decorations: List[VSCode_Model.Decoration] = // list of canonical length and order
    Par_List.map((f: () => List[VSCode_Model.Decoration]) => f(),
      List(
        () =>
          VSCode_Rendering.color_decorations("background_", VSCode_Rendering.background_colors,
            background(VSCode_Rendering.background_elements, model.content.text_range, Set.empty)),
        () =>
          VSCode_Rendering.color_decorations("foreground_", Rendering.Color.foreground_colors,
            foreground(model.content.text_range)),
        () =>
          VSCode_Rendering.color_decorations("text_", Rendering.Color.text_colors,
            text_color(model.content.text_range)),
        () =>
          VSCode_Rendering.color_decorations("text_overview_", Rendering.Color.text_overview_colors,
            text_overview_color),
        () =>
          VSCode_Rendering.color_decorations("dotted_", VSCode_Rendering.dotted_colors,
            dotted(model.content.text_range)))).flatten :::
    List(VSCode_Spell_Checker.decoration(rendering))

  def decoration_output(decoration: VSCode_Model.Decoration): LSP.Decoration =
  {
    val content =
      for (Text.Info(text_range, msgs) <- decoration.content)
      yield {
        val range = model.content.doc.range(text_range)
        LSP.DecorationOpts(range,
          msgs.map(msg => LSP.MarkedString(resources.output_pretty_tooltip(msg))))
      }
    LSP.Decoration(decoration.typ, content)
  }


  /* tooltips */

  override def timing_threshold: Double = options.real("vscode_timing_threshold")


  /* hyperlinks */

  def hyperlink_source_file(source_name: String, line1: Int, range: Symbol.Range)
    : Option[Line.Node_Range] =
  {
    for {
      platform_path <- resources.source_file(source_name)
      file <-
        (try { Some(File.absolute(new JFile(platform_path))) }
         catch { case ERROR(_) => None })
    }
    yield {
      Line.Node_Range(file.getPath,
        if (range.start > 0) {
          resources.get_file_content(resources.node_name(file)) match {
            case Some(text) =>
              val chunk = Symbol.Text_Chunk(text)
              val doc = Line.Document(text)
              doc.range(chunk.decode(range))
            case _ =>
              Line.Range(Line.Position((line1 - 1) max 0))
          }
        }
        else Line.Range(Line.Position((line1 - 1) max 0)))
    }
  }

  def hyperlink_command(id: Document_ID.Generic, range: Symbol.Range): Option[Line.Node_Range] =
  {
    if (snapshot.is_outdated) None
    else
      for {
        start <- snapshot.find_command_position(id, range.start)
        stop <- snapshot.find_command_position(id, range.stop)
      } yield Line.Node_Range(start.name, Line.Range(start.pos, stop.pos))
  }

  def hyperlink_position(pos: Position.T): Option[Line.Node_Range] =
    pos match {
      case Position.Item_File(name, line, range) => hyperlink_source_file(name, line, range)
      case Position.Item_Id(id, range) => hyperlink_command(id, range)
      case _ => None
    }

  def hyperlink_def_position(pos: Position.T): Option[Line.Node_Range] =
    pos match {
      case Position.Item_Def_File(name, line, range) => hyperlink_source_file(name, line, range)
      case Position.Item_Def_Id(id, range) => hyperlink_command(id, range)
      case _ => None
    }

  def hyperlinks(range: Text.Range): List[Line.Node_Range] =
  {
    snapshot.cumulate[List[Line.Node_Range]](
      range, Nil, VSCode_Rendering.hyperlink_elements, _ =>
        {
          case (links, Text.Info(_, XML.Elem(Markup.Path(name), _))) =>
            val file = perhaps_append_file(snapshot.node_name, name)
            Some(Line.Node_Range(file) :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.ENTITY, props), _))) =>
            hyperlink_def_position(props).map(_ :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.POSITION, props), _))) =>
            hyperlink_position(props).map(_ :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup.Citation(name), _))) =>
            val iterator =
              for {
                Text.Info(entry_range, (entry, model)) <- bibtex_entries_iterator()
                if entry == name
              } yield Line.Node_Range(model.node_name.node, model.content.doc.range(entry_range))
            if (iterator.isEmpty) None else Some((links /: iterator)(_ :+ _))

          case _ => None
        }) match { case Text.Info(_, links) :: _ => links.reverse case _ => Nil }
  }
}
