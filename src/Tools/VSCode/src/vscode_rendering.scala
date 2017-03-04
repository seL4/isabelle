/*  Title:      Tools/VSCode/src/vscode_rendering.scala
    Author:     Makarius

Isabelle/VSCode-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}


object VSCode_Rendering
{
  /* decorations */

  private def color_decorations(prefix: String, types: Rendering.Color.ValueSet,
    colors: List[Text.Info[Rendering.Color.Value]]): List[Document_Model.Decoration] =
  {
    val color_ranges =
      (Map.empty[Rendering.Color.Value, List[Text.Range]] /: colors) {
        case (m, Text.Info(range, c)) => m + (c -> (range :: m.getOrElse(c, Nil)))
      }
    types.toList.map(c =>
      Document_Model.Decoration(prefix + c.toString,
        color_ranges.getOrElse(c, Nil).reverse.map(r => Text.Info(r, Nil: List[XML.Body]))))
  }


  /* diagnostic messages */

  private val message_severity =
    Map(
      Markup.WRITELN -> Protocol.DiagnosticSeverity.Information,
      Markup.INFORMATION -> Protocol.DiagnosticSeverity.Information,
      Markup.WARNING -> Protocol.DiagnosticSeverity.Warning,
      Markup.LEGACY -> Protocol.DiagnosticSeverity.Warning,
      Markup.ERROR -> Protocol.DiagnosticSeverity.Error)


  /* markup elements */

  private val diagnostics_elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING, Markup.LEGACY, Markup.ERROR)

  private val bad_elements = Markup.Elements(Markup.BAD)

  private val hyperlink_elements =
    Markup.Elements(Markup.ENTITY, Markup.PATH, Markup.POSITION, Markup.CITATION)
}

class VSCode_Rendering(
    val model: Document_Model,
    snapshot: Document.Snapshot,
    resources: VSCode_Resources)
  extends Rendering(snapshot, resources.options, resources)
{
  /* completion */

  def completion(range: Text.Range): List[Protocol.CompletionItem] =
    semantic_completion(None, range) match {
      case Some(Text.Info(complete_range, names: Completion.Names)) =>
        model.content.try_get_text(complete_range) match {
          case Some(original) =>
            names.complete(complete_range, Completion.History.empty,
                resources.decode_text, original) match {
              case Some(result) =>
                result.items.map(item =>
                  Protocol.CompletionItem(
                    label = item.replacement,
                    detail = Some(item.description.mkString(" ")),
                    range = Some(model.content.doc.range(item.range))))
              case None => Nil
            }
          case None => Nil
        }
      case _ => Nil
    }


  /* diagnostics */

  def diagnostics: List[Text.Info[Command.Results]] =
    snapshot.cumulate[Command.Results](
      model.content.text_range, Command.Results.empty, VSCode_Rendering.diagnostics_elements, _ =>
      {
        case (res, Text.Info(_, msg @ XML.Elem(Markup(_, Markup.Serial(i)), body)))
        if body.nonEmpty => Some(res + (i -> msg))

        case _ => None
      }).filterNot(info => info.info.is_empty)

  val diagnostics_margin = options.int("vscode_diagnostics_margin")

  def diagnostics_output(results: List[Text.Info[Command.Results]]): List[Protocol.Diagnostic] =
  {
    (for {
      Text.Info(text_range, res) <- results.iterator
      range = model.content.doc.range(text_range)
      (_, XML.Elem(Markup(name, _), body)) <- res.iterator
    } yield {
      val message = resources.output_pretty(body, diagnostics_margin)
      val severity = VSCode_Rendering.message_severity.get(name)
      Protocol.Diagnostic(range, message, severity = severity)
    }).toList
  }


  /* decorations */

  def decorations: List[Document_Model.Decoration] =
    decorations_bad :::
    VSCode_Rendering.color_decorations("background_", Rendering.Color.background,
      background(model.content.text_range, Set.empty)) :::
    VSCode_Rendering.color_decorations("foreground_", Rendering.Color.foreground,
      foreground(model.content.text_range))

  def decorations_bad: List[Document_Model.Decoration] =
  {
    val content =
      snapshot.select(model.content.text_range, VSCode_Rendering.bad_elements, _ =>
        {
          case Text.Info(_, XML.Elem(_, body)) => Some(List(body))
        })
    List(Document_Model.Decoration(Protocol.Decorations.bad, content))
  }

  def decoration_output(decoration: Document_Model.Decoration): Protocol.Decoration =
  {
    val content =
      for (Text.Info(text_range, msgs) <- decoration.content)
      yield {
        val range = model.content.doc.range(text_range)
        Protocol.DecorationOptions(range,
          msgs.map(msg =>
            Protocol.MarkedString(resources.output_pretty(msg, diagnostics_margin))))
      }
    Protocol.Decoration(decoration.typ, content)
  }


  /* tooltips */

  def tooltip_margin: Int = options.int("vscode_tooltip_margin")
  def timing_threshold: Double = options.real("vscode_timing_threshold")


  /* hyperlinks */

  def hyperlink_source_file(source_name: String, line1: Int, range: Symbol.Range)
    : Option[Line.Node_Range] =
  {
    for {
      platform_path <- resources.source_file(source_name)
      file <-
        (try { Some(new JFile(platform_path).getCanonicalFile) }
         catch { case ERROR(_) => None })
    }
    yield {
      Line.Node_Range(file.getPath,
        if (range.start > 0) {
          resources.get_file_content(file) match {
            case Some(text) =>
              val chunk = Symbol.Text_Chunk(text)
              val doc = Line.Document(text, resources.text_length)
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
            val file = resources.append_file(snapshot.node_name.master_dir, name)
            Some(Line.Node_Range(file) :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.ENTITY, props), _))) =>
            hyperlink_def_position(props).map(_ :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.POSITION, props), _))) =>
            hyperlink_position(props).map(_ :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup.Citation(name), _))) =>
            val iterator =
              for {
                Text.Info(entry_range, (entry, model)) <- resources.bibtex_entries_iterator
                if entry == name
              } yield Line.Node_Range(model.node_name.node, model.content.doc.range(entry_range))
            if (iterator.isEmpty) None else Some((links /: iterator)(_ :+ _))

          case _ => None
        }) match { case Text.Info(_, links) :: _ => links.reverse case _ => Nil }
  }
}
