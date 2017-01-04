/*  Title:      Tools/VSCode/src/vscode_rendering.scala
    Author:     Makarius

Isabelle/VSCode-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle.vscode


import isabelle._

object VSCode_Rendering
{
  /* diagnostic messages */

  private val message_severity =
    Map(
      Markup.WRITELN -> Protocol.DiagnosticSeverity.Information,
      Markup.INFORMATION -> Protocol.DiagnosticSeverity.Information,
      Markup.WARNING -> Protocol.DiagnosticSeverity.Warning,
      Markup.LEGACY -> Protocol.DiagnosticSeverity.Warning,
      Markup.ERROR -> Protocol.DiagnosticSeverity.Error,
      Markup.BAD -> Protocol.DiagnosticSeverity.Error)


  /* markup elements */

  private val diagnostics_elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING, Markup.LEGACY, Markup.ERROR,
      Markup.BAD)

  private val hyperlink_elements =
    Markup.Elements(Markup.ENTITY, Markup.PATH, Markup.POSITION)
}

class VSCode_Rendering(
    val model: Document_Model,
    snapshot: Document.Snapshot,
    resources: VSCode_Resources)
  extends Rendering(snapshot, resources.options, resources)
{
  /* diagnostics */

  def diagnostics: List[Text.Info[Command.Results]] =
    snapshot.cumulate[Command.Results](
      model.doc.full_range, Command.Results.empty, VSCode_Rendering.diagnostics_elements, _ =>
      {
        case (res, Text.Info(_, msg @ XML.Elem(Markup(_, Markup.Serial(i)), body)))
        if body.nonEmpty => Some(res + (i -> msg))

        case _ => None
      })

  val diagnostics_margin = options.int("vscode_diagnostics_margin")

  def diagnostics_output(results: List[Text.Info[Command.Results]]): List[Protocol.Diagnostic] =
  {
    (for {
      Text.Info(text_range, res) <- results.iterator
      range = model.doc.range(text_range)
      (_, XML.Elem(Markup(name, _), body)) <- res.iterator
    } yield {
      val message = Pretty.string_of(body, margin = diagnostics_margin)
      val severity = VSCode_Rendering.message_severity.get(name)
      Protocol.Diagnostic(range, message, severity = severity)
    }).toList
  }


  /* tooltips */

  def tooltip_margin: Int = options.int("vscode_tooltip_margin")
  def timing_threshold: Double = options.real("vscode_timing_threshold")


  /* hyperlinks */

  def hyperlink_source_file(source_name: String, line1: Int, range: Symbol.Range)
    : Option[Line.Node_Range] =
  {
    for {
      name <- resources.source_file(source_name)
      if Path.is_wellformed(name)
    }
    yield {
      val path = Path.explode(name)
      val opt_text =
        try { Some(File.read(path)) } // FIXME content from resources/models
        catch { case ERROR(_) => None }
      Line.Node_Range(File.platform_path(path),
        opt_text match {
          case Some(text) if range.start > 0 =>
            val chunk = Symbol.Text_Chunk(text)
            val doc = Line.Document(text, resources.text_length)
            doc.range(chunk.decode(range))
          case _ =>
            Line.Range(Line.Position((line1 - 1) max 0))
        })
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

          case _ => None
        }) match { case Text.Info(_, links) :: _ => links.reverse case _ => Nil }
  }
}
