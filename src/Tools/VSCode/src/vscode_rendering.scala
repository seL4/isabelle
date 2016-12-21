/*  Title:      Tools/VSCode/src/vscode_rendering.scala
    Author:     Makarius

Isabelle/VSCode-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle.vscode


import isabelle._

object VSCode_Rendering
{
  private val hyperlink_elements =
    Markup.Elements(Markup.ENTITY, Markup.PATH, Markup.POSITION, Markup.URL)
}

class VSCode_Rendering(
    val model: Document_Model,
    snapshot: Document.Snapshot,
    options: Options,
    resources: Resources)
  extends Rendering(snapshot, options, resources)
{
  /* tooltips */

  def tooltip_margin: Int = options.int("vscode_tooltip_margin")
  def timing_threshold: Double = options.real("vscode_timing_threshold")


  /* hyperlinks */

  def hyperlinks(range: Text.Range): List[Line.Range_Node] =
  {
    snapshot.cumulate[List[Line.Range_Node]](
      range, Nil, VSCode_Rendering.hyperlink_elements, _ =>
        {
          case (links, Text.Info(_, XML.Elem(Markup.Path(name), _))) =>
            Some(Line.Range_Node(Line.Range.zero, resolve_file_url(name)) :: links)

/* FIXME
          case (links, Text.Info(_, XML.Elem(Markup.Url(name), _))) =>
            Some(PIDE.editor.hyperlink_url(name) :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.ENTITY, props), _)))
          if !props.exists(
            { case (Markup.KIND, Markup.ML_OPEN) => true
              case (Markup.KIND, Markup.ML_STRUCTURE) => true
              case _ => false }) =>
            val opt_link = PIDE.editor.hyperlink_def_position(true, snapshot, props)
            opt_link.map(_ :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.POSITION, props), _))) =>
            val opt_link = PIDE.editor.hyperlink_position(true, snapshot, props)
            opt_link.map(_ :: links)
*/

          case _ => None
        }) match { case Text.Info(_, links) :: _ => links.reverse case _ => Nil }
  }
}
