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
    Markup.Elements(Markup.ENTITY, Markup.PATH, Markup.POSITION)
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

  def hyperlinks(range: Text.Range): List[Line.Node_Range] =
  {
    snapshot.cumulate[List[Line.Node_Range]](
      range, Nil, VSCode_Rendering.hyperlink_elements, _ =>
        {
          case (links, Text.Info(_, XML.Elem(Markup.Path(name), _))) =>
            val file = resources.append_file_url(snapshot.node_name.master_dir, name)
            Some(Line.Node_Range(file) :: links)

          // FIXME more cases

          case _ => None
        }) match { case Text.Info(_, links) :: _ => links.reverse case _ => Nil }
  }
}
