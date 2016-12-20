/*  Title:      Tools/VSCode/src/vscode_rendering.scala
    Author:     Makarius

Isabelle/VSCode-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle.vscode


import isabelle._


class VSCode_Rendering(snapshot: Document.Snapshot, options: Options, resources: Resources)
  extends Rendering(snapshot, options, resources)
{
  /* tooltips */

  def tooltip_margin: Int = options.int("vscode_tooltip_margin")
  def timing_threshold: Double = options.real("vscode_timing_threshold")
}
