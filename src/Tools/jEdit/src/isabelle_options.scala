/*  Title:      Tools/jEdit/src/isabelle_options.scala
    Author:     Makarius

Editor pane for plugin options.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.AbstractOptionPane


class Isabelle_Options extends AbstractOptionPane("isabelle")
{
  // FIXME avoid hard-wired stuff
  private val relevant_options =
    Set("jedit_logic", "jedit_auto_start", "jedit_relative_font_size", "jedit_tooltip_font_size",
      "jedit_tooltip_margin", "jedit_tooltip_dismiss_delay", "jedit_load_delay")

  private val components =
    Isabelle.options.make_components(List(Isabelle_Logic.logic_selector(false)), relevant_options)

  override def _init()
  {
    for ((s, cs) <- components) {
      if (s == "") addSeparator() else addSeparator(s)
      cs.foreach(c => addComponent(c.title, c.peer))
    }
  }

  override def _save()
  {
    for ((_, cs) <- components) cs.foreach(_.save())
  }
}
