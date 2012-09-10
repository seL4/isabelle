/*  Title:      Tools/jEdit/src/isabelle_options.scala
    Author:     Makarius

Editor pane for plugin options.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.AbstractOptionPane


class Isabelle_Options extends AbstractOptionPane("isabelle")
{
  private val components = List(
    Isabelle_Logic.logic_selector(false),
    Isabelle.options.make_component("jedit_auto_start"),
    Isabelle.options.make_component("jedit_relative_font_size"),
    Isabelle.options.make_component("jedit_tooltip_font_size"),
    Isabelle.options.make_component("jedit_tooltip_margin"),
    Isabelle.options.make_component("jedit_tooltip_dismiss_delay"))

  override def _init()
  {
    for (c <- components) addComponent(c.title, c.peer)
  }

  override def _save()
  {
    for (c <- components) c.save()
  }
}
