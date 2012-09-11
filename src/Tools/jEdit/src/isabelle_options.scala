/*  Title:      Tools/jEdit/src/isabelle_options.scala
    Author:     Makarius

Editor pane for plugin options.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.{jEdit, AbstractOptionPane}


class Isabelle_Options extends AbstractOptionPane("isabelle")
{
  // FIXME avoid hard-wired stuff
  private val relevant_options =
    Set("jedit_logic", "jedit_auto_start", "jedit_font_scale", "jedit_tooltip_font_size",
      "jedit_tooltip_margin", "jedit_tooltip_dismiss_delay", "editor_load_delay",
      "editor_input_delay", "editor_output_delay", "editor_update_delay")

  relevant_options.foreach(Isabelle.options.value.check_name _)

  private val predefined =
    Isabelle_Logic.logic_selector(false) ::
      (for {
        (name, opt) <- Isabelle.options.value.options.toList
        // FIXME avoid hard-wired stuff
        if (name.startsWith("color_") && opt.section == "Rendering of Document Content")
      } yield Isabelle.options.make_color_component(opt))

  private val components = Isabelle.options.make_components(predefined, relevant_options)

  override def _init()
  {
    val dummy_property = "options.isabelle.dummy"

    for ((s, cs) <- components) {
      if (s != "") {
        jEdit.setProperty(dummy_property, s)
        addSeparator(dummy_property)
        jEdit.setProperty(dummy_property, null)
      }
      cs.foreach(c => addComponent(c.title, c.peer))
    }
  }

  override def _save()
  {
    for ((_, cs) <- components) cs.foreach(_.save())
  }
}
