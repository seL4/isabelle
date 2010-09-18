/*  Title:      Tools/jEdit/src/jedit/isabelle_options.scala
    Author:     Johannes Hölzl, TU Munich

Editor pane for plugin options.
*/

package isabelle.jedit


import javax.swing.{JComboBox, JSpinner}

import org.gjt.sp.jedit.AbstractOptionPane


class Isabelle_Options extends AbstractOptionPane("isabelle")
{
  private val logic_selector = Isabelle.logic_selector(Isabelle.Property("logic"))
  private val relative_font_size = new JSpinner()
  private val tooltip_font_size = new JSpinner()
  private val tooltip_dismiss_delay = new JSpinner()

  override def _init()
  {
    addComponent(Isabelle.Property("logic.title"), logic_selector.peer)

    addComponent(Isabelle.Property("relative-font-size.title"), {
      relative_font_size.setValue(Isabelle.Int_Property("relative-font-size", 100))
      relative_font_size
    })

    addComponent(Isabelle.Property("tooltip-font-size.title"), {
      tooltip_font_size.setValue(Isabelle.Int_Property("tooltip-font-size", 10))
      tooltip_font_size
    })

    addComponent(Isabelle.Property("tooltip-dismiss-delay.title"), {
      tooltip_dismiss_delay.setValue(Isabelle.Int_Property("tooltip-dismiss-delay", 8000))
      tooltip_dismiss_delay
    })
  }

  override def _save()
  {
    Isabelle.Property("logic") =
      logic_selector.selection.item.name

    Isabelle.Int_Property("relative-font-size") =
      relative_font_size.getValue().asInstanceOf[Int]

    Isabelle.Int_Property("tooltip-font-size") =
      tooltip_font_size.getValue().asInstanceOf[Int]

    Isabelle.Int_Property("tooltip-dismiss-delay") =
      tooltip_dismiss_delay.getValue().asInstanceOf[Int]
  }
}
