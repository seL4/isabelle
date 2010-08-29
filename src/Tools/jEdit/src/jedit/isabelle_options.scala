/*  Title:      Tools/jEdit/src/jedit/isabelle_options.scala
    Author:     Johannes Hölzl, TU Munich

Editor pane for plugin options.
*/

package isabelle.jedit


import javax.swing.{JComboBox, JSpinner}

import org.gjt.sp.jedit.AbstractOptionPane


class Isabelle_Options extends AbstractOptionPane("isabelle")
{
  private val logic_name = new JComboBox()
  private val relative_font_size = new JSpinner()
  private val tooltip_font_size = new JSpinner()
  private val tooltip_dismiss_delay = new JSpinner()

  private class List_Item(val name: String, val descr: String) {
    def this(name: String) = this(name, name)
    override def toString = descr
  }

  override def _init()
  {
    val logic = Isabelle.Property("logic")
    addComponent(Isabelle.Property("logic.title"), {
      logic_name.addItem(new List_Item("", "default (" + Isabelle.default_logic() + ")"))
      for (name <- Isabelle.system.find_logics()) {
        val item = new List_Item(name)
        logic_name.addItem(item)
        if (name == logic)
          logic_name.setSelectedItem(item)
      }
      logic_name
    })

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
      logic_name.getSelectedItem.asInstanceOf[List_Item].name

    Isabelle.Int_Property("relative-font-size") =
      relative_font_size.getValue().asInstanceOf[Int]

    Isabelle.Int_Property("tooltip-font-size") =
      tooltip_font_size.getValue().asInstanceOf[Int]

    Isabelle.Int_Property("tooltip-dismiss-delay") =
      tooltip_dismiss_delay.getValue().asInstanceOf[Int]
  }
}
