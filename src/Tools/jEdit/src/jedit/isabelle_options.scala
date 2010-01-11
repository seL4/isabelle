/*
 * Editor pane for plugin options
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.jedit


import javax.swing.{JComboBox, JSpinner}

import org.gjt.sp.jedit.AbstractOptionPane


class Isabelle_Options extends AbstractOptionPane("isabelle")
{
  private val logic_name = new JComboBox()
  private val font_size = new JSpinner()

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

    addComponent(Isabelle.Property("font-size.title"), {
      font_size.setValue(Isabelle.Int_Property("font-size"))
      font_size
    })
  }

  override def _save()
  {
    val logic = logic_name.getSelectedItem.asInstanceOf[List_Item].name
    Isabelle.Property("logic") = logic

    val size = font_size.getValue().asInstanceOf[Int]
    Isabelle.Int_Property("font-size") = size
  }
}
