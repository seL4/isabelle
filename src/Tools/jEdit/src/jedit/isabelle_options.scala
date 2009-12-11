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

  override def _init()
  {
    val logic = Isabelle.Property("logic")
    addComponent(Isabelle.Property("logic.title"), {
      for (name <- "default" :: Isabelle.system.find_logics()) {
        logic_name.addItem(name)
        if (name == logic)
          logic_name.setSelectedItem(name)
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
    val logic = logic_name.getSelectedItem.asInstanceOf[String]
    Isabelle.Property("logic") = logic

    val size = font_size.getValue().asInstanceOf[Int]
    Isabelle.Int_Property("font-size") = size
  }
}
