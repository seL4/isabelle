/*  Title:      Tools/jEdit/src/isabelle_options.scala
    Author:     Johannes Hölzl, TU Munich

Editor pane for plugin options.
*/

package isabelle.jedit


import isabelle._

import javax.swing.{JSpinner, JTextField}

import scala.swing.CheckBox

import org.gjt.sp.jedit.AbstractOptionPane


class Isabelle_Options extends AbstractOptionPane("isabelle")
{
  private val logic_selector = Isabelle.logic_selector(Isabelle.options.string("jedit_logic"))
  private val auto_start = new CheckBox()
  private val relative_font_size = new JSpinner()
  private val tooltip_font_size = new JSpinner()
  private val tooltip_margin = new JSpinner()
  private val tooltip_dismiss_delay = new JTextField()

  override def _init()
  {
    addComponent(Isabelle.options.title("jedit_logic"),
      logic_selector.peer.asInstanceOf[java.awt.Component])

    addComponent(Isabelle.options.title("jedit_auto_start"), auto_start.peer)
    auto_start.selected = Isabelle.options.bool("jedit_auto_start")

    addComponent(Isabelle.options.title("jedit_relative_font_size"), relative_font_size)
    relative_font_size.setValue(Isabelle.options.int("jedit_relative_font_size"))

    tooltip_font_size.setValue(Isabelle.options.int("jedit_tooltip_font_size"))
    addComponent(Isabelle.options.title("jedit_tooltip_font_size"), tooltip_font_size)

    tooltip_margin.setValue(Isabelle.options.int("jedit_tooltip_margin"))
    addComponent(Isabelle.options.title("jedit_tooltip_margin"), tooltip_margin)

    // FIXME InputVerifier for Double
    tooltip_dismiss_delay.setText(Isabelle.options.real("jedit_tooltip_dismiss_delay").toString)
    addComponent(Isabelle.options.title("jedit_tooltip_dismiss_delay"), tooltip_dismiss_delay)
  }

  override def _save()
  {
    Isabelle.options.string("jedit_logic") = logic_selector.selection.item.name

    Isabelle.options.bool("jedit_auto_start") = auto_start.selected

    Isabelle.options.int("jedit_relative_font_size") =
      relative_font_size.getValue().asInstanceOf[Int]

    Isabelle.options.int("jedit_tooltip_font_size") =
      tooltip_font_size.getValue().asInstanceOf[Int]

    Isabelle.options.int("jedit_tooltip_margin") =
      tooltip_margin.getValue().asInstanceOf[Int]

    Isabelle.options + ("jedit_tooltip_dismiss_delay", tooltip_dismiss_delay.getText)
  }
}
