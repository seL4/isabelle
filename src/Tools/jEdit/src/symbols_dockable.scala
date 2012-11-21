/*  Title:      Tools/jEdit/src/symbols_dockable.scala
    Author:     Fabian Immler

Dockable window for Symbol Palette.
*/

package isabelle.jedit


import isabelle._

import java.awt.Font
import org.gjt.sp.jedit.View

import scala.swing.event.ValueChanged
import scala.swing.{Action, Button, FlowPanel, TabbedPane, TextField, BorderPanel, Label}

class Symbols_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private val max_results = 50

  val searchspace =
    for ((group, symbols) <- Symbol.groups; sym <- symbols)
      yield (sym, (sym.toLowerCase + get_name(Symbol.decode(sym)).toLowerCase))

  def get_name(c: String): String =
    if (c.length >= 1) Character.getName(c.codePointAt(0)) else "??"

  private class Symbol_Component(val symbol: String) extends Button
  {
    val dec = Symbol.decode(symbol)
    font =
      new Font(Isabelle.font_family(),
        Font.PLAIN, Isabelle.font_size("jedit_font_scale").round)
    action = Action(dec) { view.getTextArea.setSelectedText(dec); view.getTextArea.requestFocus }
    tooltip = symbol + " - " + get_name(dec)
  }

  val group_tabs = new TabbedPane {
    pages ++= (for ((group, symbols) <- Symbol.groups) yield
      {
        new TabbedPane.Page(if (group == "") "Other" else group,
          new FlowPanel { contents ++= symbols map (new Symbol_Component(_)) },
          ("" /: (symbols take 10 map Symbol.decode))(_ + _ + " "))
      }).toList.sortWith(_.title.toUpperCase <= _.title.toUpperCase)
    pages += new TabbedPane.Page("Search", new BorderPanel {
      val search = new TextField(10)
      val results_panel = new FlowPanel
      add(search, BorderPanel.Position.North)
      add(results_panel, BorderPanel.Position.Center)
      listenTo(search)
      var last = search.text
      reactions += { case ValueChanged(`search`) =>
        if (search.text != last) {
          last = search.text
          results_panel.contents.clear
          val results =
            (searchspace filter (search.text.toLowerCase.split("\\s+") forall _._2.contains)
              take (max_results + 1)).toList
          for ((sym, _) <- results)
            results_panel.contents += new Symbol_Component(sym)
          if (results.length > max_results) results_panel.contents += new Label("...")
          results_panel.revalidate
          results_panel.repaint
        }
      }
    }, "Search Symbols")
  }
  set_content(group_tabs)
}
