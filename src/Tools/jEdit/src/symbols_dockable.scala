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
      yield (sym, sym.toLowerCase)

  private class Symbol_Component(val symbol: String) extends Button
  {
    val dec = Symbol.decode(symbol)
    font =
      new Font(Symbol.fonts.getOrElse(symbol, Isabelle.font_family()),
        Font.PLAIN, Isabelle.font_size("jedit_font_scale").round)
    action = Action(dec) { view.getTextArea.setSelectedText(dec); view.getTextArea.requestFocus }
    tooltip =
      JEdit_Lib.wrap_tooltip(
        symbol +
          (if (Symbol.abbrevs.isDefinedAt(symbol)) "\nabbrev: " + Symbol.abbrevs(symbol) else ""))
  }

  val group_tabs: TabbedPane = new TabbedPane {
    pages ++= (for ((group, symbols) <- Symbol.groups) yield
      {
        new TabbedPane.Page(group,
          new FlowPanel { contents ++= symbols map (new Symbol_Component(_)) })
      }).toList.sortWith(_.title <= _.title)
    pages += new TabbedPane.Page("search", new BorderPanel {
      val search = new TextField(10)
      val results_panel = new FlowPanel
      add(search, BorderPanel.Position.North)
      add(results_panel, BorderPanel.Position.Center)
      listenTo(search)
      val delay_search =
        Swing_Thread.delay_last(Time.seconds(Isabelle.options.real("editor_input_delay"))) {
          results_panel.contents.clear
          val results =
            (searchspace filter (search.text.toLowerCase.split("\\s+") forall _._2.contains)
              take (max_results + 1)).toList
          for ((sym, _) <- results)
            results_panel.contents += new Symbol_Component(sym)
          if (results.length > max_results) results_panel.contents += new Label("...")
          revalidate
          repaint
        }
      reactions += { case ValueChanged(`search`) => delay_search.invoke() }
    }, "Search Symbols")
    pages map (p => p.title = (space_explode('_', p.title) map Library.capitalize).mkString(" ") )
  }
  set_content(group_tabs)
}
