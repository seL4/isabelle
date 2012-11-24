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
  val searchspace =
    for ((group, symbols) <- Symbol.groups; sym <- symbols)
      yield (sym, sym.toLowerCase)

  private class Symbol_Component(val symbol: String) extends Button
  {
    private val decoded = Symbol.decode(symbol)
    font =
      new Font(Symbol.fonts.getOrElse(symbol, Isabelle.font_family()),
        Font.PLAIN, Isabelle.font_size("jedit_font_scale").round)
    action =
      Action(decoded) {
        val text_area = view.getTextArea
        if (Token_Markup.is_control_style(decoded))
          Token_Markup.edit_control_style(text_area, decoded)
        else text_area.setSelectedText(decoded)
        text_area.requestFocus
      }
    tooltip =
      JEdit_Lib.wrap_tooltip(
        symbol +
          (if (Symbol.abbrevs.isDefinedAt(symbol)) "\nabbrev: " + Symbol.abbrevs(symbol) else ""))
  }

  private class Reset_Component extends Button
  {
    action = Action("Reset") {
      val text_area = view.getTextArea
      Token_Markup.edit_control_style(text_area, "")
      text_area.requestFocus
    }
    tooltip = "Reset control symbols within text"
  }

  val group_tabs: TabbedPane = new TabbedPane {
    pages ++= (for ((group, symbols) <- Symbol.groups) yield
      {
        new TabbedPane.Page(group,
          new FlowPanel {
            contents ++= symbols.map(new Symbol_Component(_))
            if (group == "control") contents += new Reset_Component
          }, null)
      }).toList.sortWith(_.title <= _.title)
    pages += new TabbedPane.Page("search", new BorderPanel {
      val search = new TextField(10)
      val results_panel = new FlowPanel
      add(search, BorderPanel.Position.North)
      add(results_panel, BorderPanel.Position.Center)
      listenTo(search)
      val delay_search =
        Swing_Thread.delay_last(Time.seconds(Isabelle.options.real("editor_input_delay"))) {
          val max_results = Isabelle.options.int("jedit_symbols_search_limit") max 0
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
