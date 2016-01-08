/*  Title:      Tools/jEdit/src/symbols_dockable.scala
    Author:     Fabian Immler

Dockable window for Symbol Palette.
*/

package isabelle.jedit


import isabelle._

import scala.swing.event.{SelectionChanged, ValueChanged}
import scala.swing.{Action, Button, TabbedPane, TextField, BorderPanel, Label, ScrollPane}

import org.gjt.sp.jedit.View


class Symbols_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private class Symbol_Component(val symbol: String, is_control: Boolean) extends Button
  {
    private val font_size = Font_Info.main_size(PIDE.options.real("jedit_font_scale")).round

    font =
      Symbol.fonts.get(symbol) match {
        case None => GUI.font(size = font_size)
        case Some(font_family) => GUI.font(family = font_family, size = font_size)
      }
    action =
      Action(Symbol.decode(symbol)) {
        val text_area = view.getTextArea
        if (is_control && HTML.control.isDefinedAt(symbol))
          Token_Markup.edit_control_style(text_area, symbol)
        else
          text_area.setSelectedText(Isabelle_Encoding.maybe_decode(text_area.getBuffer, symbol))
        text_area.requestFocus
      }
    tooltip =
      GUI.tooltip_lines(
        cat_lines(symbol :: Symbol.abbrevs.get_list(symbol).map(a => "abbrev: " + a)))
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

  private val group_tabs: TabbedPane = new TabbedPane {
    pages ++=
      Symbol.groups.map({ case (group, symbols) =>
        new TabbedPane.Page(group,
          new ScrollPane(new Wrap_Panel {
            val control = group == "control"
            contents ++= symbols.map(new Symbol_Component(_, control))
            if (control) contents += new Reset_Component
          }), null)
      })

    val search_field = new TextField(10)
    val search_page =
      new TabbedPane.Page("search", new BorderPanel {
        val results_panel = new Wrap_Panel
        layout(search_field) = BorderPanel.Position.North
        layout(new ScrollPane(results_panel)) = BorderPanel.Position.Center
  
        val search_space =
          (for (sym <- Symbol.names.keysIterator) yield (sym, Word.lowercase(sym))).toList
        val search_delay =
          GUI_Thread.delay_last(PIDE.options.seconds("editor_input_delay")) {
            val search_words = Word.explode(Word.lowercase(search_field.text))
            val search_limit = PIDE.options.int("jedit_symbols_search_limit") max 0
            val results =
              for ((sym, s) <- search_space; if search_words.forall(s.contains(_))) yield sym

            results_panel.contents.clear
            for (sym <- results.take(search_limit))
              results_panel.contents += new Symbol_Component(sym, false)
            if (results.length > search_limit)
              results_panel.contents +=
                new Label("...") { tooltip = "(" + (results.length - search_limit) + " more)" }
            revalidate
            repaint
          }
          search_field.reactions += { case ValueChanged(_) => search_delay.invoke() }
      }, "Search Symbols")
    pages += search_page

    listenTo(selection)
    reactions += {
      case SelectionChanged(_) if selection.page == search_page => search_field.requestFocus
    }

    for (page <- pages)
      page.title = Word.implode(Word.explode('_', page.title).map(Word.perhaps_capitalize(_)))
  }
  set_content(group_tabs)
}
