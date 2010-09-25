/*  Title:      Tools/jEdit/src/jedit/session_dockable.scala
    Author:     Makarius

Dockable window for prover session management.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{FlowPanel, Button, TextArea, Label, ScrollPane, TabbedPane,
  Component, Swing, CheckBox}
import scala.swing.event.{ButtonClicked, SelectionChanged}

import java.awt.BorderLayout
import javax.swing.border.{BevelBorder, SoftBevelBorder}

import org.gjt.sp.jedit.View


class Session_Dockable(view: View, position: String) extends Dockable(view: View, position: String)
{
  /* main tabs */

  private val readme = new HTML_Panel(Isabelle.system, "SansSerif", 12)
  readme.render_document(Isabelle.system.try_read(List("$JEDIT_HOME/README.html")))

  private val syslog = new TextArea(Isabelle.session.syslog())
  syslog.editable = false

  private val tabs = new TabbedPane {
    pages += new TabbedPane.Page("README", Component.wrap(readme))
    pages += new TabbedPane.Page("System log", new ScrollPane(syslog))

    selection.index =
    {
      val index = Isabelle.Int_Property("session-panel.selection", 0)
      if (index >= pages.length) 0 else index
    }
    listenTo(selection)
    reactions += {
      case SelectionChanged(_) =>
        Isabelle.Int_Property("session-panel.selection") = selection.index
    }
  }

  set_content(tabs)


  /* controls */

  val session_phase = new Label(Isabelle.session.phase.toString)
  session_phase.border = new SoftBevelBorder(BevelBorder.LOWERED)
  session_phase.tooltip = "Prover status"

  private val auto_start = new CheckBox("Auto start") {
    selected = Isabelle.Boolean_Property("auto-start")
    reactions += {
      case ButtonClicked(_) =>
        Isabelle.Boolean_Property("auto-start") = selected
        if (selected) Isabelle.start_session()
    }
  }

  private val logic = Isabelle.logic_selector(Isabelle.Property("logic"))
  logic.listenTo(logic.selection)
  logic.reactions += {
    case SelectionChanged(_) => Isabelle.Property("logic") = logic.selection.item.name
  }

  private val interrupt = new Button("Interrupt") {
    reactions += { case ButtonClicked(_) => Isabelle.session.interrupt }
  }
  interrupt.tooltip = "Broadcast interrupt to all prover tasks"

  private val controls =
    new FlowPanel(FlowPanel.Alignment.Right)(session_phase, auto_start, logic, interrupt)
  add(controls.peer, BorderLayout.NORTH)


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case result: Isabelle_Process.Result =>
          if (result.is_syslog)
            Swing_Thread.now {
              val text = Isabelle.session.syslog()
              if (text != syslog.text) {
                syslog.text = text
              }
            }

        case phase: Session.Phase =>
          Swing_Thread.now { session_phase.text = " " + phase.toString + " " }

        case bad => System.err.println("Session_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init() {
    Isabelle.session.raw_messages += main_actor
    Isabelle.session.phase_changed += main_actor
  }

  override def exit() {
    Isabelle.session.raw_messages -= main_actor
    Isabelle.session.phase_changed -= main_actor
  }
}
