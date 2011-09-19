/*  Title:      Tools/jEdit/src/session_dockable.scala
    Author:     Makarius

Dockable window for prover session management.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{FlowPanel, Button, TextArea, Label, ListView, Alignment,
  ScrollPane, TabbedPane, Component, Swing}
import scala.swing.event.{ButtonClicked, SelectionChanged}

import java.lang.System
import java.awt.{BorderLayout, Graphics2D, Insets}
import javax.swing.{JList, DefaultListCellRenderer, BorderFactory}
import javax.swing.border.{BevelBorder, SoftBevelBorder}

import org.gjt.sp.jedit.{View, jEdit}


class Session_Dockable(view: View, position: String) extends Dockable(view: View, position: String)
{
  /* main tabs */

  private val readme = new HTML_Panel("SansSerif", 14)
  readme.render_document(Isabelle_System.try_read(List(Path.explode("$JEDIT_HOME/README.html"))))

  val status = new ListView(Nil: List[Document.Node.Name])
  status.peer.setLayoutOrientation(JList.VERTICAL_WRAP)
  status.selection.intervalMode = ListView.IntervalMode.Single

  private val syslog = new TextArea(Isabelle.session.syslog())

  private val tabs = new TabbedPane {
    pages += new TabbedPane.Page("README", Component.wrap(readme))
    pages += new TabbedPane.Page("Theory Status", new ScrollPane(status))
    pages += new TabbedPane.Page("System Log", new ScrollPane(syslog))

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

  private val cancel = new Button("Cancel") {
    reactions += { case ButtonClicked(_) => Isabelle.cancel_execution() }
  }
  cancel.tooltip = jEdit.getProperty("isabelle.cancel-execution.label")

  private val check = new Button("Check") {
    reactions += { case ButtonClicked(_) => Isabelle.check_buffer(view.getBuffer) }
  }
  check.tooltip = jEdit.getProperty("isabelle.check-buffer.label")

  private val logic = Isabelle.logic_selector(Isabelle.Property("logic"))
  logic.listenTo(logic.selection)
  logic.reactions += {
    case SelectionChanged(_) => Isabelle.Property("logic") = logic.selection.item.name
  }

  private val controls =
    new FlowPanel(FlowPanel.Alignment.Right)(check, cancel, session_phase, logic)
  add(controls.peer, BorderLayout.NORTH)


  /* component state -- owned by Swing thread */

  private var nodes_status: Map[Document.Node.Name, Isar_Document.Node_Status] = Map.empty

  private class Node_Renderer_Component extends Label
  {
    xAlignment = Alignment.Leading
    border = BorderFactory.createEmptyBorder(2, 2, 2, 2)

    var node_name = Document.Node.Name.empty
    override def paintComponent(gfx: Graphics2D)
    {
      nodes_status.get(node_name) match {
        case Some(st) if st.total > 0 =>
          val size = peer.getSize()
          val insets = border.getBorderInsets(this.peer)
          val w = size.width - insets.left - insets.right
          val h = size.height - insets.top - insets.bottom
          var end = size.width - insets.right
          for {
            (n, color) <- List(
              (st.unprocessed, Isabelle_Markup.unprocessed1_color),
              (st.running, Isabelle_Markup.running_color),
              (st.failed, Isabelle_Markup.error_color)) }
          {
            gfx.setColor(color)
            val v = (n * w / st.total) max (if (n > 0) 2 else 0)
            gfx.fillRect(end - v, insets.top, v, h)
            end -= v
          }
        case _ =>
      }
      super.paintComponent(gfx)
    }
  }

  private class Node_Renderer extends
    ListView.AbstractRenderer[Document.Node.Name, Node_Renderer_Component](
      new Node_Renderer_Component)
  {
    def configure(list: ListView[_], isSelected: Boolean, focused: Boolean,
      name: Document.Node.Name, index: Int)
    {
      component.opaque = false
      component.background = list.background
      component.foreground = list.foreground
      component.node_name = name
      component.text = name.theory
    }
  }
  status.renderer = new Node_Renderer

  private def handle_changed(changed_nodes: Set[Document.Node.Name])
  {
    Swing_Thread.now {
      // FIXME correlation to changed_nodes!?
      val snapshot = Isabelle.session.snapshot()

      var nodes_status1 = nodes_status
      for {
        name <- changed_nodes
        node <- snapshot.version.nodes.get(name)
        val status = Isar_Document.node_status(snapshot.state, snapshot.version, node)
      } nodes_status1 += (name -> status)

      if (nodes_status != nodes_status1) {
        nodes_status = nodes_status1
        status.listData =
          snapshot.version.topological_order.filter(
            (name: Document.Node.Name) => nodes_status.isDefinedAt(name))
      }
    }
  }


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

        case changed: Session.Commands_Changed => handle_changed(changed.nodes)

        case bad => System.err.println("Session_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init() {
    Isabelle.session.syslog_messages += main_actor
    Isabelle.session.phase_changed += main_actor
    Isabelle.session.commands_changed += main_actor
  }

  override def exit() {
    Isabelle.session.syslog_messages -= main_actor
    Isabelle.session.phase_changed -= main_actor
    Isabelle.session.commands_changed -= main_actor
  }
}
