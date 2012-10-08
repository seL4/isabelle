/*  Title:      Tools/jEdit/src/graphview_dockable.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Dockable window for graphview.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import javax.swing.{JPanel, JComponent}

import scala.actors.Actor._

import org.gjt.sp.jedit.View


class Graphview_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()


  /* component state -- owned by Swing thread */

  private val do_update = true  // FIXME

  private var current_snapshot = Document.State.init.snapshot()
  private var current_state = Command.empty.init_state
  private var current_graph: XML.Body = Nil


  /* GUI components */

  private val graphview = new JPanel

  // FIXME mutable GUI content
  private def set_graphview(snapshot: Document.Snapshot, graph: XML.Body)
  {
    graphview.removeAll()
    graphview.setLayout(new BorderLayout)
    val panel =
      new isabelle.graphview.Main_Panel(isabelle.graphview.Model.decode_graph(graph)) {
        override def make_tooltip(parent: JComponent, x: Int, y: Int, body: XML.Body): String =
        {
          val rendering = Isabelle_Rendering(snapshot, Isabelle.options.value)
          new Pretty_Tooltip(view, parent, rendering, x, y, body)
          null
        }
      }
    graphview.add(panel.peer, BorderLayout.CENTER)
    graphview.revalidate()
  }

  set_graphview(current_snapshot, current_graph)
  set_content(graphview)


  private def handle_update(follow: Boolean, restriction: Option[Set[Command]])
  {
    Swing_Thread.require()

    val (new_snapshot, new_state) =
      Document_View(view.getTextArea) match {
        case Some(doc_view) =>
          val snapshot = doc_view.model.snapshot()
          if (follow && !snapshot.is_outdated) {
            snapshot.node.command_at(doc_view.text_area.getCaretPosition).map(_._1) match {
              case Some(cmd) =>
                (snapshot, snapshot.state.command_state(snapshot.version, cmd))
              case None =>
                (Document.State.init.snapshot(), Command.empty.init_state)
            }
          }
          else (current_snapshot, current_state)
        case None => (current_snapshot, current_state)
      }

    val new_graph =
      if (!restriction.isDefined || restriction.get.contains(new_state.command)) {
        new_state.markup.cumulate[Option[XML.Body]](
          new_state.command.range, None, Some(Set(Isabelle_Markup.GRAPHVIEW)),
        {
          case (_, Text.Info(_, XML.Elem(Markup(Isabelle_Markup.GRAPHVIEW, _), graph))) =>
            Some(graph)
        }).filter(_.info.isDefined) match {
          case Text.Info(_, Some(graph)) #:: _ => graph
          case _ => Nil
        }
      }
      else current_graph

    if (new_graph != current_graph) set_graphview(new_snapshot, new_graph)

    current_snapshot = new_snapshot
    current_state = new_state
    current_graph = new_graph
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case Session.Global_Options =>  // FIXME

        case changed: Session.Commands_Changed =>
          Swing_Thread.later { handle_update(do_update, Some(changed.commands)) }

        case Session.Caret_Focus =>
          Swing_Thread.later { handle_update(do_update, None) }

        case bad =>
          java.lang.System.err.println("Graphview_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Swing_Thread.require()

    Isabelle.session.global_options += main_actor
    Isabelle.session.commands_changed += main_actor
    Isabelle.session.caret_focus += main_actor
    handle_update(do_update, None)
  }

  override def exit()
  {
    Swing_Thread.require()

    Isabelle.session.global_options -= main_actor
    Isabelle.session.commands_changed -= main_actor
    Isabelle.session.caret_focus -= main_actor
  }
}
