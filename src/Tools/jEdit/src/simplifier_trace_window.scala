/*  Title:      Tools/jEdit/src/simplifier_trace_window.scala
    Author:     Lars Hupel

Trace window with tree-style view of the simplifier trace.
*/

package isabelle.jedit


import isabelle._

import scala.annotation.tailrec
import scala.collection.immutable.SortedMap
import scala.swing.{BorderPanel, Component, Dimension, Frame}
import scala.util.matching.Regex

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


private object Simplifier_Trace_Window {
  sealed trait Trace_Tree {
    // FIXME replace with immutable tree builder
    var children: SortedMap[Long, Either[Simplifier_Trace.Item.Data, Elem_Tree]] = SortedMap.empty
    val serial: Long
    val parent: Option[Trace_Tree]
    val markup: String
    def interesting: Boolean

    def tree_children: List[Elem_Tree] = children.values.toList.collect {
      case Right(tree) => tree
    }
  }

  final class Root_Tree(val serial: Long) extends Trace_Tree {
    val parent = None
    val interesting = true
    val markup = ""
  }

  final class Elem_Tree(data: Simplifier_Trace.Item.Data, val parent: Option[Trace_Tree])
  extends Trace_Tree {
    val serial = data.serial
    val markup = data.markup

    lazy val interesting: Boolean =
      data.markup == Markup.SIMP_TRACE_STEP ||
      data.markup == Markup.SIMP_TRACE_LOG ||
      tree_children.exists(_.interesting)

    private def body_contains(regex: Regex, body: XML.Body): Boolean =
      body.exists(tree => regex.findFirstIn(XML.content(tree)).isDefined)

    def format: Option[XML.Elem] = {
      def format_hint(data: Simplifier_Trace.Item.Data): XML.Tree =
        Pretty.block(Pretty.separate(XML.Text(data.text) :: data.content))

      lazy val bodies: XML.Body =
        children.values.toList.collect {
          case Left(data) => Some(format_hint(data))
          case Right(tree) if tree.interesting => tree.format
        }.flatten.map(item =>
          XML.Elem(Markup(Markup.ITEM, Nil), List(item))
        )

      val all = XML.Text(data.text) :: data.content ::: bodies
      val res = XML.Elem(Markup(Markup.TEXT_FOLD, Nil), List(Pretty.block(Pretty.separate(all))))

      if (bodies != Nil)
        Some(res)
      else
        None
    }
  }

  @tailrec
  def walk_trace(rest: List[Simplifier_Trace.Item.Data], lookup: Map[Long, Trace_Tree]): Unit =
    rest match {
      case Nil =>
        ()
      case head :: tail =>
        lookup.get(head.parent) match {
          case Some(parent) =>
            if (head.markup == Markup.SIMP_TRACE_HINT) {
              head.props match {
                case Simplifier_Trace.Success(x)
                  if x ||
                     parent.markup == Markup.SIMP_TRACE_LOG ||
                     parent.markup == Markup.SIMP_TRACE_STEP =>
                  parent.children += ((head.serial, Left(head)))
                case _ =>
                  // ignore
              }
              walk_trace(tail, lookup)
            }
            else if (head.markup == Markup.SIMP_TRACE_IGNORE) {
              parent.parent match {
                case None =>
                  Output.error_message(
                    "Simplifier_Trace_Window: malformed ignore message with parent " + head.parent)
                case Some(tree) =>
                  tree.children -= head.parent
                  walk_trace(tail, lookup)
              }
            }
            else {
              val entry = new Elem_Tree(head, Some(parent))
              parent.children += ((head.serial, Right(entry)))
              walk_trace(tail, lookup + (head.serial -> entry))
            }

          case None =>
            Output.error_message("Simplifier_Trace_Window: unknown parent " + head.parent)
        }
    }

}


class Simplifier_Trace_Window(
  view: View,
  snapshot: Document.Snapshot,
  trace: Simplifier_Trace.Trace
) extends Frame {
  GUI_Thread.require {}

  private val pretty_text_area = new Pretty_Text_Area(view)

  size = new Dimension(500, 500)
  contents = new BorderPanel {
    layout(Component.wrap(pretty_text_area)) = BorderPanel.Position.Center
  }

  private val tree = trace.entries.headOption match {
    case Some(first) =>
      val tree = new Simplifier_Trace_Window.Root_Tree(first.parent)
      Simplifier_Trace_Window.walk_trace(trace.entries, Map(first.parent -> tree))
      tree
    case None =>
      new Simplifier_Trace_Window.Root_Tree(0)
  }

  handle_update()
  open()
  handle_resize()

  def handle_update(): Unit = {
    val output = tree.tree_children.flatMap(_.format)
    pretty_text_area.update(snapshot, Command.Results.empty, output)
  }

  def handle_resize(): Unit = pretty_text_area.zoom()


  /* resize */

  private val delay_resize =
    Delay.first(PIDE.session.update_delay, gui = true) { handle_resize() }

  peer.addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })


  /* controls */

  private val controls = Wrap_Panel(pretty_text_area.search_zoom_components)

  peer.add(controls.peer, BorderLayout.NORTH)
}
