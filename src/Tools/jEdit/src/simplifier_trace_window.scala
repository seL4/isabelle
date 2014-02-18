/*  Title:      Tools/jEdit/src/simplifier_trace_window.scala
    Author:     Lars Hupel

Trace window with tree-style view of the simplifier trace.
*/

package isabelle.jedit


import isabelle._

import scala.annotation.tailrec
import scala.collection.immutable.SortedMap
import scala.swing.{BorderPanel, CheckBox, Component, Dimension, Frame, Label, TextField}
import scala.swing.event.{Key, KeyPressed}
import scala.util.matching.Regex

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import javax.swing.SwingUtilities

import org.gjt.sp.jedit.View


private object Simplifier_Trace_Window
{
  sealed trait Trace_Tree
  {
    var children: SortedMap[Long, Elem_Tree] = SortedMap.empty
    val serial: Long
    val parent: Option[Trace_Tree]
    var hints: List[Simplifier_Trace.Item.Data]
    def set_interesting(): Unit
  }

  final class Root_Tree(val serial: Long) extends Trace_Tree
  {
    val parent = None
    val hints = Nil
    def hints_=(xs: List[Simplifier_Trace.Item.Data]) =
      throw new IllegalStateException("Root_Tree.hints")
    def set_interesting() = ()

    def format(regex: Option[Regex]): XML.Body =
      Pretty.separate(children.values.map(_.format(regex)._2)(collection.breakOut))
  }

  final class Elem_Tree(data: Simplifier_Trace.Item.Data, val parent: Option[Trace_Tree])
    extends Trace_Tree
  {
    val serial = data.serial
    var hints = List.empty[Simplifier_Trace.Item.Data]
    var interesting: Boolean = false

    def set_interesting(): Unit =
      if (!interesting)
      {
        interesting = true
        parent match {
          case Some(p) =>
            p.set_interesting()
          case None =>
        }
      }

    def format(regex: Option[Regex]): (Boolean, XML.Tree) =
    {
      def format_child(child: Elem_Tree): Option[XML.Tree] = child.format(regex) match {
        case (false, _) =>
          None
        case (true, res) =>
          Some(XML.Elem(Markup(Markup.ITEM, Nil), List(res)))
      }

      def format_hint(data: Simplifier_Trace.Item.Data): XML.Tree =
        Pretty.block(Pretty.separate(
          XML.Text(data.text) ::
          data.content
        ))

      def body_contains(regex: Regex, body: XML.Body): Boolean =
        body.exists(tree => regex.findFirstIn(XML.content(tree)).isDefined)

      val children_bodies: XML.Body =
        children.values.filter(_.interesting).flatMap(format_child).toList

      lazy val hint_bodies: XML.Body =
        hints.reverse.map(format_hint)

      val eligible = regex match {
        case None =>
          true
        case Some(r) =>
          body_contains(r, data.content) || hints.exists(h => body_contains(r, h.content))
      }

      val all =
        if (eligible)
          XML.Text(data.text) :: data.content ::: children_bodies ::: hint_bodies
        else
          XML.Text(data.text) :: children_bodies

      val res = XML.Elem(Markup(Markup.TEXT_FOLD, Nil), List(Pretty.block(Pretty.separate(all))))

      (eligible || children_bodies != Nil, res)
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
            if (head.markup == Markup.SIMP_TRACE_HINT)
            {
              parent.hints ::= head
              walk_trace(tail, lookup)
            }
            else if (head.markup == Markup.SIMP_TRACE_IGNORE)
            {
              parent.parent match {
                case None =>
                  System.err.println("Simplifier_Trace_Window: malformed ignore message with parent " + head.parent)
                case Some(tree) =>
                  tree.children -= head.parent
                  walk_trace(tail, lookup) // FIXME discard from lookup
              }
            }
            else
            {
              val entry = new Elem_Tree(head, Some(parent))
              parent.children += ((head.serial, entry))
              if (head.markup == Markup.SIMP_TRACE_STEP || head.markup == Markup.SIMP_TRACE_LOG)
                entry.set_interesting()
              walk_trace(tail, lookup + (head.serial -> entry))
            }

          case None =>
            System.err.println("Simplifier_Trace_Window: unknown parent " + head.parent)
        }
    }

}

class Simplifier_Trace_Window(view: View, snapshot: Document.Snapshot, trace: Simplifier_Trace.Trace) extends Frame
{

  import Simplifier_Trace_Window._

  Swing_Thread.require()

  val area = new Pretty_Text_Area(view)

  size = new Dimension(500, 500)
  contents = new BorderPanel {
    layout(Component.wrap(area)) = BorderPanel.Position.Center
  }

  private val tree = trace.entries.headOption match {
    case Some(first) =>
      val tree = new Root_Tree(first.parent)
      walk_trace(trace.entries, Map(first.parent -> tree))
      tree
    case None =>
      new Root_Tree(0)
  }

  do_update(None)
  open()
  do_paint()

  def do_update(regex: Option[Regex])
  {
    val xml = tree.format(regex)
    area.update(snapshot, Command.Results.empty, xml)
  }

  def do_paint()
  {
    Swing_Thread.later {
      area.resize(Rendering.font_family(), Rendering.font_size("jedit_font_scale").round)
    }
  }

  def handle_resize()
  {
    do_paint()
  }


  /* resize */

  private val delay_resize =
    Swing_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  peer.addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
    override def componentShown(e: ComponentEvent)   { delay_resize.invoke() }
  })


  /* controls */

  val use_regex = new CheckBox("Regex")

  private val controls = new Wrap_Panel(Wrap_Panel.Alignment.Right)(
    new Label {
      text = "Search"
    },
    new TextField(30) {
      listenTo(keys)
      reactions += {
        case KeyPressed(_, Key.Enter, 0, _) =>
          val input = text.trim
          val regex =
            if (input.isEmpty)
              None
            else if (use_regex.selected)
              Some(input.r)
            else
              Some(java.util.regex.Pattern.quote(input).r)
          do_update(regex)
          do_paint()
      }
    },
    use_regex
  )

  peer.add(controls.peer, BorderLayout.NORTH)
}
