/*  Title:      Tools/jEdit/src/completion_popup.scala
    Author:     Makarius

Completion popup based on javax.swing.PopupFactory.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Point, BorderLayout, Dimension}
import java.awt.event.{KeyEvent, MouseEvent, MouseAdapter, FocusAdapter, FocusEvent}
import javax.swing.{JPanel, JComponent, PopupFactory}

import scala.swing.{ListView, ScrollPane}
import scala.swing.event.MouseClicked

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.KeyEventWorkaround


object Completion_Popup
{
  sealed case class Item(name: String, text: String)
  { override def toString: String = text }

  def apply(
    opt_view: Option[View],
    parent: JComponent,
    screen_point: Point,
    items: List[Item],
    complete: Item => Unit): Completion_Popup =
  {
    Swing_Thread.require()

    require(!items.isEmpty)

    val completion = new Completion_Popup(opt_view, parent, screen_point, items, complete)
    completion.show_popup()
    completion
  }
}


class Completion_Popup private(
  opt_view: Option[View],
  parent: JComponent,
  screen_point: Point,
  items: List[Completion_Popup.Item],
  complete: Completion_Popup.Item => Unit) extends JPanel(new BorderLayout)
{
  completion =>

  Swing_Thread.require()


  /* list view */

  private val list_view = new ListView(items)
  {
    font = parent.getFont
  }
  list_view.selection.intervalMode = ListView.IntervalMode.Single
  list_view.peer.setFocusTraversalKeysEnabled(false)
  list_view.peer.setVisibleRowCount(items.length min 8)
  list_view.peer.setSelectedIndex(0)

  private def complete_selected(): Boolean =
  {
    list_view.selection.items.toList match {
      case item :: _ => complete(item); true
      case _ => false
    }
  }

  private def move_items(n: Int)
  {
    val i = list_view.peer.getSelectedIndex
    val j = ((i + n) min (items.length - 1)) max 0
    if (i != j) {
      list_view.peer.setSelectedIndex(j)
      list_view.peer.ensureIndexIsVisible(j)
    }
  }

  private def move_pages(n: Int)
  {
    val page_size = list_view.peer.getVisibleRowCount - 1
    move_items(page_size * n)
  }


  /* event handling */

  private val key_listener =
    JEdit_Lib.key_listener(
      workaround = false,
      key_pressed = (e: KeyEvent) =>
        {
          if (!e.isConsumed) {
            e.getKeyCode match {
              case KeyEvent.VK_TAB =>
                if (complete_selected()) e.consume
                hide_popup()
              case KeyEvent.VK_ESCAPE =>
                hide_popup()
                e.consume
              case KeyEvent.VK_UP => move_items(-1); e.consume
              case KeyEvent.VK_DOWN => move_items(1); e.consume
              case KeyEvent.VK_PAGE_UP => move_pages(-1); e.consume
              case KeyEvent.VK_PAGE_DOWN => move_pages(1); e.consume
              case _ =>
                if (e.isActionKey || e.isAltDown || e.isMetaDown || e.isControlDown)
                  hide_popup()
            }
          }
          if (!e.isConsumed) pass_to_view(e)
        },
      key_typed = (e: KeyEvent) =>
        {
          if (!e.isConsumed) pass_to_view(e)
        }
    )

  private def pass_to_view(e: KeyEvent)
  {
    opt_view match {
      case Some(view) if view.getKeyEventInterceptor == key_listener =>
        try {
          view.setKeyEventInterceptor(null)
          view.getInputHandler().processKeyEvent(e, View.ACTION_BAR, false)
        }
        finally { view.setKeyEventInterceptor(key_listener) }
      case _ =>
    }
  }

  list_view.peer.addKeyListener(key_listener)

  list_view.peer.addMouseListener(new MouseAdapter {
    override def mouseClicked(e: MouseEvent) {
      if (complete_selected()) e.consume
      hide_popup()
    }
  })

  list_view.peer.addFocusListener(new FocusAdapter {
    override def focusLost(e: FocusEvent) { hide_popup() }
  })


  /* main content */

  override def getFocusTraversalKeysEnabled = false

  completion.add((new ScrollPane(list_view)).peer.asInstanceOf[JComponent])


  /* popup */

  private val popup =
  {
    val screen_bounds = JEdit_Lib.screen_bounds(screen_point)

    val geometry = JEdit_Lib.window_geometry(completion, completion)

    val w = geometry.width min (screen_bounds.width / 2)
    val h = geometry.height min (screen_bounds.height / 2)

    completion.setSize(new Dimension(w, h))
    completion.setPreferredSize(new Dimension(w, h))

    val x = screen_point.x min (screen_bounds.x + screen_bounds.width - w)
    val y = screen_point.y min (screen_bounds.y + screen_bounds.height - h)
    PopupFactory.getSharedInstance.getPopup(parent, completion, x, y)
  }

  def show_popup()
  {
    opt_view.foreach(view => view.setKeyEventInterceptor(key_listener))
    popup.show
    list_view.requestFocus
  }

  def hide_popup()
  {
    opt_view match {
      case Some(view) if view.getKeyEventInterceptor == key_listener =>
        view.setKeyEventInterceptor(null)
      case _ =>
    }
    popup.hide
    parent.requestFocus
  }
}

