/*  Title:      Tools/jEdit/src/completion_popup.scala
    Author:     Makarius

Completion popup based on javax.swing.PopupFactory.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Font, Point, BorderLayout, Dimension}
import java.awt.event.{KeyEvent, MouseEvent, MouseAdapter, FocusAdapter, FocusEvent}
import javax.swing.{JPanel, JComponent, PopupFactory, SwingUtilities}

import scala.swing.{ListView, ScrollPane}
import scala.swing.event.MouseClicked

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.JEditTextArea


object Completion_Popup
{
  sealed case class Item(name: String, text: String)
  { override def toString: String = text }

  def input_text_area(text_area: JEditTextArea, evt: KeyEvent)
  {
    Swing_Thread.require()

    val buffer = text_area.getBuffer
    if (buffer.isEditable) {
      val view = text_area.getView
      val painter = text_area.getPainter
      val caret = text_area.getCaretPosition

      // FIXME
      def complete(item: Item) { }

      // FIXME
      val token_length = 0
      val items: List[Item] = Nil

      val popup_font =
        painter.getFont.deriveFont(
          (painter.getFont.getSize2D * PIDE.options.real("jedit_popup_font_scale")).toFloat
            max 10.0f)

      if (!items.isEmpty) {
        val location = text_area.offsetToXY(caret - token_length)
        if (location != null) {
          location.y = location.y + painter.getFontMetrics.getHeight
          SwingUtilities.convertPointToScreen(location, painter)
          new Completion_Popup(view.getRootPane, popup_font, location, items) {
            override def propagate(evt: KeyEvent) { JEdit_Lib.propagate_key(view, evt) }
            override def hidden() { text_area.requestFocus }
          }
        }
      }
    }
  }
}

class Completion_Popup private(
  root: JComponent,
  popup_font: Font,
  screen_point: Point,
  items: List[Completion_Popup.Item]) extends JPanel(new BorderLayout)
{
  completion =>

  Swing_Thread.require()
  require(!items.isEmpty)


  /* actions */

  def complete(item: Completion_Popup.Item) { }
  def propagate(evt: KeyEvent) { }
  def hidden() { }


  /* list view */

  private val list_view = new ListView(items)
  {
    font = popup_font
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
          propagate(e)
        },
      key_typed = propagate _
    )

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

    val x0 = root.getLocationOnScreen.x
    val y0 = root.getLocationOnScreen.y
    val w0 = root.getWidth
    val h0 = root.getHeight

    val (w, h) =
    {
      val geometry = JEdit_Lib.window_geometry(completion, completion)
      val bounds = Rendering.popup_bounds
      val w = geometry.width min (screen_bounds.width * bounds).toInt min w0
      val h = geometry.height min (screen_bounds.height * bounds).toInt min h0
      (w, h)
    }

    val (x, y) =
    {
      val x1 = x0 + w0 - w
      val y1 = y0 + h0 - h
      val x2 = screen_point.x min (screen_bounds.x + screen_bounds.width - w)
      val y2 = screen_point.y min (screen_bounds.y + screen_bounds.height - h)
      ((x2 min x1) max x0, (y2 min y1) max y0)
    }

    completion.setSize(new Dimension(w, h))
    completion.setPreferredSize(new Dimension(w, h))
    PopupFactory.getSharedInstance.getPopup(root, completion, x, y)
  }

  private def hide_popup()
  {
    popup.hide
    hidden()
  }

  popup.show
  list_view.requestFocus
}

