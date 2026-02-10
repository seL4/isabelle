/*  Title:      Tools/jEdit/src/selection_popup.scala
    Author:     Makarius

Generic selection popup.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Font, Point, BorderLayout, Dimension}
import java.awt.event.{KeyEvent, KeyListener, MouseEvent, MouseAdapter, FocusAdapter, FocusEvent}
import javax.swing.{JPanel, JComponent, JLayeredPane}
import javax.swing.border.LineBorder

import scala.swing.{ListView, ScrollPane}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.JEditTextArea


object Selection_Popup {
  /* items */

  trait Item { def select(): Unit }

  class Hyperlink(view: View, link: PIDE.editor.Hyperlink)
  extends Item {
    override def select(): Unit = link.follow(view)
    override def toString: String = link.toString
  }


  /* specific popup */

  abstract class Text_Area(
    text_area: JEditTextArea,
    range: Text.Range,
    location: Point,
    items: List[Selection_Popup.Item],
    select_enter: Boolean = false,
    select_tab: Boolean = false
  ) extends Selection_Popup(
    Some(range),
    text_area.getView.getLayeredPane,
    location,
    text_area.getPainter.getFont.deriveFont(
      Font_Info.main_size(scale = PIDE.options.real("jedit_popup_font_scale"))),
    items,
    select_enter = select_enter,
    select_tab = select_tab
  ) {
    def input(evt: KeyEvent): Unit

    override def propagate(evt: KeyEvent): Unit = {
      val view = text_area.getView
      if (view.getKeyEventInterceptor == null) {
        JEdit_Lib.propagate_key(view, evt)
      }
      else if (view.getKeyEventInterceptor == inner_key_listener) {
        try {
          view.setKeyEventInterceptor(null)
          JEdit_Lib.propagate_key(view, evt)
        }
        finally {
          if (isDisplayable) view.setKeyEventInterceptor(inner_key_listener)
        }
      }
      if (evt.getID == KeyEvent.KEY_TYPED) input(evt)
    }

    override def shutdown(refocus: Boolean): Unit = {
      val view = text_area.getView
      if (view.getKeyEventInterceptor == inner_key_listener) {
        view.setKeyEventInterceptor(null)
      }
      if (refocus) text_area.requestFocus()
      JEdit_Lib.invalidate_range(text_area, range)
    }
  }
}


/* generic popup */

class Selection_Popup(
  opt_range: Option[Text.Range],
  layered: JLayeredPane,
  location: Point,
  font: Font,
  items: List[Selection_Popup.Item],
  select_enter: Boolean = false,
  select_tab: Boolean = false
) extends JPanel(new BorderLayout) {
  panel =>

  GUI_Thread.require {}

  require(items.nonEmpty, "no selection items")
  val multi: Boolean = items.length > 1


  /* actions */

  def propagate(evt: KeyEvent): Unit = {}
  def shutdown(refocus: Boolean): Unit = {}


  /* list view */

  private val list_view = new ListView(items)
  list_view.font = font
  list_view.selection.intervalMode = ListView.IntervalMode.Single
  list_view.peer.setFocusTraversalKeysEnabled(false)
  list_view.peer.setVisibleRowCount(items.length min 8)
  list_view.peer.setSelectedIndex(0)

  for (cond <-
    List(JComponent.WHEN_FOCUSED,
      JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT,
      JComponent.WHEN_IN_FOCUSED_WINDOW)) list_view.peer.setInputMap(cond, null)

  private def select_current(): Boolean = {
    list_view.selection.items.toList match {
      case item :: _ => item.select(); true
      case _ => false
    }
  }

  private def move_items(n: Int): Unit = {
    val i = list_view.peer.getSelectedIndex
    val j = ((i + n) min (items.length - 1)) max 0
    if (i != j) {
      list_view.peer.setSelectedIndex(j)
      list_view.peer.ensureIndexIsVisible(j)
    }
  }

  private def move_pages(n: Int): Unit = {
    val page_size = list_view.peer.getVisibleRowCount - 1
    move_items(page_size * n)
  }


  /* event handling */

  val inner_key_listener: KeyListener =
    JEdit_Lib.key_listener(
      key_pressed = { (e: KeyEvent) =>
        if (!e.isConsumed && GUI.no_modifier(e)) {
          e.getKeyCode match {
            case KeyEvent.VK_ENTER if select_enter =>
              if (select_current()) e.consume()
              hide_popup()
            case KeyEvent.VK_TAB if select_tab =>
              if (select_current()) e.consume()
              hide_popup()
            case KeyEvent.VK_ESCAPE =>
              hide_popup()
              e.consume()
            case KeyEvent.VK_UP | KeyEvent.VK_KP_UP if multi =>
              move_items(-1)
              e.consume()
            case KeyEvent.VK_DOWN | KeyEvent.VK_KP_DOWN if multi =>
              move_items(1)
              e.consume()
            case KeyEvent.VK_PAGE_UP if multi =>
              move_pages(-1)
              e.consume()
            case KeyEvent.VK_PAGE_DOWN if multi =>
              move_pages(1)
              e.consume()
            case _ =>
              if (e.isActionKey || e.isAltDown || e.isMetaDown || e.isControlDown)
                hide_popup()
          }
        }
        propagate(e)
      },
      key_typed = propagate
    )

  list_view.peer.addKeyListener(inner_key_listener)

  list_view.peer.addMouseListener(new MouseAdapter {
    override def mousePressed(e: MouseEvent): Unit = {
      if (!e.isConsumed() && e.getClickCount == 1) {
        if (select_current()) e.consume()
        hide_popup()
      }
    }
  })

  list_view.peer.addFocusListener(new FocusAdapter {
    override def focusLost(e: FocusEvent): Unit = hide_popup()
  })


  /* main content */

  override def getFocusTraversalKeysEnabled = false
  panel.setBorder(new LineBorder(GUI.default_foreground_color()))

  private val scroll_pane = new ScrollPane(list_view)
  scroll_pane.horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
  scroll_pane.verticalScrollBarPolicy = ScrollPane.BarPolicy.Always
  panel.add(scroll_pane.peer.asInstanceOf[JComponent])


  /* popup */

  def active_range: Option[Text.Range] =
    if (isDisplayable) opt_range else None

  private val popup =
    new Popup(layered, panel, location) {
      override val size: Dimension = {
        val geometry = JEdit_Lib.window_geometry(component, component)
        val bounds = JEdit_Rendering.popup_bounds
        val w = geometry.width min (screen.bounds.width * bounds).toInt min root.getWidth
        val h = geometry.height min (screen.bounds.height * bounds).toInt min root.getHeight
        new Dimension(w, h)
      }
    }

  def show_popup(focus: Boolean): Unit = {
    popup.show
    if (focus) list_view.requestFocus()
  }

  def hide_popup(): Unit = {
    shutdown(list_view.peer.isFocusOwner)
    popup.hide
  }
}
