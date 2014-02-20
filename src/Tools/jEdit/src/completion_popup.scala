/*  Title:      Tools/jEdit/src/completion_popup.scala
    Author:     Makarius

Completion popup.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Font, Point, BorderLayout, Dimension}
import java.awt.event.{KeyEvent, MouseEvent, MouseAdapter, FocusAdapter, FocusEvent}
import javax.swing.{JPanel, JComponent, JLayeredPane, SwingUtilities}
import javax.swing.border.LineBorder
import javax.swing.text.DefaultCaret

import scala.swing.{ListView, ScrollPane}
import scala.swing.event.MouseClicked

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.JEditTextArea
import org.gjt.sp.jedit.gui.{HistoryTextField, KeyEventWorkaround}


object Completion_Popup
{
  /** jEdit text area **/

  object Text_Area
  {
    private val key = new Object

    def apply(text_area: JEditTextArea): Option[Completion_Popup.Text_Area] =
      text_area.getClientProperty(key) match {
        case text_area_completion: Completion_Popup.Text_Area => Some(text_area_completion)
        case _ => None
      }

    def exit(text_area: JEditTextArea)
    {
      Swing_Thread.require()
      apply(text_area) match {
        case None =>
        case Some(text_area_completion) =>
          text_area_completion.deactivate()
          text_area.putClientProperty(key, null)
      }
    }

    def init(text_area: JEditTextArea): Completion_Popup.Text_Area =
    {
      exit(text_area)
      val text_area_completion = new Text_Area(text_area)
      text_area.putClientProperty(key, text_area_completion)
      text_area_completion.activate()
      text_area_completion
    }

    def dismissed(text_area: JEditTextArea): Boolean =
    {
      Swing_Thread.require()
      apply(text_area) match {
        case Some(text_area_completion) => text_area_completion.dismissed()
        case None => false
      }
    }
  }

  class Text_Area private(text_area: JEditTextArea)
  {
    private var completion_popup: Option[Completion_Popup] = None


    /* completion action */

    private def insert(item: Completion.Item)
    {
      Swing_Thread.require()

      val buffer = text_area.getBuffer
      val len = item.original.length
      if (buffer.isEditable && len > 0) {
        JEdit_Lib.buffer_edit(buffer) {
          val caret = text_area.getCaretPosition
          JEdit_Lib.try_get_text(buffer, Text.Range(caret - len, caret)) match {
            case Some(text) if text == item.original =>
              buffer.remove(caret - len, len)
              buffer.insert(caret - len, item.replacement)
            case _ =>
          }
        }
      }
    }

    def action(immediate: Boolean = false, explicit: Boolean = false)
    {
      val view = text_area.getView
      val layered = view.getLayeredPane
      val buffer = text_area.getBuffer
      val painter = text_area.getPainter

      if (buffer.isEditable) {
        Isabelle.mode_syntax(JEdit_Lib.buffer_mode(buffer)) match {
          case Some(syntax) =>
            val caret = text_area.getCaretPosition
            val line = buffer.getLineOfOffset(caret)
            val start = buffer.getLineStartOffset(line)
            val text = buffer.getSegment(start, caret - start)

            val history = PIDE.completion_history.value
            val decode = Isabelle_Encoding.is_active(buffer)
            val context =
              PIDE.document_view(text_area) match {
                case None => Completion.Context.default
                case Some(doc_view) => doc_view.get_rendering().completion_context(caret)
              }
            syntax.completion.complete(history, decode, explicit, text, context) match {
              case Some(result) =>
                if (result.unique && result.items.head.immediate && immediate)
                  insert(result.items.head)
                else {
                  val font =
                    painter.getFont.deriveFont(Rendering.font_size("jedit_popup_font_scale"))

                  val loc1 = text_area.offsetToXY(caret - result.original.length)
                  if (loc1 != null) {
                    val loc2 =
                      SwingUtilities.convertPoint(painter,
                        loc1.x, loc1.y + painter.getFontMetrics.getHeight, layered)

                    val completion =
                      new Completion_Popup(layered, loc2, font, result.items) {
                        override def complete(item: Completion.Item) {
                          PIDE.completion_history.update(item)
                          insert(item)
                        }
                        override def propagate(evt: KeyEvent) {
                          JEdit_Lib.propagate_key(view, evt)
                          input(evt)
                        }
                        override def refocus() { text_area.requestFocus }
                      }
                    completion_popup = Some(completion)
                    completion.show_popup()
                  }
                }
              case None =>
            }
          case None =>
        }
      }
    }


    /* input key events */

    def input(evt: KeyEvent)
    {
      Swing_Thread.require()

      if (PIDE.options.bool("jedit_completion")) {
        if (!evt.isConsumed) {
          dismissed()
          if (evt.getKeyChar != '\b') {
            val special = JEdit_Lib.special_key(evt)
            if (PIDE.options.seconds("jedit_completion_delay").is_zero && !special) {
              input_delay.revoke()
              action(immediate = PIDE.options.bool("jedit_completion_immediate"))
            }
            else input_delay.invoke()
          }
        }
      }
    }

    private val input_delay =
      Swing_Thread.delay_last(PIDE.options.seconds("jedit_completion_delay")) {
        action()
      }


    /* dismiss popup */

    def dismissed(): Boolean =
    {
      Swing_Thread.require()

      completion_popup match {
        case Some(completion) =>
          completion.hide_popup()
          completion_popup = None
          true
        case None =>
          false
      }
    }


    /* activation */

    private val outer_key_listener =
      JEdit_Lib.key_listener(key_typed = input _)

    private def activate()
    {
      text_area.addKeyListener(outer_key_listener)
    }

    private def deactivate()
    {
      dismissed()
      text_area.removeKeyListener(outer_key_listener)
    }
  }



  /** history text field **/

  class History_Text_Field(
    name: String = null,
    instant_popups: Boolean = false,
    enter_adds_to_history: Boolean = true,
    syntax: Outer_Syntax = Outer_Syntax.init) extends
    HistoryTextField(name, instant_popups, enter_adds_to_history)
  {
    text_field =>

    // see https://forums.oracle.com/thread/1361677
    if (GUI.is_macos_laf) text_field.setCaret(new DefaultCaret)

    private var completion_popup: Option[Completion_Popup] = None


    /* dismiss */

    private def dismissed(): Boolean =
    {
      completion_popup match {
        case Some(completion) =>
          completion.hide_popup()
          completion_popup = None
          true
        case None =>
          false
      }
    }


    /* insert */

    private def insert(item: Completion.Item)
    {
      Swing_Thread.require()

      val len = item.original.length
      if (text_field.isEditable && len > 0) {
        val caret = text_field.getCaret.getDot
        val content = text_field.getText
        JEdit_Lib.try_get_text(content, Text.Range(caret - len, caret)) match {
          case Some(text) if text == item.original =>
            text_field.setText(
              content.substring(0, caret - len) +
              item.replacement +
              content.substring(caret))
            text_field.getCaret.setDot(caret - len + item.replacement.length)
          case _ =>
        }
      }
    }


    /* completion action */

    def action()
    {
      GUI.layered_pane(text_field) match {
        case Some(layered) if text_field.isEditable =>
          val history = PIDE.completion_history.value

          val caret = text_field.getCaret.getDot
          val text = text_field.getText.substring(0, caret)

          syntax.completion.complete(
              history, decode = true, explicit = false, text, Completion.Context.default) match {
            case Some(result) =>
              val fm = text_field.getFontMetrics(text_field.getFont)
              val loc =
                SwingUtilities.convertPoint(text_field, fm.stringWidth(text), fm.getHeight, layered)

              val completion = new Completion_Popup(layered, loc, text_field.getFont, result.items)
              {
                override def complete(item: Completion.Item) {
                  PIDE.completion_history.update(item)
                  insert(item)
                }
                override def propagate(evt: KeyEvent) {
                  if (!evt.isConsumed) text_field.processKeyEvent(evt)
                }
                override def refocus() { text_field.requestFocus }
              }
              completion_popup = Some(completion)
              completion.show_popup()

            case None =>
          }
        case _ =>
      }
    }


    /* process key event */

    private def process(evt: KeyEvent)
    {
      if (PIDE.options.bool("jedit_completion")) {
        dismissed()
        if (evt.getKeyChar != '\b') {
          val special = JEdit_Lib.special_key(evt)
          if (PIDE.options.seconds("jedit_completion_delay").is_zero && !special) {
            process_delay.revoke()
            action()
          }
          else process_delay.invoke()
        }
      }
    }

    private val process_delay =
      Swing_Thread.delay_last(PIDE.options.seconds("jedit_completion_delay")) {
        action()
      }

    override def processKeyEvent(evt0: KeyEvent)
    {
      val evt = KeyEventWorkaround.processKeyEvent(evt0)
      if (evt != null) {
        evt.getID match {
          case KeyEvent.KEY_PRESSED =>
            val key_code = evt.getKeyCode
            if (key_code == KeyEvent.VK_ESCAPE) {
              if (dismissed()) evt.consume
            }
          case KeyEvent.KEY_TYPED =>
            super.processKeyEvent(evt)
            process(evt)
            evt.consume
          case _ =>
        }
        if (!evt.isConsumed) super.processKeyEvent(evt)
      }
    }
  }
}


class Completion_Popup private(
  layered: JLayeredPane,
  location: Point,
  font: Font,
  items: List[Completion.Item]) extends JPanel(new BorderLayout)
{
  completion =>

  Swing_Thread.require()

  require(!items.isEmpty)
  val multi = items.length > 1


  /* actions */

  def complete(item: Completion.Item) { }
  def propagate(evt: KeyEvent) { }
  def refocus() { }


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

  private val inner_key_listener =
    JEdit_Lib.key_listener(
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
              case KeyEvent.VK_UP | KeyEvent.VK_KP_UP if multi =>
                move_items(-1)
                e.consume
              case KeyEvent.VK_DOWN | KeyEvent.VK_KP_DOWN if multi =>
                move_items(1)
                e.consume
              case KeyEvent.VK_PAGE_UP if multi =>
                move_pages(-1)
                e.consume
              case KeyEvent.VK_PAGE_DOWN if multi =>
                move_pages(1)
                e.consume
              case _ =>
                if (e.isActionKey || e.isAltDown || e.isMetaDown || e.isControlDown)
                  hide_popup()
            }
          }
          propagate(e)
        },
      key_typed = propagate _
    )

  list_view.peer.addKeyListener(inner_key_listener)

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
  completion.setBorder(new LineBorder(Color.BLACK))
  completion.add((new ScrollPane(list_view)).peer.asInstanceOf[JComponent])


  /* popup */

  private val popup =
  {
    val screen = JEdit_Lib.screen_location(layered, location)
    val size =
    {
      val geometry = JEdit_Lib.window_geometry(completion, completion)
      val bounds = Rendering.popup_bounds
      val w = geometry.width min (screen.bounds.width * bounds).toInt min layered.getWidth
      val h = geometry.height min (screen.bounds.height * bounds).toInt min layered.getHeight
      new Dimension(w, h)
    }
    new Popup(layered, completion, screen.relative(layered, size), size)
  }

  private def show_popup()
  {
    popup.show
    list_view.requestFocus
  }

  private val hide_popup_delay =
    Swing_Thread.delay_last(PIDE.options.seconds("jedit_completion_dismiss_delay")) {
      popup.hide
    }

  private def hide_popup()
  {
    if (list_view.peer.isFocusOwner) refocus()

    if (PIDE.options.seconds("jedit_completion_dismiss_delay").is_zero)
      popup.hide
    else hide_popup_delay.invoke()
  }
}

