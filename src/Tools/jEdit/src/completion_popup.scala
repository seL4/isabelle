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
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}
import org.gjt.sp.jedit.gui.{HistoryTextField, KeyEventWorkaround}


object Completion_Popup
{
  /** jEdit text area **/

  object Text_Area
  {
    private val key = new Object

    def apply(text_area: TextArea): Option[Completion_Popup.Text_Area] =
    {
      Swing_Thread.require()
      text_area.getClientProperty(key) match {
        case text_area_completion: Completion_Popup.Text_Area => Some(text_area_completion)
        case _ => None
      }
    }

    def active_range(text_area: TextArea): Option[Text.Range] =
      apply(text_area) match {
        case Some(text_area_completion) => text_area_completion.active_range
        case None => None
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

    def dismissed(text_area: TextArea): Boolean =
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
    // owned by Swing thread
    private var completion_popup: Option[Completion_Popup] = None

    def active_range: Option[Text.Range] =
      completion_popup match {
        case Some(completion) =>
          completion.active_range match {
            case Some((range, _)) if completion.isDisplayable => Some(range)
            case _ => None
          }
        case None => None
      }


    /* rendering */

    def rendering(rendering: Rendering, line_range: Text.Range): Option[Text.Info[Color]] =
    {
      active_range match {
        case Some(range) => range.try_restrict(line_range)
        case None =>
          val buffer = text_area.getBuffer
          val caret = text_area.getCaretPosition

          if (line_range.contains(caret)) {
            JEdit_Lib.stretch_point_range(buffer, caret).try_restrict(line_range) match {
              case Some(range) if !range.is_singularity =>
                rendering.completion_names(range) match {
                  case Some(names) => Some(names.range)
                  case None =>
                    syntax_completion(Some(rendering), false) match {
                      case Some(result) => Some(result.range)
                      case None => None
                    }
                }
              case _ => None
            }
          }
          else None
      }
    }.map(range => Text.Info(range, rendering.completion_color))


    /* syntax completion */

    def syntax_completion(
      opt_rendering: Option[Rendering], explicit: Boolean): Option[Completion.Result] =
    {
      val buffer = text_area.getBuffer
      val history = PIDE.completion_history.value
      val decode = Isabelle_Encoding.is_active(buffer)

      Isabelle.mode_syntax(JEdit_Lib.buffer_mode(buffer)) match {
        case Some(syntax) =>
          val caret = text_area.getCaretPosition
          val line = buffer.getLineOfOffset(caret)
          val start = buffer.getLineStartOffset(line)
          val text = buffer.getSegment(start, caret - start)

          val word_context =
            Completion.word_context(
              JEdit_Lib.try_get_text(buffer, JEdit_Lib.point_range(buffer, caret)))

          val context =
            (opt_rendering orElse PIDE.document_view(text_area).map(_.get_rendering()) match {
              case Some(rendering) =>
                rendering.language_context(JEdit_Lib.stretch_point_range(buffer, caret))
              case None => None
            }) getOrElse syntax.language_context

          syntax.completion.complete(history, decode, explicit, start, text, word_context, context)

        case None => None
      }
    }


    /* completion action */

    private def insert(item: Completion.Item)
    {
      Swing_Thread.require()

      val buffer = text_area.getBuffer
      val range = item.range
      if (buffer.isEditable && range.length > 0) {
        JEdit_Lib.buffer_edit(buffer) {
          JEdit_Lib.try_get_text(buffer, range) match {
            case Some(text) if text == item.original =>
              buffer.remove(range.start, range.length)
              buffer.insert(range.start, item.replacement)
              text_area.moveCaretPosition(range.start + item.replacement.length + item.move)
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
      val caret = text_area.getCaretPosition

      val history = PIDE.completion_history.value
      val decode = Isabelle_Encoding.is_active(buffer)

      def open_popup(result: Completion.Result)
      {
        val font =
          painter.getFont.deriveFont(Rendering.font_size("jedit_popup_font_scale"))

        val range = result.range
        def invalidate(): Unit = JEdit_Lib.invalidate_range(text_area, range)

        val loc1 = text_area.offsetToXY(range.start)
        if (loc1 != null) {
          val loc2 =
            SwingUtilities.convertPoint(painter,
              loc1.x, loc1.y + painter.getFontMetrics.getHeight, layered)

          val completion =
            new Completion_Popup(Some((range, invalidate _)), layered, loc2, font, result.items) {
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
          invalidate()
          completion.show_popup()
        }
      }

      def semantic_completion(): Boolean =
        explicit && {
          PIDE.document_view(text_area) match {
            case Some(doc_view) =>
              val rendering = doc_view.get_rendering()
              rendering.completion_names(JEdit_Lib.stretch_point_range(buffer, caret)) match {
                case None => false
                case Some(names) =>
                  JEdit_Lib.try_get_text(buffer, names.range) match {
                    case Some(original) =>
                      names.complete(history, decode, original) match {
                        case Some(result) if !result.items.isEmpty =>
                          open_popup(result)
                          true
                        case _ => false
                      }
                    case None => false
                  }
              }
            case _ => false
          }
        }

      def syntactic_completion(): Boolean =
        syntax_completion(None, explicit) match {
          case Some(result) =>
            result.items match {
              case List(item) if result.unique && item.immediate && immediate =>
                insert(item); true
              case _ :: _ => open_popup(result); true
              case _ => false
            }
          case None => false
        }

      if (buffer.isEditable)
        semantic_completion() || syntactic_completion()
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

    // owned by Swing thread
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

      val range = item.range
      if (text_field.isEditable && range.length > 0) {
        val content = text_field.getText
        JEdit_Lib.try_get_text(content, range) match {
          case Some(text) if text == item.original =>
            text_field.setText(
              content.substring(0, range.start) +
              item.replacement +
              content.substring(range.stop))
            text_field.getCaret.setDot(range.start + item.replacement.length + item.move)
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

          val word_context =
            Completion.word_context(JEdit_Lib.try_get_text(text_field.getText,
              Text.Range(caret, caret + 1)))  // FIXME proper point range!?

          val context = syntax.language_context

          syntax.completion.complete(history, true, false, 0, text, word_context, context) match {
            case Some(result) =>
              val fm = text_field.getFontMetrics(text_field.getFont)
              val loc =
                SwingUtilities.convertPoint(text_field, fm.stringWidth(text), fm.getHeight, layered)

              val completion =
                new Completion_Popup(None, layered, loc, text_field.getFont, result.items)
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
  val active_range: Option[(Text.Range, () => Unit)],
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
      active_range match { case Some((_, invalidate)) => invalidate() case _ => }
      popup.hide
    }

  private def hide_popup()
  {
    if (list_view.peer.isFocusOwner) refocus()

    if (PIDE.options.seconds("jedit_completion_dismiss_delay").is_zero) {
      active_range match { case Some((_, invalidate)) => invalidate() case _ => }
      popup.hide
    }
    else hide_popup_delay.invoke()
  }
}

