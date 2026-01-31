/*  Title:      Tools/jEdit/src/completion_popup.scala
    Author:     Makarius

Completion popup.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Font, Point}
import java.awt.event.KeyEvent
import javax.swing.{JLayeredPane, SwingUtilities}
import javax.swing.text.DefaultCaret

import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, Selection}
import org.gjt.sp.jedit.gui.{HistoryTextField, KeyEventWorkaround}


object Completion_Popup {
  /** options **/

  def completion_enabled: Boolean = PIDE.options.bool("jedit_completion")
  def completion_context: Boolean = PIDE.options.bool("jedit_completion_context")
  def completion_immediate: Boolean = PIDE.options.bool("jedit_completion_immediate")
  def completion_delay: Time = PIDE.options.seconds("jedit_completion_delay")
  def completion_select_enter: Boolean = PIDE.options.bool("jedit_completion_select_enter")
  def completion_select_tab: Boolean = PIDE.options.bool("jedit_completion_select_tab")



  /** items with GUI rendering **/

  class Item(item: Completion.Item, insert: Completion.Item => Unit, unicode: Boolean)
  extends Selection_Popup.Item {
    override def select(): Unit = {
      PIDE.plugin.completion_history.update(item)
      insert(item)
    }

    override def toString: String = // Swing GUI label
      item.description match {
        case a :: bs =>
          val style = GUI.Style_HTML
          def output(s: String): String = Symbol.output(unicode, Symbol.print_newlines(s))
          style.enclose(
            style.make_bold(output(a)) + style.make_text(bs.map(b => " " + output(b)).mkString))
        case Nil => ""
      }
  }



  /** jEdit text area **/

  object Text_Area {
    private val key = new Object

    def apply(text_area: TextArea): Option[Completion_Popup.Text_Area] = GUI_Thread.require {
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

    def action(
      text_area: TextArea,
      word_only: Boolean = false,
      focus: Boolean = false,
      select_enter: Boolean = completion_select_enter,
      select_tab: Boolean = completion_select_tab
    ): Boolean =
      apply(text_area) match {
        case Some(text_area_completion) =>
          if (text_area_completion.active_range.isDefined) {
            text_area_completion.action(word_only = word_only, focus = focus,
              select_enter = select_enter, select_tab = select_tab)
          }
          else {
            text_area_completion.action(
              immediate = true, explicit = true, word_only = word_only, focus = focus,
              select_enter = select_enter, select_tab = select_tab)
          }
          true
        case None => false
      }

    def exit(text_area: JEditTextArea): Unit = GUI_Thread.require {
      apply(text_area) match {
        case None =>
        case Some(text_area_completion) =>
          text_area_completion.deactivate()
          text_area.putClientProperty(key, null)
      }
    }

    def init(text_area: JEditTextArea): Completion_Popup.Text_Area = {
      exit(text_area)
      val text_area_completion = new Text_Area(text_area)
      text_area.putClientProperty(key, text_area_completion)
      text_area_completion.activate()
      text_area_completion
    }

    def dismissed(text_area: TextArea): Boolean = GUI_Thread.require {
      apply(text_area) match {
        case Some(text_area_completion) => text_area_completion.dismissed()
        case None => false
      }
    }
  }

  class Text_Area private(text_area: JEditTextArea) {
    // owned by GUI thread
    private var selection_popup: Option[Selection_Popup.Text_Area] = None

    def active_range: Option[Text.Range] =
      selection_popup match {
        case Some(panel) => panel.active_range
        case None => None
      }


    /* rendering */

    def rendering(rendering: JEdit_Rendering, line_range: Text.Range): Option[Text.Info[Color]] = {
      active_range match {
        case Some(range) => range.try_restrict(line_range)
        case None =>
          val caret = text_area.getCaretPosition
          if (line_range.contains(caret)) {
            rendering.before_caret_range(caret).try_restrict(line_range) match {
              case Some(range) if !range.is_singularity =>
                val range0 =
                  Completion.Result.merge(Completion.History.empty,
                    syntax_completion(Completion.History.empty, true, Some(rendering)),
                    rendering.path_completion(caret))
                  .map(_.range)
                rendering.semantic_completion(range0, range) match {
                  case None => range0
                  case Some(Text.Info(_, Completion.No_Completion)) => None
                  case Some(Text.Info(range1, _: Completion.Names)) => Some(range1)
                }
              case _ => None
            }
          }
          else None
      }
    }.map(range => Text.Info(range, rendering.completion_color))


    /* syntax completion */

    def syntax_completion(
      history: Completion.History,
      explicit: Boolean,
      opt_rendering: Option[JEdit_Rendering]
    ): Option[Completion.Result] = {
      val buffer = text_area.getBuffer
      val unicode = Isabelle_Encoding.is_active(buffer = buffer)

      Isabelle.buffer_syntax(buffer) match {
        case Some(syntax) =>
          val context =
            (for {
              rendering <- opt_rendering
              if completion_context
              caret_range = rendering.before_caret_range(text_area.getCaretPosition)
              context <- rendering.language_context(caret_range)
            } yield context) getOrElse syntax.language_context

          val caret = text_area.getCaretPosition
          val line_range = JEdit_Lib.line_range(buffer, text_area.getCaretLine)
          val line_start = line_range.start
          for {
            line_text <- JEdit_Lib.get_text(buffer, line_range)
            result <-
              syntax.complete(
                history, unicode, explicit, line_start, line_text, caret - line_start, context)
          } yield result

        case None => None
      }
    }


    /* completion action: text area */

    private def insert(item: Completion.Item): Unit = GUI_Thread.require {
      val buffer = text_area.getBuffer
      val range = item.range
      if (buffer.isEditable) {
        JEdit_Lib.buffer_edit(buffer) {
          JEdit_Lib.get_text(buffer, range) match {
            case Some(text) if text == item.original =>
              text_area.getSelectionAtOffset(text_area.getCaretPosition) match {

                /*rectangular selection as "tall caret"*/
                case selection : Selection.Rect
                if selection.getStart(buffer, text_area.getCaretLine) == range.stop =>
                  text_area.moveCaretPosition(range.stop)
                  (0 until Character.codePointCount(item.original, 0, item.original.length))
                    .foreach(_ => text_area.backspace())
                  text_area.setSelectedText(selection, item.replacement)
                  text_area.moveCaretPosition(text_area.getCaretPosition + item.move)

                /*other selections: rectangular, multiple range, ...*/
                case selection
                if selection != null &&
                    selection.getStart(buffer, text_area.getCaretLine) == range.start &&
                    selection.getEnd(buffer, text_area.getCaretLine) == range.stop =>
                  text_area.moveCaretPosition(range.stop + item.move)
                  text_area.getSelection.foreach(text_area.setSelectedText(_, item.replacement))

                /*no selection*/
                case _ =>
                  buffer.remove(range.start, range.length)
                  buffer.insert(range.start, item.replacement)
                  text_area.moveCaretPosition(range.start + item.replacement.length + item.move)
                  Isabelle.indent_input(text_area)
              }
            case _ =>
          }
        }
      }
    }

    def open_popup(
      range: Text.Range,
      items: List[Selection_Popup.Item],
      focus: Boolean = false,
      select_enter: Boolean = completion_select_enter,
      select_tab: Boolean = completion_select_tab
    ): Unit = {
      val view = text_area.getView
      val painter = text_area.getPainter

      val loc1 = text_area.offsetToXY(range.start)
      if (loc1 != null) {
        val loc2 =
          SwingUtilities.convertPoint(painter,
            loc1.x, loc1.y + painter.getLineHeight, view.getLayeredPane)
        val panel =
          new Selection_Popup.Text_Area(text_area, range, loc2, items,
            select_enter = select_enter, select_tab = select_tab
          ) { override def input(evt: KeyEvent): Unit = Text_Area.this.input(evt) }

        dismissed()
        selection_popup = Some(panel)
        view.setKeyEventInterceptor(panel.inner_key_listener)
        JEdit_Lib.invalidate_range(text_area, range)
        Pretty_Tooltip.dismissed_all()
        panel.show_popup(focus)
      }
    }

    def action(
      immediate: Boolean = false,
      explicit: Boolean = false,
      delayed: Boolean = false,
      word_only: Boolean = false,
      focus: Boolean = false,
      select_enter: Boolean = completion_select_enter,
      select_tab: Boolean = completion_select_tab
    ): Boolean = {
      val history = PIDE.plugin.completion_history.value
      val buffer = text_area.getBuffer
      val unicode = Isabelle_Encoding.is_active(buffer = buffer)

      if (buffer.isEditable) {
        val caret = text_area.getCaretPosition
        val opt_rendering = Document_View.get_rendering(text_area)
        val result0 = syntax_completion(history, explicit, opt_rendering)
        val (no_completion, semantic_completion) = {
          opt_rendering match {
            case Some(rendering) =>
              rendering.semantic_completion_result(history, unicode, result0.map(_.range),
                rendering.before_caret_range(caret))
            case None => (false, None)
          }
        }
        if (no_completion) false
        else {
          val result = {
            val result1 =
              if (word_only) None
              else Completion.Result.merge(history, semantic_completion, result0)
            opt_rendering match {
              case None => result1
              case Some(rendering) =>
                Completion.Result.merge(history,
                  result1,
                  JEdit_Spell_Checker.completion(rendering, explicit, caret),
                  rendering.path_completion(caret))
            }
          }
          result match {
            case Some(result) =>
              result.items match {
                case List(item) if result.unique && item.immediate && immediate =>
                  insert(item)
                  true
                case _ :: _ if !delayed =>
                  open_popup(result.range, result.items.map(new Item(_, insert, unicode)),
                    focus = focus,
                    select_enter = completion_select_enter,
                    select_tab = completion_select_tab)
              false
                case _ => false
              }
            case None => false
          }
        }
      }
      else false
    }


    /* input key events */

    def input(evt: KeyEvent): Unit = GUI_Thread.require {
      if (!evt.isConsumed) {
        dismissed()

        val special = JEdit_Lib.special_key(evt)

        if (completion_enabled) {
          if (evt.getKeyChar != '\b') {
            val immediate = completion_immediate
            if (completion_delay.is_zero && !special) {
              input_delay.revoke()
              action(immediate = immediate)
            }
            else if (!special && action(immediate = immediate, delayed = true)) input_delay.revoke()
            else input_delay.invoke()
          }
        }

        val selection = text_area.getSelection()
        if (!special && (selection == null || selection.isEmpty)) {
          Isabelle.indent_input(text_area)
        }
      }
    }

    private val input_delay = Delay.last(completion_delay, gui = true) { action() }


    /* dismiss popup */

    def dismissed(): Boolean = GUI_Thread.require {
      selection_popup match {
        case Some(panel) =>
          panel.hide_popup()
          selection_popup = None
          true
        case None =>
          false
      }
    }


    /* activation */

    private val outer_key_listener =
      JEdit_Lib.key_listener(key_typed = input)

    private def activate(): Unit =
      text_area.addKeyListener(outer_key_listener)

    private def deactivate(): Unit = {
      dismissed()
      text_area.removeKeyListener(outer_key_listener)
    }
  }



  /** history text field **/

  class History_Text_Field(
    name: String = null,
    instant_popups: Boolean = false,
    enter_adds_to_history: Boolean = true,
    syntax: Outer_Syntax = Outer_Syntax.empty) extends
    HistoryTextField(name, instant_popups, enter_adds_to_history
  ) {
    text_field =>

    // see https://forums.oracle.com/thread/1361677
    if (GUI.is_macos_laf()) text_field.setCaret(new DefaultCaret)

    // owned by GUI thread
    private var completion_popup: Option[Selection_Popup] = None


    /* dismiss */

    private def dismissed(): Boolean = {
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

    private def insert(item: Completion.Item): Unit = GUI_Thread.require {
      val range = item.range
      if (text_field.isEditable) {
        val content = text_field.getText
        range.try_substring(content) match {
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


    /* completion action: text field */

    def action(): Unit = {
      GUI.layered_pane(text_field) match {
        case Some(layered) if text_field.isEditable =>
          val history = PIDE.plugin.completion_history.value
          val unicode = Isabelle_Encoding.is_active()

          val caret = text_field.getCaret.getDot
          val text = text_field.getText

          val context = syntax.language_context

          syntax.complete(history, true, false, 0, text, caret, context) match {
            case Some(result) =>
              val fm = text_field.getFontMetrics(text_field.getFont)
              val loc =
                SwingUtilities.convertPoint(text_field, fm.stringWidth(text), fm.getHeight, layered)

              val items = result.items.map(new Item(_, insert, unicode))
              val completion =
                new Selection_Popup(None, layered, loc, text_field.getFont, items,
                  select_enter = completion_select_enter,
                  select_tab = completion_select_tab
                ) {
                  override def propagate(evt: KeyEvent): Unit =
                    if (!evt.isConsumed) text_field.processKeyEvent(evt)
                  override def shutdown(refocus: Boolean): Unit =
                    if (refocus) text_field.requestFocus()
                }
              dismissed()
              completion_popup = Some(completion)
              completion.show_popup(true)

            case None =>
          }
        case _ =>
      }
    }


    /* process key event */

    private def process(evt: KeyEvent): Unit = {
      dismissed()
      if (completion_enabled) {
        if (evt.getKeyChar != '\b') {
          val special = JEdit_Lib.special_key(evt)
          if (completion_delay.is_zero && !special) {
            process_delay.revoke()
            action()
          }
          else process_delay.invoke()
        }
      }
    }

    private val process_delay = Delay.last(completion_delay, gui = true) { action() }

    override def processKeyEvent(evt0: KeyEvent): Unit = {
      val evt = KeyEventWorkaround.processKeyEvent(evt0)
      if (evt != null) {
        evt.getID match {
          case KeyEvent.KEY_PRESSED =>
            val key_code = evt.getKeyCode
            if (key_code == KeyEvent.VK_ESCAPE) {
              if (dismissed()) evt.consume()
            }
          case KeyEvent.KEY_TYPED =>
            super.processKeyEvent(evt)
            process(evt)
            evt.consume()
          case _ =>
        }
        if (!evt.isConsumed) super.processKeyEvent(evt)
      }
    }
  }
}
