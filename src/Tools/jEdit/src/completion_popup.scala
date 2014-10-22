/*  Title:      Tools/jEdit/src/completion_popup.scala
    Author:     Makarius

Completion popup.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Font, Point, BorderLayout, Dimension}
import java.awt.event.{KeyEvent, MouseEvent, MouseAdapter, FocusAdapter, FocusEvent}
import java.io.{File => JFile}
import java.util.regex.Pattern
import javax.swing.{JPanel, JComponent, JLayeredPane, SwingUtilities}
import javax.swing.border.LineBorder
import javax.swing.text.DefaultCaret

import scala.swing.{ListView, ScrollPane}
import scala.swing.event.MouseClicked

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, Selection}
import org.gjt.sp.jedit.gui.{HistoryTextField, KeyEventWorkaround}
import org.gjt.sp.util.StandardUtilities


object Completion_Popup
{
  /** items with HTML rendering **/

  private class Item(val item: Completion.Item)
  {
    private val html =
      item.description match {
        case a :: bs =>
          "<html><b>" + HTML.encode(a) + "</b>" +
            HTML.encode(bs.map(" " + _).mkString) + "</html>"
        case Nil => ""
      }
    override def toString: String = html
  }



  /** jEdit text area **/

  object Text_Area
  {
    private val key = new Object

    def apply(text_area: TextArea): Option[Completion_Popup.Text_Area] =
    {
      GUI_Thread.require {}
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

    def action(text_area: TextArea, word_only: Boolean): Boolean =
      apply(text_area) match {
        case Some(text_area_completion) =>
          if (text_area_completion.active_range.isDefined)
            text_area_completion.action(word_only = word_only)
          else
            text_area_completion.action(immediate = true, explicit = true, word_only = word_only)
          true
        case None => false
      }

    def exit(text_area: JEditTextArea)
    {
      GUI_Thread.require {}
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
      GUI_Thread.require {}
      apply(text_area) match {
        case Some(text_area_completion) => text_area_completion.dismissed()
        case None => false
      }
    }
  }

  class Text_Area private(text_area: JEditTextArea)
  {
    // owned by GUI thread
    private var completion_popup: Option[Completion_Popup] = None

    def active_range: Option[Text.Range] =
      completion_popup match {
        case Some(completion) => completion.active_range
        case None => None
      }


    /* rendering */

    def rendering(rendering: Rendering, line_range: Text.Range): Option[Text.Info[Color]] =
    {
      active_range match {
        case Some(range) => range.try_restrict(line_range)
        case None =>
          if (line_range.contains(text_area.getCaretPosition)) {
            JEdit_Lib.before_caret_range(text_area, rendering).try_restrict(line_range) match {
              case Some(range) if !range.is_singularity =>
                rendering.semantic_completion(range) match {
                  case Some(Text.Info(_, Completion.No_Completion)) => None
                  case Some(Text.Info(range1, _: Completion.Names)) => Some(range1)
                  case None =>
                    Completion.Result.merge(Completion.History.empty,
                      syntax_completion(Completion.History.empty, false, Some(rendering)),
                      Completion.Result.merge(Completion.History.empty,
                        path_completion(rendering),
                        Bibtex_JEdit.completion(Completion.History.empty, text_area, rendering)))
                    .map(_.range)
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
      opt_rendering: Option[Rendering]): Option[Completion.Result] =
    {
      val buffer = text_area.getBuffer
      val decode = Isabelle_Encoding.is_active(buffer)

      Isabelle.mode_syntax(JEdit_Lib.buffer_mode(buffer)) match {
        case Some(syntax) =>
          val context =
            (for {
              rendering <- opt_rendering
              if PIDE.options.bool("jedit_completion_context")
              range = JEdit_Lib.before_caret_range(text_area, rendering)
              context <- rendering.language_context(range)
            } yield context) getOrElse syntax.language_context

          val caret = text_area.getCaretPosition
          val line_range = JEdit_Lib.line_range(buffer, text_area.getCaretLine)
          val line_start = line_range.start
          for {
            line_text <- JEdit_Lib.try_get_text(buffer, line_range)
            result <-
              syntax.completion.complete(
                history, decode, explicit, line_start, line_text, caret - line_start, context)
          } yield result

        case None => None
      }
    }


    /* path completion */

    def path_completion(rendering: Rendering): Option[Completion.Result] =
    {
      def complete(text: String): List[(String, List[String])] =
      {
        try {
          val path = Path.explode(text)
          val (dir, base_name) =
            if (text == "" || text.endsWith("/")) (path, "")
            else (path.dir, path.base.implode)

          val directory =
            new JFile(PIDE.resources.append(rendering.snapshot.node_name.master_dir, dir))
          val files = directory.listFiles
          if (files == null) Nil
          else {
            val ignore =
              Library.space_explode(':', PIDE.options.string("jedit_completion_path_ignore")).
                map(s => Pattern.compile(StandardUtilities.globToRE(s)))
            (for {
              file <- files.iterator

              name = file.getName
              if name.startsWith(base_name)
              if !ignore.exists(pat => pat.matcher(name).matches)

              text1 = (dir + Path.basic(name)).implode_short
              if text != text1

              is_dir = new JFile(directory, name).isDirectory
              replacement = text1 + (if (is_dir) "/" else "")
              descr = List(text1, if (is_dir) "(directory)" else "(file)")
            } yield (replacement, descr)).take(PIDE.options.int("completion_limit")).toList
          }
        }
        catch { case ERROR(_) => Nil }
      }

      for {
        r1 <- rendering.language_path(JEdit_Lib.before_caret_range(text_area, rendering))
        s1 <- JEdit_Lib.try_get_text(text_area.getBuffer, r1)
        s2 <- Library.try_unquote(s1)
        r2 = Text.Range(r1.start + 1, r1.stop - 1)
        if Path.is_valid(s2)
        paths = complete(s2)
        if !paths.isEmpty
        items = paths.map(p => Completion.Item(r2, s2, "", p._2, p._1, 0, false))
      } yield Completion.Result(r2, s2, false, items)
    }


    /* completion action: text area */

    private def insert(item: Completion.Item)
    {
      GUI_Thread.require {}

      val buffer = text_area.getBuffer
      val range = item.range
      if (buffer.isEditable) {
        JEdit_Lib.buffer_edit(buffer) {
          JEdit_Lib.try_get_text(buffer, range) match {
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
              }
            case _ =>
          }
        }
      }
    }

    def action(
      immediate: Boolean = false,
      explicit: Boolean = false,
      delayed: Boolean = false,
      word_only: Boolean = false): Boolean =
    {
      val view = text_area.getView
      val layered = view.getLayeredPane
      val buffer = text_area.getBuffer
      val painter = text_area.getPainter

      val history = PIDE.completion_history.value
      val decode = Isabelle_Encoding.is_active(buffer)

      def open_popup(result: Completion.Result)
      {
        val font =
          painter.getFont.deriveFont(
            Font_Info.main_size(PIDE.options.real("jedit_popup_font_scale")))

        val range = result.range

        val loc1 = text_area.offsetToXY(range.start)
        if (loc1 != null) {
          val loc2 =
            SwingUtilities.convertPoint(painter,
              loc1.x, loc1.y + painter.getLineHeight, layered)

          val items = result.items.map(new Item(_))
          val completion =
            new Completion_Popup(Some(range), layered, loc2, font, items)
            {
              override def complete(item: Completion.Item) {
                PIDE.completion_history.update(item)
                insert(item)
              }
              override def propagate(evt: KeyEvent) {
                if (view.getKeyEventInterceptor == null)
                  JEdit_Lib.propagate_key(view, evt)
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
              override def shutdown(focus: Boolean) {
                if (view.getKeyEventInterceptor == inner_key_listener)
                  view.setKeyEventInterceptor(null)
                if (focus) text_area.requestFocus
                JEdit_Lib.invalidate_range(text_area, range)
              }
            }
          dismissed()
          completion_popup = Some(completion)
          view.setKeyEventInterceptor(completion.inner_key_listener)
          JEdit_Lib.invalidate_range(text_area, range)
          Pretty_Tooltip.dismissed_all()
          completion.show_popup(false)
        }
      }

      if (buffer.isEditable) {
        val (no_completion, semantic_completion, opt_rendering) =
        {
          PIDE.document_view(text_area) match {
            case Some(doc_view) =>
              val rendering = doc_view.get_rendering()
              val (no_completion, result) =
              {
                val caret_range = JEdit_Lib.before_caret_range(text_area, rendering)
                rendering.semantic_completion(caret_range) match {
                  case Some(Text.Info(_, Completion.No_Completion)) => (true, None)
                  case Some(Text.Info(range, names: Completion.Names)) =>
                    val result =
                      JEdit_Lib.try_get_text(buffer, range) match {
                        case Some(original) => names.complete(range, history, decode, original)
                        case None => None
                      }
                    (false, result)
                  case None => (false, None)
                }
              }
              (no_completion, result, Some(rendering))
            case None => (false, None, None)
          }
        }
        if (no_completion) false
        else {
          val result =
          {
            val result0 =
              if (word_only) None
              else
                Completion.Result.merge(history, semantic_completion,
                  syntax_completion(history, explicit, opt_rendering))
            opt_rendering match {
              case None => result0
              case Some(rendering) =>
                Completion.Result.merge(history, result0,
                  Completion.Result.merge(history,
                    Spell_Checker.completion(text_area, explicit, rendering),
                    Completion.Result.merge(history,
                      path_completion(rendering),
                      Bibtex_JEdit.completion(history, text_area, rendering))))
            }
          }
          result match {
            case Some(result) =>
              result.items match {
                case List(item) if result.unique && item.immediate && immediate =>
                  insert(item)
                  true
                case _ :: _ if !delayed =>
                  open_popup(result)
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

    def input(evt: KeyEvent)
    {
      GUI_Thread.require {}

      if (PIDE.options.bool("jedit_completion")) {
        if (!evt.isConsumed) {
          dismissed()
          if (evt.getKeyChar != '\b') {
            val special = JEdit_Lib.special_key(evt)
            val immediate = PIDE.options.bool("jedit_completion_immediate")
            if (PIDE.options.seconds("jedit_completion_delay").is_zero && !special) {
              input_delay.revoke()
              action(immediate = immediate)
            }
            else {
              if (!special && action(immediate = immediate, delayed = true))
                input_delay.revoke()
              else
                input_delay.invoke()
            }
          }
        }
      }
    }

    private val input_delay =
      GUI_Thread.delay_last(PIDE.options.seconds("jedit_completion_delay")) {
        action()
      }


    /* dismiss popup */

    def dismissed(): Boolean =
    {
      GUI_Thread.require {}

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

    // owned by GUI thread
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
      GUI_Thread.require {}

      val range = item.range
      if (text_field.isEditable) {
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


    /* completion action: text field */

    def action()
    {
      GUI.layered_pane(text_field) match {
        case Some(layered) if text_field.isEditable =>
          val history = PIDE.completion_history.value

          val caret = text_field.getCaret.getDot
          val text = text_field.getText

          val context = syntax.language_context

          syntax.completion.complete(history, true, false, 0, text, caret, context) match {
            case Some(result) =>
              val fm = text_field.getFontMetrics(text_field.getFont)
              val loc =
                SwingUtilities.convertPoint(text_field, fm.stringWidth(text), fm.getHeight, layered)

              val items = result.items.map(new Item(_))
              val completion =
                new Completion_Popup(None, layered, loc, text_field.getFont, items)
                {
                  override def complete(item: Completion.Item) {
                    PIDE.completion_history.update(item)
                    insert(item)
                  }
                  override def propagate(evt: KeyEvent) {
                    if (!evt.isConsumed) text_field.processKeyEvent(evt)
                  }
                  override def shutdown(focus: Boolean) { if (focus) text_field.requestFocus }
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
      GUI_Thread.delay_last(PIDE.options.seconds("jedit_completion_delay")) {
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
  opt_range: Option[Text.Range],
  layered: JLayeredPane,
  location: Point,
  font: Font,
  items: List[Completion_Popup.Item]) extends JPanel(new BorderLayout)
{
  completion =>

  GUI_Thread.require {}

  require(!items.isEmpty)
  val multi = items.length > 1


  /* actions */

  def complete(item: Completion.Item) { }
  def propagate(evt: KeyEvent) { }
  def shutdown(focus: Boolean) { }


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
      case item :: _ => complete(item.item); true
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

  val inner_key_listener =
    JEdit_Lib.key_listener(
      key_pressed = (e: KeyEvent) =>
        {
          if (!e.isConsumed) {
            e.getKeyCode match {
              case KeyEvent.VK_ENTER if PIDE.options.bool("jedit_completion_select_enter") =>
                if (complete_selected()) e.consume
                hide_popup()
              case KeyEvent.VK_TAB if PIDE.options.bool("jedit_completion_select_tab") =>
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

  def active_range: Option[Text.Range] =
    if (isDisplayable) opt_range else None

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

  private def show_popup(focus: Boolean)
  {
    popup.show
    if (focus) list_view.requestFocus
  }

  private def hide_popup()
  {
    shutdown(list_view.peer.isFocusOwner)
    popup.hide
  }
}

