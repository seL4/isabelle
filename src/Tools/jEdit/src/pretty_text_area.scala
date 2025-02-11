/*  Title:      Tools/jEdit/src/pretty_text_area.scala
    Author:     Makarius

GUI component for pretty-printed text with markup, rendered like jEdit
text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Font}
import java.awt.event.KeyEvent
import java.awt.im.InputMethodRequests
import javax.swing.JTextField
import javax.swing.event.{DocumentListener, DocumentEvent}

import scala.swing.{Label, Component}
import scala.util.matching.Regex

import org.gjt.sp.jedit.{jEdit, View, Registers, JEditBeanShellAction}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.input.{DefaultInputHandlerProvider, TextAreaInputHandler}
import org.gjt.sp.jedit.textarea.JEditEmbeddedTextArea
import org.gjt.sp.jedit.search.HyperSearchResults
import org.gjt.sp.jedit.syntax.SyntaxStyle
import org.gjt.sp.jedit.gui.KeyEventTranslator
import org.gjt.sp.util.{SyntaxUtilities, Log, HtmlUtilities}

object Pretty_Text_Area {
  def make_highlight_style(): String =
    HtmlUtilities.style2html(jEdit.getProperty(HyperSearchResults.HIGHLIGHT_PROP),
      Font_Metric.default_font)

  sealed case class Search_Result(
    buffer: JEditBuffer,
    highlight_style: String,
    regex: Regex,
    line: Int,
    line_range: Text.Range
  ) {
    lazy val line_text: String =
      Library.trim_line(JEdit_Lib.get_text(buffer, line_range).getOrElse(""))
        .replace('\t',' ')

    lazy val gui_text: String = Library.string_builder(line_range.length * 2) { s =>
      val style = GUI.Style_HTML

      // see also HyperSearchResults.highlightString
      s ++= "<html><b>"
      s ++= line.toString
      s ++= ":</b> "

      val line_start = line_range.start
      val plain_start = line_text.length - line_text.stripLeading.length
      val plain_stop = line_text.stripTrailing.length

      val search_range = Text.Range(line_start + plain_start, line_start + plain_stop)
      var last = plain_start
      for (range <- JEdit_Lib.search_text(buffer, search_range, regex)) {
        val next = range.start - line_start
        if (last < next) s ++= style.make_text(line_text.substring(last, next))
        s ++= "<span style=\""
        s ++= highlight_style
        s ++= "\">"
        s ++= style.make_text(line_text.substring(next, next + range.length))
        s ++= "</span>"
        last = range.stop - line_start
      }
      if (last < plain_stop) s ++= style.make_text(line_text.substring(last))
      s ++= "</html>"
    }
    override def toString: String = gui_text
  }

  def search_title(lines: Int = 0): String =
    "Search result" + (if (lines <= 1) "" else " (" + lines + " lines)")

  sealed case class Search_Results(
    buffer: JEditBuffer,
    highlight_style: String,
    pattern: Option[Regex] = None,
    results: List[Search_Result] = Nil
  ) {
    val length: Int = results.length

    def update(start_offset: Int): (Int, Search_Results) =
    pattern match {
      case None => (length, this)
      case Some(regex) =>
        val start_line = buffer.getLineOfOffset(start_offset)
        val results1 = results.takeWhile(result => result.line < start_line)
        val results2 =
          List.from(
            for {
              line <- (start_line until buffer.getLineCount).iterator
              line_range = JEdit_Lib.line_range(buffer, line)
              if JEdit_Lib.can_search_text(buffer, line_range, regex)
            } yield Search_Result(buffer, highlight_style, regex, line, line_range))
        (results1.length, copy(results = results1 ::: results2))
    }

    def update_pattern(new_pattern: Option[Regex]): Option[Search_Results] =
      if (pattern == new_pattern) None
      else Some(copy(pattern = new_pattern, results = Nil).update(0)._2)
  }
}

class Pretty_Text_Area(
  view: View,
  close_action: () => Unit = () => (),
  propagate_keys: Boolean = false
) extends JEditEmbeddedTextArea {
  pretty_text_area =>

  GUI_Thread.require {}

  private var current_font_info: Font_Info = Font_Info.main()
  private var current_output: List[XML.Elem] = Nil
  private var current_base_snapshot = Document.Snapshot.init
  private var current_base_results = Command.Results.empty
  private var current_rendering: JEdit_Rendering =
    JEdit_Rendering(current_base_snapshot, Nil, Command.Results.empty)

  private val future_refresh = Synchronized[Option[Future[Unit]]](None)
  private def fork_refresh(body: => Unit): Future[Unit] =
    future_refresh.change_result({ old =>
      old.foreach(_.cancel())
      val future = Future.fork(body)
      (future, Some(future))
    })

  private val rich_text_area =
    new Rich_Text_Area(view, pretty_text_area, () => current_rendering, close_action,
      get_search_pattern _, () => (), caret_visible = false, enable_hovering = true)

  private var current_search_results =
    Pretty_Text_Area.Search_Results(getBuffer, Pretty_Text_Area.make_highlight_style())

  def get_search_pattern(): Option[Regex] = GUI_Thread.require { current_search_results.pattern }
  def handle_search(search: Pretty_Text_Area.Search_Results): Unit = ()

  def get_background(): Option[Color] = None

  def refresh(): Unit = {
    GUI_Thread.require {}

    getPainter.setFont(current_font_info.font)
    JEdit_Lib.init_font_context(view, getPainter)
    getPainter.setStyles(
      SyntaxUtilities.loadStyles(current_font_info.family, current_font_info.size.round))
    getPainter.setLineExtraSpacing(jEdit.getIntegerProperty("options.textarea.lineSpacing", 0))

    val fold_line_style = new Array[SyntaxStyle](4)
    for (i <- 0 to 3) {
      fold_line_style(i) =
        SyntaxUtilities.parseStyle(
          jEdit.getProperty("view.style.foldLine." + i),
          current_font_info.family, current_font_info.size.round, true)
    }
    getPainter.setFoldLineStyle(fold_line_style)

    getGutter.setForeground(jEdit.getColorProperty("view.gutter.fgColor"))
    getGutter.setBackground(jEdit.getColorProperty("view.gutter.bgColor"))
    get_background().foreach { bg => getPainter.setBackground(bg); getGutter.setBackground(bg) }
    getGutter.setHighlightedForeground(jEdit.getColorProperty("view.gutter.highlightColor"))
    getGutter.setFoldColor(jEdit.getColorProperty("view.gutter.foldColor"))
    getGutter.setFont(jEdit.getFontProperty("view.gutter.font"))
    getGutter.setBorder(0,
      jEdit.getColorProperty("view.gutter.focusBorderColor"),
      jEdit.getColorProperty("view.gutter.noFocusBorderColor"),
      getPainter.getBackground)
    getGutter.setFoldPainter(view.getTextArea.getFoldPainter)
    getGutter.setGutterEnabled(jEdit.getBooleanProperty("view.gutter.enabled"))

    if (getWidth > 0) {
      val metric = JEdit_Lib.font_metric(getPainter)
      val margin = Rich_Text.component_margin(metric, getPainter)
      val output = current_output
      val snapshot = current_base_snapshot
      val results = current_base_results

      lazy val current_refresh: Future[Unit] = fork_refresh(
        {
          val (rich_texts, rendering) =
            try {
              val rich_texts = Rich_Text.format(output, margin, metric, cache = PIDE.cache)
              val rendering = JEdit_Rendering(snapshot, rich_texts, results)
              (rich_texts, rendering)
            }
            catch {
              case exn: Throwable if !Exn.is_interrupt(exn) =>
                Log.log(Log.ERROR, this, exn)
                throw exn
            }

          GUI_Thread.later {
            if (future_refresh.value.contains(current_refresh)) {
              current_rendering = rendering

              val horizontal_offset = pretty_text_area.getHorizontalOffset

              def scroll_to(offset: Int, x: Int = horizontal_offset): Unit = {
                setCaretPosition(offset)
                JEdit_Lib.scroll_to_caret(pretty_text_area)
                pretty_text_area.setHorizontalOffset(x)
              }

              val scroll_bottom = JEdit_Lib.scrollbar_bottom(pretty_text_area)
              val scroll_start = JEdit_Lib.scrollbar_start(pretty_text_area)
              val update_start =
                JEdit_Lib.buffer_edit(getBuffer) {
                  rich_text_area.active_reset()
                  getBuffer.setFoldHandler(new Fold_Handling.Document_Fold_Handler(rendering))
                  JEdit_Lib.set_text(getBuffer, rich_texts.map(_.text))
                }

              if (update_start > 0 && scroll_bottom) {
                scroll_to(JEdit_Lib.bottom_line_offset(getBuffer))
              }
              else if (update_start > scroll_start) scroll_to(scroll_start)
              else scroll_to(0, x = 0)

              val (search_update_start, search_results) =
                current_search_results.update(update_start)
              if (current_search_results != search_results) {
                current_search_results = search_results
                handle_search(search_results)
                pretty_text_area.getPainter.repaint()
              }
            }
          }
        })
      current_refresh
    }
  }

  def resize(font_info: Font_Info): Unit = GUI_Thread.require {
    current_font_info = font_info
    refresh()
  }

  def update(
    base_snapshot: Document.Snapshot,
    base_results: Command.Results,
    output: List[XML.Elem]
  ): Unit = {
    GUI_Thread.require {}
    require(!base_snapshot.is_outdated, "document snapshot outdated")

    current_base_snapshot = base_snapshot
    current_base_results = base_results
    current_output = output.map(Protocol_Message.provide_serial)
    refresh()
  }

  def detach(): Unit = {
    GUI_Thread.require {}
    Info_Dockable(view, current_base_snapshot, current_base_results, current_output)
  }

  def detach_operation: Option[() => Unit] =
    if (current_output.isEmpty) None else Some(() => detach())


  /* search */

  private val search_label: Component = new Label("Search:") {
    tooltip = "Search and highlight output via regular expression"
  }

  private val search_field: Component =
    Component.wrap(new Completion_Popup.History_Text_Field("isabelle-search") {
      private val input_delay =
        Delay.last(PIDE.session.input_delay, gui = true) { search_action(this) }
      getDocument.addDocumentListener(new DocumentListener {
        def changedUpdate(e: DocumentEvent): Unit = input_delay.invoke()
        def insertUpdate(e: DocumentEvent): Unit = input_delay.invoke()
        def removeUpdate(e: DocumentEvent): Unit = input_delay.invoke()
      })
      setColumns(20)
      setToolTipText(search_label.tooltip)
      setFont(GUI.imitate_font(getFont, scale = 1.2))
    })

  private val search_field_foreground = search_field.foreground

  private def search_action(text_field: JTextField): Unit = {
    val (pattern, ok) =
      text_field.getText match {
        case null | "" => (None, true)
        case s =>
          val re = Library.make_regex(s)
          (re, re.isDefined)
      }
    text_field.setForeground(
      if (ok) search_field_foreground
      else current_rendering.color(Rendering.Color.error))
    for (search_results <- current_search_results.update_pattern(pattern)) {
      current_search_results = search_results
      handle_search(search_results)
      refresh()
    }
  }


  /* zoom */

  val zoom_component: Font_Info.Zoom =
    new Font_Info.Zoom { override def changed(): Unit = zoom() }

  def zoom(zoom: Font_Info.Zoom = zoom_component): Unit =
    resize(Font_Info.main(scale = PIDE.options.real("jedit_font_scale"), zoom = zoom))


  /* common GUI components */

  def search_components: List[Component] = List(search_label, search_field)

  def search_zoom_components: List[Component] = List(search_label, search_field, zoom_component)


  /* key handling */

  override def getInputMethodRequests: InputMethodRequests = null

  inputHandlerProvider =
    new DefaultInputHandlerProvider(new TextAreaInputHandler(pretty_text_area) {
      override def getAction(action: String): JEditBeanShellAction =
        pretty_text_area.getActionContext.getAction(action)
      override def processKeyEvent(evt: KeyEvent, from: Int, global: Boolean): Unit = {}
      override def handleKey(key: KeyEventTranslator.Key, dry_run: Boolean): Boolean = false
    })

  addKeyListener(JEdit_Lib.key_listener(
    key_pressed = { (evt: KeyEvent) =>
      val strict_control =
        JEdit_Lib.command_modifier(evt) && !JEdit_Lib.shift_modifier(evt)

      evt.getKeyCode match {
        case KeyEvent.VK_C | KeyEvent.VK_INSERT
        if strict_control && pretty_text_area.getSelectionCount != 0 =>
          Registers.copy(pretty_text_area, '$')
          evt.consume()

        case KeyEvent.VK_A
        if strict_control =>
          pretty_text_area.selectAll()
          evt.consume()

        case KeyEvent.VK_ESCAPE =>
          if (Isabelle.dismissed_popups(view)) evt.consume()
          else if (getSelectionCount != 0) { selectNone(); evt.consume() }

        case _ =>
      }
      if (propagate_keys) JEdit_Lib.propagate_key(view, evt)
    },
    key_typed = { (evt: KeyEvent) =>
      if (propagate_keys) JEdit_Lib.propagate_key(view, evt)
    })
  )


  /* init */

  getPainter.setStructureHighlightEnabled(false)
  getPainter.setLineHighlightEnabled(false)

  getBuffer.setTokenMarker(Isabelle.mode_token_marker("isabelle-output").get)
  getBuffer.setStringProperty("noWordSep", Symbol.decode("""_'?\<^sub>"""))

  rich_text_area.activate()
}
