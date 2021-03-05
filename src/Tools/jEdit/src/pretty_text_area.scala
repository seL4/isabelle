/*  Title:      Tools/jEdit/src/pretty_text_area.scala
    Author:     Makarius

GUI component for pretty-printed text with markup, rendered like jEdit
text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Font, Toolkit, Window}
import java.awt.event.{InputEvent, KeyEvent}
import java.awt.im.InputMethodRequests
import javax.swing.JTextField
import javax.swing.event.{DocumentListener, DocumentEvent}

import scala.swing.{Label, Component}
import scala.util.matching.Regex

import org.gjt.sp.jedit.{jEdit, View, Registers, JEditBeanShellAction}
import org.gjt.sp.jedit.input.{DefaultInputHandlerProvider, TextAreaInputHandler}
import org.gjt.sp.jedit.textarea.{AntiAlias, JEditEmbeddedTextArea}
import org.gjt.sp.jedit.syntax.SyntaxStyle
import org.gjt.sp.jedit.gui.KeyEventTranslator
import org.gjt.sp.util.{SyntaxUtilities, Log}


class Pretty_Text_Area(
  view: View,
  close_action: () => Unit = () => (),
  propagate_keys: Boolean = false) extends JEditEmbeddedTextArea
{
  text_area =>

  GUI_Thread.require {}

  private var current_font_info: Font_Info = Font_Info.main()
  private var current_body: XML.Body = Nil
  private var current_base_snapshot = Document.Snapshot.init
  private var current_base_results = Command.Results.empty
  private var current_rendering: JEdit_Rendering =
    JEdit_Rendering.text(current_base_snapshot, Nil)._2
  private var future_refresh: Option[Future[Unit]] = None

  private val rich_text_area =
    new Rich_Text_Area(view, text_area, () => current_rendering, close_action,
      get_search_pattern _, () => (), caret_visible = false, enable_hovering = true)

  private var current_search_pattern: Option[Regex] = None
  def get_search_pattern(): Option[Regex] = GUI_Thread.require { current_search_pattern }

  def get_background(): Option[Color] = None

  def refresh(): Unit =
  {
    GUI_Thread.require {}

    val font = current_font_info.font
    getPainter.setFont(font)
    getPainter.setAntiAlias(new AntiAlias(jEdit.getProperty("view.antiAlias")))
    getPainter.setFractionalFontMetricsEnabled(jEdit.getBooleanProperty("view.fracFontMetrics"))
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
    get_background().foreach(bg => { getPainter.setBackground(bg); getGutter.setBackground(bg) })
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
      val metric = JEdit_Lib.pretty_metric(getPainter)
      val margin = ((getPainter.getWidth.toDouble / metric.unit) max 20.0).floor

      val snapshot = current_base_snapshot
      val results = current_base_results
      val formatted_body = Pretty.formatted(current_body, margin = margin, metric = metric)

      future_refresh.foreach(_.cancel())
      future_refresh =
        Some(Future.fork {
          val (text, rendering) =
            try { JEdit_Rendering.text(snapshot, formatted_body, results = results) }
            catch { case exn: Throwable => Log.log(Log.ERROR, this, exn); throw exn }
          Exn.Interrupt.expose()

          GUI_Thread.later {
            current_rendering = rendering
            JEdit_Lib.buffer_edit(getBuffer) {
              rich_text_area.active_reset()
              getBuffer.setFoldHandler(new Fold_Handling.Document_Fold_Handler(rendering))
              JEdit_Lib.buffer_undo_in_progress(getBuffer, setText(text))
              setCaretPosition(0)
            }
          }
        })
    }
  }

  def resize(font_info: Font_Info): Unit =
  {
    GUI_Thread.require {}

    current_font_info = font_info
    refresh()
  }

  def update(
    base_snapshot: Document.Snapshot, base_results: Command.Results, body: XML.Body): Unit =
  {
    GUI_Thread.require {}
    require(!base_snapshot.is_outdated, "document snapshot outdated")

    current_base_snapshot = base_snapshot
    current_base_results = base_results
    current_body = body
    refresh()
  }

  def detach: Unit =
  {
    GUI_Thread.require {}
    Info_Dockable(view, current_base_snapshot, current_base_results, current_body)
  }

  def detach_operation: Option[() => Unit] =
    if (current_body.isEmpty) None else Some(() => detach)


  /* common GUI components */

  val search_label: Component = new Label("Search:") {
    tooltip = "Search and highlight output via regular expression"
  }

  val search_field: Component =
    Component.wrap(new Completion_Popup.History_Text_Field("isabelle-search")
      {
        private val input_delay =
          Delay.last(PIDE.options.seconds("editor_input_delay"), gui = true) {
            search_action(this)
          }
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

  private def search_action(text_field: JTextField): Unit =
  {
    val (pattern, ok) =
      text_field.getText match {
        case null | "" => (None, true)
        case s =>
          val re = Library.make_regex(s)
          (re, re.isDefined)
      }
    if (current_search_pattern != pattern) {
      current_search_pattern = pattern
      text_area.getPainter.repaint()
    }
    text_field.setForeground(
      if (ok) search_field_foreground
      else current_rendering.color(Rendering.Color.error))
  }


  /* key handling */

  override def getInputMethodRequests: InputMethodRequests = null

  inputHandlerProvider =
    new DefaultInputHandlerProvider(new TextAreaInputHandler(text_area) {
      override def getAction(action: String): JEditBeanShellAction =
        text_area.getActionContext.getAction(action)
      override def processKeyEvent(evt: KeyEvent, from: Int, global: Boolean): Unit = {}
      override def handleKey(key: KeyEventTranslator.Key, dry_run: Boolean): Boolean = false
    })

  addKeyListener(JEdit_Lib.key_listener(
    key_pressed = (evt: KeyEvent) =>
      {
        val strict_control =
          JEdit_Lib.command_modifier(evt) && !JEdit_Lib.shift_modifier(evt)

        evt.getKeyCode match {
          case KeyEvent.VK_C | KeyEvent.VK_INSERT
          if strict_control && text_area.getSelectionCount != 0 =>
            Registers.copy(text_area, '$')
            evt.consume

          case KeyEvent.VK_A
          if strict_control =>
            text_area.selectAll
            evt.consume

          case KeyEvent.VK_ESCAPE =>
            if (Isabelle.dismissed_popups(view)) evt.consume

          case _ =>
        }
        if (propagate_keys) JEdit_Lib.propagate_key(view, evt)
      },
    key_typed = (evt: KeyEvent) =>
      {
        if (propagate_keys) JEdit_Lib.propagate_key(view, evt)
      }
    )
  )


  /* init */

  getPainter.setStructureHighlightEnabled(false)
  getPainter.setLineHighlightEnabled(false)

  getBuffer.setTokenMarker(Isabelle.mode_token_marker("isabelle-output").get)
  getBuffer.setStringProperty("noWordSep", "_'?⇩")

  rich_text_area.activate()
}
