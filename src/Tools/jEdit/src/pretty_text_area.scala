/*  Title:      Tools/jEdit/src/pretty_text_area.scala
    Author:     Makarius

GUI component for pretty-printed text with markup, rendered like jEdit
text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Font, Toolkit, Window}
import java.awt.event.KeyEvent
import javax.swing.JTextField
import javax.swing.event.{DocumentListener, DocumentEvent}

import java.util.concurrent.{Future => JFuture}

import scala.swing.{Label, Component}
import scala.util.matching.Regex

import org.gjt.sp.jedit.{jEdit, View, Registers}
import org.gjt.sp.jedit.textarea.{AntiAlias, JEditEmbeddedTextArea}
import org.gjt.sp.jedit.syntax.SyntaxStyle
import org.gjt.sp.util.{SyntaxUtilities, Log}


object Pretty_Text_Area
{
  /* auxiliary */

  private def document_state(base_snapshot: Document.Snapshot, base_results: Command.Results,
    formatted_body: XML.Body): (String, Document.State) =
  {
    val command = Command.rich_text(Document_ID.make(), base_results, formatted_body)
    val node_name = command.node_name
    val edits: List[Document.Edit_Text] =
      List(node_name -> Document.Node.Edits(List(Text.Edit.insert(0, command.source))))

    val state0 = base_snapshot.state.define_command(command)
    val version0 = base_snapshot.version
    val nodes0 = version0.nodes

    val nodes1 = nodes0 + (node_name -> nodes0(node_name).update_commands(Linear_Set(command)))
    val version1 = Document.Version.make(version0.syntax, nodes1)
    val state1 =
      state0.continue_history(Future.value(version0), edits, Future.value(version1))
        .define_version(version1, state0.the_assignment(version0))
        .assign(version1.id, List(command.id -> List(Document_ID.make())))._2

    (command.source, state1)
  }

  private def text_rendering(base_snapshot: Document.Snapshot, base_results: Command.Results,
    formatted_body: XML.Body): (String, Rendering) =
  {
    val (text, state) = document_state(base_snapshot, base_results, formatted_body)
    val rendering = Rendering(state.snapshot(), PIDE.options.value)
    (text, rendering)
  }
}

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
  private var current_rendering: Rendering =
    Pretty_Text_Area.text_rendering(current_base_snapshot, current_base_results, Nil)._2
  private var future_rendering: Option[JFuture[Unit]] = None

  private val rich_text_area =
    new Rich_Text_Area(view, text_area, () => current_rendering, close_action,
      get_search_pattern _, caret_visible = false, enable_hovering = true)

  private var current_search_pattern: Option[Regex] = None
  def get_search_pattern(): Option[Regex] = GUI_Thread.require { current_search_pattern }

  def get_background(): Option[Color] = None

  def refresh()
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
    get_background().map(bg => { getPainter.setBackground(bg); getGutter.setBackground(bg) })
    getGutter.setHighlightedForeground(jEdit.getColorProperty("view.gutter.highlightColor"))
    getGutter.setFoldColor(jEdit.getColorProperty("view.gutter.foldColor"))
    getGutter.setFont(jEdit.getFontProperty("view.gutter.font"))
    getGutter.setBorder(0,
      jEdit.getColorProperty("view.gutter.focusBorderColor"),
      jEdit.getColorProperty("view.gutter.noFocusBorderColor"),
      getPainter.getBackground)
    getGutter.setFoldPainter(getFoldPainter)
    getGutter.setGutterEnabled(jEdit.getBooleanProperty("view.gutter.enabled"))

    if (getWidth > 0) {
      val metric = JEdit_Lib.pretty_metric(getPainter)
      val margin = (getPainter.getWidth.toDouble / metric.unit) max 20.0

      val base_snapshot = current_base_snapshot
      val base_results = current_base_results
      val formatted_body = Pretty.formatted(current_body, margin, metric)

      future_rendering.map(_.cancel(true))
      future_rendering =
        Some(Simple_Thread.submit_task {
          val (text, rendering) =
            try { Pretty_Text_Area.text_rendering(base_snapshot, base_results, formatted_body) }
            catch { case exn: Throwable => Log.log(Log.ERROR, this, exn); throw exn }
          Exn.Interrupt.expose()

          GUI_Thread.later {
            current_rendering = rendering
            JEdit_Lib.buffer_edit(getBuffer) {
              rich_text_area.active_reset()
              getBuffer.setReadOnly(false)
              getBuffer.setFoldHandler(new Fold_Handling.Document_Fold_Handler(rendering))
              setText(text)
              setCaretPosition(0)
              getBuffer.setReadOnly(true)
            }
          }
        })
    }
  }

  def resize(font_info: Font_Info)
  {
    GUI_Thread.require {}

    current_font_info = font_info
    refresh()
  }

  def update(base_snapshot: Document.Snapshot, base_results: Command.Results, body: XML.Body)
  {
    GUI_Thread.require {}
    require(!base_snapshot.is_outdated)

    current_base_snapshot = base_snapshot
    current_base_results = base_results
    current_body = body
    refresh()
  }

  def detach
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
          GUI_Thread.delay_last(PIDE.options.seconds("editor_input_delay")) {
            search_action(this)
          }
        getDocument.addDocumentListener(new DocumentListener {
          def changedUpdate(e: DocumentEvent) { input_delay.invoke() }
          def insertUpdate(e: DocumentEvent) { input_delay.invoke() }
          def removeUpdate(e: DocumentEvent) { input_delay.invoke() }
        })
        setColumns(20)
        setToolTipText(search_label.tooltip)
        setFont(GUI.imitate_font(Font_Info.main_family(), getFont, 1.2))
      })

  private val search_field_foreground = search_field.foreground

  private def search_action(text_field: JTextField)
  {
    val (pattern, ok) =
      text_field.getText match {
        case null | "" => (None, true)
        case s =>
          try { (Some(new Regex(s)), true) }
          catch { case ERROR(_) => (None, false) }
      }
    if (current_search_pattern != pattern) {
      current_search_pattern = pattern
      text_area.getPainter.repaint()
    }
    text_field.setForeground(
      if (ok) search_field_foreground else current_rendering.error_color)
  }


  /* key handling */

  addKeyListener(JEdit_Lib.key_listener(
    key_pressed = (evt: KeyEvent) =>
      {
        evt.getKeyCode match {
          case KeyEvent.VK_C
          if (evt.getModifiers & Toolkit.getDefaultToolkit.getMenuShortcutKeyMask) != 0 &&
              text_area.getSelectionCount != 0 =>
            Registers.copy(text_area, '$')
            evt.consume

          case KeyEvent.VK_A
          if (evt.getModifiers & Toolkit.getDefaultToolkit.getMenuShortcutKeyMask) != 0 =>
            text_area.selectAll
            evt.consume

          case KeyEvent.VK_ESCAPE =>
            if (PIDE.dismissed_popups(view)) evt.consume

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

  getBuffer.setTokenMarker(Isabelle.token_marker("isabelle-output").get)
  getBuffer.setReadOnly(true)
  getBuffer.setStringProperty("noWordSep", "_'.?")

  rich_text_area.activate()
}

