/*  Title:      Tools/jEdit/src/pretty_text_area.scala
    Author:     Makarius

GUI component for pretty-printed with markup, rendered like jEdit text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Font, FontMetrics, Toolkit}
import java.awt.event.{ActionListener, ActionEvent, KeyEvent}
import javax.swing.{KeyStroke, JComponent}

import org.gjt.sp.jedit.{jEdit, View, Registers}
import org.gjt.sp.jedit.textarea.{AntiAlias, JEditEmbeddedTextArea}
import org.gjt.sp.util.SyntaxUtilities


object Pretty_Text_Area
{
  private def text_rendering(base_snapshot: Document.Snapshot, formatted_body: XML.Body):
    (String, Isabelle_Rendering) =
  {
    val (text, state) = Pretty_Text_Area.document_state(base_snapshot, formatted_body)
    val rendering = Isabelle_Rendering(state.snapshot(), Isabelle.options.value)
    (text, rendering)
  }

  private def document_state(base_snapshot: Document.Snapshot, formatted_body: XML.Body)
    : (String, Document.State) =
  {
    val command = Command.rich_text(Document.new_id(), formatted_body)
    val node_name = command.node_name
    val edits: List[Document.Edit_Text] =
      List(node_name -> Document.Node.Edits(List(Text.Edit.insert(0, command.source))))

    val state0 = base_snapshot.state.define_command(command)
    val version0 = base_snapshot.version
    val nodes0 = version0.nodes

    assert(nodes0(node_name).commands.isEmpty)

    val nodes1 = nodes0 + (node_name -> nodes0(node_name).update_commands(Linear_Set(command)))
    val version1 = Document.Version.make(version0.syntax, nodes1)
    val state1 =
      state0.continue_history(Future.value(version0), edits, Future.value(version1))._2
        .define_version(version1, state0.the_assignment(version0))
        .assign(version1.id, List(command.id -> Some(Document.new_id())))._2

    (command.source, state1)
  }
}

class Pretty_Text_Area(view: View) extends JEditEmbeddedTextArea
{
  text_area =>

  Swing_Thread.require()

  private var current_font_family = "Dialog"
  private var current_font_size: Int = 12
  private var current_body: XML.Body = Nil
  private var current_base_snapshot = Document.State.init.snapshot()
  private var current_rendering: Isabelle_Rendering =
    Pretty_Text_Area.text_rendering(current_base_snapshot, Nil)._2
  private var future_rendering: Option[java.util.concurrent.Future[Unit]] = None

  private val rich_text_area = new Rich_Text_Area(view, text_area, () => current_rendering)

  def refresh()
  {
    Swing_Thread.require()

    val font = new Font(current_font_family, Font.PLAIN, current_font_size)
    getPainter.setFont(font)
    getPainter.setAntiAlias(new AntiAlias(jEdit.getProperty("view.antiAlias")))
    getPainter.setStyles(SyntaxUtilities.loadStyles(current_font_family, current_font_size))

    val font_metrics = getPainter.getFontMetrics(font)
    val margin = (getWidth / (font_metrics.charWidth(Pretty.spc) max 1) - 4) max 20

    val base_snapshot = current_base_snapshot
    val formatted_body = Pretty.formatted(current_body, margin, Pretty.font_metric(font_metrics))

    future_rendering.map(_.cancel(true))
    future_rendering = Some(default_thread_pool.submit(() =>
      {
        val (text, rendering) = Pretty_Text_Area.text_rendering(base_snapshot, formatted_body)
        Simple_Thread.interrupted_exception()

        Swing_Thread.later {
          current_rendering = rendering

          try {
            getBuffer.beginCompoundEdit
            getBuffer.setReadOnly(false)
            setText(text)
            setCaretPosition(0)
            getBuffer.setReadOnly(true)
          }
          finally {
            getBuffer.endCompoundEdit
          }
        }
      }))
  }

  def resize(font_family: String, font_size: Int)
  {
    Swing_Thread.require()

    current_font_family = font_family
    current_font_size = font_size
    refresh()
  }

  def update(base_snapshot: Document.Snapshot, body: XML.Body)
  {
    Swing_Thread.require()
    require(!base_snapshot.is_outdated)

    current_base_snapshot = base_snapshot
    current_body = body
    refresh()
  }


  /* keyboard actions */

  private val action_listener = new ActionListener {
    def actionPerformed(e: ActionEvent) {
      e.getActionCommand match {
        case "copy" => Registers.copy(text_area, '$')
        case _ =>
      }
    }
  }

  registerKeyboardAction(action_listener, "copy",
    KeyStroke.getKeyStroke(KeyEvent.VK_COPY, 0), JComponent.WHEN_FOCUSED)
  registerKeyboardAction(action_listener, "copy",
    KeyStroke.getKeyStroke(KeyEvent.VK_C,
      Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()), JComponent.WHEN_FOCUSED)


  /* init */

  override def isCaretVisible: Boolean = false

  getPainter.setStructureHighlightEnabled(false)
  getPainter.setLineHighlightEnabled(false)

  getBuffer.setTokenMarker(new Token_Markup.Marker(true, None))
  getBuffer.setReadOnly(true)

  rich_text_area.activate()
}

