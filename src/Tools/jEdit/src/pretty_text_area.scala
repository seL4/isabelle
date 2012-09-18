/*  Title:      Tools/jEdit/src/pretty_text_area.scala
    Author:     Makarius

GUI component for pretty-printed with markup, rendered like jEdit text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Font, FontMetrics}

import org.gjt.sp.jedit.{jEdit, View}
import org.gjt.sp.jedit.textarea.{AntiAlias, JEditEmbeddedTextArea}
import org.gjt.sp.util.SyntaxUtilities

import scala.swing.{BorderPanel, Component}


object Pretty_Text_Area
{
  def document_state(formatted_body: XML.Body): (String, Document.State) =
  {
    val command = Command.rich_text(Document.new_id(), formatted_body)
    val node_name = command.node_name

    val edits: List[Document.Edit_Text] =
      List(node_name -> Document.Node.Edits(List(Text.Edit.insert(0, command.source))))

    val state0 = Document.State.init.define_command(command)
    val version0 = state0.history.tip.version.get_finished
    val nodes0 = version0.nodes

    val nodes1 = nodes0 + (node_name -> nodes0(node_name).update_commands(Linear_Set(command)))
    val version1 = Document.Version.make(version0.syntax, nodes1)
    val state1 =
      state0.continue_history(Future.value(version0), edits, Future.value(version1))._2
        .define_version(version1, state0.the_assignment(version0))
        .assign(version1.id, List(command.id -> Some(Document.new_id())))._2

    (command.source, state1)
  }
}

class Pretty_Text_Area(view: View) extends BorderPanel
{
  Swing_Thread.require()

  private var current_font_metrics: FontMetrics = null
  private var current_font_family = "Dialog"
  private var current_font_size: Int = 12
  private var current_margin: Int = 0
  private var current_body: XML.Body = Nil
  private var current_rendering: Isabelle_Rendering = text_rendering()._2

  val text_area = new JEditEmbeddedTextArea
  val rich_text_area = new Rich_Text_Area(view, text_area, () => current_rendering)

  private def text_rendering(): (String, Isabelle_Rendering) =
  {
    Swing_Thread.require()

    val body =
      Pretty.formatted(current_body, current_margin, Pretty.font_metric(current_font_metrics))
    val (text, state) = Pretty_Text_Area.document_state(body)
    val rendering = Isabelle_Rendering(state.snapshot(), Isabelle.options.value)

    (text, rendering)
  }

  def refresh()
  {
    Swing_Thread.require()

    val font = new Font(current_font_family, Font.PLAIN, current_font_size)

    val painter = text_area.getPainter
    painter.setFont(font)
    painter.setAntiAlias(new AntiAlias(jEdit.getProperty("view.antiAlias")))
    painter.setStyles(SyntaxUtilities.loadStyles(current_font_family, current_font_size))

    current_font_metrics = painter.getFontMetrics(font)
    current_margin = (size.width / (current_font_metrics.charWidth(Pretty.spc) max 1) - 4) max 20

    val (text, rendering) = text_rendering()
    current_rendering = rendering

    val buffer = text_area.getBuffer
    try {
      buffer.beginCompoundEdit
      text_area.setText(text)
      text_area.setCaretPosition(0)
    }
    finally {
      buffer.endCompoundEdit
    }
  }

  def resize(font_family: String, font_size: Int)
  {
    Swing_Thread.require()

    current_font_family = font_family
    current_font_size = font_size
    refresh()
  }

  def update(body: XML.Body)
  {
    Swing_Thread.require()

    current_body = body
    refresh()
  }

  rich_text_area.activate()
  layout(Component.wrap(text_area)) = BorderPanel.Position.Center
}

