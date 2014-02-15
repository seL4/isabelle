/*  Title:      Tools/jEdit/src/isabelle.scala
    Author:     Makarius

Global configuration and convenience operations for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import scala.swing.CheckBox
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.textarea.JEditTextArea
import org.gjt.sp.jedit.gui.{DockableWindowManager, CompleteWord}


object Isabelle
{
  /* editor modes */

  val modes =
    List(
      "isabelle",         // theory source
      "isabelle-ml",      // ML source
      "isabelle-markup",  // SideKick markup tree
      "isabelle-news",    // NEWS
      "isabelle-options", // etc/options
      "isabelle-output",  // pretty text area output
      "isabelle-root")    // session ROOT

  private lazy val symbols_syntax = Outer_Syntax.init().no_tokens

  def mode_syntax(name: String): Option[Outer_Syntax] =
    name match {
      case "isabelle" | "isabelle-markup" =>
        val syntax = PIDE.session.recent_syntax
        if (syntax == Outer_Syntax.empty) None else Some(syntax)
      case "isabelle-options" => Some(Options.options_syntax)
      case "isabelle-root" => Some(Build.root_syntax)
      case "isabelle-ml" | "isabelle-news" => Some(symbols_syntax)
      case "isabelle-output" => None
      case _ => None
    }


  /* token markers */

  private val markers =
    Map(modes.map(name => (name, new Token_Markup.Marker(name))): _*)

  def token_marker(name: String): Option[Token_Markup.Marker] = markers.get(name)


  /* dockable windows */

  private def wm(view: View): DockableWindowManager = view.getDockableWindowManager

  def docked_theories(view: View): Option[Theories_Dockable] =
    wm(view).getDockableWindow("isabelle-theories") match {
      case dockable: Theories_Dockable => Some(dockable)
      case _ => None
    }

  def docked_timing(view: View): Option[Timing_Dockable] =
    wm(view).getDockableWindow("isabelle-timing") match {
      case dockable: Timing_Dockable => Some(dockable)
      case _ => None
    }

  def docked_output(view: View): Option[Output_Dockable] =
    wm(view).getDockableWindow("isabelle-output") match {
      case dockable: Output_Dockable => Some(dockable)
      case _ => None
    }

  def docked_raw_output(view: View): Option[Raw_Output_Dockable] =
    wm(view).getDockableWindow("isabelle-raw-output") match {
      case dockable: Raw_Output_Dockable => Some(dockable)
      case _ => None
    }

  def docked_simplifier_trace(view: View): Option[Simplifier_Trace_Dockable] =
    wm(view).getDockableWindow("isabelle-simp-trace") match {
      case dockable: Simplifier_Trace_Dockable => Some(dockable)
      case _ => None
    }

  def docked_protocol(view: View): Option[Protocol_Dockable] =
    wm(view).getDockableWindow("isabelle-protocol") match {
      case dockable: Protocol_Dockable => Some(dockable)
      case _ => None
    }

  def docked_monitor(view: View): Option[Monitor_Dockable] =
    wm(view).getDockableWindow("isabelle-monitor") match {
      case dockable: Monitor_Dockable => Some(dockable)
      case _ => None
    }


  /* continuous checking */

  private val CONTINUOUS_CHECKING = "editor_continuous_checking"

  def continuous_checking: Boolean = PIDE.options.bool(CONTINUOUS_CHECKING)

  def continuous_checking_=(b: Boolean)
  {
    Swing_Thread.require()

    if (continuous_checking != b) {
      PIDE.options.bool(CONTINUOUS_CHECKING) = b
      PIDE.options_changed()
      PIDE.editor.flush()
    }
  }

  def set_continuous_checking() { continuous_checking = true }
  def reset_continuous_checking() { continuous_checking = false }
  def toggle_continuous_checking() { continuous_checking = !continuous_checking }

  class Continuous_Checking extends CheckBox("Continuous checking")
  {
    tooltip = "Continuous checking of proof document (visible and required parts)"
    reactions += { case ButtonClicked(_) => continuous_checking = selected }
    def load() { selected = continuous_checking }
    load()
  }


  /* required document nodes */

  private def node_required_update(view: View, toggle: Boolean = false, set: Boolean = false)
  {
    Swing_Thread.require()
    PIDE.document_model(view.getBuffer) match {
      case Some(model) =>
        model.node_required = (if (toggle) !model.node_required else set)
      case None =>
    }
  }

  def set_node_required(view: View) { node_required_update(view, set = true) }
  def reset_node_required(view: View) { node_required_update(view, set = false) }
  def toggle_node_required(view: View) { node_required_update(view, toggle = true) }


  /* font size */

  def reset_font_size(view: View): Unit =
    Rendering.font_size_change(view, _ => PIDE.options.int("jedit_reset_font_size"))

  def increase_font_size(view: View): Unit =
    Rendering.font_size_change(view, i => i + ((i / 10) max 1))

  def decrease_font_size(view: View): Unit =
    Rendering.font_size_change(view, i => i - ((i / 10) max 1))


  /* structured edits */

  def insert_line_padding(text_area: JEditTextArea, text: String)
  {
    val buffer = text_area.getBuffer
    JEdit_Lib.buffer_edit(buffer) {
      val text1 =
        if (text_area.getSelectionCount == 0) {
          def pad(range: Text.Range): String =
            if (JEdit_Lib.try_get_text(buffer, range) == Some("\n")) "" else "\n"

          val caret = JEdit_Lib.point_range(buffer, text_area.getCaretPosition)
          val before_caret = JEdit_Lib.point_range(buffer, caret.start - 1)
          pad(before_caret) + text + pad(caret)
        }
        else text
      text_area.setSelectedText(text1)
    }
  }

  def edit_command(
    snapshot: Document.Snapshot,
    buffer: Buffer,
    padding: Boolean,
    id: Document_ID.Generic,
    s: String)
  {
    if (!snapshot.is_outdated) {
      snapshot.state.find_command(snapshot.version, id) match {
        case Some((node, command)) =>
          node.command_start(command) match {
            case Some(start) =>
              JEdit_Lib.buffer_edit(buffer) {
                val range = command.proper_range + start
                if (padding) {
                  buffer.insert(start + range.length, "\n" + s)
                }
                else {
                  buffer.remove(start, range.length)
                  buffer.insert(start, s)
                }
              }
            case None =>
          }
        case None =>
      }
    }
  }


  /* completion */

  def complete(view: View)
  {
    Completion_Popup.Text_Area(view.getTextArea) match {
      case Some(text_area_completion) =>
        text_area_completion.action(immediate = true, explicit = true)
      case None => CompleteWord.completeWord(view)
    }
  }


  /* control styles */

  def control_sub(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.sub_decoded) }

  def control_sup(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.sup_decoded) }

  def control_bold(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.bold_decoded) }

  def control_reset(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, "") }


  /* block styles */

  private def enclose_input(text_area: JEditTextArea, s1: String, s2: String)
  {
    s1.foreach(text_area.userInput(_))
    s2.foreach(text_area.userInput(_))
    s2.foreach(_ => text_area.goToPrevCharacter(false))
  }

  def input_bsub(text_area: JEditTextArea)
  { enclose_input(text_area, Symbol.bsub_decoded, Symbol.esub_decoded) }

  def input_bsup(text_area: JEditTextArea)
  { enclose_input(text_area, Symbol.bsup_decoded, Symbol.esup_decoded) }
}

