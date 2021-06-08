/*  Title:      Tools/jEdit/src/isabelle.scala
    Author:     Makarius

Global configuration and convenience operations for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Point, Frame, Rectangle}

import scala.swing.CheckBox
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.{jEdit, View, Buffer, EditBus}
import org.gjt.sp.jedit.msg.ViewUpdate
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, StructureMatcher, Selection}
import org.gjt.sp.jedit.syntax.TokenMarker
import org.gjt.sp.jedit.indent.IndentRule
import org.gjt.sp.jedit.gui.{DockableWindowManager, CompleteWord}
import org.jedit.options.CombinedOptions


object Isabelle
{
  /* editor modes */

  val modes =
    List(
      "isabelle",         // theory source
      "isabelle-ml",      // ML source
      "isabelle-news",    // NEWS
      "isabelle-options", // etc/options
      "isabelle-output",  // pretty text area output
      "isabelle-root",    // session ROOT
      "sml")              // Standard ML (not Isabelle/ML)

  private val ml_syntax: Outer_Syntax =
    Outer_Syntax.empty.no_tokens.
      set_language_context(Completion.Language_Context.ML_outer)

  private val sml_syntax: Outer_Syntax =
    Outer_Syntax.empty.no_tokens.
      set_language_context(Completion.Language_Context.SML_outer)

  private val news_syntax: Outer_Syntax =
    Outer_Syntax.empty.no_tokens

  def mode_syntax(mode: String): Option[Outer_Syntax] =
    mode match {
      case "isabelle" => Some(PIDE.resources.session_base.overall_syntax)
      case "isabelle-options" => Some(Options.options_syntax)
      case "isabelle-root" => Some(Sessions.root_syntax)
      case "isabelle-ml" => Some(ml_syntax)
      case "isabelle-news" => Some(news_syntax)
      case "isabelle-output" => None
      case "sml" => Some(sml_syntax)
      case _ => None
    }

  def buffer_syntax(buffer: JEditBuffer): Option[Outer_Syntax] =
    if (buffer == null) None
    else
      (JEdit_Lib.buffer_mode(buffer), Document_Model.get(buffer)) match {
        case ("isabelle", Some(model)) =>
          Some(PIDE.session.recent_syntax(model.node_name))
        case (mode, _) => mode_syntax(mode)
      }


  /* token markers */

  private val mode_markers: Map[String, TokenMarker] =
    Map(modes.map(mode => (mode, new Token_Markup.Marker(mode, None))): _*) +
      ("bibtex" -> new JEdit_Bibtex.Token_Marker)

  def mode_token_marker(mode: String): Option[TokenMarker] = mode_markers.get(mode)

  def buffer_token_marker(buffer: Buffer): Option[TokenMarker] =
  {
    val mode = JEdit_Lib.buffer_mode(buffer)
    if (mode == "isabelle") Some(new Token_Markup.Marker(mode, Some(buffer)))
    else mode_token_marker(mode)
  }


  /* text structure */

  def indent_rule(mode: String): Option[IndentRule] =
    mode match {
      case "isabelle" | "isabelle-options" | "isabelle-root" =>
        Some(Text_Structure.Indent_Rule)
      case _ => None
    }

  def structure_matchers(mode: String): List[StructureMatcher] =
    if (mode == "isabelle") List(Text_Structure.Matcher) else Nil


  /* dockable windows */

  private def wm(view: View): DockableWindowManager = view.getDockableWindowManager

  def debugger_dockable(view: View): Option[Debugger_Dockable] =
    wm(view).getDockableWindow("isabelle-debugger") match {
      case dockable: Debugger_Dockable => Some(dockable)
      case _ => None
    }

  def documentation_dockable(view: View): Option[Documentation_Dockable] =
    wm(view).getDockableWindow("isabelle-documentation") match {
      case dockable: Documentation_Dockable => Some(dockable)
      case _ => None
    }

  def monitor_dockable(view: View): Option[Monitor_Dockable] =
    wm(view).getDockableWindow("isabelle-monitor") match {
      case dockable: Monitor_Dockable => Some(dockable)
      case _ => None
    }

  def output_dockable(view: View): Option[Output_Dockable] =
    wm(view).getDockableWindow("isabelle-output") match {
      case dockable: Output_Dockable => Some(dockable)
      case _ => None
    }

  def protocol_dockable(view: View): Option[Protocol_Dockable] =
    wm(view).getDockableWindow("isabelle-protocol") match {
      case dockable: Protocol_Dockable => Some(dockable)
      case _ => None
    }

  def query_dockable(view: View): Option[Query_Dockable] =
    wm(view).getDockableWindow("isabelle-query") match {
      case dockable: Query_Dockable => Some(dockable)
      case _ => None
    }

  def raw_output_dockable(view: View): Option[Raw_Output_Dockable] =
    wm(view).getDockableWindow("isabelle-raw-output") match {
      case dockable: Raw_Output_Dockable => Some(dockable)
      case _ => None
    }

  def simplifier_trace_dockable(view: View): Option[Simplifier_Trace_Dockable] =
    wm(view).getDockableWindow("isabelle-simplifier-trace") match {
      case dockable: Simplifier_Trace_Dockable => Some(dockable)
      case _ => None
    }

  def sledgehammer_dockable(view: View): Option[Sledgehammer_Dockable] =
    wm(view).getDockableWindow("isabelle-sledgehammer") match {
      case dockable: Sledgehammer_Dockable => Some(dockable)
      case _ => None
    }

  def state_dockable(view: View): Option[State_Dockable] =
    wm(view).getDockableWindow("isabelle-state") match {
      case dockable: State_Dockable => Some(dockable)
      case _ => None
    }

  def symbols_dockable(view: View): Option[Symbols_Dockable] =
    wm(view).getDockableWindow("isabelle-symbols") match {
      case dockable: Symbols_Dockable => Some(dockable)
      case _ => None
    }

  def syslog_dockable(view: View): Option[Syslog_Dockable] =
    wm(view).getDockableWindow("isabelle-syslog") match {
      case dockable: Syslog_Dockable => Some(dockable)
      case _ => None
    }

  def theories_dockable(view: View): Option[Theories_Dockable] =
    wm(view).getDockableWindow("isabelle-theories") match {
      case dockable: Theories_Dockable => Some(dockable)
      case _ => None
    }

  def timing_dockable(view: View): Option[Timing_Dockable] =
    wm(view).getDockableWindow("isabelle-timing") match {
      case dockable: Timing_Dockable => Some(dockable)
      case _ => None
    }


  /* continuous checking */

  private val CONTINUOUS_CHECKING = "editor_continuous_checking"

  def continuous_checking: Boolean = PIDE.options.bool(CONTINUOUS_CHECKING)
  def continuous_checking_=(b: Boolean): Unit =
    GUI_Thread.require {
      if (continuous_checking != b) {
        PIDE.options.bool(CONTINUOUS_CHECKING) = b
        PIDE.session.update_options(PIDE.options.value)
        PIDE.plugin.deps_changed()
      }
    }

  def set_continuous_checking(): Unit = { continuous_checking = true }
  def reset_continuous_checking(): Unit = { continuous_checking = false }
  def toggle_continuous_checking(): Unit = { continuous_checking = !continuous_checking }

  class Continuous_Checking extends CheckBox("Continuous checking")
  {
    tooltip = "Continuous checking of proof document (visible and required parts)"
    reactions += { case ButtonClicked(_) => continuous_checking = selected }
    def load(): Unit = { selected = continuous_checking }
    load()
  }


  /* update state */

  def update_state(view: View): Unit =
    state_dockable(view).foreach(_.update_request())


  /* required document nodes */

  def set_node_required(view: View): Unit = Document_Model.view_node_required(view, set = true)
  def reset_node_required(view: View): Unit = Document_Model.view_node_required(view, set = false)
  def toggle_node_required(view: View): Unit = Document_Model.view_node_required(view, toggle = true)


  /* full screen */

  // see toggleFullScreen() method in jEdit/org/gjt/sp/jedit/View.java
  def toggle_full_screen(view: View): Unit =
  {
    if (PIDE.options.bool("jedit_toggle_full_screen") ||
        Untyped.get[Boolean](view, "fullScreenMode")) view.toggleFullScreen()
    else {
      Untyped.set[Boolean](view, "fullScreenMode", true)
      val screen = GUI.screen_size(view)
      view.dispose()

      view.updateFullScreenProps()
      Untyped.set[Rectangle](view, "windowedBounds", view.getBounds)
      view.setUndecorated(true)
      view.setBounds(screen.full_screen_bounds)
      view.validate()

      view.setVisible(true)
      view.toFront()
      view.closeAllMenus()
      view.getEditPane.getTextArea.requestFocus()
      EditBus.send(new ViewUpdate(view, ViewUpdate.FULL_SCREEN_TOGGLED))
    }
  }


  /* font size */

  def reset_font_size(): Unit =
    Font_Info.main_change.reset(PIDE.options.int("jedit_reset_font_size").toFloat)
  def increase_font_size(): Unit = Font_Info.main_change.step(1)
  def decrease_font_size(): Unit = Font_Info.main_change.step(-1)


  /* structured edits */

  def indent_enabled(buffer: JEditBuffer, option: String): Boolean =
    indent_rule(JEdit_Lib.buffer_mode(buffer)).isDefined &&
    buffer.getStringProperty("autoIndent") == "full" &&
    PIDE.options.bool(option)

  def indent_input(text_area: TextArea): Unit =
  {
    val buffer = text_area.getBuffer
    val line = text_area.getCaretLine
    val caret = text_area.getCaretPosition

    if (text_area.isEditable && indent_enabled(buffer, "jedit_indent_input")) {
      buffer_syntax(buffer) match {
        case Some(syntax) =>
          val nav = new Text_Structure.Navigator(syntax, buffer, true)
          nav.iterator(line, 1).nextOption() match {
            case Some(Text.Info(range, tok))
            if range.stop == caret && syntax.keywords.is_indent_command(tok) =>
              buffer.indentLine(line, true)
            case _ =>
          }
        case None =>
      }
    }
  }

  def newline(text_area: TextArea): Unit =
  {
    if (!text_area.isEditable()) text_area.getToolkit().beep()
    else {
      val buffer = text_area.getBuffer
      val line = text_area.getCaretLine
      val caret = text_area.getCaretPosition

      def nl: Unit = text_area.userInput('\n')

      if (indent_enabled(buffer, "jedit_indent_newline")) {
        buffer_syntax(buffer) match {
          case Some(syntax) =>
            val keywords = syntax.keywords

            val (toks1, toks2) = Text_Structure.split_line_content(buffer, keywords, line, caret)

            if (toks1.isEmpty) buffer.removeTrailingWhiteSpace(Array(line))
            else if (keywords.is_indent_command(toks1.head)) buffer.indentLine(line, true)

            if (toks2.isEmpty || keywords.is_indent_command(toks2.head)) {
              text_area.setSelectedText("\n")
              if (!buffer.indentLine(line + 1, true)) text_area.goToStartOfWhiteSpace(false)
            }
            else nl
          case None => nl
        }
      }
      else nl
    }
  }

  def insert_line_padding(text_area: JEditTextArea, text: String): Unit =
  {
    val buffer = text_area.getBuffer
    JEdit_Lib.buffer_edit(buffer) {
      val text1 =
        if (text_area.getSelectionCount == 0) {
          def pad(range: Text.Range): String =
            if (JEdit_Lib.get_text(buffer, range) == Some("\n")) "" else "\n"

          val caret = JEdit_Lib.caret_range(text_area)
          val before_caret = JEdit_Lib.point_range(buffer, caret.start - 1)
          pad(before_caret) + text + pad(caret)
        }
        else text
      text_area.setSelectedText(text1)
    }
  }

  def edit_command(
    snapshot: Document.Snapshot,
    text_area: TextArea,
    padding: Boolean,
    id: Document_ID.Generic,
    text: String): Unit =
  {
    val buffer = text_area.getBuffer
    if (!snapshot.is_outdated && text != "") {
      (snapshot.find_command(id), Document_Model.get(buffer)) match {
        case (Some((node, command)), Some(model)) if command.node_name == model.node_name =>
          node.command_start(command) match {
            case Some(start) =>
              JEdit_Lib.buffer_edit(buffer) {
                val range = command.core_range + start
                JEdit_Lib.buffer_edit(buffer) {
                  if (padding) {
                    text_area.moveCaretPosition(start + range.length)
                    val start_line = text_area.getCaretLine + 1
                    text_area.setSelectedText("\n" + text)
                    val end_line = text_area.getCaretLine
                    for (line <- start_line to end_line) {
                      Token_Markup.Line_Context.refresh(buffer, line)
                      buffer.indentLine(line, true)
                    }
                  }
                  else {
                    buffer.remove(start, range.length)
                    text_area.moveCaretPosition(start)
                    text_area.setSelectedText(text)
                  }
                }
              }
            case None =>
          }
        case _ =>
      }
    }
  }


  /* formal entities */

  def goto_entity(view: View): Unit =
  {
    val text_area = view.getTextArea
    for {
      doc_view <- Document_View.get(text_area)
      rendering = doc_view.get_rendering()
      caret_range = JEdit_Lib.caret_range(text_area)
      link <- rendering.hyperlink_entity(caret_range)
    } link.info.follow(view)
  }

  def select_entity(text_area: JEditTextArea): Unit =
  {
    for (doc_view <- Document_View.get(text_area)) {
      val rendering = doc_view.get_rendering()
      val caret_range = JEdit_Lib.caret_range(text_area)
      val buffer_range = JEdit_Lib.buffer_range(text_area.getBuffer)
      val active_focus = rendering.caret_focus_ranges(caret_range, buffer_range)
      if (active_focus.nonEmpty) {
        text_area.selectNone()
        for (r <- active_focus)
          text_area.addToSelection(new Selection.Range(r.start, r.stop))
      }
    }
  }


  /* completion */

  def complete(view: View, word_only: Boolean): Unit =
    Completion_Popup.Text_Area.action(view.getTextArea, word_only)


  /* control styles */

  def control_sub(text_area: JEditTextArea): Unit =
    Syntax_Style.edit_control_style(text_area, Symbol.sub)

  def control_sup(text_area: JEditTextArea): Unit =
    Syntax_Style.edit_control_style(text_area, Symbol.sup)

  def control_bold(text_area: JEditTextArea): Unit =
    Syntax_Style.edit_control_style(text_area, Symbol.bold)

  def control_emph(text_area: JEditTextArea): Unit =
    Syntax_Style.edit_control_style(text_area, Symbol.emph)

  def control_reset(text_area: JEditTextArea): Unit =
    Syntax_Style.edit_control_style(text_area, "")


  /* block styles */

  private def enclose_input(text_area: JEditTextArea, s1: String, s2: String): Unit =
  {
    s1.foreach(text_area.userInput)
    s2.foreach(text_area.userInput)
    s2.foreach(_ => text_area.goToPrevCharacter(false))
  }

  def input_bsub(text_area: JEditTextArea): Unit =
    enclose_input(text_area, Symbol.bsub_decoded, Symbol.esub_decoded)

  def input_bsup(text_area: JEditTextArea): Unit =
    enclose_input(text_area, Symbol.bsup_decoded, Symbol.esup_decoded)


  /* antiquoted cartouche */

  def antiquoted_cartouche(text_area: TextArea): Unit =
  {
    val buffer = text_area.getBuffer
    for {
      doc_view <- Document_View.get(text_area)
      rendering = doc_view.get_rendering()
      caret_range = JEdit_Lib.caret_range(text_area)
      antiq_range <- rendering.antiquoted(caret_range)
      antiq_text <- JEdit_Lib.get_text(buffer, antiq_range)
      body_text <- Antiquote.read_antiq_body(antiq_text)
      (name, arg) <- Token.read_antiq_arg(Keyword.Keywords.empty, body_text)
      if Symbol.is_ascii_identifier(name)
    } {
      val op_text =
        Isabelle_Encoding.perhaps_decode(buffer,
          Symbol.control_prefix + name + Symbol.control_suffix)
      val arg_text =
        if (arg.isEmpty) ""
        else if (Isabelle_Encoding.is_active(buffer)) Symbol.cartouche_decoded(arg.get)
        else Symbol.cartouche(arg.get)

      buffer.remove(antiq_range.start, antiq_range.length)
      text_area.moveCaretPosition(antiq_range.start)
      text_area.selectNone
      text_area.setSelectedText(op_text + arg_text)
    }
  }


  /* spell-checker dictionary */

  def update_dictionary(text_area: JEditTextArea, include: Boolean, permanent: Boolean): Unit =
  {
    for {
      spell_checker <- PIDE.plugin.spell_checker.get
      doc_view <- Document_View.get(text_area)
      rendering = doc_view.get_rendering()
      range = JEdit_Lib.caret_range(text_area)
      Text.Info(_, word) <- Spell_Checker.current_word(rendering, range)
    } {
      spell_checker.update(word, include, permanent)
      JEdit_Lib.jedit_views().foreach(_.repaint())
    }
  }

  def reset_dictionary(): Unit =
  {
    for (spell_checker <- PIDE.plugin.spell_checker.get)
    {
      spell_checker.reset()
      JEdit_Lib.jedit_views().foreach(_.repaint())
    }
  }


  /* debugger */

  def toggle_breakpoint(text_area: JEditTextArea): Unit =
  {
    GUI_Thread.require {}

    if (PIDE.session.debugger.is_active()) {
      Debugger_Dockable.get_breakpoint(text_area, text_area.getCaretPosition) match {
        case Some((command, breakpoint)) =>
          PIDE.session.debugger.toggle_breakpoint(command, breakpoint)
          jEdit.propertiesChanged()
        case None =>
      }
    }
  }


  /* plugin options */

  def plugin_options(frame: Frame): Unit =
  {
    GUI_Thread.require {}
    jEdit.setProperty("Plugin Options.last", "isabelle-general")
    new CombinedOptions(frame, 1)
  }


  /* popups */

  def dismissed_popups(view: View): Boolean =
  {
    var dismissed = false

    JEdit_Lib.jedit_text_areas(view).foreach(text_area =>
      if (Completion_Popup.Text_Area.dismissed(text_area)) dismissed = true)

    if (Pretty_Tooltip.dismissed_all()) dismissed = true

    dismissed
  }


  /* tooltips */

  def show_tooltip(view: View, control: Boolean): Unit =
  {
    GUI_Thread.require {}

    val text_area = view.getTextArea
    val painter = text_area.getPainter
    val caret_range = JEdit_Lib.caret_range(text_area)
    for {
      doc_view <- Document_View.get(text_area)
      rendering = doc_view.get_rendering()
      tip <- rendering.tooltip(caret_range, control)
      loc0 <- Option(text_area.offsetToXY(caret_range.start))
    } {
      val loc = new Point(loc0.x, loc0.y + painter.getLineHeight * 3 / 4)
      val results = rendering.snapshot.command_results(tip.range)
      Pretty_Tooltip(view, painter, loc, rendering, results, tip)
    }
  }


  /* error navigation */

  private def goto_error(
    view: View,
    range: Text.Range,
    avoid_range: Text.Range = Text.Range.offside,
    which: String = "")(get: List[Text.Markup] => Option[Text.Markup]): Unit =
  {
    GUI_Thread.require {}

    val text_area = view.getTextArea
    for (doc_view <- Document_View.get(text_area)) {
      val rendering = doc_view.get_rendering()
      val errs = rendering.errors(range).filterNot(_.range.overlaps(avoid_range))
      get(errs) match {
        case Some(err) =>
          PIDE.editor.goto_buffer(false, view, view.getBuffer, err.range.start)
        case None =>
          view.getStatus.setMessageAndClear("No " + which + "error in current document snapshot")
      }
    }
  }

  def goto_first_error(view: View): Unit =
    goto_error(view, JEdit_Lib.buffer_range(view.getBuffer))(_.headOption)

  def goto_last_error(view: View): Unit =
    goto_error(view, JEdit_Lib.buffer_range(view.getBuffer))(_.lastOption)

  def goto_prev_error(view: View): Unit =
  {
    val caret_range = JEdit_Lib.caret_range(view.getTextArea)
    val range = Text.Range(0, caret_range.stop)
    goto_error(view, range, avoid_range = caret_range, which = "previous ")(_.lastOption)
  }

  def goto_next_error(view: View): Unit =
  {
    val caret_range = JEdit_Lib.caret_range(view.getTextArea)
    val range = Text.Range(caret_range.start, view.getBuffer.getLength)
    goto_error(view, range, avoid_range = caret_range, which = "next ")(_.headOption)
  }


  /* java monitor */

  def java_monitor(view: View): Unit =
    Java_Monitor.java_monitor_external(view, look_and_feel = GUI.current_laf)
}
