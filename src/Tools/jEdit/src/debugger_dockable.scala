/*  Title:      Tools/jEdit/src/debugger_dockable.scala
    Author:     Makarius

Dockable window for Isabelle/ML debugger.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.KeyEvent
import javax.swing.JMenuItem
import javax.swing.event.TreeSelectionEvent

import scala.collection.immutable.SortedMap
import scala.swing.{Button, Label, Component}

import org.gjt.sp.jedit.{jEdit, View}
import org.gjt.sp.jedit.menu.EnhancedMenuItem
import org.gjt.sp.jedit.textarea.JEditTextArea


object Debugger_Dockable {
  /* breakpoints */

  def get_breakpoint(text_area: JEditTextArea, offset: Text.Offset): Option[(Command, Long)] = {
    GUI_Thread.require {}

    Document_View.get(text_area) match {
      case Some(doc_view) =>
        val rendering = Document_View.rendering(doc_view)
        val range = JEdit_Lib.point_range(text_area.getBuffer, offset)
        rendering.breakpoint(range)
      case None => None
    }
  }


  /* context menu */

  def context_menu(text_area: JEditTextArea, offset: Text.Offset): List[JMenuItem] =
    if (PIDE.session.debugger.is_active() && get_breakpoint(text_area, offset).isDefined) {
      val context = jEdit.getActionContext()
      val name = "isabelle.toggle-breakpoint"
      List(new EnhancedMenuItem(context.getAction(name).getLabel, name, context))
    }
    else Nil
}

class Debugger_Dockable(view: View, position: String) extends Dockable(view, position) {
  dockable =>

  GUI_Thread.require {}

  private val debugger = PIDE.session.debugger


  /* component state -- owned by GUI thread */

  private var current_snapshot = Document.Snapshot.init
  private var current_threads: Debugger.Threads = SortedMap.empty
  private var current_output: List[XML.Tree] = Nil


  /* pretty text area */

  private val output: Output_Area =
    new Output_Area(view, root_name = "Threads", split = true) {
      override def handle_resize(): Unit = pretty_text_area.zoom(zoom)

      override def handle_update(): Unit = {
        val new_snapshot = PIDE.editor.current_node_snapshot(view).getOrElse(current_snapshot)
        val (new_threads, new_output) = debugger.status(tree_selection())

        if (new_threads != current_threads) update_tree(new_threads)

        if (new_output != current_output) {
          pretty_text_area.update(new_snapshot, Command.Results.empty, Pretty.separate(new_output))
        }

        current_snapshot = new_snapshot
        current_threads = new_threads
        current_output = new_output
      }

      override def handle_focus(): Unit = update_focus()
    }

  override def detach_operation: Option[() => Unit] =
    output.pretty_text_area.detach_operation

  output.init_gui(dockable)


  /* tree view */

  private def tree_selection(): Option[Debugger.Context] =
    output.tree.get_selection({ case c: Debugger.Context => c })

  private def thread_selection(): Option[String] = tree_selection().map(_.thread_name)

  private def update_tree(threads: Debugger.Threads): Unit = {
    val thread_contexts =
      (for ((a, b) <- threads.iterator)
        yield Debugger.Context(a, b)).toList

    val new_tree_selection =
      tree_selection() match {
        case Some(c) if thread_contexts.contains(c) => Some(c)
        case Some(c) if thread_contexts.exists(t => c.thread_name == t.thread_name) =>
          Some(c.reset)
        case _ => thread_contexts.headOption
      }

    output.tree.clear()

    for (thread <- thread_contexts) {
      val thread_node = Tree_View.Node(thread)
      for ((_, i) <- thread.debug_states.zipWithIndex)
        thread_node.add(Tree_View.Node(thread.select(i)))
      output.tree.root.add(thread_node)
    }

    output.tree.reload_model()

    output.tree.expandRow(0)
    for (i <- Range.inclusive(output.tree.getRowCount - 1, 1, -1)) output.tree.expandRow(i)

    new_tree_selection match {
      case Some(c) =>
        val i =
          (for (t <- thread_contexts.iterator.takeWhile(t => c.thread_name != t.thread_name))
            yield t.size).sum
        output.tree.addSelectionRow(i + c.index + 1)
      case None =>
    }

    output.tree.revalidate()
  }

  def update_vals(): Unit = {
    tree_selection() match {
      case Some(c) if c.stack_state.isDefined =>
        debugger.print_vals(c, sml_button.selected, context_field.getText)
      case Some(c) =>
        debugger.clear_output(c.thread_name)
      case None =>
    }
  }


  /* controls */

  private val break_button = new GUI.Check("Break", init = debugger.is_break()) {
    tooltip = "Break running threads at next possible breakpoint"
    override def clicked(state: Boolean): Unit = debugger.set_break(state)
  }

  private val continue_button = new GUI.Button("Continue") {
    tooltip = "Continue program on current thread, until next breakpoint"
    override def clicked(): Unit = thread_selection().foreach(debugger.continue)
  }

  private val step_button = new GUI.Button("Step") {
    tooltip = "Single-step in depth-first order"
    override def clicked(): Unit = thread_selection().foreach(debugger.step)
  }

  private val step_over_button = new GUI.Button("Step over") {
    tooltip = "Single-step within this function"
    override def clicked(): Unit = thread_selection().foreach(debugger.step_over)
  }

  private val step_out_button = new GUI.Button("Step out") {
    tooltip = "Single-step outside this function"
    override def clicked(): Unit = thread_selection().foreach(debugger.step_out)
  }

  private val context_label = new Label("Context:") {
    tooltip = "Isabelle/ML context: type theory, Proof.context, Context.generic"
  }
  private val context_field =
    new Completion_Popup.History_Text_Field("isabelle-debugger-context") {
      override def processKeyEvent(evt: KeyEvent): Unit = {
        if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER) {
          eval_expression()
        }
        super.processKeyEvent(evt)
      }
      setColumns(20)
      setToolTipText(context_label.tooltip)
      setFont(GUI.imitate_font(getFont, scale = 1.2))
    }

  private val expression_label = new Label("ML:") {
    tooltip = "Isabelle/ML or Standard ML expression"
  }
  private val expression_field =
    new Completion_Popup.History_Text_Field("isabelle-debugger-expression") {
      override def processKeyEvent(evt: KeyEvent): Unit = {
        if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER) {
          eval_expression()
        }
        super.processKeyEvent(evt)
      }
      { val max = getPreferredSize; max.width = Int.MaxValue; setMaximumSize(max) }
      setColumns(40)
      setToolTipText(expression_label.tooltip)
      setFont(GUI.imitate_font(getFont, scale = 1.2))
    }

  private val eval_button =
    new GUI.Button("<html><b>Eval</b></html>") {
      tooltip = "Evaluate ML expression within optional context"
      override def clicked(): Unit = eval_expression()
    }

  private def eval_expression(): Unit = {
    context_field.addCurrentToHistory()
    expression_field.addCurrentToHistory()
    tree_selection() match {
      case Some(c) if c.debug_index.isDefined =>
        debugger.eval(c, sml_button.selected, context_field.getText, expression_field.getText)
      case _ =>
    }
  }

  private val sml_button = new GUI.Check("SML") {
    tooltip = "Official Standard ML instead of Isabelle/ML"
  }

  private val zoom =
    new Font_Info.Zoom { override def changed(): Unit = output.handle_resize() }

  private val controls =
    Wrap_Panel(
      List(
        break_button, continue_button, step_button, step_over_button, step_out_button,
        context_label, Component.wrap(context_field),
        expression_label, Component.wrap(expression_field), eval_button, sml_button) :::
      output.pretty_text_area.search_components :::
      List(output.pretty_text_area.search_field, zoom))

  add(controls.peer, BorderLayout.NORTH)


  /* focus */

  override def focusOnDefaultComponent(): Unit = eval_button.requestFocus()

  private def update_focus(): Unit = {
    for (c <- tree_selection()) {
      debugger.set_focus(c)
      for {
        pos <- c.debug_position
        link <- PIDE.editor.hyperlink_position(false, current_snapshot, pos)
      } link.follow(view)
    }
    JEdit_Lib.jedit_text_areas(view.getBuffer).foreach(_.repaint())
  }

  output.tree.addTreeSelectionListener({ (e: TreeSelectionEvent) =>
    update_focus()
    update_vals()
  })


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later { output.handle_resize() }

      case Debugger.Update =>
        GUI_Thread.later {
          break_button.selected = debugger.is_break()
          output.handle_update()
        }
    }

  override def init(): Unit = {
    PIDE.session.global_options += main
    PIDE.session.debugger_updates += main
    debugger.init(dockable)
    output.handle_update()
    jEdit.propertiesChanged()
  }

  override def exit(): Unit = {
    PIDE.session.global_options -= main
    PIDE.session.debugger_updates -= main
    output.delay_resize.revoke()
    debugger.exit(dockable)
    jEdit.propertiesChanged()
  }
}
