/*  Title:      Tools/jEdit/src/debugger_dockable.scala
    Author:     Makarius

Dockable window for Isabelle/ML debugger.
*/

package isabelle.jedit


import isabelle._

import java.awt.{BorderLayout, Dimension}
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent, MouseEvent, MouseAdapter,
  FocusAdapter, FocusEvent}
import javax.swing.{JTree, JMenuItem}
import javax.swing.tree.{DefaultMutableTreeNode, DefaultTreeModel, TreeSelectionModel}
import javax.swing.event.{TreeSelectionEvent, TreeSelectionListener}

import scala.swing.{Button, Label, Component, ScrollPane, SplitPane, Orientation,
  CheckBox, BorderPanel}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.{jEdit, View}
import org.gjt.sp.jedit.menu.EnhancedMenuItem
import org.gjt.sp.jedit.textarea.JEditTextArea


object Debugger_Dockable
{
  /* state entries */

  sealed case class Thread_Entry(thread_name: String, debug_states: List[Debugger.Debug_State])
  {
    override def toString: String = thread_name
  }

  sealed case class Stack_Entry(debug_state: Debugger.Debug_State, index: Int)
  {
    override def toString: String = debug_state.function
  }


  /* breakpoints */

  def toggle_breakpoint(command: Command, breakpoint: Long)
  {
    GUI_Thread.require {}

    Debugger.toggle_breakpoint(command, breakpoint)
    jEdit.propertiesChanged()
  }

  def get_breakpoint(text_area: JEditTextArea, offset: Text.Offset): Option[(Command, Long)] =
  {
    GUI_Thread.require {}

    PIDE.document_view(text_area) match {
      case Some(doc_view) =>
        val rendering = doc_view.get_rendering()
        val range = JEdit_Lib.point_range(text_area.getBuffer, offset)
        rendering.breakpoint(range)
      case None => None
    }
  }


  /* context menu */

  def context_menu(text_area: JEditTextArea, offset: Text.Offset): List[JMenuItem] =
    if (Debugger.is_active() && get_breakpoint(text_area, offset).isDefined) {
      val context = jEdit.getActionContext()
      val name = "isabelle.toggle-breakpoint"
      List(new EnhancedMenuItem(context.getAction(name).getLabel, name, context))
    }
    else Nil
}

class Debugger_Dockable(view: View, position: String) extends Dockable(view, position)
{
  GUI_Thread.require {}


  /* component state -- owned by GUI thread */

  private var current_snapshot = Document.Snapshot.init
  private var current_threads: Map[String, List[Debugger.Debug_State]] = Map.empty
  private var current_output: List[XML.Tree] = Nil


  /* pretty text area */

  val pretty_text_area = new Pretty_Text_Area(view)

  override def detach_operation = pretty_text_area.detach_operation

  private def handle_resize()
  {
    GUI_Thread.require {}

    pretty_text_area.resize(
      Font_Info.main(PIDE.options.real("jedit_font_scale") * zoom.factor / 100))
  }

  private def handle_update()
  {
    GUI_Thread.require {}

    val new_snapshot = PIDE.editor.current_node_snapshot(view).getOrElse(current_snapshot)
    val new_threads = Debugger.threads()
    val new_output =
    {
      val output = Debugger.output()
      val current_thread_selection = thread_selection()
      (for {
        (thread_name, results) <- output
        if current_thread_selection.isEmpty || current_thread_selection.get == thread_name
        (_, tree) <- results.iterator
      } yield tree).toList
    }

    if (new_threads != current_threads) {
      val thread_entries =
        (for ((a, b) <- new_threads.iterator)
          yield Debugger_Dockable.Thread_Entry(a, b)).toList.sortBy(_.thread_name)
      update_tree(thread_entries)
    }

    if (new_output != current_output)
      pretty_text_area.update(new_snapshot, Command.Results.empty, Pretty.separate(new_output))

    current_snapshot = new_snapshot
    current_threads = new_threads
    current_output = new_output
  }


  /* tree view */

  private val root = new DefaultMutableTreeNode("Threads")

  val tree = new JTree(root)
  tree.setRowHeight(0)
  tree.getSelectionModel.setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)

  def tree_selection(): Option[(Debugger_Dockable.Thread_Entry, Option[Int])] =
    tree.getSelectionPath match {
      case null => None
      case path =>
        path.getPath.toList.map(n => n.asInstanceOf[DefaultMutableTreeNode].getUserObject) match {
          case List(_, t: Debugger_Dockable.Thread_Entry) =>
            Some((t, None))
          case List(_, t: Debugger_Dockable.Thread_Entry, s: Debugger_Dockable.Stack_Entry) =>
            Some((t, Some(s.index)))
          case _ => None
        }
    }

  def thread_selection(): Option[String] = tree_selection().map(sel => sel._1.thread_name)

  def index_selection(): Option[(Debugger_Dockable.Thread_Entry, Int)] =
    tree_selection() match {
      case Some((t, opt_index)) =>
        val i = opt_index getOrElse 0
        if (i < t.debug_states.length) Some((t, i)) else None
      case _ => None
    }

  def focus_selection(): Option[Position.T] =
    index_selection() match {
      case Some((t, i)) => Some(t.debug_states(i).pos)
      case None => None
    }

  private def update_tree(thread_entries: List[Debugger_Dockable.Thread_Entry])
  {
    val old_thread_selection =
      thread_selection() orElse
      thread_entries.collectFirst { case t if t.debug_states.nonEmpty => t.thread_name }

    tree.clearSelection
    root.removeAllChildren

    for (thread_entry <- thread_entries) {
      val thread_node = new DefaultMutableTreeNode(thread_entry)
      for ((debug_state, i) <- thread_entry.debug_states.zipWithIndex) {
        val stack_node =
          new DefaultMutableTreeNode(Debugger_Dockable.Stack_Entry(debug_state, i))
        thread_node.add(stack_node)
      }
      root.add(thread_node)
    }

    tree.getModel.asInstanceOf[DefaultTreeModel].reload(root)

    old_thread_selection match {
      case Some(thread_name) if thread_entries.exists(t => t.thread_name == thread_name) =>
        val i =
          (for (t <- thread_entries.iterator.takeWhile(t => t.thread_name != thread_name))
            yield 1 + t.debug_states.length).sum
        tree.addSelectionRow(i + 1)
      case _ =>
    }
    for (i <- 0 until tree.getRowCount) tree.expandRow(i)

    tree.revalidate()
  }

  tree.addTreeSelectionListener(
    new TreeSelectionListener {
      override def valueChanged(e: TreeSelectionEvent) { update_focus(focus_selection()) }
    })

  tree.addMouseListener(new MouseAdapter {
    override def mouseClicked(e: MouseEvent)
    {
      val click = tree.getPathForLocation(e.getX, e.getY)
      if (click != null && e.getClickCount == 1) {
        (click.getLastPathComponent, tree.getLastSelectedPathComponent) match {
          case (node: DefaultMutableTreeNode, node1: DefaultMutableTreeNode) if node == node1 =>
            index_selection() match {
              case Some((t, i)) =>
                Debugger.print_vals(t.thread_name, i, sml_button.selected, context_field.getText)
              case None =>
            }
          case _ =>
        }
      }
    }
  })

  private val tree_pane = new ScrollPane(Component.wrap(tree))
  tree_pane.horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.verticalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.minimumSize = new Dimension(200, 100)


  /* controls */

  private val context_label = new Label("Context:") {
    tooltip = "Isabelle/ML context: type theory, Proof.context, Context.generic"
  }
  private val context_field =
    new Completion_Popup.History_Text_Field("isabelle-debugger-context")
    {
      setColumns(20)
      setToolTipText(context_label.tooltip)
      setFont(GUI.imitate_font(getFont, Font_Info.main_family(), 1.2))
    }

  private val expression_label = new Label("ML:") {
    tooltip = "Isabelle/ML or Standard ML expression"
  }
  private val expression_field =
    new Completion_Popup.History_Text_Field("isabelle-debugger-expression")
    {
      override def processKeyEvent(evt: KeyEvent)
      {
        if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER)
          eval_expression()
        super.processKeyEvent(evt)
      }
      { val max = getPreferredSize; max.width = Integer.MAX_VALUE; setMaximumSize(max) }
      setColumns(40)
      setToolTipText(expression_label.tooltip)
      setFont(GUI.imitate_font(getFont, Font_Info.main_family(), 1.2))
    }

  private val sml_button = new CheckBox("SML") {
    tooltip = "Official Standard ML instead of Isabelle/ML"
    selected = false
  }

  private val eval_button = new Button("<html><b>Eval</b></html>") {
      tooltip = "Evaluate ML expression within optional context"
      reactions += { case ButtonClicked(_) => eval_expression() }
    }

  private def eval_expression()
  {
    context_field.addCurrentToHistory()
    expression_field.addCurrentToHistory()
    tree_selection() match {
      case Some((t, opt_index)) if t.debug_states.nonEmpty =>
        Debugger.eval(t.thread_name, opt_index getOrElse 0,
          sml_button.selected, context_field.getText, expression_field.getText)
      case _ =>
    }
  }

  private val step_button = new Button("Step") {
    tooltip = "Single-step in depth-first order"
    reactions += { case ButtonClicked(_) => thread_selection().map(Debugger.step(_)) }
  }

  private val step_over_button = new Button("Step over") {
    tooltip = "Single-step within this function"
    reactions += { case ButtonClicked(_) => thread_selection().map(Debugger.step_over(_)) }
  }

  private val step_out_button = new Button("Step out") {
    tooltip = "Single-step outside this function"
    reactions += { case ButtonClicked(_) => thread_selection().map(Debugger.step_out(_)) }
  }

  private val continue_button = new Button("Continue") {
    tooltip = "Continue program on current thread, until next breakpoint"
    reactions += { case ButtonClicked(_) => thread_selection().map(Debugger.continue(_)) }
  }

  private val zoom = new Font_Info.Zoom_Box { def changed = handle_resize() }

  private val controls =
    new Wrap_Panel(Wrap_Panel.Alignment.Right)(
      step_button, step_over_button, step_out_button, continue_button,
      context_label, Component.wrap(context_field),
      expression_label, Component.wrap(expression_field), sml_button, eval_button,
      pretty_text_area.search_label, pretty_text_area.search_field, zoom)
  add(controls.peer, BorderLayout.NORTH)


  /* focus */

  override def focusOnDefaultComponent { eval_button.requestFocus }

  addFocusListener(new FocusAdapter {
    override def focusGained(e: FocusEvent) { update_focus(focus_selection()) }
    override def focusLost(e: FocusEvent) { update_focus(None) }
  })

  private def update_focus(focus: Option[Position.T])
  {
    if (Debugger.focus(focus) && focus.isDefined)
      PIDE.editor.hyperlink_position(false, current_snapshot, focus.get).foreach(_.follow(view))
  }


  /* main panel */

  val main_panel = new SplitPane(Orientation.Vertical) {
    oneTouchExpandable = true
    leftComponent = tree_pane
    rightComponent = Component.wrap(pretty_text_area)
  }
  set_content(main_panel)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        Debugger.set_session(PIDE.session)
        GUI_Thread.later { handle_resize() }

      case _: Debugger.Update =>
        GUI_Thread.later { handle_update() }
    }

  override def init()
  {
    PIDE.session.global_options += main
    PIDE.session.debugger_updates += main
    Debugger.set_session(PIDE.session)
    Debugger.inc_active()
    handle_update()
    jEdit.propertiesChanged()
  }

  override def exit()
  {
    PIDE.session.global_options -= main
    PIDE.session.debugger_updates -= main
    delay_resize.revoke()
    update_focus(None)
    Debugger.dec_active()
    jEdit.propertiesChanged()
  }


  /* resize */

  private val delay_resize =
    GUI_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
    override def componentShown(e: ComponentEvent) { delay_resize.invoke() }
  })
}
