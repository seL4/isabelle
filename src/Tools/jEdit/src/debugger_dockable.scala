/*  Title:      Tools/jEdit/src/debugger_dockable.scala
    Author:     Makarius

Dockable window for Isabelle/ML debugger.
*/

package isabelle.jedit


import isabelle._
import isabelle.jedit_base.Dockable

import java.awt.{BorderLayout, Dimension}
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent, FocusAdapter, FocusEvent,
  MouseEvent, MouseAdapter}
import javax.swing.{JTree, JMenuItem}
import javax.swing.tree.{DefaultMutableTreeNode, DefaultTreeModel, TreeSelectionModel}
import javax.swing.event.{TreeSelectionEvent, TreeSelectionListener}

import scala.collection.immutable.SortedMap
import scala.swing.{Button, Label, Component, ScrollPane, SplitPane, Orientation,
  CheckBox, BorderPanel}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.{jEdit, View}
import org.gjt.sp.jedit.menu.EnhancedMenuItem
import org.gjt.sp.jedit.textarea.JEditTextArea


object Debugger_Dockable
{
  /* breakpoints */

  def get_breakpoint(text_area: JEditTextArea, offset: Text.Offset): Option[(Command, Long)] =
  {
    GUI_Thread.require {}

    Document_View.get(text_area) match {
      case Some(doc_view) =>
        val rendering = doc_view.get_rendering()
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

class Debugger_Dockable(view: View, position: String) extends Dockable(view, position)
{
  GUI_Thread.require {}

  private val debugger = PIDE.session.debugger


  /* component state -- owned by GUI thread */

  private var current_snapshot = Document.Snapshot.init
  private var current_threads: Debugger.Threads = SortedMap.empty
  private var current_output: List[XML.Tree] = Nil


  /* pretty text area */

  val pretty_text_area = new Pretty_Text_Area(view)

  override def detach_operation: Option[() => Unit] = pretty_text_area.detach_operation

  private def handle_resize(): Unit =
  {
    GUI_Thread.require {}

    pretty_text_area.resize(
      Font_Info.main(PIDE.options.real("jedit_font_scale") * zoom.factor / 100))
  }

  private def handle_update(): Unit =
  {
    GUI_Thread.require {}

    val new_snapshot = PIDE.editor.current_node_snapshot(view).getOrElse(current_snapshot)
    val (new_threads, new_output) = debugger.status(tree_selection())

    if (new_threads != current_threads)
      update_tree(new_threads)

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

  def tree_selection(): Option[Debugger.Context] =
    tree.getLastSelectedPathComponent match {
      case node: DefaultMutableTreeNode =>
        node.getUserObject match {
          case c: Debugger.Context => Some(c)
          case _ => None
        }
      case _ => None
    }

  def thread_selection(): Option[String] = tree_selection().map(_.thread_name)

  private def update_tree(threads: Debugger.Threads): Unit =
  {
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

    tree.clearSelection
    root.removeAllChildren

    for (thread <- thread_contexts) {
      val thread_node = new DefaultMutableTreeNode(thread)
      for ((debug_state, i) <- thread.debug_states.zipWithIndex)
        thread_node.add(new DefaultMutableTreeNode(thread.select(i)))
      root.add(thread_node)
    }

    tree.getModel.asInstanceOf[DefaultTreeModel].reload(root)

    tree.expandRow(0)
    for (i <- Range.inclusive(tree.getRowCount - 1, 1, -1)) tree.expandRow(i)

    new_tree_selection match {
      case Some(c) =>
        val i =
          (for (t <- thread_contexts.iterator.takeWhile(t => c.thread_name != t.thread_name))
            yield t.size).sum
        tree.addSelectionRow(i + c.index + 1)
      case None =>
    }

    tree.revalidate()
  }

  def update_vals(): Unit =
  {
    tree_selection() match {
      case Some(c) if c.stack_state.isDefined =>
        debugger.print_vals(c, sml_button.selected, context_field.getText)
      case Some(c) =>
        debugger.clear_output(c.thread_name)
      case None =>
    }
  }

  tree.addTreeSelectionListener(
    new TreeSelectionListener {
      override def valueChanged(e: TreeSelectionEvent): Unit =
      {
        update_focus()
        update_vals()
      }
    })
  tree.addMouseListener(
    new MouseAdapter {
      override def mouseClicked(e: MouseEvent): Unit =
      {
        val click = tree.getPathForLocation(e.getX, e.getY)
        if (click != null && e.getClickCount == 1)
          update_focus()
      }
    })

  private val tree_pane = new ScrollPane(Component.wrap(tree))
  tree_pane.horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.verticalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.minimumSize = new Dimension(200, 100)


  /* controls */

  private val break_button = new CheckBox("Break") {
    tooltip = "Break running threads at next possible breakpoint"
    selected = debugger.is_break()
    reactions += { case ButtonClicked(_) => debugger.set_break(selected) }
  }

  private val continue_button = new Button("Continue") {
    tooltip = "Continue program on current thread, until next breakpoint"
    reactions += { case ButtonClicked(_) => thread_selection().map(debugger.continue) }
  }

  private val step_button = new Button("Step") {
    tooltip = "Single-step in depth-first order"
    reactions += { case ButtonClicked(_) => thread_selection().map(debugger.step) }
  }

  private val step_over_button = new Button("Step over") {
    tooltip = "Single-step within this function"
    reactions += { case ButtonClicked(_) => thread_selection().map(debugger.step_over) }
  }

  private val step_out_button = new Button("Step out") {
    tooltip = "Single-step outside this function"
    reactions += { case ButtonClicked(_) => thread_selection().map(debugger.step_out) }
  }

  private val context_label = new Label("Context:") {
    tooltip = "Isabelle/ML context: type theory, Proof.context, Context.generic"
  }
  private val context_field =
    new Completion_Popup.History_Text_Field("isabelle-debugger-context")
    {
      override def processKeyEvent(evt: KeyEvent): Unit =
      {
        if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER)
          eval_expression()
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
    new Completion_Popup.History_Text_Field("isabelle-debugger-expression")
    {
      override def processKeyEvent(evt: KeyEvent): Unit =
      {
        if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER)
          eval_expression()
        super.processKeyEvent(evt)
      }
      { val max = getPreferredSize; max.width = Integer.MAX_VALUE; setMaximumSize(max) }
      setColumns(40)
      setToolTipText(expression_label.tooltip)
      setFont(GUI.imitate_font(getFont, scale = 1.2))
    }

  private val eval_button = new Button("<html><b>Eval</b></html>") {
      tooltip = "Evaluate ML expression within optional context"
      reactions += { case ButtonClicked(_) => eval_expression() }
    }

  private def eval_expression(): Unit =
  {
    context_field.addCurrentToHistory()
    expression_field.addCurrentToHistory()
    tree_selection() match {
      case Some(c) if c.debug_index.isDefined =>
        debugger.eval(c, sml_button.selected, context_field.getText, expression_field.getText)
      case _ =>
    }
  }

  private val sml_button = new CheckBox("SML") {
    tooltip = "Official Standard ML instead of Isabelle/ML"
    selected = false
  }

  private val zoom = new Font_Info.Zoom_Box { def changed = handle_resize() }

  private val controls =
    Wrap_Panel(
      List(
        break_button, continue_button, step_button, step_over_button, step_out_button,
        context_label, Component.wrap(context_field),
        expression_label, Component.wrap(expression_field), eval_button, sml_button,
        pretty_text_area.search_label, pretty_text_area.search_field, zoom))

  add(controls.peer, BorderLayout.NORTH)


  /* focus */

  override def focusOnDefaultComponent(): Unit = eval_button.requestFocus

  addFocusListener(new FocusAdapter {
    override def focusGained(e: FocusEvent): Unit = update_focus()
  })

  private def update_focus(): Unit =
  {
    for (c <- tree_selection()) {
      debugger.set_focus(c)
      for {
        pos <- c.debug_position
        link <- PIDE.editor.hyperlink_position(false, current_snapshot, pos)
      } link.follow(view)
    }
    JEdit_Lib.jedit_text_areas(view.getBuffer).foreach(_.repaint())
  }


  /* main panel */

  val main_panel: SplitPane = new SplitPane(Orientation.Vertical) {
    oneTouchExpandable = true
    leftComponent = tree_pane
    rightComponent = Component.wrap(pretty_text_area)
  }
  set_content(main_panel)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later { handle_resize() }

      case Debugger.Update =>
        GUI_Thread.later {
          break_button.selected = debugger.is_break()
          handle_update()
        }
    }

  override def init(): Unit =
  {
    PIDE.session.global_options += main
    PIDE.session.debugger_updates += main
    debugger.init()
    handle_update()
    jEdit.propertiesChanged()
  }

  override def exit(): Unit =
  {
    PIDE.session.global_options -= main
    PIDE.session.debugger_updates -= main
    delay_resize.revoke()
    debugger.exit()
    jEdit.propertiesChanged()
  }


  /* resize */

  private val delay_resize =
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })
}
