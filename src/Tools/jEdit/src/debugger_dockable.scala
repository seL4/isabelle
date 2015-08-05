/*  Title:      Tools/jEdit/src/debugger_dockable.scala
    Author:     Makarius

Dockable window for Isabelle/ML debugger.
*/

package isabelle.jedit


import isabelle._

import java.awt.{BorderLayout, Dimension}
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent, MouseEvent, MouseAdapter}
import javax.swing.{JTree, JScrollPane}
import javax.swing.tree.{DefaultMutableTreeNode, DefaultTreeModel, TreeSelectionModel}
import javax.swing.event.{TreeSelectionEvent, TreeSelectionListener}

import scala.swing.{Button, Label, Component, SplitPane, Orientation}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.View


object Debugger_Dockable
{
  sealed case class Tree_Entry(thread_name: String, debug_states: List[Debugger.Debug_State])
  {
    override def toString: String = thread_name
  }
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

    val new_state = Debugger.current_state()

    val new_snapshot = PIDE.editor.current_node_snapshot(view).getOrElse(current_snapshot)
    val new_threads = new_state.threads
    val new_output =  // FIXME select by thread name
      (for ((_, results) <- new_state.output; (_, tree) <- results.iterator)
        yield tree).toList ::: List(XML.Text(new_threads.toString))

    if (new_threads != current_threads) {
      val entries =
        (for ((a, b) <- new_threads.iterator)
          yield Debugger_Dockable.Tree_Entry(a, b)).toList.sortBy(_.thread_name)
      update_tree(entries)
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

  private def update_tree(entries: List[Debugger_Dockable.Tree_Entry])
  {
    tree.clearSelection
    val tree_model = tree.getModel.asInstanceOf[DefaultTreeModel]

    root.removeAllChildren
    val entry_nodes = entries.map(entry => new DefaultMutableTreeNode(entry))
    for (node <- entry_nodes) root.add(node)

    tree_model.reload(root)
    for (i <- 0 until tree.getRowCount) tree.expandRow(i)

    for ((entry, node) <- entries zip entry_nodes) {
      for (debug_state <- entry.debug_states) {
        val sub_node = new DefaultMutableTreeNode(debug_state.function)
        node.add(sub_node)
      }
    }
    tree_model.reload(root)

    tree.revalidate()
  }

  private def action(node: DefaultMutableTreeNode)
  {
    node.getUserObject match {
      case _ => // FIXME
    }
  }

  tree.addMouseListener(new MouseAdapter {
    override def mouseClicked(e: MouseEvent)
    {
      val click = tree.getPathForLocation(e.getX, e.getY)
      if (click != null && e.getClickCount == 1) {
        (click.getLastPathComponent, tree.getLastSelectedPathComponent) match {
          case (node: DefaultMutableTreeNode, node1: DefaultMutableTreeNode) if node == node1 =>
            action(node)
          case _ =>
        }
      }
    }
  })

  val tree_view = new JScrollPane(tree)
  tree_view.setMinimumSize(new Dimension(200, 50))


  /* controls */

  private val context_label = new Label("Context:") { tooltip = "Isabelle/ML context (optional)" }
  private val context_field =
    new Completion_Popup.History_Text_Field("isabelle-debugger-context")
    {
      setColumns(20)
      setToolTipText(context_label.tooltip)
      setFont(GUI.imitate_font(getFont, Font_Info.main_family(), 1.2))
    }

  private val expression_label = new Label("ML:") { tooltip = "Isabelle/ML expression" }
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

  private val eval_button = new Button("<html><b>Eval</b></html>") {
      tooltip = "Evaluate Isabelle/ML expression within optional context"
      reactions += { case ButtonClicked(_) => eval_expression() }
    }
  override def focusOnDefaultComponent { eval_button.requestFocus }

  private def eval_expression()
  {
    // FIXME
    Output.writeln("eval context = " + quote(context_field.getText) + " expression = " +
      quote(expression_field.getText))
  }

  private val debugger_active =
    new JEdit_Options.Check_Box("ML_debugger_active", "Active", "Enable debugger at run-time")

  private val debugger_stepping =
    new JEdit_Options.Check_Box("ML_debugger_stepping", "Stepping", "Enable single-step mode")

  private val zoom = new Font_Info.Zoom_Box { def changed = handle_resize() }

  private val controls =
    new Wrap_Panel(Wrap_Panel.Alignment.Right)(
      context_label, Component.wrap(context_field),
      expression_label, Component.wrap(expression_field), eval_button,
      pretty_text_area.search_label, pretty_text_area.search_field,
      debugger_stepping, debugger_active, zoom)
  add(controls.peer, BorderLayout.NORTH)


  /* main panel */

  val main_panel = new SplitPane(Orientation.Vertical) {
    oneTouchExpandable = true
    leftComponent = Component.wrap(tree_view)
    rightComponent = Component.wrap(pretty_text_area)
  }
  set_content(main_panel)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        Debugger.init(PIDE.session)
        GUI_Thread.later {
          debugger_active.load()
          debugger_stepping.load()
          handle_resize()
        }

      case _: Debugger.Update =>
        GUI_Thread.later { handle_update() }
    }

  override def init()
  {
    PIDE.session.global_options += main
    PIDE.session.debugger_updates += main
    Debugger.init(PIDE.session)
    handle_update()
  }

  override def exit()
  {
    PIDE.session.global_options -= main
    PIDE.session.debugger_updates -= main
    delay_resize.revoke()
  }


  /* resize */

  private val delay_resize =
    GUI_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
    override def componentShown(e: ComponentEvent) { delay_resize.invoke() }
  })
}
