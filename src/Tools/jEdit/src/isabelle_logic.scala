/*  Title:      Tools/jEdit/src/isabelle_logic.scala
    Author:     Makarius

Isabellel logic session.
*/

package isabelle.jedit


import isabelle._

import scala.swing.ComboBox
import scala.swing.event.SelectionChanged


object Isabelle_Logic
{
  private val option_name = "jedit_logic"

  private def jedit_logic(): String =
    Isabelle_System.default_logic(
      Isabelle_System.getenv("JEDIT_LOGIC"),
      PIDE.options.string(option_name))

  private class Logic_Entry(val name: String, val description: String)
  {
    override def toString = description
  }

  def logic_selector(autosave: Boolean): Option_Component =
  {
    Swing_Thread.require {}

    val entries =
      new Logic_Entry("", "default (" + jedit_logic() + ")") ::
        Isabelle_Logic.session_list().map(name => new Logic_Entry(name, name))

    val component = new ComboBox(entries) with Option_Component {
      name = option_name
      val title = "Logic"
      def load: Unit =
      {
        val logic = PIDE.options.string(option_name)
        entries.find(_.name == logic) match {
          case Some(entry) => selection.item = entry
          case None =>
        }
      }
      def save: Unit = PIDE.options.string(option_name) = selection.item.name
    }

    component.load()
    if (autosave) {
      component.listenTo(component.selection)
      component.reactions += { case SelectionChanged(_) => component.save() }
    }
    component.tooltip = "Logic session name (change requires restart)"
    component
  }

  def session_args(): List[String] =
  {
    val modes =
      space_explode(',', PIDE.options.string("jedit_print_mode")) :::
      space_explode(',', Isabelle_System.getenv("JEDIT_PRINT_MODE"))

    modes.map("-m" + _) ::: List("-r", "-q", jedit_logic())
  }

  def session_dirs(): List[Path] = Path.split(Isabelle_System.getenv("JEDIT_SESSION_DIRS"))

  def session_list(): List[String] =
  {
    val dirs = session_dirs().map((false, _))
    val session_tree = Build.find_sessions(PIDE.options.value, dirs)
    val (main_sessions, other_sessions) =
      session_tree.topological_order.partition(p => p._2.groups.contains("main"))
    main_sessions.map(_._1).sorted ::: other_sessions.map(_._1).sorted
  }

  def session_content(inlined_files: Boolean): Build.Session_Content =
  {
    val dirs = session_dirs()
    val name = session_args().last
    Build.session_content(PIDE.options.value, inlined_files, dirs, name)
  }
}

