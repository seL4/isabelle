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
  private def default_logic(): String =
  {
    val logic = Isabelle_System.getenv("JEDIT_LOGIC")
    if (logic != "") logic
    else Isabelle_System.getenv_strict("ISABELLE_LOGIC")
  }

  private class Logic_Entry(val name: String, val description: String)
  {
    override def toString = description
  }

  private val opt_name = "jedit_logic"

  def logic_selector(autosave: Boolean): Option_Component =
  {
    Swing_Thread.require()

    val entries =
      new Logic_Entry("", "default (" + default_logic() + ")") ::
        Isabelle_System.find_logics().map(name => new Logic_Entry(name, name))

    val component = new ComboBox(entries) with Option_Component {
      name = opt_name
      val title = "Logic"
      def load: Unit =
      {
        val logic = Isabelle.options.string(opt_name)
        entries.find(_.name == logic) match {
          case Some(entry) => selection.item = entry
          case None =>
        }
      }
      def save: Unit = Isabelle.options.string(opt_name) = selection.item.name
    }

    component.load()
    if (autosave) {
      component.listenTo(component.selection)
      component.reactions += { case SelectionChanged(_) => component.save() }
    }
    component.tooltip = Isabelle.options.value.check_name(opt_name).print_default
    component
  }

  def session_args(): List[String] =
  {
    val modes = space_explode(',', Isabelle_System.getenv("JEDIT_PRINT_MODE")).map("-m" + _)
    val logic =
      Isabelle.options.string(opt_name) match {
        case "" => default_logic()
        case logic => logic
      }
    modes ::: List(logic)
  }

  def session_content(inlined_files: Boolean): Build.Session_Content =
  {
    val dirs = Path.split(Isabelle_System.getenv("JEDIT_SESSION_DIRS"))
    val name = Path.explode(session_args().last).base.implode  // FIXME more robust
    Build.session_content(inlined_files, dirs, name).check_errors
  }
}

