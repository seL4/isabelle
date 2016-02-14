/*  Title:      Tools/jEdit/src/isabelle_logic.scala
    Author:     Makarius

Isabelle logic session.
*/

package isabelle.jedit


import isabelle._

import scala.swing.ComboBox
import scala.swing.event.SelectionChanged


object Isabelle_Logic
{
  private val option_name = "jedit_logic"

  def session_name(): String =
    Isabelle_System.default_logic(
      Isabelle_System.getenv("JEDIT_LOGIC"),
      PIDE.options.string(option_name))

  private class Logic_Entry(val name: String, val description: String)
  {
    override def toString: String = description
  }

  def logic_selector(autosave: Boolean): Option_Component =
  {
    GUI_Thread.require {}

    val entries =
      new Logic_Entry("", "default (" + session_name() + ")") ::
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

  def session_build_mode(): String = Isabelle_System.getenv("JEDIT_BUILD_MODE")

  def session_build(progress: Progress = Ignore_Progress, no_build: Boolean = false): Int =
  {
    val mode = session_build_mode()

    Build.build(options = PIDE.options.value, progress = progress,
      build_heap = true, no_build = no_build, system_mode = mode == "" || mode == "system",
      dirs = session_dirs(), sessions = List(session_name()))
  }

  def session_args(): String =
  {
    val print_modes =
      (space_explode(',', PIDE.options.string("jedit_print_mode")) :::
       space_explode(',', Isabelle_System.getenv("JEDIT_PRINT_MODE"))).map("-m " + _)
    (print_modes ::: List("-r", "-q", File.shell_quote(session_name()))).mkString(" ")
  }

  def session_start(): Unit = PIDE.session.start("Isabelle", session_args())

  def session_dirs(): List[Path] = Path.split(Isabelle_System.getenv("JEDIT_SESSION_DIRS"))

  def session_list(): List[String] =
  {
    val session_tree = Build.find_sessions(PIDE.options.value, dirs = session_dirs())
    val (main_sessions, other_sessions) =
      session_tree.topological_order.partition(p => p._2.groups.contains("main"))
    main_sessions.map(_._1).sorted ::: other_sessions.map(_._1).sorted
  }

  def session_content(inlined_files: Boolean): Build.Session_Content =
  {
    val content =
      Build.session_content(PIDE.options.value, inlined_files, session_dirs(), session_name())
    content.copy(known_theories =
      content.known_theories.mapValues(name => name.map(File.platform_path(_))))
  }
}
