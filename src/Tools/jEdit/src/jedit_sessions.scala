/*  Title:      Tools/jEdit/src/jedit_sessions.scala
    Author:     Makarius

Isabelle/jEdit session information, based on implicit process environment
and explicit options.
*/

package isabelle.jedit


import isabelle._

import scala.swing.ComboBox
import scala.swing.event.SelectionChanged


object JEdit_Sessions
{
  /* session info */

  private val option_name = "jedit_logic"

  sealed case class Info(name: String, open_root: Position.T)

  def session_dirs(): List[Path] = Path.split(Isabelle_System.getenv("JEDIT_SESSION_DIRS"))

  def session_options(options: Options): Options =
    Isabelle_System.getenv("JEDIT_ML_PROCESS_POLICY") match {
      case "" => options
      case s => options.string("ML_process_policy") = s
    }

  def session_info(options: Options): Info =
  {
    val logic =
      Isabelle_System.default_logic(
        Isabelle_System.getenv("JEDIT_LOGIC"),
        options.string(option_name))

    (for {
      sessions <-
        try { Some(Sessions.load(session_options(options), dirs = session_dirs())) }
        catch { case ERROR(_) => None }
      info <- sessions.get(logic)
      parent <- info.parent
      if Isabelle_System.getenv("JEDIT_LOGIC_ROOT") == "true"
    } yield Info(parent, info.pos)) getOrElse Info(logic, Position.none)
  }

  def session_name(options: Options): String = session_info(options).name

  def session_base_info(options: Options): Sessions.Base_Info =
  {
    Sessions.session_base_info(options,
      session_name(options),
      dirs = JEdit_Sessions.session_dirs(),
      all_known = true).platform_path
  }

  def session_build_mode(): String = Isabelle_System.getenv("JEDIT_BUILD_MODE")

  def session_build(
    options: Options, progress: Progress = No_Progress, no_build: Boolean = false): Int =
  {
    val mode = session_build_mode()

    Build.build(options = session_options(options), progress = progress,
      build_heap = true, no_build = no_build, system_mode = mode == "" || mode == "system",
      dirs = session_dirs(), sessions = List(session_name(options))).rc
  }

  def session_start(options: Options)
  {
    val modes =
      (space_explode(',', options.string("jedit_print_mode")) :::
       space_explode(',', Isabelle_System.getenv("JEDIT_PRINT_MODE"))).reverse

    Isabelle_Process.start(PIDE.session, session_options(options),
      logic = session_name(options), dirs = session_dirs(), modes = modes,
      store = Sessions.store(session_build_mode() == "system"),
      phase_changed = PIDE.plugin.session_phase_changed)
  }

  def session_list(options: Options): List[String] =
  {
    val sessions = Sessions.load(options, dirs = session_dirs())
    val (main_sessions, other_sessions) =
      sessions.imports_topological_order.partition(info => info.groups.contains("main"))
    main_sessions.map(_.name).sorted ::: other_sessions.map(_.name).sorted
  }


  /* logic selector */

  private class Logic_Entry(val name: String, val description: String)
  {
    override def toString: String = description
  }

  def logic_selector(options: Options_Variable, autosave: Boolean): Option_Component =
  {
    GUI_Thread.require {}

    val entries =
      new Logic_Entry("", "default (" + session_name(options.value) + ")") ::
        session_list(options.value).map(name => new Logic_Entry(name, name))

    val component = new ComboBox(entries) with Option_Component {
      name = option_name
      val title = "Logic"
      def load: Unit =
      {
        val logic = options.string(option_name)
        entries.find(_.name == logic) match {
          case Some(entry) => selection.item = entry
          case None =>
        }
      }
      def save: Unit = options.string(option_name) = selection.item.name
    }

    component.load()
    if (autosave) {
      component.listenTo(component.selection)
      component.reactions += { case SelectionChanged(_) => component.save() }
    }
    component.tooltip = "Logic session name (change requires restart)"
    component
  }
}
