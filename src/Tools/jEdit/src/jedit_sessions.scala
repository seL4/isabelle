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
  /* session options */

  def session_options(options: Options): Options =
    Isabelle_System.getenv("JEDIT_ML_PROCESS_POLICY") match {
      case "" => options
      case s => options.string.update("ML_process_policy", s)
    }

  def session_dirs(): List[Path] =
    Path.split(Isabelle_System.getenv("JEDIT_SESSION_DIRS"))

  def session_build_mode(): String = Isabelle_System.getenv("JEDIT_BUILD_MODE")


  /* raw logic info */

  private val jedit_logic_option = "jedit_logic"

  def logic_name(options: Options): String =
    Isabelle_System.default_logic(
      Isabelle_System.getenv("JEDIT_LOGIC"),
      options.string(jedit_logic_option))

  def logic_ancestor: Option[String] = proper_string(Isabelle_System.getenv("JEDIT_LOGIC_ANCESTOR"))
  def logic_focus: Boolean = Isabelle_System.getenv("JEDIT_LOGIC_FOCUS") == "true"
  def logic_base: Boolean = Isabelle_System.getenv("JEDIT_LOGIC_BASE") == "true"
  def logic_parent: Boolean = Isabelle_System.getenv("JEDIT_LOGIC_PARENT") == "true"

  def logic_info(options: Options): Option[Sessions.Info] =
    try { Sessions.load(session_options(options), dirs = session_dirs()).get(logic_name(options)) }
    catch { case ERROR(_) => None }

  def logic_root(options: Options): Position.T =
    if (Isabelle_System.getenv("JEDIT_LOGIC_ROOT") == "true") {
      logic_info(options).map(_.pos) getOrElse Position.none
    }
    else Position.none


  /* logic selector */

  private class Logic_Entry(val name: String, val description: String)
  {
    override def toString: String = description
  }

  def logic_selector(options: Options_Variable, autosave: Boolean): Option_Component =
  {
    GUI_Thread.require {}

    val session_list =
    {
      val sessions = Sessions.load(options.value, dirs = session_dirs())
      val (main_sessions, other_sessions) =
        sessions.imports_topological_order.partition(info => info.groups.contains("main"))
      main_sessions.map(_.name).sorted ::: other_sessions.map(_.name).sorted
    }

    val entries =
      new Logic_Entry("", "default (" + logic_name(options.value) + ")") ::
        session_list.map(name => new Logic_Entry(name, name))

    val component = new ComboBox(entries) with Option_Component {
      name = jedit_logic_option
      val title = "Logic"
      def load: Unit =
      {
        val logic = options.string(jedit_logic_option)
        entries.find(_.name == logic) match {
          case Some(entry) => selection.item = entry
          case None =>
        }
      }
      def save: Unit = options.string(jedit_logic_option) = selection.item.name
    }

    component.load()
    if (autosave) {
      component.listenTo(component.selection)
      component.reactions += { case SelectionChanged(_) => component.save() }
    }
    component.tooltip = "Logic session name (change requires restart)"
    component
  }


  /* session build process */

  def session_base_info(options: Options): Sessions.Base_Info =
    Sessions.base_info(options,
      dirs = JEdit_Sessions.session_dirs(),
      session =
        if (logic_parent) logic_info(options).flatMap(_.parent) getOrElse logic_name(options)
        else logic_name(options),
      ancestor_session = logic_ancestor,
      all_known = !logic_focus,
      focus_session = logic_focus,
      required_session = logic_base)

  def session_build(
    options: Options, progress: Progress = No_Progress, no_build: Boolean = false): Int =
  {
    val mode = session_build_mode()

    Build.build(options = session_options(options), progress = progress,
      build_heap = true, no_build = no_build, system_mode = mode == "" || mode == "system",
      dirs = session_dirs(), infos = PIDE.resources.session_base_info.infos,
      sessions = List(PIDE.resources.session_name)).rc
  }

  def session_start(options: Options)
  {
    Isabelle_Process.start(PIDE.session, session_options(options),
      sessions = Some(PIDE.resources.session_base_info.sessions),
      logic = PIDE.resources.session_name,
      store = Sessions.store(session_build_mode() == "system"),
      modes =
        (space_explode(',', options.string("jedit_print_mode")) :::
         space_explode(',', Isabelle_System.getenv("JEDIT_PRINT_MODE"))).reverse,
      phase_changed = PIDE.plugin.session_phase_changed)
  }
}
