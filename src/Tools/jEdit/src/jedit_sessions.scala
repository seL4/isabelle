/*  Title:      Tools/jEdit/src/jedit_sessions.scala
    Author:     Makarius

Isabelle/jEdit session information, based on implicit process environment
and explicit options.
*/

package isabelle.jedit


import isabelle._


object JEdit_Sessions {
  /* session options */

  def session_dirs: List[Path] =
    Path.split(Isabelle_System.getenv("JEDIT_SESSION_DIRS")).filterNot(p => p.implode == "-")

  def session_no_build: Boolean =
    Isabelle_System.getenv("JEDIT_NO_BUILD") == "true"

  def session_options(options: Options): Options = {
    val options1 =
      Isabelle_System.getenv("JEDIT_BUILD_MODE") match {
        case "default" => options
        case mode => options.bool.update("system_heaps", mode == "system")
      }

    val options2 =
      Isabelle_System.getenv("JEDIT_ML_PROCESS_POLICY") match {
        case "" => options1
        case s => options1.string.update("ML_process_policy", s)
      }

    options2
  }

  def sessions_structure(
    options: Options = PIDE.options.value,
    dirs: List[Path] = session_dirs
  ): Sessions.Structure = {
    Sessions.load_structure(session_options(options), dirs = dirs)
  }


  /* raw logic info */

  private val jedit_logic_option = "jedit_logic"

  def logic_name(options: Options): String =
    Isabelle_System.default_logic(
      Isabelle_System.getenv("JEDIT_LOGIC"),
      options.string(jedit_logic_option))

  def logic_ancestor: Option[String] = proper_string(Isabelle_System.getenv("JEDIT_LOGIC_ANCESTOR"))
  def logic_requirements: Boolean = Isabelle_System.getenv("JEDIT_LOGIC_REQUIREMENTS") == "true"
  def logic_include_sessions: List[String] =
    space_explode(':', Isabelle_System.getenv("JEDIT_INCLUDE_SESSIONS"))

  def logic_info(options: Options): Option[Sessions.Info] =
    try { sessions_structure(options = options).get(logic_name(options)) }
    catch { case ERROR(_) => None }

  def logic_root(options: Options): Position.T =
    if (logic_requirements) logic_info(options).map(_.pos) getOrElse Position.none
    else Position.none


  /* logic selector */

  def logic_selector(options: Options_Variable, autosave: Boolean = false): JEdit_Options.Entry = {
    GUI_Thread.require {}

    val default_entry =
      GUI.Selector.Item("", description = "default (" + logic_name(options.value) + ")")

    val session_entries = {
      val sessions = sessions_structure(options = options.value)
      val all_sessions = sessions.imports_topological_order
      val main_sessions = all_sessions.filter(name => sessions(name).main_group)

      main_sessions.map(GUI.Selector.item(_)) ::: List(GUI.Selector.separator()) :::
      all_sessions.sorted.map(GUI.Selector.item(_, batch = 1))
    }

    new GUI.Selector(default_entry :: session_entries) with JEdit_Options.Entry {
      name = jedit_logic_option
      tooltip = "Logic session name (change requires restart)"
      val title = "Logic"
      def load(): Unit = {
        val logic = options.string(jedit_logic_option)
        entries.find {
          case item: GUI.Selector.Item[_] => item.value == logic
          case _ => false
        } match {
          case Some(entry) => selection.item = entry
          case None =>
        }
      }
      def save(): Unit =
        for (item <- selection.item.get_value) options.string(jedit_logic_option) = item

      override def changed(): Unit = if (autosave) save()

      load()
    }
  }


  /* session build process */

  def session_base_info(options: Options): Sessions.Base_Info =
    Sessions.base_info(options,
      dirs = JEdit_Sessions.session_dirs,
      include_sessions = logic_include_sessions,
      session = logic_name(options),
      session_ancestor = logic_ancestor,
      session_requirements = logic_requirements)

  def session_build(
    options: Options,
    progress: Progress = new Progress,
    no_build: Boolean = false
  ): Int = {
    Build.build(session_options(options),
      selection = Sessions.Selection.session(PIDE.resources.session_base.session_name),
      progress = progress, build_heap = true, no_build = no_build, dirs = session_dirs,
      infos = PIDE.resources.session_base_info.infos).rc
  }

  def session_start(options0: Options): Unit = {
    val session = PIDE.session
    val options = session_options(options0)
    val sessions_structure = PIDE.resources.session_base_info.sessions_structure
    val store = Sessions.store(options)

    session.phase_changed += PIDE.plugin.session_phase_changed

    Isabelle_Process.start(session, options, sessions_structure, store,
      logic = PIDE.resources.session_base.session_name,
      modes =
        (space_explode(',', options.string("jedit_print_mode")) :::
         space_explode(',', Isabelle_System.getenv("JEDIT_PRINT_MODE"))).reverse)
  }
}
