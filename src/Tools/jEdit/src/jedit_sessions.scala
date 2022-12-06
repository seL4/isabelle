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


  /* session selectors */

  class Selector(
    val options: Options_Variable,
    val option_name: String,
    autosave: Boolean,
    batches: List[GUI.Selector.Entry[String]]*)
  extends GUI.Selector[String](batches: _*) with JEdit_Options.Entry {
    name = option_name
    tooltip = Word.capitalize(options.value.description(option_name))

    override val title: String =
      options.value.check_name(option_name).title("jedit")
    override def load(): Unit = {
      val value = options.string(option_name)
      for (entry <- find_value(_ == value)) selection.item = entry
    }
    override def save(): Unit =
      for (value <- selection_value) options.string(option_name) = value

    override def changed(): Unit = if (autosave) save()

    load()
  }

  def logic_selector(options: Options_Variable, autosave: Boolean = false): JEdit_Options.Entry =
    GUI_Thread.require {
      val sessions = sessions_structure(options = options.value)
      val all_sessions = sessions.imports_topological_order
      val main_sessions = all_sessions.filter(name => sessions(name).main_group)

      val default_entry =
        GUI.Selector.item_description("", "default (" + logic_name(options.value) + ")")

      new Selector(options, jedit_logic_option, autosave,
        default_entry :: main_sessions.map(GUI.Selector.item),
        all_sessions.sorted.map(GUI.Selector.item))
    }

  def document_selector(options: Options_Variable, autosave: Boolean = false): JEdit_Options.Entry =
    GUI_Thread.require {
      val sessions = sessions_structure(options = options.value)
      val all_sessions = sessions.build_topological_order.sorted
      val doc_sessions = all_sessions.filter(name => sessions(name).doc_group)

      new Selector(options, "editor_document_session", autosave,
        doc_sessions.map(GUI.Selector.item),
        all_sessions.map(GUI.Selector.item))
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
