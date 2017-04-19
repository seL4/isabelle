/*  Title:      Pure/Tools/update_imports.scala
    Author:     Makarius

Update theory imports to use session qualifiers.
*/

package isabelle


object Update_Imports
{
  /* update imports */

  def update_imports(
    options: Options,
    progress: Progress = No_Progress,
    selection: Sessions.Selection = Sessions.Selection.empty,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    verbose: Boolean = false)
  {
    val full_sessions = Sessions.load(options, dirs, select_dirs)
    val (selected, selected_sessions) = full_sessions.selection(selection)
    val deps =
      Sessions.deps(selected_sessions, progress = progress, verbose = verbose,
        global_theories = full_sessions.global_theories)

    // FIXME
    selected.foreach(progress.echo(_))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("update_imports", "update theory imports to use session qualifiers", args =>
    {
      var select_dirs: List[Path] = Nil
      var requirements = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
      var options = Options.init()
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle update_imports [OPTIONS] [SESSIONS ...]

  Options are:
    -D DIR       include session directory and select its sessions
    -R           operate on requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Update theory imports to use session qualifiers.

  Old versions of files are preserved by appending "~~".
""",
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "R" -> (_ => requirements = true),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "o:" -> (arg => options = options + arg),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)
      if (args.isEmpty) getopts.usage()

      val selection =
        Sessions.Selection(requirements, all_sessions, exclude_session_groups,
          exclude_sessions, session_groups, sessions)

      val progress = new Console_Progress(verbose = verbose)

      update_imports(options, progress = progress, selection = selection,
        dirs = dirs, select_dirs = select_dirs, verbose = verbose)
    })
}
