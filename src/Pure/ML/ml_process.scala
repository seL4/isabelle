/*  Title:      Pure/ML/ml_process.scala
    Author:     Makarius

The raw ML process.
*/

package isabelle


import java.io.{File => JFile}


object ML_Process
{
  def apply(options: Options,
    sessions_structure: Sessions.Structure,
    store: Sessions.Store,
    logic: String = "",
    raw_ml_system: Boolean = false,
    use_prelude: List[String] = Nil,
    eval_main: String = "",
    args: List[String] = Nil,
    modes: List[String] = Nil,
    cwd: JFile = null,
    env: Map[String, String] = Isabelle_System.settings(),
    redirect: Boolean = false,
    cleanup: () => Unit = () => (),
    session_base: Option[Sessions.Base] = None): Bash.Process =
  {
    val logic_name = Isabelle_System.default_logic(logic)

    val heaps: List[String] =
      if (raw_ml_system) Nil
      else {
        sessions_structure.selection(logic_name).
          build_requirements(List(logic_name)).
          map(a => File.platform_path(store.the_heap(a)))
      }

    val eval_init =
      if (heaps.isEmpty) {
        List(
          """
          fun chapter (_: string) = ();
          fun section (_: string) = ();
          fun subsection (_: string) = ();
          fun subsubsection (_: string) = ();
          fun paragraph (_: string) = ();
          fun subparagraph (_: string) = ();
          val ML_file = PolyML.use;
          """,
          if (Platform.is_windows)
            "fun exit 0 = OS.Process.exit OS.Process.success" +
            " | exit 1 = OS.Process.exit OS.Process.failure" +
            " | exit rc = OS.Process.exit (RunCall.unsafeCast (Word8.fromInt rc))"
          else
            "fun exit rc = Posix.Process.exit (Word8.fromInt rc)",
          "PolyML.Compiler.prompt1 := \"Poly/ML> \"",
          "PolyML.Compiler.prompt2 := \"Poly/ML# \"")
      }
      else
        List(
          "(PolyML.SaveState.loadHierarchy " +
            ML_Syntax.print_list(ML_Syntax.print_string_bytes)(heaps) +
          "; PolyML.print_depth 0) handle exn => (TextIO.output (TextIO.stdErr, General.exnMessage exn ^ " +
          ML_Syntax.print_string_bytes(": " + logic_name + "\n") +
          "); OS.Process.exit OS.Process.failure)")

    val eval_modes =
      if (modes.isEmpty) Nil
      else List("Print_Mode.add_modes " + ML_Syntax.print_list(ML_Syntax.print_string_bytes)(modes))

    // options
    val isabelle_process_options = Isabelle_System.tmp_file("options")
    Isabelle_System.chmod("600", File.path(isabelle_process_options))
    File.write(isabelle_process_options, YXML.string_of_body(options.encode))
    val env_options = Map("ISABELLE_PROCESS_OPTIONS" -> File.standard_path(isabelle_process_options))
    val eval_options = if (heaps.isEmpty) Nil else List("Options.load_default ()")

    // session base
    val init_session = Isabelle_System.tmp_file("init_session", ext = "ML")
    val init_session_name = init_session.getAbsolutePath
    Isabelle_System.chmod("600", File.path(init_session))
    File.write(init_session,
      session_base match {
        case None => ""
        case Some(base) =>
          def print_table(table: List[(String, String)]): String =
            ML_Syntax.print_list(
              ML_Syntax.print_pair(
                ML_Syntax.print_string_bytes, ML_Syntax.print_string_bytes))(table)
          def print_list: List[String] => String =
            ML_Syntax.print_list(ML_Syntax.print_string_bytes)
          def print_sessions: List[(String, Position.T)] => String =
            ML_Syntax.print_list(
              ML_Syntax.print_pair(ML_Syntax.print_string_bytes, ML_Syntax.print_properties))
          def print_bibtex_entries: List[(String, List[String])] => String =
            ML_Syntax.print_list(
              ML_Syntax.print_pair(ML_Syntax.print_string_bytes,
                ML_Syntax.print_list(ML_Syntax.print_string_bytes)))

          "Resources.init_session" +
            "{session_positions = " + print_sessions(sessions_structure.session_positions) +
            ", session_directories = " + print_table(sessions_structure.dest_session_directories) +
            ", session_chapters = " + print_table(sessions_structure.session_chapters) +
            ", bibtex_entries = " + print_bibtex_entries(sessions_structure.bibtex_entries) +
            ", docs = " + print_list(base.doc_names) +
            ", global_theories = " + print_table(base.global_theories.toList) +
            ", loaded_theories = " + print_list(base.loaded_theories.keys) + "}"
      })

    // process
    val eval_process =
      proper_string(eval_main).getOrElse(
        if (heaps.isEmpty) {
          "PolyML.print_depth " + ML_Syntax.print_int(options.int("ML_print_depth"))
        }
        else "Isabelle_Process.init ()")

    // ISABELLE_TMP
    val isabelle_tmp = Isabelle_System.tmp_dir("process")
    val env_tmp =
      Map("ISABELLE_TMP" -> File.standard_path(isabelle_tmp),
        "POLYSTATSDIR" -> isabelle_tmp.getAbsolutePath)

    val env_functions = Map("ISABELLE_SCALA_FUNCTIONS" -> Scala.functions.mkString(","))

    val ml_runtime_options =
    {
      val ml_options = Word.explode(Isabelle_System.getenv("ML_OPTIONS"))
      val ml_options1 =
        if (ml_options.exists(_.containsSlice("gcthreads"))) ml_options
        else ml_options ::: List("--gcthreads", options.int("threads").toString)
      val ml_options2 =
        if (!Platform.is_windows || ml_options.exists(_.containsSlice("codepage"))) ml_options1
        else ml_options1 ::: List("--codepage", "utf8")
      ml_options2 ::: List("--exportstats")
    }

    // bash
    val bash_args =
      ml_runtime_options :::
      (eval_init ::: eval_modes ::: eval_options).flatMap(List("--eval", _)) :::
      List("--use", init_session_name,
        "--eval", "OS.FileSys.remove " + ML_Syntax.print_string_bytes(init_session_name)) :::
      use_prelude.flatMap(List("--use", _)) ::: List("--eval", eval_process) ::: args

    Bash.process(
      "exec " + options.string("ML_process_policy") + """ "$ML_HOME/poly" -q """ +
        Bash.strings(bash_args),
      cwd = cwd,
      env = env ++ env_options ++ env_tmp ++ env_functions,
      redirect = redirect,
      cleanup = () =>
        {
          isabelle_process_options.delete
          init_session.delete
          Isabelle_System.rm_tree(isabelle_tmp)
          cleanup()
        })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("process", "raw ML process (batch mode)", args =>
  {
    var dirs: List[Path] = Nil
    var eval_args: List[String] = Nil
    var logic = Isabelle_System.getenv("ISABELLE_LOGIC")
    var modes: List[String] = Nil
    var options = Options.init()

    val getopts = Getopts("""
Usage: isabelle process [OPTIONS]

  Options are:
    -T THEORY    load theory
    -d DIR       include session directory
    -e ML_EXPR   evaluate ML expression on startup
    -f ML_FILE   evaluate ML file on startup
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(logic) + """)
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Run the raw Isabelle ML process in batch mode.
""",
      "T:" -> (arg =>
        eval_args = eval_args ::: List("--eval", "use_thy " + ML_Syntax.print_string_bytes(arg))),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "e:" -> (arg => eval_args = eval_args ::: List("--eval", arg)),
      "f:" -> (arg => eval_args = eval_args ::: List("--use", arg)),
      "l:" -> (arg => logic = arg),
      "m:" -> (arg => modes = arg :: modes),
      "o:" -> (arg => options = options + arg))

    val more_args = getopts(args)
    if (args.isEmpty || more_args.nonEmpty) getopts.usage()

    val sessions_structure = Sessions.load_structure(options, dirs = dirs)
    val store = Sessions.store(options)

    val result =
      ML_Process(options, sessions_structure, store, logic = logic, args = eval_args, modes = modes)
        .result(
          progress_stdout = Output.writeln(_, stdout = true),
          progress_stderr = Output.writeln(_))

    sys.exit(result.rc)
  })
}
