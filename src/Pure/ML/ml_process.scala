/*  Title:      Pure/ML/ml_process.scala
    Author:     Makarius

The raw ML process.
*/

package isabelle


import java.io.{File => JFile}


object ML_Process
{
  def apply(options: Options,
    logic: String = "",
    args: List[String] = Nil,
    dirs: List[Path] = Nil,
    modes: List[String] = Nil,
    raw_ml_system: Boolean = false,
    cwd: JFile = null,
    env: Map[String, String] = Isabelle_System.settings(),
    redirect: Boolean = false,
    cleanup: () => Unit = () => (),
    channel: Option[System_Channel] = None,
    sessions_structure: Option[Sessions.Structure] = None,
    session_base: Option[Sessions.Base] = None,
    store: Option[Sessions.Store] = None): Bash.Process =
  {
    val logic_name = Isabelle_System.default_logic(logic)
    val _store = store.getOrElse(Sessions.store(options))

    val heaps: List[String] =
      if (raw_ml_system) Nil
      else {
        val selection = Sessions.Selection(sessions = List(logic_name))
        val selected_sessions =
          sessions_structure.getOrElse(Sessions.load_structure(options, dirs = dirs))
            .selection(selection)
        selected_sessions.build_requirements(List(logic_name)).
          map(a => File.platform_path(_store.the_heap(a)))
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
          if (Isabelle_System.getenv("ML_SYSTEM") == "polyml-5.6")
            """
              structure FixedInt = IntInf;
              structure RunCall =
              struct
                open RunCall
                val loadWord: word * word -> word =
                  run_call2 RuntimeCalls.POLY_SYS_load_word;
                val storeWord: word * word * word -> unit =
                  run_call3 RuntimeCalls.POLY_SYS_assign_word;
              end;
            """
          else "",
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
    File.write(isabelle_process_options, YXML.string_of_body(options.encode))
    val env_options = Map("ISABELLE_PROCESS_OPTIONS" -> File.standard_path(isabelle_process_options))
    val eval_options = if (heaps.isEmpty) Nil else List("Options.load_default ()")

    // session base
    val eval_session_base =
      session_base match {
        case None => Nil
        case Some(base) =>
          def print_table(table: List[(String, String)]): String =
            ML_Syntax.print_list(
              ML_Syntax.print_pair(
                ML_Syntax.print_string_bytes, ML_Syntax.print_string_bytes))(table)
          def print_list(list: List[String]): String =
            ML_Syntax.print_list(ML_Syntax.print_string_bytes)(list)
          def print_sessions(list: List[(String, Position.T)]): String =
            ML_Syntax.print_list(
              ML_Syntax.print_pair(ML_Syntax.print_string_bytes, ML_Syntax.print_properties))(list)

          List("Resources.init_session_base" +
            " {sessions = " + print_sessions(base.known.sessions.toList) +
            ", docs = " + print_list(base.doc_names) +
            ", global_theories = " + print_table(base.global_theories.toList) +
            ", loaded_theories = " + print_list(base.loaded_theories.keys) +
            ", known_theories = " + print_table(base.dest_known_theories) + "}")
      }

    // process
    val eval_process =
      if (heaps.isEmpty)
        List("PolyML.print_depth " + ML_Syntax.print_int(options.int("ML_print_depth")))
      else
        channel match {
          case None =>
            List("Isabelle_Process.init_options ()")
          case Some(ch) =>
            List("Isabelle_Process.init_protocol " + ML_Syntax.print_string_bytes(ch.server_name))
        }

    // ISABELLE_TMP
    val isabelle_tmp = Isabelle_System.tmp_dir("process")
    val env_tmp = Map("ISABELLE_TMP" -> File.standard_path(isabelle_tmp))

    val ml_runtime_options =
    {
      val ml_options = Word.explode(Isabelle_System.getenv("ML_OPTIONS"))
      if (ml_options.exists(_.containsSlice("gcthreads"))) ml_options
      else ml_options ::: List("--gcthreads", options.int("threads").toString)
    }

    // bash
    val bash_args =
      ml_runtime_options :::
      (eval_init ::: eval_modes ::: eval_options ::: eval_session_base ::: eval_process).
        map(eval => List("--eval", eval)).flatten ::: args

    Bash.process(
      "exec " + options.string("ML_process_policy") + """ "$ML_HOME/poly" -q """ +
        Bash.strings(bash_args),
      cwd = cwd,
      env = env ++ env_options ++ env_tmp,
      redirect = redirect,
      cleanup = () =>
        {
          isabelle_process_options.delete
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
    if (args.isEmpty || !more_args.isEmpty) getopts.usage()

    val rc = ML_Process(options, logic = logic, args = eval_args, dirs = dirs, modes = modes).
      result().print_stdout.rc
    sys.exit(rc)
  })
}
