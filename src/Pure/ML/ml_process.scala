/*  Title:      Pure/ML/ml_process.scala
    Author:     Makarius

The raw ML process.
*/

package isabelle


import java.util.{Map => JMap, HashMap}


object ML_Process {
  /* process */

  def apply(
    options: Options,
    session_background: Sessions.Background,
    session_heaps: List[Path],
    use_prelude: List[String] = Nil,
    eval_main: String = "",
    args: List[String] = Nil,
    modes: List[String] = Nil,
    cwd: Path = Path.current,
    env: JMap[String, String] = Isabelle_System.Settings.env(),
    redirect: Boolean = false,
    cleanup: () => Unit = () => ()
  ): Bash.Process = {
    val ml_options = options.standard_ml()
    val ml_settings = ML_Settings(ml_options)

    val eval_init =
      if (session_heaps.isEmpty) {
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
      else {
        List(
          "(PolyML.SaveState.loadHierarchy " +
            ML_Syntax.print_list(
              ML_Syntax.print_string_bytes)(session_heaps.map(File.platform_path)) +
          "; PolyML.print_depth 0)")
      }

    val eval_modes =
      if (modes.isEmpty) Nil
      else List("Print_Mode.add_modes " + ML_Syntax.print_list(ML_Syntax.print_string_bytes)(modes))


    // options
    val eval_options = if (session_heaps.isEmpty) Nil else List("Options.load_default ()")
    val isabelle_process_options = Isabelle_System.tmp_file("options")
    File.restrict(File.path(isabelle_process_options))
    File.write(isabelle_process_options, YXML.string_of_body(ml_options.encode))

    // session resources
    val eval_init_session = if (session_heaps.isEmpty) Nil else List("Resources.init_session_env ()")
    val init_session = Isabelle_System.tmp_file("init_session")
    File.restrict(File.path(init_session))
    File.write(init_session, YXML.string_of_body(new Resources(session_background).init_session_xml))

    // process
    val eval_process =
      proper_string(eval_main).getOrElse(
        if (session_heaps.isEmpty) {
          "PolyML.print_depth " + ML_Syntax.print_int(ml_options.int("ML_print_depth"))
        }
        else "Isabelle_Process.init ()")

    // ISABELLE_TMP
    val isabelle_tmp = Isabelle_System.tmp_dir("process")

    val ml_runtime_options = {
      val ml_options0 = Word.explode(ml_settings.ml_options)
      val ml_options1 =
        if (ml_options0.exists(_.containsSlice("gcthreads"))) ml_options0
        else ml_options0 ::: List("--gcthreads", ml_options.threads().toString)
      val ml_options2 =
        if (!Platform.is_windows || ml_options0.exists(_.containsSlice("codepage"))) ml_options1
        else ml_options1 ::: List("--codepage", "utf8")
      ml_options2 ::: List("--exportstats")
    }

    // bash
    val bash_args =
      ml_runtime_options :::
      (eval_init ::: eval_modes ::: eval_options ::: eval_init_session).flatMap(List("--eval", _)) :::
      use_prelude.flatMap(List("--use", _)) ::: List("--eval", eval_process) ::: args

    val bash_env = new HashMap(env)
    bash_env.put("ML_PLATFORM", ml_settings.ml_platform)
    bash_env.put("ML_HOME", File.standard_path(ml_settings.ml_home))
    bash_env.put("ISABELLE_PROCESS_OPTIONS", File.standard_path(isabelle_process_options))
    bash_env.put("ISABELLE_INIT_SESSION", File.standard_path(init_session))
    bash_env.put("ISABELLE_TMP", File.standard_path(isabelle_tmp))
    bash_env.put("POLYSTATSDIR", isabelle_tmp.getAbsolutePath)

    val process_policy = ml_options.string("process_policy")
    val process_prefix = if_proper(process_policy, process_policy + " ")

    Bash.process(
      process_prefix + File.bash_path(ml_settings.polyml_exe) + " -q " + Bash.strings(bash_args),
      cwd = cwd,
      env = bash_env,
      redirect = redirect,
      cleanup = { () =>
        isabelle_process_options.delete
        init_session.delete
        Isabelle_System.rm_tree(isabelle_tmp)
        cleanup()
      })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("process", "raw ML process (batch mode)",
    Scala_Project.here,
    { args =>
      var dirs: List[Path] = Nil
      var eval_args: List[String] = Nil
      var logic = Isabelle_System.default_logic()
      var modes: List[String] = Nil
      var options = Options.init()

      val getopts = Getopts("""
Usage: isabelle process [OPTIONS]

  Options are:
    -d DIR       include session directory
    -e ML_EXPR   evaluate ML expression on startup
    -f ML_FILE   evaluate ML file on startup
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(logic) + """)
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Run the raw Isabelle ML process in batch mode.
""",
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "e:" -> (arg => eval_args = eval_args ::: List("--eval", arg)),
        "f:" -> (arg => eval_args = eval_args ::: List("--use", arg)),
        "l:" -> (arg => logic = arg),
        "m:" -> (arg => modes = arg :: modes),
        "o:" -> (arg => options = options + arg))

      val more_args = getopts(args)
      if (args.isEmpty || more_args.nonEmpty) getopts.usage()

      val store = Store(options)
      val session_background = Sessions.background(options, logic, dirs = dirs).check_errors
      val session_heaps = store.session_heaps(session_background, logic = logic)
      val result =
        ML_Process(options, session_background, session_heaps, args = eval_args, modes = modes)
          .result(
            progress_stdout = Output.writeln(_, stdout = true),
            progress_stderr = Output.writeln(_))

      sys.exit(result.rc)
    })
}
