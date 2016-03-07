/*  Title:      Pure/System/ml_process.scala
    Author:     Makarius

The underlying ML process.
*/

package isabelle


object ML_Process
{
  def apply(options: Options,
    heap: String = "",
    args: List[String] = Nil,
    process_socket: String = "",
    secure: Boolean = false,
    modes: List[String] = Nil): Bash.Process =
  {
    val load_heaps =
    {
      if (heap == "RAW_ML_SYSTEM") Nil
      else if (heap.iterator.contains('/')) {
        val heap_path = Path.explode(heap)
        if (!heap_path.is_file) error("Bad heap file: " + heap_path)
        List(heap_path)
      }
      else {
        val dirs = Isabelle_System.find_logics_dirs()
        val heap_name = if (heap == "") Isabelle_System.getenv_strict("ISABELLE_LOGIC") else heap
        dirs.map(_ + Path.basic(heap_name)).find(_.is_file) match {
          case Some(heap_path) => List(heap_path)
          case None =>
            error("Unknown logic " + quote(heap) + " -- no heap file found in:\n" +
              cat_lines(dirs.map(dir => "  " + dir.implode)))
        }
      }
    }

    val eval_heaps =
      load_heaps.map(load_heap =>
        "PolyML.SaveState.loadState " + ML_Syntax.print_string_raw(File.platform_path(load_heap)) +
        " handle exn => (TextIO.output (TextIO.stdErr, General.exnMessage exn ^ " +
        ML_Syntax.print_string_raw(": " + load_heap.toString + "\n") +
        "); OS.Process.exit OS.Process.failure)")

    val eval_exit =
      if (load_heaps.isEmpty) {
        List(
          if (Platform.is_windows)
            "fun exit 0 = OS.Process.exit OS.Process.success" +
            " | exit 1 = OS.Process.exit OS.Process.failure" +
            " | exit rc = OS.Process.exit (RunCall.unsafeCast (Word8.fromInt rc))"
          else
            "fun exit rc = Posix.Process.exit (Word8.fromInt rc)"
        )
      }
      else Nil

    val eval_secure = if (secure) List("Secure.set_secure ()") else Nil

    val eval_modes =
      if (modes.isEmpty) Nil
      else List("Print_Mode.add_modes " + ML_Syntax.print_list(ML_Syntax.print_string_raw _)(modes))


    // options
    val isabelle_process_options = Isabelle_System.tmp_file("options")
    File.write(isabelle_process_options, YXML.string_of_body(options.encode))
    val bash_env = Map("ISABELLE_PROCESS_OPTIONS" -> File.standard_path(isabelle_process_options))
    val eval_options = List("Options.load_default ()")

    val eval_process =
      if (process_socket == "") Nil
      else List("Isabelle_Process.init " + ML_Syntax.print_string_raw(process_socket))

    val bash_script =
      """
        [ -z "$ISABELLE_TMP_PREFIX" ] && ISABELLE_TMP_PREFIX=/tmp/isabelle

        export ISABELLE_PID="$$"
        export ISABELLE_TMP="$ISABELLE_TMP_PREFIX$ISABELLE_PID"
        mkdir -p "$ISABELLE_TMP"
        chmod $(umask -S) "$ISABELLE_TMP"

        librarypath "$ML_HOME"
        "$ML_HOME/poly" -q -i $ML_OPTIONS "$@"
        RC="$?"

        rm -f "$ISABELLE_PROCESS_OPTIONS"
        rmdir "$ISABELLE_TMP"

        exit "$RC"
      """

    val bash_args =
      List("-c", bash_script, "ml_process") :::
      (eval_heaps ::: eval_exit ::: eval_secure ::: eval_modes ::: eval_options ::: eval_process).
        map(eval => List("--eval", eval)).flatten ::: args

    Bash.process(null, bash_env, false, bash_args:_*)
  }
}
