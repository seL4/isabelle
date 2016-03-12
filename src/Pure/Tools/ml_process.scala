/*  Title:      Pure/Tools/ml_process.scala
    Author:     Makarius

The raw ML process.
*/

package isabelle


import java.io.{File => JFile}


object ML_Process
{
  def apply(options: Options,
    heap: String = "",
    args: List[String] = Nil,
    modes: List[String] = Nil,
    secure: Boolean = false,
    cwd: JFile = null,
    env: Map[String, String] = Map.empty,
    redirect: Boolean = false,
    channel: Option[System_Channel] = None): Bash.Process =
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
            error("Unknown logic " + quote(heap_name) + " -- no heap file found in:\n" +
              cat_lines(dirs.map(dir => "  " + dir.implode)))
        }
      }
    }

    val eval_heaps =
      load_heaps.map(load_heap =>
        "(PolyML.SaveState.loadState " + ML_Syntax.print_string_raw(File.platform_path(load_heap)) +
        "; PolyML.print_depth 0) handle exn => (TextIO.output (TextIO.stdErr, General.exnMessage exn ^ " +
        ML_Syntax.print_string_raw(": " + load_heap.toString + "\n") +
        "); OS.Process.exit OS.Process.failure)")

    val eval_initial =
      if (load_heaps.isEmpty) {
        List(
          if (Platform.is_windows)
            "fun exit 0 = OS.Process.exit OS.Process.success" +
            " | exit 1 = OS.Process.exit OS.Process.failure" +
            " | exit rc = OS.Process.exit (RunCall.unsafeCast (Word8.fromInt rc))"
          else
            "fun exit rc = Posix.Process.exit (Word8.fromInt rc)",
          "PolyML.Compiler.prompt1 := \"ML> \"",
          "PolyML.Compiler.prompt2 := \"ML# \"")
      }
      else Nil

    val eval_modes =
      if (modes.isEmpty) Nil
      else List("Print_Mode.add_modes " + ML_Syntax.print_list(ML_Syntax.print_string_raw _)(modes))

    // options
    val isabelle_process_options = Isabelle_System.tmp_file("options")
    File.write(isabelle_process_options, YXML.string_of_body(options.encode))
    val env_options = Map("ISABELLE_PROCESS_OPTIONS" -> File.standard_path(isabelle_process_options))
    val eval_options = if (load_heaps.isEmpty) Nil else List("Options.load_default ()")

    val eval_secure = if (secure) List("Secure.set_secure ()") else Nil

    val eval_process =
      if (load_heaps.isEmpty)
        List("PolyML.print_depth 10")
      else
        channel match {
          case None =>
            List("(default_print_depth 10; Isabelle_Process.init_options ())")
          case Some(ch) =>
            List("(default_print_depth 10; Isabelle_Process.init_protocol " +
              ML_Syntax.print_string_raw(ch.server_name) + ")")
        }

    // bash
    val bash_args =
      Word.explode(Isabelle_System.getenv("ML_OPTIONS")) :::
      (eval_heaps ::: eval_initial ::: eval_modes ::: eval_options ::: eval_secure ::: eval_process).
        map(eval => List("--eval", eval)).flatten ::: args

    Bash.process(
      """
        [ -z "$ISABELLE_TMP_PREFIX" ] && ISABELLE_TMP_PREFIX=/tmp/isabelle

        export ISABELLE_TMP="$ISABELLE_TMP_PREFIX$$"
        mkdir -p "$ISABELLE_TMP"
        chmod $(umask -S) "$ISABELLE_TMP"

        librarypath "$ML_HOME"
        "$ML_HOME/poly" -q """ + File.bash_args(bash_args) + """
        RC="$?"

        rm -f "$ISABELLE_PROCESS_OPTIONS"
        rmdir "$ISABELLE_TMP"

        exit "$RC"
      """, cwd = cwd, env = env ++ env_options, redirect = redirect)
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      var eval_args: List[String] = Nil
      var modes: List[String] = Nil
      var options = Options.init()

      val getopts = Getopts("""
Usage: isabelle process [OPTIONS] [HEAP]

  Options are:
    -e ML_EXPR   evaluate ML expression on startup
    -f ML_FILE   evaluate ML file on startup
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Run the raw Isabelle ML process in batch mode, using a given heap image.

  If HEAP is a plain name (default ISABELLE_LOGIC=""" +
  quote(Isabelle_System.getenv("ISABELLE_LOGIC")) + """), it is searched in
  ISABELLE_PATH; if it contains a slash, it is taken as literal file;
  if it is "RAW_ML_SYSTEM", the initial ML heap is used.
""",
        "e:" -> (arg => eval_args = eval_args ::: List("--eval", arg)),
        "f:" -> (arg => eval_args = eval_args ::: List("--use", arg)),
        "m:" -> (arg => modes = arg :: modes),
        "o:" -> (arg => options = options + arg))

      if (args.isEmpty) getopts.usage()
      val heap =
        getopts(args) match {
          case Nil => ""
          case List(heap) => heap
          case _ => getopts.usage()
        }

      ML_Process(options, heap = heap, args = eval_args ::: args.toList, modes = modes).
        result().print_stdout.rc
    }
  }
}
