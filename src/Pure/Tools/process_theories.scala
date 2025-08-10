/*  Title:      Pure/Tools/process_theories.scala
    Author:     Makarius

Process theories within an adhoc session context.
*/

package isabelle


import java.io.{File => JFile}

import scala.collection.mutable
import scala.util.matching.Regex


object Process_Theories {
  /** process theories **/

  def read_files(path: Path): List[Path] =
    Library.trim_split_lines(File.read(path)).map(Path.explode)

  def process_theories(
    options: Options,
    logic: String,
    theories: List[String],
    files: List[Path] = Nil,
    dirs: List[Path] = Nil,
    output_messages: Boolean = false,
    message_head: List[Regex],
    message_body: List[Regex],
    margin: Double = Pretty.default_margin,
    breakgain: Double = Pretty.default_breakgain,
    metric: Pretty.Metric = Symbol.Metric,
    progress: Progress = new Progress
  ): Build.Results = {
    Isabelle_System.with_tmp_dir("private") { private_dir =>
      /* options */

      val build_engine = Build.Engine(Build.engine_name(options))
      val build_options = build_engine.build_options(options)


      /* session directory and files */

      val private_prefix = private_dir.implode + "/"

      val session_name = Sessions.DRAFT
      val session_dir = Isabelle_System.make_directory(private_dir + Path.basic(session_name))

      {
        var seen = Set.empty[JFile]
        for (path0 <- files) {
          val path = path0.canonical
          val file = path.file
          if (!seen(file)) {
            seen += file
            val target = session_dir + path.base
            if (target.is_file) {
              error("Duplicate session source file " + path.base + " --- from " + path)
            }
            Isabelle_System.copy_file(path, target)
          }
        }
      }

      /* session theories */

      val more_theories =
        for (path <- files; name <- Thy_Header.get_thy_name(path.implode))
          yield name

      val session_theories = theories ::: more_theories


      /* session imports */

      val sessions_structure = Sessions.load_structure(build_options, dirs = dirs)

      val session_imports =
        Set.from(
          for {
            name <- session_theories.iterator
            session = sessions_structure.theory_qualifier(name)
            if session.nonEmpty
          } yield session).toList


      /* build adhoc session */

      val session_entry =
        Sessions.Session_Entry(
          parent = Some(logic),
          theories = session_theories.map(a => (Nil, List(((a, Position.none), false)))),
          imports = session_imports)

      val session_info =
        Sessions.Info.make(session_entry, draft_session = true,
          dir = session_dir, options = options)

      def session_setup(setup_session_name: String, session: Session): Unit = {
        if (output_messages && setup_session_name == session_name) {
          session.all_messages += Session.Consumer[Prover.Message]("process_theories") {
            case output: Prover.Output
              if Protocol.is_exported(output.message) || Protocol.is_state(output.message) =>
              output.properties match {
                case Position.Line_File(line, file0) =>
                  val file = Library.perhaps_unprefix(private_prefix, file0)
                  val pos = Position.Line_File(line, file)
                  if (Build.print_log_check(pos, output.message, message_head, message_body)) {
                    progress.echo(Protocol.message_text(output.message, heading = true, pos = pos,
                      margin = margin, breakgain = breakgain, metric = metric))
                  }
                case _ =>
              }
            case _ =>
          }
        }
      }

      Build.build(options, private_dir = Some(private_dir), progress = progress,
        infos = List(session_info), selection = Sessions.Selection.session(session_name),
        session_setup = session_setup)
    }
  }



  /** Isabelle tool wrapper **/

  val isabelle_tool = Isabelle_Tool("process_theories",
    "process theories within an adhoc session context",
    Scala_Project.here,
    { args =>
      val message_head = new mutable.ListBuffer[Regex]
      val message_body = new mutable.ListBuffer[Regex]
      var output_messages = false
      val dirs = new mutable.ListBuffer[Path]
      val files = new mutable.ListBuffer[Path]
      var logic = Isabelle_System.getenv("ISABELLE_LOGIC")
      var margin = Pretty.default_margin
      var options = Options.init()
      var verbose = false


      val getopts = Getopts("""
Usage: isabelle process_theories [OPTIONS] [THEORIES...]

  Options are:
    -F FILE      include addition session files, listed in FILE
    -H REGEX     filter messages by matching against head
    -M REGEX     filter messages by matching against body
    -O           output messages
    -d DIR       include session directory
    -f FILE      include addition session files
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(logic) + """)
    -m MARGIN    margin for pretty printing (default: """ + margin + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose

  Process theories within an adhoc session context.
""",
        "F:" -> (arg => files ++= read_files(Path.explode(arg))),
        "H:" -> (arg => message_head += arg.r),
        "M:" -> (arg => message_body += arg.r),
        "O" -> (_ => output_messages = true),
        "d:" -> (arg => dirs += Path.explode(arg)),
        "f:" -> (arg => files += Path.explode(arg)),
        "l:" -> (arg => logic = arg),
        "m:" -> (arg => margin = Value.Double.parse(arg)),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true))

      val theories = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      val results =
        progress.interrupt_handler {
          process_theories(options, logic, theories, files = files.toList, dirs = dirs.toList,
            output_messages = output_messages, message_head = message_head.toList,
            message_body = message_body.toList, margin = margin, progress = progress)
        }

      sys.exit(results.rc)
    })
}
