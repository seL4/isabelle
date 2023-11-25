/*  Title:      Tools/Demo/src/demo_tool.scala
    Author:     Makarius

Isabelle command-line tool demo.
*/

package isabelle.demo

import isabelle._


object Demo_Tool {
  /* component resources */

  def home: Path = Path.explode("$ISABELLE_DEMO_HOME")
  def readme: Path = home + Path.explode("README.md")


  /* main entry point in Scala */

  def demo(options: Options, args: List[String], progress: Progress = new Progress): Unit = {
    val prefix = options.string("demo_prefix")
    for (arg <- args) progress.echo(Library.prefix_lines(prefix, arg))
    if (progress.verbose) progress.echo("\nSee also " + readme.expand)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("demo", "Isabelle command-line tool demo",
      Scala_Project.here, { args =>
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle demo [OPTIONS] ARGS ...

  Options are:
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode: print more explanations

  Echo given arguments, with optional verbose mode. Example:

    isabelle demo -v -o demo_prefix="+++ " A B C
""",
          "o:" -> (arg => options = options + arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.isEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        demo(options, more_args, progress = progress)
      })
}

class Tools extends Isabelle_Scala_Tools(Demo_Tool.isabelle_tool)
