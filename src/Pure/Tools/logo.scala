/*  Title:      Pure/Tools/logo.scala
    Author:     Makarius

Create variants of the Isabelle logo (PDF).
*/

package isabelle


object Logo
{
  /* create logo */

  def create_logo(logo_name: String, output_file: Path, quiet: Boolean = false): Unit =
  {
    Isabelle_System.with_tmp_file("logo", ext = "eps")(tmp_file =>
    {
      val template = File.read(Path.explode("$ISABELLE_HOME/lib/logo/isabelle_any.eps"))
      File.write(tmp_file, template.replace("<any>", logo_name))
      Isabelle_System.bash(
        "\"$ISABELLE_EPSTOPDF\" --filter < " + File.bash_path(tmp_file) +
          " > " + File.bash_path(output_file)).check
      if (!quiet) Output.writeln(output_file.expand.implode)
    })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("logo", "create variants of the Isabelle logo (PDF)", Scala_Project.here, args =>
    {
      var output: Option[Path] = None
      var quiet = false

      val getopts = Getopts("""
Usage: isabelle logo [OPTIONS] [NAME]

  Options are:
    -o FILE      alternative output file
    -q           quiet mode

  Create variant NAME of the Isabelle logo as "isabelle_name.pdf".
""",
        "o:" -> (arg => output = Some(Path.explode(arg))),
        "q" -> (_ => quiet = true))

      val more_args = getopts(args)
      val (logo_name, output_file) =
        more_args match {
          case Nil => ("", Path.explode("isabelle").pdf)
          case List(a) => (a, output.getOrElse(Path.explode("isabelle_" + Word.lowercase(a)).pdf))
          case _ => getopts.usage()
        }

      create_logo(logo_name, output_file, quiet = quiet)
    })
}
