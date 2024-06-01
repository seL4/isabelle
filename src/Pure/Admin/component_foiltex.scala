/*  Title:      Pure/Admin/component_foiltex.scala
    Author:     Makarius

Build Isabelle component for FoilTeX.

See also https://ctan.org/pkg/foiltex
*/

package isabelle


object Component_Foiltex {
  /* build FoilTeX component */

  val default_url = "https://mirrors.ctan.org/macros/latex/contrib/foiltex.zip"

  def build_foiltex(
    download_url: String = default_url,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.with_tmp_file("download", ext = "zip") { download_file =>
      Isabelle_System.with_tmp_dir("download") { download_dir =>

        /* download */

        Isabelle_System.download_file(download_url, download_file, progress = progress)
        Isabelle_System.extract(download_file, download_dir)

        val foiltex_dir = File.get_dir(download_dir, title = download_url)


        /* component */

        val README = Path.explode("README")
        val version = {
          val Version = """^.*Instructions for FoilTeX Version\s*(.*)$""".r
          split_lines(File.read(foiltex_dir + README))
            .collectFirst({ case Version(v) => v })
            .getOrElse(error("Failed to detect version in " + README))
        }

        val component = "foiltex-" + version
        val component_dir =
          Components.Directory(target_dir + Path.basic(component)).create(progress = progress)

        Isabelle_System.extract(download_file, component_dir.path, strip = true)

        Isabelle_System.bash("pdflatex foiltex.ins", cwd = component_dir.path).check
        (component_dir.path + Path.basic("foiltex.log")).file.delete()


        /* settings */

        component_dir.write_settings("""
ISABELLE_FOILTEX_HOME="$COMPONENT"
""")


        /* README */

        Isabelle_System.move_file(component_dir.README,
          component_dir.path + Path.basic("README.flt"))

        File.write(component_dir.README,
          """This is FoilTeX from
""" + download_url + """


    Makarius
    """ + Date.Format.date(Date.now()) + "\n")
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_foiltex", "build component for FoilTeX",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_url

        val getopts = Getopts("""
Usage: isabelle component_foiltex [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")

  Build component for FoilTeX: slides in LaTeX.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_foiltex(download_url = download_url, target_dir = target_dir, progress = progress)
      })
}
