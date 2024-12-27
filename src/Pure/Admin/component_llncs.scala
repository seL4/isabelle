/*  Title:      Pure/Admin/component_llncs.scala
    Author:     Makarius

Build Isabelle component for Springer LaTeX LNCS style.

See also:

  - https://ctan.org/pkg/llncs?lang=en
  - https://www.springer.com/gp/computer-science/lncs/conference-proceedings-guidelines
*/

package isabelle


object Component_LLNCS {
  /* build llncs component */

  val default_url = "https://mirrors.ctan.org/macros/latex/contrib/llncs.zip"

  def build_llncs(
    download_url: String = default_url,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.with_tmp_file("download", ext = "zip") { download_file =>
      Isabelle_System.with_tmp_dir("download") { download_dir =>

        /* download */

        Isabelle_System.download_file(download_url, download_file, progress = progress)
        Isabelle_System.extract(download_file, download_dir)

        val llncs_dir = File.get_dir(download_dir, title = download_url)


        /* component */

        val README_md = Path.explode("README.md")
        val version = {
          val Version = """^_.* v(.*)_$""".r
          split_lines(File.read(llncs_dir + README_md))
            .collectFirst({ case Version(v) => v })
            .getOrElse(error("Failed to detect version in " + README_md))
        }

        val component = "llncs-" + version
        val component_dir =
          Components.Directory(target_dir + Path.basic(component)).create(progress = progress)

        Isabelle_System.extract(download_file, component_dir.path, strip = true)


        /* settings */

        component_dir.write_settings("""
ISABELLE_LLNCS_HOME="$COMPONENT"
""")


        /* README */

        File.change(component_dir.path + README_md)(_.replace("&nbsp;", HTML.space))

        File.write(component_dir.README,
          """This is the Springer LaTeX LNCS style for authors from
""" + download_url + """


    Makarius
    """ + Date.Format.date(Date.now()) + "\n")
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_llncs", "build component for Springer LaTeX LNCS style",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_url

        val getopts = Getopts("""
Usage: isabelle component_llncs [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")

  Build component for Springer LaTeX LNCS style.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_llncs(download_url = download_url, target_dir = target_dir, progress = progress)
      })
}
