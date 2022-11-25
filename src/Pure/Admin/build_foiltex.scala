/*  Title:      Pure/Admin/build_foiltex.scala
    Author:     Makarius

Build Isabelle component for FoilTeX.

See also https://ctan.org/pkg/foiltex
*/

package isabelle


object Build_Foiltex {
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

        val README = Path.explode("README")
        val README_flt = Path.explode("README.flt")
        Isabelle_System.move_file(foiltex_dir + README, foiltex_dir + README_flt)

        Isabelle_System.bash("pdflatex foiltex.ins", cwd = foiltex_dir.file).check


        /* component */

        val version = {
          val Version = """^.*Instructions for FoilTeX Version\s*(.*)$""".r
          split_lines(File.read(foiltex_dir + README_flt))
            .collectFirst({ case Version(v) => v })
            .getOrElse(error("Failed to detect version in " + README_flt))
        }

        val component = "foiltex-" + version
        val component_dir =
          Components.Directory.create(target_dir + Path.basic(component), progress = progress)

        Isabelle_System.rm_tree(component_dir.path)
        Isabelle_System.copy_dir(foiltex_dir, component_dir.path)
        Isabelle_System.make_directory(component_dir.etc)


        /* settings */

        File.write(component_dir.settings,
          """# -*- shell-script -*- :mode=shellscript:

ISABELLE_FOILTEX_HOME="$COMPONENT"
""")


        /* README */

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
    Isabelle_Tool("build_foiltex", "build component for FoilTeX",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_url

        val getopts = Getopts("""
Usage: isabelle build_foiltex [OPTIONS]

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
