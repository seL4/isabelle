/*  Title:      Pure/Admin/build_lipics.scala
    Author:     Makarius

Build Isabelle component for Dagstuhl LIPIcs style.

See also:

  - https://github.com/dagstuhl-publishing/styles
  - https://submission.dagstuhl.de/documentation/authors
  - https://www.dagstuhl.de/en/publications/lipics
*/

package isabelle


object Build_LIPIcs {
  /* files for document preparation */

  val document_files: List[Path] =
    for (name <- List("cc-by.pdf", "lipics-logo-bw.pdf", "lipics-v2021.cls"))
      yield Path.explode("$ISABELLE_LIPICS_HOME/" + name)


  /* build lipics component */

  val default_url = "https://github.com/dagstuhl-publishing/styles/archive/refs/tags/v2021.1.2.tar.gz"

  def build_lipics(
    download_url: String = default_url,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.with_tmp_file("download", ext = "tar.gz") { download_file =>
      Isabelle_System.with_tmp_dir("download") { download_dir =>

        /* download */

        Isabelle_System.download_file(download_url, download_file, progress = progress)
        Isabelle_System.gnutar("-xzf " + File.bash_path(download_file),
          dir = download_dir, strip = 1).check

        val lipics_dir = download_dir + Path.explode("LIPIcs/authors")


        /* component */

        val version = {
          val Version = """^*.* v(.*)$""".r
          val changelog = Path.explode("CHANGELOG.md")
          split_lines(File.read(lipics_dir + changelog))
            .collectFirst({ case Version(v) => v })
            .getOrElse(error("Failed to detect version in " + changelog))
        }

        val component = "lipics-" + version
        val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component))
        progress.echo("Component " + component_dir)

        Isabelle_System.copy_dir(lipics_dir, component_dir)


        /* settings */

        val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
        File.write(etc_dir + Path.basic("settings"),
          """# -*- shell-script -*- :mode=shellscript:

ISABELLE_LIPICS_HOME="$COMPONENT/authors"
""")


        /* README */

        File.write(component_dir + Path.basic("README"),
          """This is the Dagstuhl LIPIcs style for authors from
""" + download_url + """


    Makarius
    """ + Date.Format.date(Date.now()) + "\n")
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_lipics", "build component for Dagstuhl LIPIcs style",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_url

        val getopts = Getopts("""
Usage: isabelle build_lipics [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")

  Build component for Dagstuhl LIPIcs style.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_lipics(download_url = download_url, target_dir = target_dir, progress = progress)
      })
}
