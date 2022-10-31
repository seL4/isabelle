/*  Title:      Pure/Admin/build_easychair.scala
    Author:     Makarius

Build Isabelle component for Easychair style.

See also https://easychair.org/publications/for_authors
*/

package isabelle


object Build_Easychair {
  /* build easychair component */

  val default_url = "https://easychair.org/publications/easychair.zip"

  def build_easychair(
    download_url: String = default_url,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.require_command("unzip", test = "-h")

    Isabelle_System.with_tmp_file("download", ext = "zip") { download_file =>
      Isabelle_System.with_tmp_dir("download") { download_dir =>

        /* download */

        Isabelle_System.download_file(download_url, download_file, progress = progress)
        Isabelle_System.bash("unzip -x " + File.bash_path(download_file),
          cwd = download_dir.file).check

        val easychair_dir =
          File.read_dir(download_dir) match {
            case List(name) => download_dir + Path.explode(name)
            case bad =>
              error("Expected exactly one directory entry in " + download_file +
                bad.mkString("\n", "\n  ", ""))
          }


        /* component */

        val version =
          Library.try_unprefix("EasyChair", easychair_dir.file_name)
            .getOrElse("Failed to detect version from " + quote(easychair_dir.file_name))

        val component = "easychair-" + version
        val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component))
        progress.echo("Component " + component_dir)

        component_dir.file.delete
        Isabelle_System.copy_dir(easychair_dir, component_dir)


        /* settings */

        val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
        File.write(etc_dir + Path.basic("settings"),
          """# -*- shell-script -*- :mode=shellscript:

ISABELLE_EASYCHAIR_HOME="$COMPONENT"
""")


        /* README */

        File.write(component_dir + Path.basic("README"),
          """This is the Easychair style for authors from
""" + download_url + """


    Makarius
    """ + Date.Format.date(Date.now()) + "\n")
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_easychair", "build component for Easychair style",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_url

        val getopts = Getopts("""
Usage: isabelle build_easychair [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")

  Build component for Easychair style.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_easychair(download_url = download_url, target_dir = target_dir, progress = progress)
      })
}
