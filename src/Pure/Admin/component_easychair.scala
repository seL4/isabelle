/*  Title:      Pure/Admin/component_easychair.scala
    Author:     Makarius

Build Isabelle component for Easychair LaTeX style.

See also https://easychair.org/publications/for_authors
*/

package isabelle


object Component_Easychair {
  /* build easychair component */

  val default_url = "https://easychair.org/publications/easychair.zip"

  def build_easychair(
    download_url: String = default_url,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.with_tmp_file("download", ext = "zip") { download_file =>
      Isabelle_System.with_tmp_dir("download") { download_dir =>

        /* download */

        Isabelle_System.download_file(download_url, download_file, progress = progress)
        Isabelle_System.extract(download_file, download_dir)

        val easychair_dir = File.get_dir(download_dir, title = download_url)


        /* component */

        val version =
          Library.try_unprefix("EasyChair", easychair_dir.file_name)
            .getOrElse("Failed to detect version from " + quote(easychair_dir.file_name))

        val component = "easychair-" + version
        val component_dir =
          Components.Directory(target_dir + Path.basic(component)).create(progress = progress)

        Isabelle_System.extract(download_file, component_dir.path, strip = true)


        /* settings */

        component_dir.write_settings("""
ISABELLE_EASYCHAIR_HOME="$COMPONENT"
""")


        /* README */

        File.write(component_dir.README,
          """This is the Easychair style for authors from
""" + download_url + """


    Makarius
    """ + Date.Format.date(Date.now()) + "\n")
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_easychair", "build component for Easychair LaTeX style",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_url

        val getopts = Getopts("""
Usage: isabelle component_easychair [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")

  Build component for Easychair LaTeX style.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_easychair(download_url = download_url, target_dir = target_dir, progress = progress)
      })
}
