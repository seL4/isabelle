/*  Title:      Pure/Admin/component_pdfjs.scala
    Author:     Makarius

Build Isabelle component for Mozilla PDF.js.

See also:

  - https://github.com/mozilla/pdf.js
  - https://github.com/mozilla/pdf.js/releases
  - https://github.com/mozilla/pdf.js/wiki/Setup-PDF.js-in-a-website
*/

package isabelle


object Component_PDFjs {
  /* build pdfjs component */

  val default_url = "https://github.com/mozilla/pdf.js/releases/download"
  val default_version = "5.4.149"

  def build_pdfjs(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component name */

    val component = "pdfjs-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download */

    val download_url = base_url + "/v" + version
    Isabelle_System.with_tmp_file("archive", ext = "zip") { archive_file =>
      Isabelle_System.download_file(download_url + "/pdfjs-" + version + "-legacy-dist.zip",
        archive_file, progress = progress)
      Isabelle_System.extract(archive_file, component_dir.path)
    }


    /* settings */

    component_dir.write_settings("""
ISABELLE_PDFJS_HOME="$COMPONENT"
""")


    /* README */

    File.write(component_dir.README,
      """This is PDF.js from
""" + download_url + """


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_pdfjs", "build component for Mozilla PDF.js",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_pdfjs [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")

  Build component for PDF.js.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_pdfjs(base_url = base_url, version = version, target_dir = target_dir,
          progress = progress)
      })
}
