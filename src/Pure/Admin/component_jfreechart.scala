/*  Title:      Pure/Admin/component_jfreechart.scala
    Author:     Makarius

Build Isabelle jfreechart component from official sources.
*/

package isabelle


object Component_JFreeChart {
  /* build jfreechart */

  val default_source_url = "https://github.com/jfree/jfreechart/archive/refs/tags/v{V}.tar.gz"
  val default_version = "1.5.6"

  def build_jfreechart(
    target_dir: Path = Path.current,
    source_url: String = default_source_url,
    version: String = default_version,
    progress: Progress = new Progress,
  ): Unit = {
    /* component */

    val component_name = "jfreechart-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


    /* download and build */

    Isabelle_System.make_directory(component_dir.lib)

    val archive_url = source_url.replace("{V}", version)
    val build_script = "mvn clean verify"
    val jar_name = "jfreechart-{V}.jar".replace("{V}", version)

    Isabelle_System.with_tmp_dir("build") { build_dir =>
      val archive_name =
        Url.get_base_name(archive_url) getOrElse
          error("Malformed source URL " + quote(archive_url))
      val archive_path = build_dir + Path.basic(archive_name)

      Isabelle_System.download_file(archive_url, archive_path, progress = progress)
      Isabelle_System.extract(archive_path, build_dir, strip = true)
      Isabelle_System.extract(archive_path, component_dir.path, strip = true)
      (component_dir.path + Path.basic(".gitignore")).file.delete

      progress.echo("Building JFreeChart from source ...")
      Isabelle_System.bash(build_script, cwd = build_dir).check
      Isabelle_System.copy_file(
        build_dir + Path.basic("target") + Path.basic(jar_name), component_dir.lib)
    }


    /* settings */

    component_dir.write_settings("""
ISABELLE_JFREECHART_HOME="$COMPONENT"

classpath "$ISABELLE_JFREECHART_HOME/lib/""" + jar_name + """"
""")


    /* README */

    File.write(component_dir.README,
      """This distribution of jfreechart-""" + version + """ is based on
""" + archive_url + """

It has been built from sources like this:

  """ + build_script + """

See also https://www.jfree.org/jfreechart/samples.html and
https://github.com/jfree/jfreechart/releases/download/v""" + version +
  """/jfreechart-""" + version + """-intro.pdf


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_jfreechart", "build Isabelle jfreechart component from official downloads",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var source_url = default_source_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_jfreechart [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       source URL (default: """ + quote(default_source_url) + """)
    -V VERSION   version (default: """ + quote(default_version) + """)

  Build jfreechart component from official downloads.""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => source_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_jfreechart(target_dir = target_dir, source_url = source_url,
          version = version, progress = progress)
      })
}
