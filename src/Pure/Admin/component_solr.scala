/*  Author:     Fabian Huch, TU Muenchen

Build Isabelle Solr component from official downloads. See also: https://solr.apache.org/
*/

package isabelle


object Component_Solr {
  val default_download_url = "https://dlcdn.apache.org/solr/solr/9.7.0/solr-9.7.0.tgz"


  /* build solr */

  def build_solr(
    download_url: String = default_download_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit =
    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      /* component */

      val Archive_Name = """^.*/([^/]+)$""".r
      val Version = """^solr-(.*)\.tgz$""".r

      val archive_name =
        download_url match {
          case Archive_Name(name) => name
          case _ => error("Failed to determine source archive name from " + quote(download_url))
        }

      val version =
        archive_name match {
          case Version(version) => version
          case _ => error("Failed to determine component version from " + quote(archive_name))
        }

      val component_name = "solr-" + version
      val component_dir =
        Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


      /* download */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      Isabelle_System.extract(archive_path, tmp_dir)
      val source_dir = File.get_dir(tmp_dir, title = download_url)

      Isabelle_System.copy_file(source_dir + Path.explode("LICENSE.txt"), component_dir.path)

      val webapp_lib_dir = source_dir + Path.explode("server/solr-webapp/webapp/WEB-INF/lib")
      val server_lib_dir = source_dir + Path.explode("server/lib")


      /* jars */

      Isabelle_System.make_directory(component_dir.lib)

      val jars =
        File.find_files(webapp_lib_dir.file, _.getName.endsWith(".jar")) ++
          File.find_files(server_lib_dir.file, _.getName.endsWith(".jar"))

      for (jar <- jars) Isabelle_System.copy_file(jar, component_dir.lib.file)


      /* settings */

      def jar_path(file: String): String = "$SOLR_HOME/lib/" + file

      val classpath = List("solr-solrj", "solr-api", "solr-core").map(_ + "-" + version + ".jar")
      val solr_jars = File.read_dir(component_dir.lib).filterNot(classpath.contains)

      component_dir.write_settings("""
SOLR_HOME="$COMPONENT"
SOLR_JARS=""" + quote(solr_jars.map(jar_path).mkString(":")) + """
classpath """ + quote(classpath.map(jar_path).mkString(":")) + """

SOLR_LUCENE_VERSION="9.10"
SOLR_SCHEMA_VERSION="1.6"
""")


      /* README */

      File.write(component_dir.README,
        "This Isabelle component provides Solr " + version + " jars from\n" + download_url + """

        Fabian Huch
        """ + Date.Format.date(Date.now()) + "\n")
    }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_solr", "build Isabelle solr jar distribution", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_solr [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -v           verbose

  Build solr component from official download.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_solr(download_url = download_url, progress = progress, target_dir = target_dir)
      })
}
