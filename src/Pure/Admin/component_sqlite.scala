/*  Title:      Pure/Admin/component_sqlite.scala
    Author:     Makarius

Build Isabelle sqlite component from official download.
*/

package isabelle


object Component_SQLite {
  /* build sqlite */

  val default_main_url =
    "https://repo1.maven.org/maven2/org/xerial/sqlite-jdbc/3.48.0.0/sqlite-jdbc-3.48.0.0.jar"

  val default_logger_url =
    "https://repo1.maven.org/maven2/org/slf4j/slf4j-api/2.0.16/slf4j-api-2.0.16.jar"

  private def jar_name(url: String): String = {
    Url.get_base_name(url, suffix = ".jar") getOrElse
      error("Malformed jar URL: " + quote(url))
  }

  private def nop_name(s: String): String = s.replace("-api", "-nop")

  def build_sqlite(
    main_url: String = default_main_url,
    logger_url: String = default_logger_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    val main_name = jar_name(main_url)
    val logger_name = jar_name(logger_url)


    /* component */

    val component_name = main_name.replace("-jdbc", "")
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

    def download(url: String): Path = {
      val path = component_dir.lib + Path.basic(Url.get_base_name(url).get)
      Isabelle_System.download_file(url, path, progress = progress)
      path
    }


    /* README */

    File.write(component_dir.README,
      "This is " + main_name + " from\n" + main_url +
      "\ntogether with " + logger_name + " from\n" + logger_url +
        "\n\n        Makarius\n        " + Date.Format.date(Date.now()) + "\n")


    /* settings */

    component_dir.write_settings("""
ISABELLE_SQLITE_HOME="$COMPONENT"

classpath "$ISABELLE_SQLITE_HOME/lib/""" + main_name + """.jar"
classpath "$ISABELLE_SQLITE_HOME/lib/""" + logger_name + """.jar"
classpath "$ISABELLE_SQLITE_HOME/lib/""" + nop_name(logger_name) + """.jar"
""")


    /* main jar */

    Isabelle_System.make_directory(component_dir.lib)
    val jar = download(main_url)

    Isabelle_System.with_tmp_dir("build") { jar_dir =>
      Isabelle_System.extract(jar, jar_dir)

      val jar_files =
        List(
          "META-INF/maven/org.xerial/sqlite-jdbc/LICENSE" -> ".",
          "META-INF/maven/org.xerial/sqlite-jdbc/LICENSE.zentus" -> ".",
          "org/sqlite/native/Linux/aarch64/libsqlitejdbc.so" -> "arm64-linux",
          "org/sqlite/native/Linux/x86_64/libsqlitejdbc.so" -> "x86_64-linux",
          "org/sqlite/native/Mac/aarch64/libsqlitejdbc.dylib" -> "arm64-darwin",
          "org/sqlite/native/Mac/x86_64/libsqlitejdbc.dylib" -> "x86_64-darwin",
          "org/sqlite/native/Windows/x86_64/sqlitejdbc.dll" -> "x86_64-windows")

      for ((file, dir) <- jar_files) {
        val target = Isabelle_System.make_directory(component_dir.path + Path.explode(dir))
        Isabelle_System.copy_file(jar_dir + Path.explode(file), target)
      }

      File.set_executable(component_dir.path + Path.explode("x86_64-windows/sqlitejdbc.dll"))
    }


    /* logger jars */

    download(logger_url)
    download(nop_name(logger_url))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_sqlite", "build Isabelle sqlite component from official download",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var main_url = default_main_url
        var logger_url = default_logger_url

        val getopts = Getopts("""
Usage: isabelle component_sqlite [OPTIONS] DOWNLOAD

  Options are:
    -D DIR       target directory (default ".")
    -U URL       main URL
                 (default: """" + default_main_url + """")
    -V URL       logger URL
                 (default: """" + default_logger_url + """")

  Build sqlite component from the specified download URL (JAR), see also
  https://github.com/xerial/sqlite-jdbc and
  https://oss.sonatype.org/content/repositories/releases/org/xerial/sqlite-jdbc
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => main_url = arg),
          "V:" -> (arg => logger_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_sqlite(main_url = main_url, logger_url = logger_url,
          progress = progress, target_dir = target_dir)
      })
}
