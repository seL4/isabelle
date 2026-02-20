/*  Title:      Pure/Admin/build_app.scala
    Author:     Makarius

Build standalone desktop app from Isabelle distribution archive.
*/

package isabelle


object Build_App {
  /** build app **/

  def build_app(dist_archive: String,
    dist_name: String = "",
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      val dist_dir = Isabelle_System.new_directory(tmp_dir + Path.explode("dist"))
      val dummy_dir = Isabelle_System.new_directory(tmp_dir + Path.explode("dummy"))


      /* platform */

      val platform = Isabelle_Platform.local
      val platform_name = platform.ISABELLE_PLATFORM(windows = true, apple = true)
      val platform_family = Platform.Family.from_platform(platform_name)

      val platform_prefix =
        if (platform.is_windows) Path.current
        else if (platform.is_macos) Path.explode("Contents")
        else Path.explode("lib")


      /* Isabelle distribution directory */

      val dist_archive_path =
        Url.get_base_name(dist_archive) match {
          case Some(name) if Url.is_wellformed(dist_archive) =>
            val download_dir = Isabelle_System.make_directory(tmp_dir + Path.basic("download"))
            val download_path = download_dir + Path.basic(name)
            Isabelle_System.download_file(dist_archive, download_path, progress = progress)
            download_path
          case _ => Path.explode(dist_archive)
        }

      Isabelle_System.extract(dist_archive_path, dist_dir, strip = true)

      val isabelle_identifier = File.read(dist_dir + Build_Release.ISABELLE_IDENTIFIER)


      /* java classpath and options */

      val java_classpath: List[String] = {
        val Pattern = """^\s*-classpath\s*"([^"]*)".*$""".r
        split_lines(File.read(dist_dir + Build_Release.ISABELLE_APP))
          .collectFirst({ case Pattern(s) => Library.space_explode(':', s) })
          .getOrElse(error("Failed to retrieve classpath from " + Build_Release.ISABELLE_APP))
      }

      val java_options =
        Build_Release.read_isabelle_options(platform_family, dist_dir, isabelle_identifier) :::
          List("-splash:$APPDIR/lib/logo/isabelle.gif")


      /* java app package */

      Isabelle_System.make_directory(target_dir)

      def jpackage(args: String): Unit = {
        val script = "isabelle_java jpackage" + args
        progress.echo_if(progress.verbose, script)
        progress.bash(script, cwd = target_dir, echo = progress.verbose).check
      }

      val app_name = proper_string(dist_name).getOrElse(isabelle_identifier)
      val app_prefix = target_dir.absolute + Path.basic(app_name) + platform_prefix
      val app_dir = app_prefix + Path.basic("app")

      progress.echo("Building app " + quote(app_name) + " for " + platform_name + " ...")
      jpackage(
        " --name " + Bash.string(app_name) +
        " --type app-image" +
        " --input " + File.bash_platform_path(dummy_dir) +
        " --main-jar " + File.bash_platform_path(dist_dir + Path.explode("lib/classes/isabelle.jar")) +
        " --copyright 'Isabelle contributors: various open-source lincenses'" +
        " --description 'Isabelle prover platform'" +
        " --vendor 'Isabelle'" +
        if_proper(progress.verbose, " --verbose"))


      /* Isabelle directory structure */

      progress.echo("Preparing Isabelle directory structure ...")

      Isabelle_System.copy_dir(dist_dir, app_dir, direct = true)

      for { path <-
        List(
          Build_Release.isabelle_options_path(platform_family, app_dir, isabelle_identifier),
          app_dir + Path.basic(isabelle_identifier).exe_if(platform.is_windows))
      } yield path.check_file.file.delete

      File.write(app_dir + Path.basic(app_name + ".cfg"),
        Library.cat_lines(
          "[Application]" ::
          java_classpath.map(s => "app.classpath=" + s.replace("ISABELLE_HOME", "APPDIR")) :::
          List("app.mainclass=isabelle.jedit.JEdit_Main",
            "",
            "[JavaOptions]",
            "java-options=-Djpackage.app-version=1.0",
            "java-options=-Disabelle.root=$APPDIR") :::
          java_options.map("java-options=" + _)))


      /* java runtime */

      val runtime_dir = app_prefix + Path.basic("runtime")

      val jdk_dir =
        Components.Directory(app_dir).read_components().filter(_.containsSlice("jdk")) match {
          case List(jdk) => app_dir + Path.explode(jdk) + Path.basic(platform_name)
          case _ => error("Failed to determine jdk component")
        }

      Isabelle_System.rm_tree(runtime_dir)
      Isabelle_System.symlink(File.perhaps_relative_path(app_prefix, jdk_dir), runtime_dir)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_app", "build standalone desktop app from Isabelle distribution archive",
      Scala_Project.here,
      { args =>
          var target_dir = Path.current
          var dist_name = ""
          var verbose = false

          val getopts = Getopts("""
Usage: Admin/build_app [OPTIONS] ARCHIVE

  Options are:
    -D DIR       target directory (default ".")
    -n NAME      app name (default ISABELLE_IDENTIFIER)
    -v           verbose

  Build standalone desktop app from Isabelle distribution archive (file or URL).
""",
            "D:" -> (arg => target_dir = Path.explode(arg)),
            "n:" -> (arg => dist_name = arg),
            "v" -> (_ => verbose = true))

          val more_args = getopts(args)
          val dist_archive =
            more_args match {
              case List(a) => a
              case _ => getopts.usage()
            }

          val progress = new Console_Progress(verbose = verbose)

          build_app(dist_archive, dist_name = dist_name, target_dir = target_dir, progress = progress)
        })
}
