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

      val platform_suffix = if (platform.is_macos) "/Contents" else ""


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
          List("-splash:$ROOTDIR" + platform_suffix + "/lib/logo/isabelle.gif") :::
          (if (platform.is_macos)
            List("-Xdock:icon=$ROOTDIR/Contents/lib/logo/isabelle_transparent-128.png")
           else Nil)


      /* java app package */

      Isabelle_System.make_directory(target_dir)

      def jpackage(args: String): Unit = {
        val script = "isabelle_java jpackage" + args
        progress.echo_if(progress.verbose, script)
        progress.bash(script, cwd = target_dir, echo = progress.verbose).check
      }

      val app_name = proper_string(dist_name).getOrElse(isabelle_identifier)
      val app_prefix =
        target_dir.absolute + Path.basic(app_name).app_if(platform.is_macos) + platform_prefix

      val app_icon =
        if (platform.is_macos) Some(dist_dir + Path.explode("Contents/Resources/isabelle.icns"))
        else None

      progress.echo("Building app " + quote(app_name) + " for " + platform_name + " ...")
      jpackage(
        " --name " + Bash.string(app_name) +
        " --type app-image" +
        " --input " + File.bash_platform_path(dummy_dir) +
        " --main-jar " + File.bash_platform_path(dist_dir + Path.explode("lib/classes/isabelle.jar")) +
        " --copyright 'Isabelle contributors: various open-source lincenses'" +
        " --description 'Isabelle prover platform'" +
        " --vendor 'Isabelle'" +
        if_proper(app_icon, " --icon " + File.bash_platform_path(app_icon.get)) +
        if_proper(progress.verbose, " --verbose"))


      /* Isabelle directory structure */

      progress.echo("Preparing Isabelle directory structure ...")

      val isabelle_home =
        if (platform.is_macos) app_prefix
        else target_dir.absolute + Path.basic(app_name)

      Isabelle_System.make_directory(isabelle_home)
      Isabelle_System.copy_dir(dist_dir, isabelle_home, direct = true)

      for { path <-
        List(
          Build_Release.isabelle_options_path(platform_family, isabelle_home, isabelle_identifier),
          isabelle_home + Build_Release.ISABELLE_APP,
          isabelle_home + Path.basic(isabelle_identifier).exe_if(platform.is_windows))
      } yield path.check_file.file.delete

      if (platform.is_macos) {
        Isabelle_System.rm_tree(isabelle_home + Path.explode("Contents"))
      }

      if (platform.is_linux) {
        Isabelle_System.symlink(Path.basic("bin") + Path.basic(app_name), isabelle_home)
      }

      File.write(app_prefix + Path.explode("app/" + app_name + ".cfg"),
        Library.cat_lines(
          "[Application]" ::
          java_classpath.map(s =>
            "app.classpath=" + s.replace("ISABELLE_HOME", "ROOTDIR" + platform_suffix)) :::
          List("app.mainclass=isabelle.jedit.JEdit_Main",
            "",
            "[JavaOptions]",
            "java-options=-Djpackage.app-version=1.0",
            "java-options=-Disabelle.root=$ROOTDIR" + platform_suffix) :::
          java_options.map("java-options=" + _)))


      /* java runtime */

      val jdk_dir =
        Components.Directory(isabelle_home).read_components().filter(_.containsSlice("jdk")) match {
          case List(jdk) => isabelle_home + Path.explode(jdk) + Path.basic(platform_name)
          case _ => error("Failed to determine jdk component")
        }

      val runtime_dir = app_prefix + Path.basic("runtime")
      Isabelle_System.rm_tree(runtime_dir)

      if (platform.is_linux) {
        Isabelle_System.symlink(
          Path.parent + File.perhaps_relative_path(isabelle_home, jdk_dir), runtime_dir)
      }
      else if (platform.is_macos) {
        val contents_dir = Isabelle_System.make_directory(runtime_dir + Path.explode("Contents"))
        Isabelle_System.symlink(
          File.perhaps_relative_path(contents_dir, jdk_dir),
          contents_dir + Path.explode("Home"))
      }
      else if (platform.is_windows) {
        Isabelle_System.copy_dir(jdk_dir, runtime_dir)
      }
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
