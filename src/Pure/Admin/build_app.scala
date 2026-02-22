/*  Title:      Pure/Admin/build_app.scala
    Author:     Makarius

Build standalone desktop app from Isabelle distribution archive.
*/

package isabelle

import java.io.IOException
import java.nio.file.Files


object Build_App {
  /** resources **/

  val ADMIN_MACOS_ENTITLEMENTS: Path =
    Path.explode("~~/Admin/macOS/app/entitlements.plist")



  /** build app **/

  def build_app(dist_archive: String,
    dist_name: String = "",
    target_dir: Path = Path.current,
    codesign_keychain: String = "",
    codesign_user: String = "",
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      val dummy_dir = Isabelle_System.new_directory(tmp_dir + Path.explode("dummy"))


      /* target directory */

      Isabelle_System.make_directory(target_dir)

      def execute(script: String): Process_Result = {
        progress.echo_if(progress.verbose, script)
        progress.bash(script, cwd = target_dir, echo = progress.verbose).check
      }

      def jpackage(args: String): Process_Result =
        execute("isabelle_java jpackage " + args)


      /* platform */

      val platform = Isabelle_Platform.local
      val platform_name = platform.ISABELLE_PLATFORM(windows = true, apple = true)
      val platform_name_emulated = platform.ISABELLE_PLATFORM()
      val platform_family = Platform.Family.from_platform(platform_name)

      val platform_prefix =
        if (platform.is_windows) Path.current
        else if (platform.is_macos) Path.explode("Contents")
        else Path.explode("lib")

      val platform_suffix = if (platform.is_macos) "/Contents/Resources" else ""


      /* Isabelle distribution directory */

      val dist_dir = {
        val dist_archive_path =
          Url.get_base_name(dist_archive) match {
            case Some(name) if Url.is_wellformed(dist_archive) =>
              val download_dir = Isabelle_System.make_directory(tmp_dir + Path.basic("download"))
              val download_path = download_dir + Path.basic(name)
              Isabelle_System.download_file(dist_archive, download_path, progress = progress)
              download_path
            case _ => Path.explode(dist_archive)
          }
        val dist_parent = Isabelle_System.new_directory(tmp_dir + Path.explode("dist"))
        if (dist_archive.endsWith(".exe")) {
          Isabelle_System.bash(
            "7z x -y " + File.bash_platform_path(dist_archive_path), cwd = dist_parent).check
        }
        else Isabelle_System.extract(dist_archive_path, dist_parent)
        File.get_dir(dist_parent, title = dist_archive)
      }

      val isabelle_identifier = File.read(dist_dir + Build_Release.ISABELLE_IDENTIFIER)


      /* java classpath and options */

      val java_classpath: List[String] =
        if (platform.is_windows) {
          val exe =
            File.get_entry(dist_dir,
              pred = (path: Path) => path.is_file && path.implode.endsWith(".exe"),
              title = "Isabelle distribution: main exe")
          val list =
            for {
              b <- Bytes.read(dist_dir + exe).space_explode(0)
              s <- b.wellformed_text
              if s.containsSlice(".jar")
            } yield s.replace("\\", "/").replace("%EXEDIR%", "$ISABELLE_HOME")
          list match {
            case List(s) => space_explode(';', s)
            case _ => error("Failed to retrieve classpath from " + exe)
          }
        }
        else {
          val Pattern = """^\s*-classpath\s*"([^"]*)".*$""".r
          split_lines(File.read(dist_dir + Build_Release.ISABELLE_APP))
            .collectFirst({ case Pattern(s) => Library.space_explode(':', s) })
            .getOrElse(error("Failed to retrieve classpath from " + Build_Release.ISABELLE_APP))
        }

      val java_options =
        Build_Release.read_isabelle_options(platform_family, dist_dir, isabelle_identifier) :::
          (if (platform.is_macos)
            List("-Xdock:icon=$ROOTDIR/Contents/lib/logo/isabelle_transparent-128.png")
           else Nil)


      /* file associations */

      val file_associations = tmp_dir + Path.explode("file-associations.props")

      File.write(file_associations,
"""
extension=thy
icon=theory.icns
description=Isabelle theory file
mac.CFBundleTypeRole=Editor
""")


      /* java app package */

      val app_name = proper_string(dist_name).getOrElse(isabelle_identifier)
      val app_root = target_dir.absolute + Path.basic(app_name).app_if(platform.is_macos)
      val app_prefix = app_root + platform_prefix
      val app_resources = app_prefix + Path.explode("Resources")
      val app_identifier = "isabelle." + app_name
      val app_icon = if (platform.is_macos) Some(dist_dir + Build_Release.ISABELLE_ICNS) else None

      progress.echo("Building app " + quote(app_name) + " for " + platform_name + " ...")
      jpackage(
        " --name " + Bash.string(app_name) +
        " --type app-image" +
        " --input " + File.bash_platform_path(dummy_dir) +
        " --main-jar " + File.bash_platform_path(dist_dir + Path.explode("lib/classes/isabelle.jar")) +
        " --copyright 'Isabelle contributors: various open-source lincenses'" +
        " --description 'Isabelle prover platform'" +
        " --vendor 'Isabelle'" +
        if_proper(platform.is_macos,
          " --file-associations " + File.bash_platform_path(file_associations) +
          " --mac-package-identifier " + Bash.string(app_identifier)) +
        if_proper(app_icon, " --icon " + File.bash_platform_path(app_icon.get)) +
        if_proper(progress.verbose, " --verbose"))


      /* Isabelle directory structure */

      progress.echo("Preparing Isabelle directory structure ...")

      val isabelle_home = if (platform.is_macos) app_resources else app_root

      Isabelle_System.make_directory(isabelle_home)
      Isabelle_System.copy_dir(dist_dir, isabelle_home, direct = true)

      for { path <-
        List(
          Build_Release.isabelle_options_path(platform_family, isabelle_home, isabelle_identifier),
          isabelle_home + Path.basic(isabelle_identifier).exe_if(platform.is_windows)) :::
        (if (platform.is_windows)
          List(isabelle_home + Path.explode(isabelle_identifier).exe.ext("manifest"))
         else List(isabelle_home + Build_Release.ISABELLE_APP))
      } yield path.check_file.file.delete

      if (platform.is_macos) {
        File.change_lines(isabelle_home + Path.explode("etc/settings")) { lines =>
          lines.map(line =>
            line.replace(
              "$USER_HOME/.isabelle",
              "$USER_HOME/Library/Application Support/Isabelle"))
        }
        Isabelle_System.rm_tree(isabelle_home + Path.explode("Contents"))
        Isabelle_System.copy_file(isabelle_home + Build_Release.THEORY_ICNS, app_resources)

        val bad_files =
          File.find_files(app_root.file, pred = { file =>
            try { Files.getPosixFilePermissions(file.toPath); false }
            catch { case _: IOException => true }
          })
        for (file <- bad_files) {
          progress.echo_warning("Suppressing bad file " + File.path(file))
          file.delete
        }

        for {
          name <- Components.Directory(isabelle_home).read_components()
          if name.containsSlice("jdk") || name.containsSlice("vscodium")
        } {
          val dir = isabelle_home + Path.explode(name) + Path.basic(platform_name_emulated)
          progress.echo_warning("Suppressing redundant " + dir)
          Isabelle_System.rm_tree(dir)
        }
      }

      if (platform.is_linux) {
        Isabelle_System.symlink(Path.basic("bin") + Path.basic(app_name), isabelle_home)
        (app_prefix + Path.basic("lib") + Path.basic(app_name).png).file.delete
      }


      /* java runtime */

      val jdk_dir =
        Components.Directory(isabelle_home).read_components().filter(_.containsSlice("jdk")) match {
          case List(jdk) =>
            val platform_dir = isabelle_home + Path.explode(jdk) + Path.basic(platform_name)
            if (platform.is_macos) {
              File.get_entry(platform_dir,
                pred = { path =>
                  val name = path.file_name
                  name.startsWith("zulu-") && name.endsWith(".jdk")
                },
                title = "zulu-*.jdk")
            }
            else platform_dir
          case _ => error("Failed to determine jdk component")
        }

      val jdk_relative_path =
        File.relative_path(isabelle_home, jdk_dir)
          .getOrElse(error("Cannot determine relative path from " + jdk_dir))

      Isabelle_System.rm_tree(app_prefix + Path.basic("runtime"))


      /* app configuration */

      File.write(app_prefix + Path.explode("app/" + app_name + ".cfg"),
        Library.cat_lines(
          List("[Application]",
            "app.splash=$ROOTDIR" + platform_suffix + "/lib/logo/isabelle.gif",
            "app.runtime=$ROOTDIR" + platform_suffix + "/" + jdk_relative_path.implode) :::
          java_classpath.map(s =>
            "app.classpath=" + s.replace("ISABELLE_HOME", "ROOTDIR" + platform_suffix)) :::
          List("app.mainclass=isabelle.jedit.JEdit_Main",
            "",
            "[JavaOptions]",
            "java-options=-Djpackage.app-version=1.0",
            "java-options=-Disabelle.root=$ROOTDIR" + platform_suffix) :::
          (if (platform.is_windows) List("java-options=-Dcygwin.root=$ROOTDIR/contrib/cygwin")
           else Nil) :::
          java_options.map("java-options=" + _)))


      /* macOS packaging */

      if (platform.is_macos && codesign_user.nonEmpty) {
        progress.echo("Building signed dmg ...")
        jpackage(
          " --app-image " + File.bash_platform_path(app_root) +
          " --type dmg --dest " + Bash.string(app_name + ".dmg") +
          " --mac-sign" +
          " --mac-package-signing-prefix " + Bash.string(app_identifier) +
          " --mac-entitlements " + File.bash_platform_path(ADMIN_MACOS_ENTITLEMENTS) +
          " --mac-signing-key-user-name " + Bash.string(codesign_user) +
          if_proper(codesign_keychain,
            " --mac-signing-keychain " + Bash.string(codesign_keychain)) +
          if_proper(progress.verbose, " --verbose"))
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
          var codesign_keychain = ""
          var codesign_user = ""
          var verbose = false

          val getopts = Getopts("""
Usage: Admin/build_app [OPTIONS] ARCHIVE

  Options are:
    -D DIR       target directory (default ".")
    -K NAME      macOS codesign keychain name (e.g. "login.keychain")
    -S NAME      macOS codesign user name (e.g. "John Doe (M2NGOH5LAE)")
    -n NAME      app name (default ISABELLE_IDENTIFIER)
    -v           verbose

  Build standalone desktop app from Isabelle distribution archive (file or URL).
""",
            "D:" -> (arg => target_dir = Path.explode(arg)),
            "K:" -> (arg => codesign_keychain = arg),
            "S:" -> (arg => codesign_user = arg),
            "n:" -> (arg => dist_name = arg),
            "v" -> (_ => verbose = true))

          val more_args = getopts(args)
          val dist_archive =
            more_args match {
              case List(a) => a
              case _ => getopts.usage()
            }

          val progress = new Console_Progress(verbose = verbose)

          build_app(dist_archive, dist_name = dist_name, target_dir = target_dir,
            codesign_keychain = codesign_keychain, codesign_user = codesign_user,
            progress = progress)
        })
}
