/*  Title:      Pure/Admin/build_release.scala
    Author:     Makarius

Build full Isabelle distribution from repository.
*/

package isabelle


object Build_Release
{
  /** release info **/

  sealed case class Bundle_Info(
    platform: Platform.Family.Value,
    platform_description: String,
    name: String)
  {
    def path: Path = Path.explode(name)
  }

  class Release private[Build_Release](
    progress: Progress,
    val date: Date,
    val dist_name: String,
    val dist_dir: Path,
    val dist_version: String,
    val ident: String)
  {
    val isabelle_dir: Path = dist_dir + Path.explode(dist_name)
    val isabelle_archive: Path = dist_dir + Path.explode(dist_name + ".tar.gz")
    val isabelle_library_archive: Path = dist_dir + Path.explode(dist_name + "_library.tar.gz")

    def other_isabelle(dir: Path): Other_Isabelle =
      Other_Isabelle(dir + Path.explode(dist_name),
        isabelle_identifier = dist_name + "-build",
        progress = progress)

    def bundle_info(platform: Platform.Family.Value): Bundle_Info =
      platform match {
        case Platform.Family.linux => Bundle_Info(platform, "Linux", dist_name + "_linux.tar.gz")
        case Platform.Family.macos => Bundle_Info(platform, "macOS", dist_name + "_macos.tar.gz")
        case Platform.Family.windows => Bundle_Info(platform, "Windows", dist_name + ".exe")
      }
  }



  /** generated content **/

  /* patch release */

  private def change_file(dir: Path, name: String, f: String => String)
  {
    val file = dir + Path.explode(name)
    File.write(file, f(File.read(file)))
  }

  private val getsettings_file: String = "lib/scripts/getsettings"

  private val ISABELLE_ID = """ISABELLE_ID="(.+)"""".r

  def patch_release(release: Release, is_official: Boolean)
  {
    val dir = release.isabelle_dir

    for (name <- List("src/Pure/System/distribution.ML", "src/Pure/System/distribution.scala"))
    {
      change_file(dir, name,
        s =>
          s.replaceAllLiterally("val is_identified = false", "val is_identified = true")
           .replaceAllLiterally("val is_official = false", "val is_official = " + is_official))
    }

    change_file(dir, getsettings_file,
      s =>
        s.replaceAllLiterally("ISABELLE_ID=\"\"", "ISABELLE_ID=" + quote(release.ident))
         .replaceAllLiterally("ISABELLE_IDENTIFIER=\"\"",
            "ISABELLE_IDENTIFIER=" + quote(release.dist_name)))

    change_file(dir, "lib/html/library_index_header.template",
      s => s.replaceAllLiterally("{ISABELLE}", release.dist_name))

    for {
      name <-
        List(
          "src/Pure/System/distribution.ML",
          "src/Pure/System/distribution.scala",
          "lib/Tools/version") }
    {
      change_file(dir, name,
        s => s.replaceAllLiterally("repository version", release.dist_version))
    }

    change_file(dir, "README",
      s => s.replaceAllLiterally("some repository version of Isabelle", release.dist_version))
  }


  /* ANNOUNCE */

  def make_announce(release: Release)
  {
    File.write(release.isabelle_dir + Path.explode("ANNOUNCE"),
"""
IMPORTANT NOTE
==============

This is a snapshot of Isabelle/""" + release.ident + """ from the repository.

""")
  }


  /* NEWS */

  def make_news(other_isabelle: Other_Isabelle, dist_version: String)
  {
    val target = other_isabelle.isabelle_home + Path.explode("doc")
    val target_fonts = Isabelle_System.make_directory(target + Path.explode("fonts"))
    other_isabelle.copy_fonts(target_fonts)

    HTML.write_document(target, "NEWS.html",
      List(HTML.title("NEWS (" + dist_version + ")")),
      List(
        HTML.chapter("NEWS"),
        HTML.source(
          Symbol.decode(File.read(other_isabelle.isabelle_home + Path.explode("NEWS"))))))
  }


  /* bundled components */

  class Bundled(platform: Option[Platform.Family.Value] = None)
  {
    def detect(s: String): Boolean =
      s.startsWith("#bundled") && !s.startsWith("#bundled ")

    def apply(name: String): String =
      "#bundled" + (platform match { case None => "" case Some(plat) => "-" + plat }) + ":" + name

    private val Pattern1 = ("""^#bundled:(.*)$""").r
    private val Pattern2 = ("""^#bundled-(.*):(.*)$""").r

    def unapply(s: String): Option[String] =
      s match {
        case Pattern1(name) => Some(name)
        case Pattern2(Platform.Family(plat), name) if platform == Some(plat) => Some(name)
        case _ => None
      }
  }

  def record_bundled_components(dir: Path)
  {
    val catalogs =
      List("main", "bundled").map((_, new Bundled())) :::
      default_platform_families.flatMap(platform =>
        List(platform.toString, "bundled-" + platform.toString).
          map((_, new Bundled(platform = Some(platform)))))

    File.append(Components.components(dir),
      terminate_lines("#bundled components" ::
        (for {
          (catalog, bundled) <- catalogs.iterator
          path = Components.admin(dir) + Path.basic(catalog)
          if path.is_file
          line <- split_lines(File.read(path))
          if line.nonEmpty && !line.startsWith("#") && !line.startsWith("jedit_build")
        } yield bundled(line)).toList))
  }

  def get_bundled_components(dir: Path, platform: Platform.Family.Value): (List[String], String) =
  {
    val Bundled = new Bundled(platform = Some(platform))
    val components =
      for {
        Bundled(name) <- Components.read_components(dir)
        if !name.startsWith("jedit_build")
      } yield name
    val jdk_component =
      components.find(_.startsWith("jdk")) getOrElse error("Missing jdk component")
    (components, jdk_component)
  }

  def activate_components(dir: Path, platform: Platform.Family.Value, more_names: List[String])
  {
    def contrib_name(name: String): String =
      Components.contrib(name = name).implode

    val Bundled = new Bundled(platform = Some(platform))
    Components.write_components(dir,
      Components.read_components(dir).flatMap(line =>
        line match {
          case Bundled(name) =>
            if (Components.check_dir(Components.contrib(dir, name))) Some(contrib_name(name))
            else None
          case _ => if (Bundled.detect(line)) None else Some(line)
        }) ::: more_names.map(contrib_name))
  }

  def make_contrib(dir: Path)
  {
    Isabelle_System.make_directory(Components.contrib(dir))
    File.write(Components.contrib(dir, "README"),
"""This directory contains add-on components that contribute to the main
Isabelle distribution.  Separate licensing conditions apply, see each
directory individually.
""")
  }



  /** build release **/

  private def execute(dir: Path, script: String): Unit =
    Isabelle_System.bash(script, cwd = dir.file).check

  private def execute_tar(dir: Path, args: String): Unit =
    Isabelle_System.gnutar(args, dir = dir).check


  /* build heaps on remote server */

  private def remote_build_heaps(
    options: Options,
    platform: Platform.Family.Value,
    build_sessions: List[String],
    local_dir: Path)
  {
    val server_option = "build_host_" + platform.toString
    options.string(server_option) match {
      case SSH.Target(user, host) =>
        using(SSH.open_session(options, host = host, user = user))(ssh =>
        {
          Isabelle_System.with_tmp_file("tmp", "tar")(local_tmp_tar =>
          {
            execute_tar(local_dir, "-cf " + File.bash_path(local_tmp_tar) + " .")
            ssh.with_tmp_dir(remote_dir =>
            {
              val remote_tmp_tar = remote_dir + Path.basic("tmp.tar")
              ssh.write_file(remote_tmp_tar, local_tmp_tar)
              val remote_commands =
                List(
                  "cd " + File.bash_path(remote_dir),
                  "tar -xf tmp.tar",
                  "./bin/isabelle build -o system_heaps -b -- " + Bash.strings(build_sessions),
                  "tar -cf tmp.tar heaps")
              ssh.execute(remote_commands.mkString(" && ")).check
              ssh.read_file(remote_tmp_tar, local_tmp_tar)
            })
            execute_tar(local_dir, "-xf " + File.bash_path(local_tmp_tar))
          })
        })
      case s => error("Bad " + server_option + ": " + quote(s))
    }
  }


  /* main */

  private val default_platform_families: List[Platform.Family.Value] =
    List(Platform.Family.linux, Platform.Family.windows, Platform.Family.macos)

  def build_release(base_dir: Path,
    options: Options,
    components_base: Path = Components.default_components_base,
    progress: Progress = new Progress,
    rev: String = "",
    afp_rev: String = "",
    official_release: Boolean = false,
    proper_release_name: Option[String] = None,
    platform_families: List[Platform.Family.Value] = default_platform_families,
    more_components: List[Path] = Nil,
    website: Option[Path] = None,
    build_sessions: List[String] = Nil,
    build_library: Boolean = false,
    parallel_jobs: Int = 1): Release =
  {
    val hg = Mercurial.repository(Path.explode("$ISABELLE_HOME"))

    val release =
    {
      val date = Date.now()
      val dist_name = proper_release_name getOrElse ("Isabelle_" + Date.Format.date(date))
      val dist_dir = (base_dir + Path.explode("dist-" + dist_name)).absolute

      val version = proper_string(rev) orElse proper_release_name getOrElse "tip"
      val ident =
        try { hg.id(version) }
        catch { case ERROR(msg) => cat_error("Bad repository version: " + version, msg) }

      val dist_version =
        proper_release_name match {
          case Some(name) => name + ": " + Date.Format("LLLL uuuu")(date)
          case None => "Isabelle repository snapshot " + ident + " " + Date.Format.date(date)
        }

      new Release(progress, date, dist_name, dist_dir, dist_version, ident)
    }


    /* make distribution */

    if (release.isabelle_archive.is_file) {
      progress.echo_warning("Release archive already exists: " + release.isabelle_archive)

      val archive_ident =
        Isabelle_System.with_tmp_dir("build_release")(tmp_dir =>
          {
            val getsettings = Path.explode(release.dist_name + "/" + getsettings_file)
            execute_tar(tmp_dir, "-xzf " +
              File.bash_path(release.isabelle_archive) + " " + File.bash_path(getsettings))
            split_lines(File.read(tmp_dir + getsettings))
              .collectFirst({ case ISABELLE_ID(ident) => ident })
              .getOrElse(error("Failed to read ISABELLE_ID from " + release.isabelle_archive))
          })

      if (release.ident != archive_ident) {
        error("Mismatch of release identification " + release.ident +
          " vs. archive " + archive_ident)
      }
    }
    else {
      progress.echo_warning("Producing release archive " + release.isabelle_archive + " ...")

      Isabelle_System.make_directory(release.dist_dir)

      if (release.isabelle_dir.is_dir)
        error("Directory " + release.isabelle_dir + " already exists")


      progress.echo_warning("Retrieving Mercurial repository version " + release.ident)

      hg.archive(release.isabelle_dir.expand.implode, rev = release.ident, options = "--type files")

      for (name <- List(".hg_archival.txt", ".hgtags", ".hgignore", "README_REPOSITORY")) {
        (release.isabelle_dir + Path.explode(name)).file.delete
      }


      progress.echo_warning("Preparing distribution " + quote(release.dist_name))

      patch_release(release, proper_release_name.isDefined && official_release)

      if (proper_release_name.isEmpty) make_announce(release)

      make_contrib(release.isabelle_dir)

      execute(release.isabelle_dir, """find . -print | xargs chmod -f u+rw""")

      record_bundled_components(release.isabelle_dir)


      /* build tools and documentation */

      val other_isabelle = release.other_isabelle(release.dist_dir)

      other_isabelle.init_settings(
        other_isabelle.init_components(components_base = components_base, catalogs = List("main")))
      other_isabelle.resolve_components(echo = true)

      try {
        val export_classpath =
          "export CLASSPATH=" + Bash.string(other_isabelle.getenv("ISABELLE_CLASSPATH")) + "\n"
        other_isabelle.bash(export_classpath + "./Admin/build all", echo = true).check
        other_isabelle.bash(export_classpath + "./bin/isabelle jedit -b", echo = true).check
      }
      catch { case ERROR(msg) => cat_error("Failed to build tools:", msg) }

      try {
        other_isabelle.bash(
          "./bin/isabelle build_doc -a -o system_heaps -j " + parallel_jobs, echo = true).check
      }
      catch { case ERROR(msg) => cat_error("Failed to build documentation:", msg) }

      make_news(other_isabelle, release.dist_version)

      for (name <- List("Admin", "browser_info", "heaps")) {
        Isabelle_System.rm_tree(other_isabelle.isabelle_home + Path.explode(name))
      }

      other_isabelle.cleanup()


      progress.echo_warning("Creating distribution archive " + release.isabelle_archive)

      def execute_dist_name(script: String): Unit =
        Isabelle_System.bash(script, cwd = release.dist_dir.file,
          env = Isabelle_System.settings() + ("DIST_NAME" -> release.dist_name)).check

      execute_dist_name("""
set -e

chmod -R a+r "$DIST_NAME"
chmod -R u+w "$DIST_NAME"
chmod -R g=o "$DIST_NAME"
find "$DIST_NAME" -type f "(" -name "*.thy" -o -name "*.ML" -o -name "*.scala" ")" -print | xargs chmod -f u-w
""")

      execute_tar(release.dist_dir, "-czf " +
        File.bash_path(release.isabelle_archive) + " " + Bash.string(release.dist_name))

      execute_dist_name("""
set -e

mv "$DIST_NAME" "${DIST_NAME}-old"
mkdir "$DIST_NAME"

mv "${DIST_NAME}-old/README" "${DIST_NAME}-old/NEWS" "${DIST_NAME}-old/ANNOUNCE" \
  "${DIST_NAME}-old/COPYRIGHT" "${DIST_NAME}-old/CONTRIBUTORS" "$DIST_NAME"
mkdir "$DIST_NAME/doc"
mv "${DIST_NAME}-old/doc/"*.pdf \
  "${DIST_NAME}-old/doc/"*.html \
  "${DIST_NAME}-old/doc/"*.css \
  "${DIST_NAME}-old/doc/fonts" \
  "${DIST_NAME}-old/doc/Contents" "$DIST_NAME/doc"

rm -f Isabelle && ln -sf "$DIST_NAME" Isabelle

rm -rf "${DIST_NAME}-old"
""")
    }


    /* make application bundles */

    val bundle_infos = platform_families.map(release.bundle_info)

    for (bundle_info <- bundle_infos) {
      val isabelle_name = release.dist_name
      val platform = bundle_info.platform

      progress.echo("\nApplication bundle for " + platform)

      Isabelle_System.with_tmp_dir("build_release")(tmp_dir =>
      {
        // release archive

        execute_tar(tmp_dir, "-xzf " + File.bash_path(release.isabelle_archive))
        val other_isabelle = release.other_isabelle(tmp_dir)
        val isabelle_target = other_isabelle.isabelle_home


        // bundled components

        progress.echo("Bundled components:")

        val contrib_dir = Components.contrib(isabelle_target)

        val (bundled_components, jdk_component) =
          get_bundled_components(isabelle_target, platform)

        Components.resolve(components_base, bundled_components,
          target_dir = Some(contrib_dir),
          copy_dir = Some(release.dist_dir + Path.explode("contrib")),
          progress = progress)

        val more_components_names =
          more_components.map(Components.unpack(contrib_dir, _, progress = progress))

        Components.purge(contrib_dir, platform)

        activate_components(isabelle_target, platform, more_components_names)


        // Java parameters

        val java_options_title = "# Java runtime options"
        val java_options: List[String] =
          (for {
            variable <-
              List(
                "ISABELLE_JAVA_SYSTEM_OPTIONS",
                "JEDIT_JAVA_SYSTEM_OPTIONS",
                "JEDIT_JAVA_OPTIONS")
            opt <- Word.explode(other_isabelle.getenv(variable))
          } yield opt) ::: List("-Disabelle.jedit_server=" + isabelle_name)

        val classpath: List[Path] =
        {
          val base = isabelle_target.absolute
          Path.split(other_isabelle.getenv("ISABELLE_CLASSPATH")).map(path =>
          {
            val abs_path = path.absolute
            File.relative_path(base, abs_path) match {
              case Some(rel_path) => rel_path
              case None => error("Bad ISABELLE_CLASSPATH element: " + abs_path)
            }
          }) ::: List(Path.explode("src/Tools/jEdit/dist/jedit.jar"))
        }

        val jedit_options = Path.explode("src/Tools/jEdit/etc/options")
        val jedit_props = Path.explode("src/Tools/jEdit/dist/properties/jEdit.props")


        // build heaps

        if (build_sessions.nonEmpty) {
          progress.echo("Building heaps ...")
          remote_build_heaps(options, platform, build_sessions, isabelle_target)
        }


        // application bundling

        platform match {
          case Platform.Family.linux =>
            File.write(isabelle_target + jedit_options,
              File.read(isabelle_target + jedit_options)
                .replaceAll("jedit_reset_font_size : int =.*", "jedit_reset_font_size : int = 24"))

            File.write(isabelle_target + jedit_props,
              File.read(isabelle_target + jedit_props)
                .replaceAll("console.fontsize=.*", "console.fontsize=18")
                .replaceAll("helpviewer.fontsize=.*", "helpviewer.fontsize=18")
                .replaceAll("metal.primary.fontsize=.*", "metal.primary.fontsize=18")
                .replaceAll("metal.secondary.fontsize=.*", "metal.secondary.fontsize=18")
                .replaceAll("view.fontsize=.*", "view.fontsize=24")
                .replaceAll("view.gutter.fontsize=.*", "view.gutter.fontsize=16"))

            File.write(isabelle_target + Path.explode("Isabelle.options"),
              terminate_lines(java_options_title :: java_options))

            val isabelle_app = isabelle_target + Path.explode("lib/scripts/Isabelle_app")
            File.write(isabelle_app,
              File.read(Path.explode("~~/Admin/Linux/Isabelle_app"))
                .replaceAllLiterally("{CLASSPATH}",
                  classpath.map("$ISABELLE_HOME/" + _).mkString(":"))
                .replaceAllLiterally("/jdk/", "/" + jdk_component + "/"))
            File.set_executable(isabelle_app, true)

            val linux_app = isabelle_target + Path.explode("contrib/linux_app")
            File.move(linux_app + Path.explode("Isabelle"),
              isabelle_target + Path.explode(isabelle_name))
            Isabelle_System.rm_tree(linux_app)

            val archive_name = isabelle_name + "_linux.tar.gz"
            progress.echo("Packaging " + archive_name + " ...")
            execute_tar(tmp_dir,
              "-czf " + File.bash_path(release.dist_dir + Path.explode(archive_name)) + " " +
              Bash.string(isabelle_name))


          case Platform.Family.macos =>
            File.write(isabelle_target + jedit_props,
              File.read(isabelle_target + jedit_props)
                .replaceAll("lookAndFeel=.*", "lookAndFeel=com.apple.laf.AquaLookAndFeel")
                .replaceAll("delete-line.shortcut=.*", "delete-line.shortcut=C+d")
                .replaceAll("delete.shortcut2=.*", "delete.shortcut2=A+d"))


            // MacOS application bundle

            File.move(isabelle_target + Path.explode("contrib/macos_app"), tmp_dir)

            val isabelle_app = Path.explode(isabelle_name + ".app")
            val app_dir = tmp_dir + isabelle_app
            File.move(tmp_dir + Path.explode("macos_app/Isabelle.app"), app_dir)

            val app_contents = app_dir + Path.explode("Contents")
            val app_resources = app_contents + Path.explode("Resources")
            File.move(tmp_dir + Path.explode(isabelle_name), app_resources)

            File.write(app_contents + Path.explode("Info.plist"),
              File.read(Path.explode("~~/Admin/MacOS/Info.plist"))
                .replaceAllLiterally("{ISABELLE_NAME}", isabelle_name)
                .replaceAllLiterally("{JAVA_OPTIONS}",
                  terminate_lines(java_options.map(opt => "<string>" + opt + "</string>"))))

            for (cp <- classpath) {
              File.link(
                Path.explode("../Resources/" + isabelle_name + "/") + cp,
                app_contents + Path.explode("Java"),
                force = true)
            }

            File.link(
              Path.explode("../Resources/" + isabelle_name + "/contrib/" +
                jdk_component + "/x86_64-darwin"),
              app_contents + Path.explode("PlugIns/bundled.jdk"),
              force = true)

            File.link(
              Path.explode("../../Info.plist"),
              app_resources + Path.explode(isabelle_name + "/" + isabelle_name + ".plist"),
              force = true)

            File.link(
              Path.explode("Contents/Resources/" + isabelle_name),
              app_dir + Path.explode("Isabelle"),
              force = true)


            // application archive

            val archive_name = isabelle_name + "_macos.tar.gz"
            progress.echo("Packaging " + archive_name + " ...")
            execute_tar(tmp_dir,
              "-czf " + File.bash_path(release.dist_dir + Path.explode(archive_name)) + " " +
              File.bash_path(isabelle_app))


          case Platform.Family.windows =>
            File.write(isabelle_target + jedit_props,
              File.read(isabelle_target + jedit_props)
                .replaceAll("lookAndFeel=.*",
                  "lookAndFeel=com.sun.java.swing.plaf.windows.WindowsLookAndFeel")
                .replaceAll("foldPainter=.*", "foldPainter=Square"))


            // application launcher

            File.move(isabelle_target + Path.explode("contrib/windows_app"), tmp_dir)

            val app_template = Path.explode("~~/Admin/Windows/launch4j")

            File.write(isabelle_target + Path.explode(isabelle_name + ".l4j.ini"),
              (java_options_title :: java_options).map(_ + "\r\n").mkString)

            val isabelle_xml = Path.explode("isabelle.xml")
            val isabelle_exe = Path.explode(isabelle_name + ".exe")

            File.write(tmp_dir + isabelle_xml,
              File.read(app_template + isabelle_xml)
                .replaceAllLiterally("{ISABELLE_NAME}", isabelle_name)
                .replaceAllLiterally("{OUTFILE}",
                  File.platform_path(isabelle_target + isabelle_exe))
                .replaceAllLiterally("{ICON}",
                  File.platform_path(app_template + Path.explode("isabelle_transparent.ico")))
                .replaceAllLiterally("{SPLASH}",
                  File.platform_path(app_template + Path.explode("isabelle.bmp")))
                .replaceAllLiterally("{CLASSPATH}",
                  cat_lines(classpath.map(cp =>
                    "    <cp>%EXEDIR%\\" + File.platform_path(cp).replace('/', '\\') + "</cp>")))
                .replaceAllLiterally("\\jdk\\", "\\" + jdk_component + "\\"))

            execute(tmp_dir,
              "\"windows_app/launch4j-${ISABELLE_PLATFORM_FAMILY}/launch4j\" isabelle.xml")

            File.copy(app_template + Path.explode("manifest.xml"),
              isabelle_target + isabelle_exe.ext("manifest"))


            // Cygwin setup

            val cygwin_template = Path.explode("~~/Admin/Windows/Cygwin")

            File.copy(cygwin_template + Path.explode("Cygwin-Terminal.bat"), isabelle_target)

            val cygwin_mirror =
              File.read(isabelle_target + Path.explode("contrib/cygwin/isabelle/cygwin_mirror"))

            val cygwin_bat = Path.explode("Cygwin-Setup.bat")
            File.write(isabelle_target + cygwin_bat,
              File.read(cygwin_template + cygwin_bat)
                .replaceAllLiterally("{MIRROR}", cygwin_mirror))
            File.set_executable(isabelle_target + cygwin_bat, true)

            for (name <- List("isabelle/postinstall", "isabelle/rebaseall")) {
              val path = Path.explode(name)
              File.copy(cygwin_template + path,
                isabelle_target + Path.explode("contrib/cygwin") + path)
            }

            execute(isabelle_target,
              """find . -type f -not -name "*.exe" -not -name "*.dll" """ +
              (if (Platform.is_macos) "-perm +100" else "-executable") +
              " -print0 > contrib/cygwin/isabelle/executables")

            execute(isabelle_target,
              """find . -type l -exec echo "{}" ";" -exec readlink "{}" ";" """ +
              """> contrib/cygwin/isabelle/symlinks""")

            execute(isabelle_target, """find . -type l -exec rm "{}" ";" """)

            File.write(isabelle_target + Path.explode("contrib/cygwin/isabelle/uninitialized"), "")


            // executable archive (self-extracting 7z)

            val archive_name = isabelle_name + ".7z"
            val exe_archive = tmp_dir + Path.explode(archive_name)
            exe_archive.file.delete

            progress.echo("Packaging " + archive_name + " ...")
            execute(tmp_dir,
              "7z -y -bd a " + File.bash_path(exe_archive) + " " + Bash.string(isabelle_name))
            if (!exe_archive.is_file) error("Failed to create archive: " + exe_archive)

            val sfx_exe = tmp_dir + Path.explode("windows_app/7zsd_All_x64.sfx")
            val sfx_txt =
              File.read(Path.explode("~~/Admin/Windows/Installer/sfx.txt")).
                replaceAllLiterally("{ISABELLE_NAME}", isabelle_name)

            Bytes.write(release.dist_dir + isabelle_exe,
              Bytes.read(sfx_exe) + Bytes(sfx_txt) + Bytes.read(exe_archive))
            File.set_executable(release.dist_dir + isabelle_exe, true)
        }
      })
      progress.echo("DONE")
    }


    /* minimal website */

    for (dir <- website) {
      val website_platform_bundles =
        for {
          bundle_info <- bundle_infos
          if (release.dist_dir + bundle_info.path).is_file
        } yield (bundle_info.name, bundle_info)

      val isabelle_link =
        HTML.link(Isabelle_Cronjob.isabelle_repos_source + "/rev/" + release.ident,
          HTML.text("Isabelle/" + release.ident))
      val afp_link =
        HTML.link(AFP.repos_source + "/rev/" + afp_rev, HTML.text("AFP/" + afp_rev))

      HTML.write_document(dir, "index.html",
        List(HTML.title(release.dist_name)),
        List(
          HTML.section(release.dist_name),
          HTML.subsection("Platforms"),
          HTML.itemize(
            website_platform_bundles.map({ case (bundle, bundle_info) =>
              List(HTML.link(bundle, HTML.text(bundle_info.platform_description))) })),
          HTML.subsection("Repositories"),
          HTML.itemize(
            List(List(isabelle_link)) ::: (if (afp_rev == "") Nil else List(List(afp_link))))))

      for ((bundle, _) <- website_platform_bundles)
        File.copy(release.dist_dir + Path.explode(bundle), dir)
    }


    /* HTML library */

    if (build_library) {
      if (release.isabelle_library_archive.is_file) {
        progress.echo_warning("Library archive already exists: " + release.isabelle_library_archive)
      }
      else {
        Isabelle_System.with_tmp_dir("build_release")(tmp_dir =>
          {
            val bundle =
              release.dist_dir + Path.explode(release.dist_name + "_" + Platform.family + ".tar.gz")
            execute_tar(tmp_dir, "-xzf " + File.bash_path(bundle))

            val other_isabelle = release.other_isabelle(tmp_dir)

            Isabelle_System.make_directory(other_isabelle.etc)
            File.write(other_isabelle.etc_preferences, "ML_system_64 = true\n")

            other_isabelle.bash("bin/isabelle build -f -j " + parallel_jobs +
              " -o browser_info -o document=pdf -o document_variants=document:outline=/proof,/ML" +
              " -o system_heaps -c -a -d '~~/src/Benchmarks'", echo = true).check
            other_isabelle.isabelle_home_user.file.delete

            execute(tmp_dir, "chmod -R a+r " + Bash.string(release.dist_name))
            execute(tmp_dir, "chmod -R g=o " + Bash.string(release.dist_name))
            execute_tar(tmp_dir, "-czf " + File.bash_path(release.isabelle_library_archive) +
              " " + Bash.string(release.dist_name + "/browser_info"))
          })
      }
    }

    release
  }



  /** command line entry point **/

  def main(args: Array[String])
  {
    Command_Line.tool {
      var afp_rev = ""
      var components_base: Path = Components.default_components_base
      var official_release = false
      var proper_release_name: Option[String] = None
      var website: Option[Path] = None
      var build_sessions: List[String] = Nil
      var more_components: List[Path] = Nil
      var parallel_jobs = 1
      var build_library = false
      var options = Options.init()
      var platform_families = default_platform_families
      var rev = ""

      val getopts = Getopts("""
Usage: Admin/build_release [OPTIONS] BASE_DIR

  Options are:
    -A REV       corresponding AFP changeset id
    -C DIR       base directory for Isabelle components (default: """ +
        Components.default_components_base + """)
    -O           official release (not release-candidate)
    -R RELEASE   proper release with name
    -W WEBSITE   produce minimal website in given directory
    -b SESSIONS  build platform-specific session images (separated by commas)
    -c ARCHIVE   clean bundling with additional component .tar.gz archive
    -j INT       maximum number of parallel jobs (default 1)
    -l           build library
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p NAMES     platform families (default: """ + default_platform_families.mkString(",") + """)
    -r REV       Mercurial changeset id (default: RELEASE or tip)

  Build Isabelle release in base directory, using the local repository clone.
""",
        "A:" -> (arg => afp_rev = arg),
        "C:" -> (arg => components_base = Path.explode(arg)),
        "O" -> (_ => official_release = true),
        "R:" -> (arg => proper_release_name = Some(arg)),
        "W:" -> (arg => website = Some(Path.explode(arg))),
        "b:" -> (arg => build_sessions = space_explode(',', arg)),
        "c:" -> (arg =>
          {
            val path = Path.explode(arg)
            Components.Archive.get_name(path.file_name)
            more_components = more_components ::: List(path)
          }),
        "j:" -> (arg => parallel_jobs = Value.Int.parse(arg)),
        "l" -> (_ => build_library = true),
        "o:" -> (arg => options = options + arg),
        "p:" -> (arg => platform_families = space_explode(',', arg).map(Platform.Family.parse)),
        "r:" -> (arg => rev = arg))

      val more_args = getopts(args)
      val base_dir = more_args match { case List(base_dir) => base_dir case _ => getopts.usage() }

      val progress = new Console_Progress()

      if (platform_families.contains(Platform.Family.windows) && !Isabelle_System.bash("7z i").ok)
        error("Building for windows requires 7z")

      build_release(Path.explode(base_dir), options, components_base = components_base,
        progress = progress, rev = rev, afp_rev = afp_rev, official_release = official_release,
        proper_release_name = proper_release_name, website = website,
        platform_families =
          if (platform_families.isEmpty) default_platform_families
          else platform_families,
        more_components = more_components, build_sessions = build_sessions,
        build_library = build_library, parallel_jobs = parallel_jobs)
    }
  }
}
