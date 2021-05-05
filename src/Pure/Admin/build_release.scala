/*  Title:      Pure/Admin/build_release.scala
    Author:     Makarius

Build full Isabelle distribution from repository.
*/

package isabelle


object Build_Release
{
  /** release context **/

  private def execute(dir: Path, script: String): Unit =
    Isabelle_System.bash(script, cwd = dir.file).check

  private def execute_tar(dir: Path, args: String, strip: Int = 0): Unit =
    Isabelle_System.gnutar(args, dir = dir, strip = strip).check

  object Release_Context
  {
    def apply(
      target_dir: Path,
      release_name: String = "",
      components_base: Path = Components.default_components_base,
      progress: Progress = new Progress): Release_Context =
    {
      val date = Date.now()
      val dist_name = proper_string(release_name) getOrElse ("Isabelle_" + Date.Format.date(date))
      val dist_dir = (target_dir + Path.explode("dist-" + dist_name)).absolute
      new Release_Context(release_name, dist_name, dist_dir, components_base, progress)
    }
  }

  class Release_Context private[Build_Release](
    val release_name: String,
    val dist_name: String,
    val dist_dir: Path,
    val components_base: Path,
    val progress: Progress)
  {
    override def toString: String = dist_name

    val isabelle: Path = Path.explode(dist_name)
    val isabelle_dir: Path = dist_dir + isabelle
    val isabelle_archive: Path = dist_dir + isabelle.tar.gz
    val isabelle_library_archive: Path = dist_dir + Path.explode(dist_name + "_library.tar.gz")

    def other_isabelle(dir: Path): Other_Isabelle =
      Other_Isabelle(dir + isabelle,
        isabelle_identifier = dist_name + "-build",
        progress = progress)

    def make_announce(id: String): Unit =
    {
      if (release_name.isEmpty) {
        File.write(isabelle_dir + Path.explode("ANNOUNCE"),
          """
IMPORTANT NOTE
==============

This is a snapshot of Isabelle/""" + id + """ from the repository.
""")
      }
    }

    def make_contrib(): Unit =
    {
      Isabelle_System.make_directory(Components.contrib(isabelle_dir))
      File.write(Components.contrib(isabelle_dir, name = "README"),
        """This directory contains add-on components that contribute to the main
Isabelle distribution.  Separate licensing conditions apply, see each
directory individually.
""")
    }

    def bundle_info(platform: Platform.Family.Value): Bundle_Info =
      platform match {
        case Platform.Family.linux => Bundle_Info(platform, "Linux", dist_name + "_linux.tar.gz")
        case Platform.Family.macos => Bundle_Info(platform, "macOS", dist_name + "_macos.tar.gz")
        case Platform.Family.windows => Bundle_Info(platform, "Windows", dist_name + ".exe")
      }
  }

  sealed case class Bundle_Info(
    platform: Platform.Family.Value,
    platform_description: String,
    name: String)
  {
    def path: Path = Path.explode(name)
  }



  /** release archive **/

  val ISABELLE: Path = Path.basic("Isabelle")
  val ISABELLE_ID: Path = Path.explode("etc/ISABELLE_ID")
  val ISABELLE_TAGS: Path = Path.explode("etc/ISABELLE_TAGS")
  val ISABELLE_IDENTIFIER: Path = Path.explode("etc/ISABELLE_IDENTIFIER")

  object Release_Archive
  {
    def make(bytes: Bytes, rename: String = ""): Release_Archive =
    {
      Isabelle_System.with_tmp_dir("tmp")(dir =>
        Isabelle_System.with_tmp_file("archive", ext = "tar.gz")(archive_path =>
        {
          val isabelle_dir = Isabelle_System.make_directory(dir + ISABELLE)

          Bytes.write(archive_path, bytes)
          execute_tar(isabelle_dir, "-xzf " + File.bash_path(archive_path), strip = 1)

          val id = File.read(isabelle_dir + ISABELLE_ID)
          val tags = File.read(isabelle_dir + ISABELLE_TAGS)
          val identifier = File.read(isabelle_dir + ISABELLE_IDENTIFIER)

          val (bytes1, identifier1) =
            if (rename.isEmpty || rename == identifier) (bytes, identifier)
            else {
              File.write(isabelle_dir + ISABELLE_IDENTIFIER, rename)
              Isabelle_System.move_file(isabelle_dir, dir + Path.basic(rename))
              execute_tar(dir, "-czf " + File.bash_path(archive_path) + " " + Bash.string(rename))
              (Bytes.read(archive_path), rename)
            }
          new Release_Archive(bytes1, id, tags, identifier1)
        })
      )
    }

    def read(path: Path, rename: String = ""): Release_Archive =
      make(Bytes.read(path), rename = rename)

    def get(url: String, rename: String = "", progress: Progress = new Progress): Release_Archive =
    {
      val bytes =
        if (Path.is_wellformed(url)) Bytes.read(Path.explode(url))
        else Isabelle_System.download(url, progress = progress).bytes
      make(bytes, rename = rename)
    }
  }

  case class Release_Archive private[Build_Release](
    bytes: Bytes, id: String, tags: String, identifier: String)
  {
    override def toString: String = identifier
  }



  /** generated content **/

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

  def record_bundled_components(dir: Path): Unit =
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

  def activate_components(
    dir: Path, platform: Platform.Family.Value, more_names: List[String]): Unit =
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


  /** build release **/

  /* build heaps on remote server */

  private def remote_build_heaps(
    options: Options,
    platform: Platform.Family.Value,
    build_sessions: List[String],
    local_dir: Path): Unit =
  {
    val server_option = "build_host_" + platform.toString
    options.string(server_option) match {
      case SSH.Target(user, host) =>
        using(SSH.open_session(options, host = host, user = user))(ssh =>
          Isabelle_System.with_tmp_file("tmp", ext = "tar")(local_tmp_tar =>
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
                  "bin/isabelle build -o system_heaps -b -- " + Bash.strings(build_sessions),
                  "tar -cf tmp.tar heaps")
              ssh.execute(remote_commands.mkString(" && ")).check
              ssh.read_file(remote_tmp_tar, local_tmp_tar)
            })
            execute_tar(local_dir, "-xf " + File.bash_path(local_tmp_tar))
          })
        )
      case s => error("Bad " + server_option + ": " + quote(s))
    }
  }


  /* Isabelle application */

  def make_isabelle_options(path: Path, options: List[String], line_ending: String = "\n"): Unit =
  {
    val title = "# Java runtime options"
    File.write(path, (title :: options).map(_ + line_ending).mkString)
  }

  def make_isabelle_app(
    platform: Platform.Family.Value,
    isabelle_target: Path,
    isabelle_name: String,
    jdk_component: String,
    classpath: List[Path],
    dock_icon: Boolean = false): Unit =
  {
    val script = """#!/usr/bin/env bash
#
# Author: Makarius
#
# Main Isabelle application script.

# minimal Isabelle environment

ISABELLE_HOME="$(cd "$(dirname "$0")"; cd "$(pwd -P)/../.."; pwd)"
source "$ISABELLE_HOME/lib/scripts/isabelle-platform"

#paranoia settings -- avoid intrusion of alien options
unset "_JAVA_OPTIONS"
unset "JAVA_TOOL_OPTIONS"

#paranoia settings -- avoid problems of Java/Swing versus XIM/IBus etc.
unset XMODIFIERS

COMPONENT="$ISABELLE_HOME/contrib/""" + jdk_component + """"
source "$COMPONENT/etc/settings"


# main

declare -a JAVA_OPTIONS=($(perl -p -e 's,#.*$,,g;' "$ISABELLE_HOME/Isabelle.options"))

"$ISABELLE_HOME/bin/isabelle" env "$ISABELLE_HOME/lib/scripts/java-gui-setup"

exec "$ISABELLE_JDK_HOME/bin/java" \
  "-Disabelle.root=$ISABELLE_HOME" "${JAVA_OPTIONS[@]}" \
  -classpath """" + classpath.map(p => "$ISABELLE_HOME/" + p.implode).mkString(":") + """" \
  "-splash:$ISABELLE_HOME/lib/logo/isabelle.gif" \
""" + (if (dock_icon) """"-Xdock:icon=$ISABELLE_HOME/lib/logo/isabelle_transparent-128.png" \
""" else "") + """isabelle.Main "$@"
"""
    val script_path = isabelle_target + Path.explode("lib/scripts/Isabelle_app")
    File.write(script_path, script)
    File.set_executable(script_path, true)

    val component_dir = isabelle_target + Path.explode("contrib/Isabelle_app")
    Isabelle_System.move_file(
      component_dir + Path.explode(Platform.standard_platform(platform)) + Path.explode("Isabelle"),
      isabelle_target + Path.explode(isabelle_name))
    Isabelle_System.rm_tree(component_dir)
  }


  def make_isabelle_plist(path: Path, isabelle_name: String, isabelle_rev: String): Unit =
  {
    File.write(path, """<?xml version="1.0" ?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
<key>CFBundleDevelopmentRegion</key>
<string>English</string>
<key>CFBundleIconFile</key>
<string>isabelle.icns</string>
<key>CFBundleIdentifier</key>
<string>de.tum.in.isabelle</string>
<key>CFBundleDisplayName</key>
<string>""" + isabelle_name + """</string>
<key>CFBundleInfoDictionaryVersion</key>
<string>6.0</string>
<key>CFBundleName</key>
<string>""" + isabelle_name + """</string>
<key>CFBundlePackageType</key>
<string>APPL</string>
<key>CFBundleShortVersionString</key>
<string>""" + isabelle_name + """</string>
<key>CFBundleSignature</key>
<string>????</string>
<key>CFBundleVersion</key>
<string>""" + isabelle_rev + """</string>
<key>NSHumanReadableCopyright</key>
<string></string>
<key>LSMinimumSystemVersion</key>
<string>10.11</string>
<key>LSApplicationCategoryType</key>
<string>public.app-category.developer-tools</string>
<key>NSHighResolutionCapable</key>
<string>true</string>
<key>NSSupportsAutomaticGraphicsSwitching</key>
<string>true</string>
<key>CFBundleDocumentTypes</key>
<array>
<dict>
<key>CFBundleTypeExtensions</key>
<array>
<string>thy</string>
</array>
<key>CFBundleTypeIconFile</key>
<string>theory.icns</string>
<key>CFBundleTypeName</key>
<string>Isabelle theory file</string>
<key>CFBundleTypeRole</key>
<string>Editor</string>
<key>LSTypeIsPackage</key>
<false/>
</dict>
</array>
</dict>
</plist>
""")
  }


  /* main */

  private val default_platform_families: List[Platform.Family.Value] =
    List(Platform.Family.linux, Platform.Family.windows, Platform.Family.macos)

  def use_release_archive(
    context: Release_Context,
    archive: Release_Archive,
    id: String = ""): Unit =
  {
    if (id.nonEmpty && id != archive.id) {
      error("Mismatch of release identification " + id + " vs. archive " + archive.id)
    }

    if (!context.isabelle_archive.is_file || Bytes.read(context.isabelle_archive) != archive.bytes) {
      Bytes.write(context.isabelle_archive, archive.bytes)
    }
  }

  def build_release_archive(
    context: Release_Context,
    version: String,
    parallel_jobs: Int = 1): Unit =
  {
    val progress = context.progress

    val hg = Mercurial.repository(Path.ISABELLE_HOME)
    val id =
      try { hg.id(version) }
      catch { case ERROR(msg) => cat_error("Bad repository version: " + version, msg) }

    if (context.isabelle_archive.is_file) {
      progress.echo_warning("Found existing release archive: " + context.isabelle_archive)
      use_release_archive(context, Release_Archive.read(context.isabelle_archive), id = id)
    }
    else {
      progress.echo_warning("Preparing release " + context.dist_name + " ...")

      Isabelle_System.new_directory(context.dist_dir)

      hg.archive(context.isabelle_dir.expand.implode, rev = id, options = "--type files")

      for (name <- List(".hg_archival.txt", ".hgtags", ".hgignore", "README_REPOSITORY")) {
        (context.isabelle_dir + Path.explode(name)).file.delete
      }

      File.write(context.isabelle_dir + ISABELLE_ID, id)
      File.write(context.isabelle_dir + ISABELLE_TAGS, hg.tags(rev = id))
      File.write(context.isabelle_dir + ISABELLE_IDENTIFIER, context.dist_name)

      context.make_announce(id)

      context.make_contrib()

      execute(context.isabelle_dir, """find . -print | xargs chmod -f u+rw""")

      record_bundled_components(context.isabelle_dir)


      /* build tools and documentation */

      val other_isabelle = context.other_isabelle(context.dist_dir)

      other_isabelle.init_settings(
        other_isabelle.init_components(
          components_base = context.components_base, catalogs = List("main")))
      other_isabelle.resolve_components(echo = true)

      try {
        val export_classpath =
          "export CLASSPATH=" + Bash.string(other_isabelle.getenv("ISABELLE_CLASSPATH")) + "\n"
        other_isabelle.bash(export_classpath + "Admin/build all", echo = true).check
        other_isabelle.bash(export_classpath + "bin/isabelle jedit -b", echo = true).check
      }
      catch { case ERROR(msg) => cat_error("Failed to build tools:", msg) }

      try {
        other_isabelle.bash(
          "bin/isabelle build_doc -a -o system_heaps -j " + parallel_jobs, echo = true).check
      }
      catch { case ERROR(msg) => cat_error("Failed to build documentation:", msg) }

      other_isabelle.make_news()

      for (name <- List("Admin", "browser_info", "heaps")) {
        Isabelle_System.rm_tree(other_isabelle.isabelle_home + Path.explode(name))
      }

      other_isabelle.cleanup()


      progress.echo_warning("Creating release archive " + context.isabelle_archive + " ...")

      execute(context.dist_dir, """chmod -R a+r . && chmod -R u+w . && chmod -R g=o .""")
      execute(context.dist_dir,
        """find . -type f "(" -name "*.thy" -o -name "*.ML" -o -name "*.scala" ")" -print | xargs chmod -f u-w""")
      execute_tar(context.dist_dir, "-czf " +
        File.bash_path(context.isabelle_archive) + " " + Bash.string(context.dist_name))
    }
  }

  def build_release(
    options: Options,
    context: Release_Context,
    afp_rev: String = "",
    platform_families: List[Platform.Family.Value] = default_platform_families,
    more_components: List[Path] = Nil,
    website: Option[Path] = None,
    build_sessions: List[String] = Nil,
    build_library: Boolean = false,
    parallel_jobs: Int = 1): Unit =
  {
    val progress = context.progress


    /* release directory */

    val archive = Release_Archive.read(context.isabelle_archive)

    for (path <- List(context.isabelle, ISABELLE)) {
      Isabelle_System.rm_tree(context.dist_dir + path)
    }

    Isabelle_System.with_tmp_file("archive", ext = "tar.gz")(archive_path =>
    {
      Bytes.write(archive_path, archive.bytes)
      val extract =
        List("README", "NEWS", "ANNOUNCE", "COPYRIGHT", "CONTRIBUTORS", "doc").
          map(name => context.release_name + "/" + name)
      execute_tar(context.dist_dir,
        "-xzf " + File.bash_path(archive_path) + " " + Bash.strings(extract))
    })

    Isabelle_System.symlink(Path.explode(context.dist_name), context.dist_dir + ISABELLE)


    /* make application bundles */

    val bundle_infos = platform_families.map(context.bundle_info)

    for (bundle_info <- bundle_infos) {
      val isabelle_name = context.dist_name
      val platform = bundle_info.platform

      progress.echo("\nApplication bundle for " + platform)

      Isabelle_System.with_tmp_dir("build_release")(tmp_dir =>
      {
        // release archive

        execute_tar(tmp_dir, "-xzf " + File.bash_path(context.isabelle_archive))
        val other_isabelle = context.other_isabelle(tmp_dir)
        val isabelle_target = other_isabelle.isabelle_home


        // bundled components

        progress.echo("Bundled components:")

        val contrib_dir = Components.contrib(isabelle_target)

        val (bundled_components, jdk_component) =
          get_bundled_components(isabelle_target, platform)

        Components.resolve(context.components_base, bundled_components,
          target_dir = Some(contrib_dir),
          copy_dir = Some(context.dist_dir + Path.explode("contrib")),
          progress = progress)

        val more_components_names =
          more_components.map(Components.unpack(contrib_dir, _, progress = progress))

        Components.purge(contrib_dir, platform)

        activate_components(isabelle_target, platform, more_components_names)


        // Java parameters

        val java_options: List[String] =
          (for {
            variable <-
              List(
                "ISABELLE_JAVA_SYSTEM_OPTIONS",
                "JEDIT_JAVA_SYSTEM_OPTIONS",
                "JEDIT_JAVA_OPTIONS")
            opt <- Word.explode(other_isabelle.getenv(variable))
          }
          yield {
            val s = "-Dapple.awt.application.name="
            if (opt.startsWith(s)) s + isabelle_name else opt
          }) ::: List("-Disabelle.jedit_server=" + isabelle_name)

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
            File.change(isabelle_target + jedit_options,
              _.replaceAll("jedit_reset_font_size : int =.*", "jedit_reset_font_size : int = 24"))

            File.change(isabelle_target + jedit_props,
              _.replaceAll("console.fontsize=.*", "console.fontsize=18")
               .replaceAll("helpviewer.fontsize=.*", "helpviewer.fontsize=18")
               .replaceAll("metal.primary.fontsize=.*", "metal.primary.fontsize=18")
               .replaceAll("metal.secondary.fontsize=.*", "metal.secondary.fontsize=18")
               .replaceAll("view.fontsize=.*", "view.fontsize=24")
               .replaceAll("view.gutter.fontsize=.*", "view.gutter.fontsize=16"))

            make_isabelle_options(
              isabelle_target + Path.explode("Isabelle.options"), java_options)

            make_isabelle_app(platform, isabelle_target, isabelle_name, jdk_component, classpath)

            val archive_name = isabelle_name + "_linux.tar.gz"
            progress.echo("Packaging " + archive_name + " ...")
            execute_tar(tmp_dir,
              "-czf " + File.bash_path(context.dist_dir + Path.explode(archive_name)) + " " +
              Bash.string(isabelle_name))


          case Platform.Family.macos =>
            File.change(isabelle_target + jedit_props,
              _.replaceAll("delete-line.shortcut=.*", "delete-line.shortcut=C+d")
               .replaceAll("delete.shortcut2=.*", "delete.shortcut2=A+d"))


            // macOS application bundle

            val app_contents = isabelle_target + Path.explode("Contents")

            for (icon <- List("lib/logo/isabelle.icns", "lib/logo/theory.icns")) {
              Isabelle_System.copy_file(isabelle_target + Path.explode(icon),
                Isabelle_System.make_directory(app_contents + Path.explode("Resources")))
            }

            make_isabelle_plist(
              app_contents + Path.explode("Info.plist"), isabelle_name, archive.id)

            make_isabelle_app(platform, isabelle_target, isabelle_name, jdk_component,
              classpath, dock_icon = true)

            val isabelle_options = Path.explode("Isabelle.options")
            make_isabelle_options(
              isabelle_target + isabelle_options,
              java_options ::: List("-Disabelle.app=true"))


            // application archive

            val archive_name = isabelle_name + "_macos.tar.gz"
            progress.echo("Packaging " + archive_name + " ...")

            val isabelle_app = Path.explode(isabelle_name + ".app")
            Isabelle_System.move_file(tmp_dir + Path.explode(isabelle_name),
              tmp_dir + isabelle_app)

            execute_tar(tmp_dir,
              "-czf " + File.bash_path(context.dist_dir + Path.explode(archive_name)) + " " +
              File.bash_path(isabelle_app))


          case Platform.Family.windows =>
            File.change(isabelle_target + jedit_props,
              _.replaceAll("foldPainter=.*", "foldPainter=Square"))


            // application launcher

            Isabelle_System.move_file(isabelle_target + Path.explode("contrib/windows_app"), tmp_dir)

            val app_template = Path.explode("~~/Admin/Windows/launch4j")

            make_isabelle_options(
              isabelle_target + Path.explode(isabelle_name + ".l4j.ini"),
              java_options, line_ending = "\r\n")

            val isabelle_xml = Path.explode("isabelle.xml")
            val isabelle_exe = Path.explode(isabelle_name + ".exe")

            File.write(tmp_dir + isabelle_xml,
              File.read(app_template + isabelle_xml)
                .replace("{ISABELLE_NAME}", isabelle_name)
                .replace("{OUTFILE}", File.platform_path(isabelle_target + isabelle_exe))
                .replace("{ICON}",
                  File.platform_path(app_template + Path.explode("isabelle_transparent.ico")))
                .replace("{SPLASH}",
                  File.platform_path(app_template + Path.explode("isabelle.bmp")))
                .replace("{CLASSPATH}",
                  cat_lines(classpath.map(cp =>
                    "    <cp>%EXEDIR%\\" + File.platform_path(cp).replace('/', '\\') + "</cp>")))
                .replace("\\jdk\\", "\\" + jdk_component + "\\"))

            execute(tmp_dir,
              "\"windows_app/launch4j-${ISABELLE_PLATFORM_FAMILY}/launch4j\" isabelle.xml")

            Isabelle_System.copy_file(app_template + Path.explode("manifest.xml"),
              isabelle_target + isabelle_exe.ext("manifest"))


            // Cygwin setup

            val cygwin_template = Path.explode("~~/Admin/Windows/Cygwin")

            Isabelle_System.copy_file(cygwin_template + Path.explode("Cygwin-Terminal.bat"),
              isabelle_target)

            val cygwin_mirror =
              File.read(isabelle_target + Path.explode("contrib/cygwin/isabelle/cygwin_mirror"))

            val cygwin_bat = Path.explode("Cygwin-Setup.bat")
            File.write(isabelle_target + cygwin_bat,
              File.read(cygwin_template + cygwin_bat).replace("{MIRROR}", cygwin_mirror))
            File.set_executable(isabelle_target + cygwin_bat, true)

            for (name <- List("isabelle/postinstall", "isabelle/rebaseall")) {
              val path = Path.explode(name)
              Isabelle_System.copy_file(cygwin_template + path,
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
              File.read(Path.explode("~~/Admin/Windows/Installer/sfx.txt"))
                .replace("{ISABELLE_NAME}", isabelle_name)

            Bytes.write(context.dist_dir + isabelle_exe,
              Bytes.read(sfx_exe) + Bytes(sfx_txt) + Bytes.read(exe_archive))
            File.set_executable(context.dist_dir + isabelle_exe, true)
        }
      })
      progress.echo("DONE")
    }


    /* minimal website */

    for (dir <- website) {
      val website_platform_bundles =
        for {
          bundle_info <- bundle_infos
          if (context.dist_dir + bundle_info.path).is_file
        } yield (bundle_info.name, bundle_info)

      val isabelle_link =
        HTML.link(Isabelle_System.isabelle_repository.changeset(archive.id),
          HTML.text("Isabelle/" + archive.id))
      val afp_link =
        HTML.link(Isabelle_System.afp_repository.changeset(afp_rev),
          HTML.text("AFP/" + afp_rev))

      HTML.write_document(dir, "index.html",
        List(HTML.title(context.dist_name)),
        List(
          HTML.section(context.dist_name),
          HTML.subsection("Downloads"),
          HTML.itemize(
            List(HTML.link(context.dist_name + ".tar.gz", HTML.text("Source archive"))) ::
            website_platform_bundles.map({ case (bundle, bundle_info) =>
              List(HTML.link(bundle, HTML.text(bundle_info.platform_description + " bundle"))) })),
          HTML.subsection("Repositories"),
          HTML.itemize(
            List(List(isabelle_link)) ::: (if (afp_rev == "") Nil else List(List(afp_link))))))

      Isabelle_System.copy_file(context.isabelle_archive, dir)

      for ((bundle, _) <- website_platform_bundles) {
        Isabelle_System.copy_file(context.dist_dir + Path.explode(bundle), dir)
      }
    }


    /* HTML library */

    if (build_library) {
      if (context.isabelle_library_archive.is_file) {
        progress.echo_warning("Library archive already exists: " + context.isabelle_library_archive)
      }
      else {
        Isabelle_System.with_tmp_dir("build_release")(tmp_dir =>
          {
            val bundle =
              context.dist_dir + Path.explode(context.dist_name + "_" + Platform.family + ".tar.gz")
            execute_tar(tmp_dir, "-xzf " + File.bash_path(bundle))

            val other_isabelle = context.other_isabelle(tmp_dir)

            Isabelle_System.make_directory(other_isabelle.etc)
            File.write(other_isabelle.etc_preferences, "ML_system_64 = true\n")

            other_isabelle.bash("bin/isabelle build -f -j " + parallel_jobs +
              " -o browser_info -o document=pdf -o document_variants=document:outline=/proof,/ML" +
              " -o system_heaps -c -a -d '~~/src/Benchmarks'", echo = true).check
            other_isabelle.isabelle_home_user.file.delete

            execute(tmp_dir, "chmod -R a+r " + Bash.string(context.dist_name))
            execute(tmp_dir, "chmod -R g=o " + Bash.string(context.dist_name))
            execute_tar(tmp_dir, "-czf " + File.bash_path(context.isabelle_library_archive) +
              " " + Bash.string(context.dist_name + "/browser_info"))
          })
      }
    }
  }



  /** command line entry point **/

  def main(args: Array[String]): Unit =
  {
    Command_Line.tool {
      var afp_rev = ""
      var components_base: Path = Components.default_components_base
      var target_dir = Path.current
      var release_name = ""
      var source_archive = ""
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
    -D DIR       target directory (default ".")
    -R RELEASE   explicit release name
    -S ARCHIVE   use existing source archive (file or URL)
    -W WEBSITE   produce minimal website in given directory
    -b SESSIONS  build platform-specific session images (separated by commas)
    -c ARCHIVE   clean bundling with additional component .tar.gz archive
    -j INT       maximum number of parallel jobs (default 1)
    -l           build library
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p NAMES     platform families (default: """ + default_platform_families.mkString(",") + """)
    -r REV       Mercurial changeset id (default: ARCHIVE or RELEASE or tip)

  Build Isabelle release in base directory, using the local repository clone.
""",
        "A:" -> (arg => afp_rev = arg),
        "C:" -> (arg => components_base = Path.explode(arg)),
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "R:" -> (arg => release_name = arg),
        "S:" -> (arg => source_archive = arg),
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
      if (more_args.nonEmpty) getopts.usage()

      if (platform_families.contains(Platform.Family.windows) && !Isabelle_System.bash("7z i").ok)
        error("Building for windows requires 7z")

      def make_context(name: String): Release_Context =
        Release_Context(target_dir,
          release_name = name,
          components_base = components_base,
          progress = new Console_Progress())

      val context =
        if (source_archive.isEmpty) {
          val context = make_context(release_name)
          val version = proper_string(rev) orElse proper_string(release_name) getOrElse "tip"
          build_release_archive(context, version, parallel_jobs = parallel_jobs)
          context
        }
        else {
          val archive = Release_Archive.get(source_archive, rename = release_name)
          val context = make_context(proper_string(release_name) getOrElse archive.identifier)
          Isabelle_System.new_directory(context.dist_dir)
          use_release_archive(context, archive, id = rev)
          context
        }

      build_release(options, context, afp_rev = afp_rev,
        platform_families =
          if (platform_families.isEmpty) default_platform_families
          else platform_families,
        more_components = more_components, build_sessions = build_sessions,
        build_library = build_library, parallel_jobs = parallel_jobs, website = website)
    }
  }
}
