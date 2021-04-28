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
    val ident: String,
    val tags: String)
  {
    val isabelle: Path = Path.explode(dist_name)
    val isabelle_dir: Path = dist_dir + isabelle
    val isabelle_id: Path = isabelle_dir + Path.explode("etc/ISABELLE_ID")
    val isabelle_tags: Path = isabelle_dir + Path.explode("etc/ISABELLE_TAGS")
    val isabelle_identifier: Path = isabelle_dir + Path.explode("etc/ISABELLE_IDENTIFIER")
    val isabelle_archive: Path = dist_dir + Path.explode(dist_name + ".tar.gz")
    val isabelle_library_archive: Path = dist_dir + Path.explode(dist_name + "_library.tar.gz")

    def other_isabelle(dir: Path): Other_Isabelle =
      Other_Isabelle(dir + isabelle,
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

  /* ANNOUNCE */

  def make_announce(release: Release): Unit =
  {
    File.write(release.isabelle_dir + Path.explode("ANNOUNCE"),
"""
IMPORTANT NOTE
==============

This is a snapshot of Isabelle/""" + release.ident + """ from the repository.

""")
  }


  /* NEWS */

  def make_news(other_isabelle: Other_Isabelle, dist_version: String): Unit =
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

  def make_contrib(dir: Path): Unit =
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
    local_dir: Path): Unit =
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

  def build_release(options: Options,
    target_dir: Path = Path.current,
    components_base: Path = Components.default_components_base,
    progress: Progress = new Progress,
    rev: String = "",
    afp_rev: String = "",
    proper_release_name: Option[String] = None,
    platform_families: List[Platform.Family.Value] = default_platform_families,
    more_components: List[Path] = Nil,
    website: Option[Path] = None,
    build_sessions: List[String] = Nil,
    build_library: Boolean = false,
    parallel_jobs: Int = 1): Release =
  {
    val hg = Mercurial.repository(Path.ISABELLE_HOME)

    val release =
    {
      val date = Date.now()
      val dist_name = proper_release_name getOrElse ("Isabelle_" + Date.Format.date(date))
      val dist_dir = (target_dir + Path.explode("dist-" + dist_name)).absolute

      val version = proper_string(rev) orElse proper_release_name getOrElse "tip"
      val ident =
        try { hg.id(version) }
        catch { case ERROR(msg) => cat_error("Bad repository version: " + version, msg) }
      val tags = hg.tags(rev = ident)

      val dist_version =
        proper_release_name match {
          case Some(name) => name + ": " + Date.Format("LLLL uuuu")(date)
          case None => "Isabelle repository snapshot " + ident + " " + Date.Format.date(date)
        }

      new Release(progress, date, dist_name, dist_dir, dist_version, ident, tags)
    }


    /* make distribution */

    if (release.isabelle_archive.is_file) {
      progress.echo_warning("Release archive already exists: " + release.isabelle_archive)

      val archive_ident =
        Isabelle_System.with_tmp_dir("build_release")(tmp_dir =>
          {
            val isabelle_id = release.isabelle + Path.explode("etc/ISABELLE_ID")
            execute_tar(tmp_dir, "-xzf " +
              File.bash_path(release.isabelle_archive) + " " + File.bash_path(isabelle_id))
            Isabelle_System.isabelle_id(root = tmp_dir + release.isabelle)
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

      File.write(release.isabelle_id, release.ident)
      File.write(release.isabelle_tags, release.tags)
      File.write(release.isabelle_identifier, release.dist_name)

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
              "-czf " + File.bash_path(release.dist_dir + Path.explode(archive_name)) + " " +
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
              app_contents + Path.explode("Info.plist"), isabelle_name, release.ident)

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
              "-czf " + File.bash_path(release.dist_dir + Path.explode(archive_name)) + " " +
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
        Isabelle_System.copy_file(release.dist_dir + Path.explode(bundle), dir)
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

  def main(args: Array[String]): Unit =
  {
    Command_Line.tool {
      var afp_rev = ""
      var components_base: Path = Components.default_components_base
      var target_dir = Path.current
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
    -D DIR       target directory (default ".")
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
        "D:" -> (arg => target_dir = Path.explode(arg)),
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
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      if (platform_families.contains(Platform.Family.windows) && !Isabelle_System.bash("7z i").ok)
        error("Building for windows requires 7z")

      build_release(options, target_dir = target_dir, components_base = components_base,
        progress = progress, rev = rev, afp_rev = afp_rev,
        proper_release_name = proper_release_name, website = website,
        platform_families =
          if (platform_families.isEmpty) default_platform_families
          else platform_families,
        more_components = more_components, build_sessions = build_sessions,
        build_library = build_library, parallel_jobs = parallel_jobs)
    }
  }
}
