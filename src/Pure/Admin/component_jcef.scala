/*  Title:      Pure/Admin/component_jcef.scala
    Author:     Makarius

Build Isabelle component for Java Chromium Embedded Framework (JCEF).
See also:

  - https://github.com/jcefmaven/jcefbuild
  - https://github.com/chromiumembedded/java-cef
*/

package isabelle


object Component_JCEF {
  /* platform information */

  sealed case class JCEF_Platform(
    platform_name: String, archive: String, lib: String, library: String)

  private val linux_library =
    """ISABELLE_JCEF_LIBRARY="$ISABELLE_JCEF_LIB/libcef.so"
      export LD_LIBRARY_PATH="$ISABELLE_JCEF_LIB:$JAVA_HOME/lib:$LD_LIBRARY_PATH""""

  private val macos_library =
    """export JAVA_LIBRARY_PATH="$ISABELLE_JCEF_HOME/bin/jcef_app.app/Contents/Java:$ISABELLE_JCEF_LIB:$JAVA_LIBRARY_PATH""""

  private val windows_library =
    """export PATH="$ISABELLE_JCEF_LIB:$PATH""""

  val platforms: List[JCEF_Platform] =
    List(
      JCEF_Platform("x86_64-linux", "linux-amd64.tar.gz", "bin/lib/linux64", linux_library),
      JCEF_Platform("arm64-linux", "linux-arm64.tar.gz", "bin/lib/linux64", linux_library),
      JCEF_Platform("x86_64-darwin", "macosx-amd64.tar.gz",
        "bin/jcef_app.app/Contents/Frameworks/Chromium Embedded Framework.framework/Libraries", macos_library),
      JCEF_Platform("arm64-darwin", "macosx-arm64.tar.gz",
        "bin/jcef_app.app/Contents/Frameworks/Chromium Embedded Framework.framework/Libraries", macos_library),
      JCEF_Platform("x86_64-windows", "windows-amd64.tar.gz", "bin/lib/win64", windows_library))


  /* build JCEF */

  val default_url = "https://github.com/jcefmaven/jcefbuild/releases/download"
  val default_version = "1.0.61"

  def build_jcef(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component name */

    val component = "jcef-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download and assemble platforms */

    val platform_settings: List[String] =
      for (platform <- platforms) yield {
        Isabelle_System.with_tmp_file("archive", ext = "tar.gz") { archive_file =>
          val url = base_url + "/" + version + "/" + platform.archive
          Isabelle_System.download_file(url, archive_file, progress = progress)

          val platform_dir = component_dir.path + Path.explode(platform.platform_name)
          Isabelle_System.make_directory(platform_dir)
          Isabelle_System.gnutar("-xzf " + File.bash_path(archive_file), dir = platform_dir).check

          for {
            file <- File.find_files(platform_dir.file).iterator
            name = file.getName
            if File.is_dll(name) || File.is_exe(name)
          } File.set_executable(File.path(file), true)

          val classpath =
            File.find_files(platform_dir.file, pred = file => File.is_jar(file.getName))
              .flatMap(file => File.relative_path(platform_dir, File.path(file)))
              .map(_.implode).sorted.map(jar => "        " + quote("$ISABELLE_JCEF_HOME/" + jar))
              .mkString(" \\\n")

          "    " + platform.platform_name + ")\n" +
          "      " + "classpath \\\n" + classpath + "\n" +
          "      " + "ISABELLE_JCEF_LIB=\"$ISABELLE_JCEF_HOME/" + platform.lib + "\"\n" +
          "      " + platform.library + "\n" +
          "      " + ";;"
        }
      }


    /* settings */

    File.write(component_dir.settings,
      """# -*- shell-script -*- :mode=shellscript:

ISABELLE_JCEF_PLATFORM="${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}"
if [ -d "$COMPONENT/$ISABELLE_JCEF_PLATFORM" ]
then
  ISABELLE_JCEF_HOME="$COMPONENT/$ISABELLE_JCEF_PLATFORM"
  ISABELLE_JCEF_LIBRARY=""
  case "$ISABELLE_JCEF_PLATFORM" in
""" + cat_lines(platform_settings) + """
  esac
fi
""")


    /* README */

    File.write(component_dir.README,
      """This distribution of Java Chromium Embedded Framework (JCEF)
has been assembled from the binary builds from
https://github.com/jcefmaven/jcefbuild/releases/tag/""" +version + """

Examples invocations:

* Command-line

  isabelle env bash -c 'isabelle java -Djava.library.path="$(platform_path "$ISABELLE_JCEF_LIB")" tests.detailed.MainFrame'

* Scala REPL (e.g. Isabelle/jEdit Console)

  import isabelle._
  System.setProperty("java.library.path", File.platform_path(Path.explode("$ISABELLE_JCEF_LIB")))
  org.cef.CefApp.startup(Array())
  GUI_Thread.later { val frame = new tests.detailed.MainFrame(false, false, false, 60, Array()); frame.setSize(1200,900); frame.setVisible(true) }

* Demo websites

    https://mozilla.github.io/pdf.js/web/viewer.html
    https://www.w3schools.com/w3css/w3css_demo.asp


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_jcef", "build component for Java Chromium Embedded Framework",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_jcef [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")

  Build component for Java Chromium Embedded Framework.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_jcef(base_url = base_url, version = version, target_dir = target_dir,
          progress = progress)
      })
}
