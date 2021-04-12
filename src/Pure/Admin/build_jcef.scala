/*  Title:      Pure/Admin/build_jcef.scala
    Author:     Makarius

Build Isabelle component for Java Chromium Embedded Framework (JCEF).
See also:

  - https://github.com/jcefbuild/jcefbuild
  - https://github.com/chromiumembedded/java-cef
*/

package isabelle


object Build_JCEF
{
  /* platform information */

  sealed case class JCEF_Platform(platform_name: String, archive: String)
  {
    def archive_path: Path = Path.explode(archive)
    def dir(component_dir: Path): Path = component_dir + Path.basic(platform_name)
  }

  val platforms: List[JCEF_Platform] =
    List(
      JCEF_Platform("x86_64-linux", "linux64.zip"),
      JCEF_Platform("x86_64-windows", "win64.zip"),
      JCEF_Platform("x86_64-darwin", "macosx64.zip"))


  /* build JCEF */

  val default_url = "https://github.com/jcefbuild/jcefbuild/releases/download"
  val default_version = "v1.0.10-83.4.0+gfd6631b+chromium-83.0.4103.106"

  def build_jcef(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress): Unit =
  {
    /* component name */

    val Version = """^([^+]+).*$""".r
    val component =
      version match {
        case Version(name) => "jcef-" + name
        case _ => error("Bad component version " + quote(version))
      }
    val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component))
    progress.echo("Component " + component_dir)


    /* download and assemble platforms */

    for (platform <- platforms) {
      Isabelle_System.with_tmp_file("archive", ext = "zip")(archive_file =>
      {
        val url = base_url + "/" + Url.encode(version) + "/" + platform.archive
        Isabelle_System.download_file(url, archive_file, progress = progress)
        Isabelle_System.bash("unzip -x " + File.bash_path(archive_file),
            cwd = component_dir.file).check

        val unzip_dir = component_dir + Path.explode("java-cef-build-bin")
        for {
          file <- File.find_files(unzip_dir.file).iterator
          name = file.getName if name.containsSlice("LICENSE")
          target_file = component_dir + Path.explode(name) if !target_file.is_file
        } Isabelle_System.move_file(File.path(file), target_file)

        val platform_dir = component_dir + Path.explode(platform.platform_name)
        Isabelle_System.move_file(unzip_dir + Path.explode("bin"), platform_dir)
        for {
          file <- File.find_files(platform_dir.file).iterator
          name = file.getName
          if name.endsWith(".dll") || name.endsWith(".exe")
        } File.set_executable(File.path(file), true)

        Isabelle_System.rm_tree(unzip_dir)
      })
    }


    /* settings */

    val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
    File.write(etc_dir + Path.basic("settings"),
      """# -*- shell-script -*- :mode=shellscript:

if [ -d "$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}" ]
then
  ISABELLE_JCEF_HOME="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}"
  ISABELLE_JCEF_LIBRARY=""
  case "$ISABELLE_PLATFORM_FAMILY" in
    linux)
      classpath "$ISABELLE_JCEF_HOME/"*.jar
      ISABELLE_JCEF_LIB="$ISABELLE_JCEF_HOME/lib/linux64"
      ISABELLE_JCEF_LIBRARY="$ISABELLE_JCEF_LIB/libcef.so"
      export LD_LIBRARY_PATH="$ISABELLE_JCEF_LIB:$LD_LIBRARY_PATH"
      ;;
    windows)
      classpath "$ISABELLE_JCEF_HOME/"*.jar
      ISABELLE_JCEF_LIB="$ISABELLE_JCEF_HOME/lib/win64"
      export PATH="$ISABELLE_JCEF_LIB:$PATH"
      ;;
    macos)
      classpath "$ISABELLE_JCEF_HOME/jcef_app.app/Contents/Java/"*.jar
      ISABELLE_JCEF_LIB="$ISABELLE_JCEF_HOME/jcef_app.app/Contents/Frameworks/Chromium Embedded Framework.framework/Libraries"
      export JAVA_LIBRARY_PATH="$ISABELLE_JCEF_HOME/jcef_app.app/Contents/Java:$ISABELLE_JCEF_LIB:$JAVA_LIBRARY_PATH"
      ;;
  esac
fi
""")


    /* README */

    File.write(component_dir + Path.basic("README"),
      """This distribution of Java Chromium Embedded Framework (JCEF)
has been assembled from the binary builds from
""" + base_url + """

Examples invocations:

* command-line

  isabelle env bash -c 'isabelle java -Djava.library.path="$(platform_path "$ISABELLE_JCEF_LIB")" tests.detailed.MainFrame'

* Scala REPL (e.g. Isabelle/jEdit Console)

  import isabelle._
  System.setProperty("java.library.path", File.platform_path(Path.explode("$ISABELLE_JCEF_LIB")))
  org.cef.CefApp.startup(Array())
  GUI_Thread.later { val frame = new tests.detailed.MainFrame(false, false, false, Array()); frame.setSize(1200,900); frame.setVisible(true) }


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_jcef", "build component for Java Chromium Embedded Framework",
      Scala_Project.here, args =>
    {
      var target_dir = Path.current
      var base_url = default_url
      var version = default_version

      val getopts = Getopts("""
Usage: isabelle build_jcef [OPTIONS]

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
