/*  Title:      Pure/Admin/component_flatlaf.scala
    Author:     Makarius

Build Isabelle flatlaf component from official downloads.
*/

package isabelle


object Component_FlatLaf {
  /* jars and native libraries */

  sealed case class Lib(template: String, exe: Boolean = false) {
    def path(version: String): Path =
      Path.explode(template.replace("{V}", version))

    def jar_name(version: String): Option[String] =
      if (File.is_jar(template)) Some(path(version).file_name) else None
  }

  private val libs =
    List(
      Lib("flatlaf/{V}/flatlaf-{V}-no-natives.jar"),
      Lib("flatlaf/{V}/flatlaf-{V}-macos-arm64.dylib"),
      Lib("flatlaf/{V}/flatlaf-{V}-macos-x86_64.dylib"),
      Lib("flatlaf/{V}/flatlaf-{V}-linux-arm64.so"),
      Lib("flatlaf/{V}/flatlaf-{V}-linux-x86_64.so"),
      Lib("flatlaf/{V}/flatlaf-{V}-windows-x86_64.dll", exe = true))


  /* build flatlaf */

  val default_download_url = "https://repo1.maven.org/maven2/com/formdev"
  val default_version = "3.6"

  def build_flatlaf(
    target_dir: Path = Path.current,
    download_url: String = default_download_url,
    version: String = default_version,
    progress: Progress = new Progress,
  ): Unit = {
    /* component */

    val component_name = "flatlaf-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


    /* download */

    Isabelle_System.make_directory(component_dir.lib)

    for (lib <- libs) {
      val lib_path = lib.path(version)
      val target = component_dir.lib + Path.basic(lib_path.file_name)
      Isabelle_System.download_file(
        download_url + "/" + lib_path.implode, target, progress = progress)
      if (lib.exe) File.set_executable(target)
    }

    val jar_names = libs.flatMap(_.jar_name(version))


    /* settings */

    val classpath =
      libs.flatMap(_.jar_name(version)).map(a => "$ISABELLE_FLATLAF_HOME/lib/" + a)
        .mkString(":")

    component_dir.write_settings("""
ISABELLE_FLATLAF_HOME="$COMPONENT"

classpath """ + quote(classpath) + """

isabelle_scala_service "isabelle.FlatLightLaf"
isabelle_scala_service "isabelle.FlatDarkLaf"
""")


    /* README */

    File.write(component_dir.README,
      """This is the FlatLaf Java/Swing look-and-feel from
https://www.formdev.com/flatlaf and
https://mvnrepository.com/artifact/com.formdev

It is covered by the Apache License 2.0 license.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_flatlaf", "build Isabelle flatlaf component from official downloads",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_flatlaf [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """ + quote(default_download_url) + """)
    -V VERSION   version (default: """ + quote(default_version) + """)

  Build flatlaf component from official downloads.""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_flatlaf(target_dir = target_dir, download_url = download_url, version = version,
          progress = progress)
      })
}
