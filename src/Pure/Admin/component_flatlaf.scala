/*  Title:      Pure/Admin/component_flatlaf.scala
    Author:     Makarius

Build Isabelle flatlaf component from official downloads.
*/

package isabelle


object Component_FlatLaf {
  /* platform information */

  sealed case class Platform_Info(name: String, exe: Boolean = false)

  private val platforms =
    List(
      Platform_Info("flatlaf-{V}-macos-arm64.dylib"),
      Platform_Info("flatlaf-{V}-macos-x86_64.dylib"),
      Platform_Info("flatlaf-{V}-linux-x86_64.so"),
      Platform_Info("flatlaf-{V}-windows-x86_64.dll", exe = true))


  /* build flatlaf */

  val default_download_url = "https://repo1.maven.org/maven2/com/formdev/flatlaf"
  val default_portable_version = "2.6"
  val default_native_version = "3.5.4"

  def build_flatlaf(
    target_dir: Path = Path.current,
    download_url: String = default_download_url,
    portable_version: String = default_portable_version,
    native_version: String = default_native_version,
    progress: Progress = new Progress,
  ): Unit = {
    /* component */

    val component_name = "flatlaf-" + native_version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


    /* download */

    Isabelle_System.make_directory(component_dir.lib)

    def download(name: String, version: String, dir: Path): Path = {
      val download_name = name.replace("{V}", version)
      val target = dir + Path.basic(download_name)
      Isabelle_System.download_file(
        download_url + "/" + version + "/" + download_name, target, progress = progress)
      target
    }

    download("flatlaf-{V}-no-natives.jar", native_version, component_dir.lib)
    download("flatlaf-{V}.jar", portable_version, component_dir.lib)

    for (platform <- platforms) {
      val path = download(platform.name, native_version, component_dir.lib)
      if (platform.exe) File.set_executable(path)
    }


    /* settings */

    component_dir.write_settings("""
ISABELLE_FLATLAF_HOME="$COMPONENT"

if [ "$ISABELLE_PLATFORM64" = "arm64-linux" ]; then
  classpath "$ISABELLE_FLATLAF_HOME/lib/flatlaf-""" + portable_version + """.jar"
else
  classpath "$ISABELLE_FLATLAF_HOME/lib/flatlaf-""" + native_version + """-no-natives.jar"
fi

isabelle_scala_service "isabelle.FlatLightLaf"
isabelle_scala_service "isabelle.FlatDarkLaf"
""")


    /* README */

    File.write(component_dir.README,
      """This is the FlatLaf Java/Swing look-and-feel from
https://www.formdev.com/flatlaf and
https://mvnrepository.com/artifact/com.formdev/flatlaf

It is covered by the Apache License 2.0 license.

The last portable version was """ + portable_version + ", but current " + native_version +
""" requires a Java jar
together with a native library (e.g. in the same directory).


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
        var native_version = default_native_version
        var portable_version = default_portable_version

        val getopts = Getopts("""
Usage: isabelle component_flatlaf [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """ + quote(default_download_url) + """)
    -N VERSION   native version (default: """ + quote(default_native_version) + """)
    -P VERSION   portable version (default: """ + quote(default_portable_version) + """)

  Build flatlaf component from official downloads.""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg),
          "N:" -> (arg => native_version = arg),
          "P:" -> (arg => portable_version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_flatlaf(target_dir = target_dir, download_url = download_url,
          portable_version = portable_version, native_version = native_version, progress = progress)
      })
}
