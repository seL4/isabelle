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
  val default_version = "3.5.4"

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

    def download(name: String, exe: Boolean = false): Unit = {
      val download_name = name.replace("{V}", version)
      val target = component_dir.lib + Path.basic(download_name)
      Isabelle_System.download_file(
        download_url + "/" + version + "/" + download_name, target, progress = progress)
      if (exe) File.set_executable(target)
    }

    download("flatlaf-{V}-no-natives.jar")

    for (platform <- platforms) download(platform.name, exe = platform.exe)


    /* settings */

    component_dir.write_settings("""
ISABELLE_FLATLAF_HOME="$COMPONENT"

classpath "$ISABELLE_FLATLAF_HOME/lib/flatlaf-""" + version + """-no-natives.jar"

isabelle_scala_service "isabelle.FlatLightLaf"
isabelle_scala_service "isabelle.FlatDarkLaf"
""")


    /* README */

    File.write(component_dir.README,
      """This is the FlatLaf Java/Swing look-and-feel from
https://www.formdev.com/flatlaf and
https://mvnrepository.com/artifact/com.formdev/flatlaf

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
