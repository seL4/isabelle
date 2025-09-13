/*  Title:      Pure/Admin/component_zstd.scala
    Author:     Makarius

Build Isabelle zstd-jni component from official download.
*/

package isabelle


object Component_Zstd {
  /* platforms */

  sealed case class Platform_Info(name: String, template: String, exe: Boolean = false) {
    def install(jar_dir: Path, component_dir: Path, version: String): Unit = {
      val source = jar_dir + Path.explode(template.replace("{V}", version))
      val target = Isabelle_System.make_directory(component_dir + Path.basic(name))
      Isabelle_System.copy_file(source, target)
      if (exe) File.set_executable(target + source.base)
    }
  }

  private val platforms =
    List(
      Platform_Info("arm64-darwin", "darwin/aarch64/libzstd-jni-{V}.dylib"),
      Platform_Info("x86_64-darwin", "darwin/x86_64/libzstd-jni-{V}.dylib"),
      Platform_Info("arm64-linux", "linux/aarch64/libzstd-jni-{V}.so"),
      Platform_Info("x86_64-linux", "linux/amd64/libzstd-jni-{V}.so"),
      Platform_Info("x86_64-windows", "win/amd64/libzstd-jni-{V}.dll", exe = true))


  /* build zstd */

  val license_url = "https://raw.githubusercontent.com/luben/zstd-jni/master/LICENSE"
  val default_download_url = "https://repo1.maven.org/maven2/com/github/luben/zstd-jni"
  val default_version = "1.5.7-4"

  def build_zstd(
    target_dir: Path = Path.current,
    download_url: String = default_download_url,
    version: String = default_version,
    progress: Progress = new Progress,
  ): Unit = {
    /* component */

    val component_name = "zstd-jni-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

    File.write(component_dir.README,
      "This is " + component_name + " from\n" + download_url +
        "\n\n        Makarius\n        " + Date.Format.date(Date.now()) + "\n")

    Isabelle_System.download_file(license_url, component_dir.LICENSE, progress = progress)


    /* jar */

    Isabelle_System.make_directory(component_dir.lib)

    val jar_name = component_name + ".jar"
    val jar = component_dir.lib + Path.basic(jar_name)
    Isabelle_System.download_file(
      download_url + "/" + version + "/" + jar_name, jar, progress = progress)

    Isabelle_System.with_tmp_dir("build") { jar_dir =>
      Isabelle_System.extract(jar, jar_dir)
      for (platform <- platforms) platform.install(jar_dir, component_dir.path, version)
    }


    /* settings */

    component_dir.write_settings("""
ISABELLE_ZSTD_HOME="$COMPONENT"

classpath "$ISABELLE_ZSTD_HOME/lib/""" + jar_name + """"
""")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_zstd", "build Isabelle zstd-jni component from official download",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_zstd [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """ + quote(default_download_url) + """)
    -V VERSION   version (default: """ + quote(default_version) + """)

  Build zstd-jni component from the specified download base URL and VERSION,
  see also https://github.com/luben/zstd-jni
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_zstd(target_dir = target_dir, download_url = download_url,
          version = version, progress = progress)
      })
}
