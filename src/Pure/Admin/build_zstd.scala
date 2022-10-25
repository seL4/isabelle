/*  Title:      Pure/Admin/build_zstd.scala
    Author:     Makarius

Build Isabelle zstd-jni component from official download.
*/

package isabelle


object Build_Zstd {
  /* platforms */

  sealed case class Platform(name: String, template: String, exe: Boolean = false) {
    def install(jar_dir: Path, component_dir: Path, version: String): Unit = {
      val source = jar_dir + Path.explode(template.replace("{V}", version))
      val target = Isabelle_System.make_directory(component_dir + Path.basic(name))
      Isabelle_System.copy_file(source, target)
      if (exe) File.set_executable(target + source.base, true)
    }
  }

  private val platforms =
    List(
      Platform("arm64-darwin", "darwin/aarch64/libzstd-jni-{V}.dylib"),
      Platform("x86_64-darwin", "darwin/x86_64/libzstd-jni-{V}.dylib"),
      Platform("arm64-linux", "linux/aarch64/libzstd-jni-{V}.so"),
      Platform("x86_64-linux", "linux/amd64/libzstd-jni-{V}.so"),
      Platform("x86_64-windows", "win/amd64/libzstd-jni-{V}.dll", exe = true))


  /* build zstd */

  val license_url = "https://raw.githubusercontent.com/luben/zstd-jni/master/LICENSE"
  val default_download_url = "https://repo1.maven.org/maven2/com/github/luben/zstd-jni"
  val default_version = "1.5.2-5"

  def build_zstd(
    target_dir: Path = Path.current,
    download_url: String = default_download_url,
    version: String = default_version,
    progress: Progress = new Progress,
  ): Unit = {
    /* component */

    val component_name = "zstd-jni-" + version
    val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component_name))
    progress.echo("Component " + component_dir)

    File.write(component_dir + Path.basic("README"),
      "This is " + component_name + " from\n" + download_url +
        "\n\n        Makarius\n        " + Date.Format.date(Date.now()) + "\n")

    Isabelle_System.download_file(
      license_url, component_dir + Path.basic("LICENSE"), progress = progress)


    /* jar */

    val jar_name = component_name + ".jar"
    val jar = component_dir + Path.basic(jar_name)
    Isabelle_System.download_file(
      download_url + "/" + version + "/" + jar_name, jar, progress = progress)

    Isabelle_System.with_tmp_dir("build") { jar_dir =>
      progress.echo("Unpacking " + jar)
      Isabelle_System.bash("isabelle_jdk jar xf " + File.bash_path(jar.absolute),
        cwd = jar_dir.file).check
      for (platform <- platforms) platform.install(jar_dir, component_dir, version)
    }


    /* settings */

    val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))

    File.write(etc_dir + Path.basic("settings"),
"""# -*- shell-script -*- :mode=shellscript:

ISABELLE_ZSTD_HOME="$COMPONENT"

classpath "$ISABELLE_ZSTD_HOME/""" + jar_name + """"
""")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_zstd", "build Isabelle zstd-jni component from official download",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle build_zstd [OPTIONS]

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
