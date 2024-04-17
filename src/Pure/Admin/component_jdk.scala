/*  Title:      Pure/Admin/component_jdk.scala
    Author:     Makarius

Build Isabelle jdk component using downloads from Azul.
*/

package isabelle


import java.nio.file.Files
import java.nio.file.attribute.PosixFilePermission


object Component_JDK {
  /* platform information */

  sealed case class Download_Platform(name: String, url_template: String) {
    override def toString: String = name

    def url(base_url: String, jdk_version: String, zulu_version: String): String =
      base_url + "/" + url_template.replace("{V}", jdk_version).replace("{Z}", zulu_version)
  }

  val platforms: List[Download_Platform] =
    List(
      Download_Platform("arm64-darwin", "zulu{Z}-jdk{V}-macosx_aarch64.tar.gz"),
      Download_Platform("arm64-linux", "zulu{Z}-jdk{V}-linux_aarch64.tar.gz"),
      Download_Platform("x86_64-darwin", "zulu{Z}-jdk{V}-macosx_x64.tar.gz"),
      Download_Platform("x86_64-linux", "zulu{Z}-jdk{V}-linux_x64.tar.gz"),
      Download_Platform("x86_64-windows", "zulu{Z}-jdk{V}-win_x64.zip"))


  /* build jdk */

  val default_base_url = "https://cdn.azul.com/zulu/bin"
  val default_jdk_version = "21.0.3"
  val default_zulu_version = "21.34.19-ca"

  def build_jdk(
    target_dir: Path = Path.current,
    base_url: String = default_base_url,
    jdk_version: String = default_jdk_version,
    zulu_version: String = default_zulu_version,
    progress: Progress = new Progress,
  ): Unit = {
    if (Platform.is_windows) error("Cannot build on Windows")


    /* component */

    val component = "jdk-" + jdk_version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download */

    for (platform <- platforms) {
      Isabelle_System.with_tmp_dir("download", component_dir.path.file) { dir =>
        val url = platform.url(base_url, jdk_version, zulu_version)
        val name = Library.take_suffix(_ != '/', url.toList)._2.mkString
        val file = dir + Path.basic(name)
        Isabelle_System.download_file(url, file, progress = progress)

        val platform_dir = component_dir.path + Path.basic(platform.name)
        Isabelle_System.extract(file, platform_dir, strip = true)
      }
    }


    /* permissions */

    for (file <- File.find_files(component_dir.path.file, include_dirs = true)) {
      val name = file.getName
      val path = file.toPath
      val perms = Files.getPosixFilePermissions(path)
      perms.add(PosixFilePermission.OWNER_READ)
      perms.add(PosixFilePermission.GROUP_READ)
      perms.add(PosixFilePermission.OTHERS_READ)
      perms.add(PosixFilePermission.OWNER_WRITE)
      if (File.is_dll(name) || File.is_exe(name) || file.isDirectory) {
        perms.add(PosixFilePermission.OWNER_EXECUTE)
        perms.add(PosixFilePermission.GROUP_EXECUTE)
        perms.add(PosixFilePermission.OTHERS_EXECUTE)
      }
      Files.setPosixFilePermissions(path, perms)
    }


    /* settings */

    component_dir.write_settings("""
case "$ISABELLE_PLATFORM_FAMILY" in
  linux*)
    ISABELLE_JAVA_PLATFORM="$ISABELLE_PLATFORM64"
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
  windows*)
    ISABELLE_JAVA_PLATFORM="$ISABELLE_WINDOWS_PLATFORM64"
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
  macos*)
    if [ -n "$ISABELLE_APPLE_PLATFORM64" -a -d "$COMPONENT/$ISABELLE_APPLE_PLATFORM64" ]
    then
      ISABELLE_JAVA_PLATFORM="$ISABELLE_APPLE_PLATFORM64"
    else
      ISABELLE_JAVA_PLATFORM="$ISABELLE_PLATFORM64"
    fi
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
esac
""")


    /* README */

    File.write(component_dir.README,
      """This is OpenJDK """ + jdk_version + """ based on downloads by Azul, see also
https://www.azul.com/downloads/?package=jdk

The main license is GPL2, but some modules are covered by other (more liberal)
licenses, see legal/* for details.

Linux, Windows, macOS all work uniformly, depending on platform-specific
subdirectories.
""")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_jdk", "build Isabelle jdk component using downloads from Azul",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_base_url
        var jdk_version = default_jdk_version
        var zulu_version = default_zulu_version

        val getopts = Getopts("""
Usage: isabelle component_jdk [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       base URL (default: """" + default_base_url + """")
    -V NAME      JDK version (default: """" + default_jdk_version + """")
    -Z NAME      Zulu version (default: """" + default_zulu_version + """")

  Build Isabelle jdk component using downloads from Azul.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => jdk_version = arg),
          "Z:" -> (arg => zulu_version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_jdk(target_dir = target_dir, base_url = base_url,
          jdk_version = jdk_version, zulu_version = zulu_version, progress = progress)
      })
}
