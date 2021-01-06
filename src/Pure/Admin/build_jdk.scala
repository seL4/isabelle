/*  Title:      Pure/Admin/build_jdk.scala
    Author:     Makarius

Build Isabelle jdk component from original platform installations.
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.Files
import java.nio.file.attribute.PosixFilePermission

import scala.util.matching.Regex


object Build_JDK
{
  /* platform and version information */

  sealed case class JDK_Platform(
    platform_name: String,
    platform_regex: Regex,
    exe: String = "java",
    macos_home: Boolean = false,
    jdk_version: String = "")
  {
    override def toString: String = platform_name

    def platform_path: Path = Path.explode(platform_name)

    def detect(jdk_dir: Path): Option[JDK_Platform] =
    {
      val major_version =
      {
        val Major_Version = """.*jdk(\d+).*$""".r
        val jdk_name = jdk_dir.file.getName
        jdk_name match {
          case Major_Version(s) => s
          case _ => error("Cannot determine major version from " + quote(jdk_name))
        }
      }

      val path = jdk_dir + Path.explode("bin") + Path.explode(exe)
      if (path.is_file) {
        val file_descr = Isabelle_System.bash("file -b " + File.bash_path(path)).check.out
        if (platform_regex.pattern.matcher(file_descr).matches) {
          val Version = ("^(" + major_version + """\.[0-9.]+\+\d+)(?:-LTS)?$""").r
          val version_lines =
            Isabelle_System.bash("strings " + File.bash_path(path)).check
              .out_lines.flatMap({ case Version(s) => Some(s) case _ => None })
          version_lines match {
            case List(jdk_version) => Some(copy(jdk_version = jdk_version))
            case _ => error("Expected unique version within executable " + path)
          }
        }
        else None
      }
      else None
    }
  }

  val templates: List[JDK_Platform] =
    List(
      JDK_Platform("arm64-darwin", """.*Mach-O 64-bit.*arm64.*""".r, macos_home = true),
      JDK_Platform("arm64-linux", """.*ELF 64-bit.*ARM aarch64.*""".r),
      JDK_Platform("x86_64-darwin", """.*Mach-O 64-bit.*x86[-_]64.*""".r, macos_home = true),
      JDK_Platform("x86_64-linux", """.*ELF 64-bit.*x86[-_]64.*""".r),
      JDK_Platform("x86_64-windows", """.*PE32\+ executable.*x86[-_]64.*""".r, exe = "java.exe"))


  /* README */

  def readme(jdk_version: String): String =
"""This is OpenJDK """ + jdk_version + """ based on downloads by Azul, see also
https://www.azul.com/downloads/zulu-community/?package=jdk

The main license is GPL2, but some modules are covered by other (more liberal)
licenses, see legal/* for details.

Linux, Windows, macOS all work uniformly, depending on platform-specific
subdirectories.
"""


  /* settings */

  val settings: String =
"""# -*- shell-script -*- :mode=shellscript:

case "$ISABELLE_PLATFORM_FAMILY" in
  linux)
    ISABELLE_JAVA_PLATFORM="$ISABELLE_PLATFORM64"
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
  windows)
    ISABELLE_JAVA_PLATFORM="$ISABELLE_WINDOWS_PLATFORM64"
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
  macos)
    if [ -n "$ISABELLE_APPLE_PLATFORM64" -a -d "$COMPONENT/$ISABELLE_APPLE_PLATFORM64" ]
    then
      ISABELLE_JAVA_PLATFORM="$ISABELLE_APPLE_PLATFORM64"
    else
      ISABELLE_JAVA_PLATFORM="$ISABELLE_PLATFORM64"
    fi
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
esac
"""


  /* extract archive */

  def extract_archive(dir: Path, archive: Path): JDK_Platform =
  {
    try {
      val tmp_dir = Isabelle_System.make_directory(dir + Path.explode("tmp"))

      if (archive.get_ext == "zip") {
        Isabelle_System.bash(
          "unzip -x " + File.bash_path(archive.absolute), cwd = tmp_dir.file).check
      }
      else {
        Isabelle_System.gnutar("-xzf " + File.bash_path(archive), dir = tmp_dir).check
      }

      val dir_entry =
        File.read_dir(tmp_dir) match {
          case List(s) => s
          case _ => error("Archive contains multiple directories")
        }

      val jdk_dir = tmp_dir + Path.explode(dir_entry)
      val platform =
        templates.view.flatMap(_.detect(jdk_dir))
          .headOption.getOrElse(error("Failed to detect JDK platform"))

      val platform_dir = dir + platform.platform_path
      if (platform_dir.is_dir) error("Directory already exists: " + platform_dir)

      File.move(jdk_dir, platform_dir)

      platform
    }
    catch { case ERROR(msg) => cat_error(msg, "The error(s) above occurred for " + archive) }
  }


  /* build jdk */

  def build_jdk(
    archives: List[Path],
    progress: Progress = new Progress,
    target_dir: Path = Path.current)
  {
    if (Platform.is_windows) error("Cannot build jdk on Windows")

    Isabelle_System.with_tmp_dir("jdk")(dir =>
      {
        progress.echo("Extracting ...")
        val platforms = archives.map(extract_archive(dir, _))

        val jdk_version =
          platforms.map(_.jdk_version).distinct match {
            case List(version) => version
            case Nil => error("No archives")
            case versions =>
              error("Archives contain multiple JDK versions: " + commas_quote(versions))
          }

        templates.filterNot(p1 => platforms.exists(p2 => p1.platform_name == p2.platform_name))
        match {
          case Nil =>
          case missing => error("Missing platforms: " + commas_quote(missing.map(_.platform_name)))
        }

        val jdk_name = "jdk-" + jdk_version
        val jdk_path = Path.explode(jdk_name)
        val component_dir = dir + jdk_path

        Isabelle_System.make_directory(component_dir + Path.explode("etc"))
        File.write(Components.settings(component_dir), settings)
        File.write(component_dir + Path.explode("README"), readme(jdk_version))

        for (platform <- platforms) File.move(dir + platform.platform_path, component_dir)

        for (file <- File.find_files(component_dir.file, include_dirs = true)) {
          val path = file.toPath
          val perms = Files.getPosixFilePermissions(path)
          perms.add(PosixFilePermission.OWNER_READ)
          perms.add(PosixFilePermission.GROUP_READ)
          perms.add(PosixFilePermission.OTHERS_READ)
          perms.add(PosixFilePermission.OWNER_WRITE)
          if (file.isDirectory) {
            perms.add(PosixFilePermission.OWNER_WRITE)
            perms.add(PosixFilePermission.OWNER_EXECUTE)
            perms.add(PosixFilePermission.GROUP_EXECUTE)
            perms.add(PosixFilePermission.OTHERS_EXECUTE)
          }
          Files.setPosixFilePermissions(path, perms)
        }

        progress.echo("Archiving ...")
        Isabelle_System.gnutar(
          "-czf " + File.bash_path(target_dir + jdk_path.ext("tar.gz")) + " " + jdk_name,
          dir = dir).check
      })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_jdk", "build Isabelle jdk component from original archives",
      Scala_Project.here, args =>
    {
      var target_dir = Path.current

      val getopts = Getopts("""
Usage: isabelle build_jdk [OPTIONS] ARCHIVES...

  Options are:
    -D DIR       target directory (default ".")

  Build jdk component from tar.gz archives, with original jdk archives
  for Linux, Windows, and macOS.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)))

      val more_args = getopts(args)
      if (more_args.isEmpty) getopts.usage()

      val archives = more_args.map(Path.explode)
      val progress = new Console_Progress()

      build_jdk(archives = archives, progress = progress, target_dir = target_dir)
    })
}
