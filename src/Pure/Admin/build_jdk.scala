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
  /* version */

  def detect_version(s: String): String =
  {
    val Version_Dir_Entry = """^jdk-([0-9.]+\+\d+)$""".r
    s match {
      case Version_Dir_Entry(version) => version
      case _ => error("Cannot detect JDK version from " + quote(s))
    }
  }


  /* platform */

  sealed case class JDK_Platform(name: String, home: String, exe: String, regex: Regex)
  {
    override def toString: String = name

    def detect(jdk_dir: Path): Boolean =
    {
      val path = jdk_dir + Path.explode(exe)
      if (path.is_file) {
        val file_descr = Isabelle_System.bash("file -b " + File.bash_path(path)).check.out
        regex.pattern.matcher(file_descr).matches
      }
      else false
    }
  }
  val jdk_platforms =
    List(
      JDK_Platform("arm64-linux", ".", "bin/java", """.*ELF 64-bit.*ARM aarch64.*""".r),
      JDK_Platform("x86_64-linux", ".", "bin/java", """.*ELF 64-bit.*x86[-_]64.*""".r),
      JDK_Platform("x86_64-windows", ".", "bin/java.exe", """.*PE32\+ executable.*x86[-_]64.*""".r),
      JDK_Platform("x86_64-darwin", "Contents/Home", "Contents/Home/bin/java",
        """.*Mach-O 64-bit.*x86[-_]64.*""".r))


  /* README */

  def readme(version: String): String =
"""This is OpenJDK """ + version + """ as required for Isabelle.

See https://adoptopenjdk.net for the original downloads, which are covered
the GPL2 (with various liberal exceptions, see legal/*).

Linux (arm64 and x86_64), Windows (x86_64), and macOS (x86_64) all work
uniformly, depending on certain platform-specific subdirectories.
"""


  /* settings */

  val settings =
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
    ISABELLE_JAVA_PLATFORM="$ISABELLE_PLATFORM64"
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM/Contents/Home"
    ;;
esac
"""


  /* extract archive */

  private def suppress_name(name: String): Boolean = name.startsWith("._")

  def extract_archive(dir: Path, archive: Path): (String, JDK_Platform) =
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
        File.read_dir(tmp_dir).filterNot(suppress_name) match {
          case List(s) => s
          case _ => error("Archive contains multiple directories")
        }
      val version = detect_version(dir_entry)

      val jdk_dir = tmp_dir + Path.explode(dir_entry)
      val platform =
        jdk_platforms.find(_.detect(jdk_dir)) getOrElse error("Failed to detect JDK platform")

      val platform_dir = dir + Path.explode(platform.name)
      if (platform_dir.is_dir) error("Directory already exists: " + platform_dir)

      File.link(Path.current, jdk_dir + Path.explode(platform.home) + Path.explode("jre"))

      File.move(jdk_dir, platform_dir)

      (version, platform)
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
        val extracted = archives.map(extract_archive(dir, _))

        val version =
          extracted.map(_._1).distinct match {
            case List(version) => version
            case Nil => error("No archives")
            case versions =>
              error("Archives contain multiple JDK versions: " + commas_quote(versions))
          }

        val missing_platforms =
          jdk_platforms.filterNot(p1 => extracted.exists({ case (_, p2) => p1.name == p2.name }))
        if (missing_platforms.nonEmpty)
          error("Missing platforms: " + commas_quote(missing_platforms.map(_.name)))

        val jdk_name = "jdk-" + version
        val jdk_path = Path.explode(jdk_name)
        val component_dir = dir + jdk_path

        Isabelle_System.make_directory(component_dir + Path.explode("etc"))
        File.write(Components.settings(component_dir), settings)
        File.write(component_dir + Path.explode("README"), readme(version))

        for ((_, platform) <- extracted)
          File.move(dir + Path.explode(platform.name), component_dir)

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

        File.find_files((component_dir + Path.explode("x86_64-darwin")).file,
          file => suppress_name(file.getName)).foreach(_.delete)

        progress.echo("Sharing ...")
        val main_dir :: other_dirs =
          jdk_platforms.map(platform => (component_dir + Path.explode(platform.name)).file.toPath)
        for {
          file1 <- File.find_files(main_dir.toFile).iterator
          path1 = file1.toPath
          dir2 <- other_dirs.iterator
        } {
          val path2 = dir2.resolve(main_dir.relativize(path1))
          val file2 = path2.toFile
          if (!Files.isSymbolicLink(path2) && file2.isFile && File.eq_content(file1, file2)) {
            file2.delete
            Files.createLink(path2, path1)
          }
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
  for Linux (arm64 and x86_64), Windows (x86_64), Mac OS X (x86_64).
""",
        "D:" -> (arg => target_dir = Path.explode(arg)))

      val more_args = getopts(args)
      if (more_args.isEmpty) getopts.usage()

      val archives = more_args.map(Path.explode)
      val progress = new Console_Progress()

      build_jdk(archives = archives, progress = progress, target_dir = target_dir)
    })
}
