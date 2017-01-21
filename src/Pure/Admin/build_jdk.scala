/*  Title:      Pure/Admin/build_jdk.scala
    Author:     Makarius

Build Isabelle jdk component from original platform installations.
*/

package isabelle


import scala.util.matching.Regex


object Build_JDK
{
  /* version */

  sealed case class Version(short: String, full: String)

  def detect_version(s: String): Version =
  {
    val Version_Dir_Entry = """^jdk1\.(\d+)\.0_(\d+)(?:\.jdk)?$""".r
    s match {
      case Version_Dir_Entry(a, b) => Version(a + "u" + b, "1." + a + ".0_" + b)
      case _ => error("Cannot detect JDK version from " + quote(s))
    }
  }


  /* platform */

  sealed case class JDK_Platform(name: String, exe: String, regex: Regex)
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
    List(JDK_Platform("x86-linux", "bin/java", """.*ELF 32-bit.*80386.*""".r),
      JDK_Platform("x86_64-linux", "bin/java", """.*ELF 64-bit.*x86[-_]64.*""".r),
      JDK_Platform("x86-windows", "bin/java.exe", """.*PE32 executable.*80386.*""".r),
      JDK_Platform("x86_64-windows", "bin/java.exe", """.*PE32\+ executable.*x86[-_]64.*""".r),
      JDK_Platform("x86_64-darwin", "Contents/Home/bin/java", """.*Mach-O 64-bit.*x86[-_]64.*""".r))


  /* README */

  def readme(version: Version): String =
"""This is JDK/JRE """ + version.full + """ as required for Isabelle.

See http://www.oracle.com/technetwork/java/javase/downloads/index.html
for the original downloads, which are covered by the Oracle Binary
Code License Agreement for Java SE.

Linux, Windows, Mac OS X all work uniformly, depending on certain
platform-specific subdirectories.
"""


  /* settings */

  val settings =
"""# -*- shell-script -*- :mode=shellscript:

case "$ISABELLE_PLATFORM_FAMILY" in
  linux)
    ISABELLE_JAVA_PLATFORM="${ISABELLE_PLATFORM64:-$ISABELLE_PLATFORM32}"
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
  windows)
    if [ ! -e "$COMPONENT/x86_64-windows" ]; then
      ISABELLE_JAVA_PLATFORM="x86-windows"
    elif "$COMPONENT/x86_64-windows/jre/bin/java" -version > /dev/null 2> /dev/null; then
      ISABELLE_JAVA_PLATFORM="x86_64-windows"
    else
      ISABELLE_JAVA_PLATFORM="x86-windows"
    fi
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
  macos)
    if [ -z "$ISABELLE_PLATFORM64" ]; then
      echo "### Java unavailable on 32bit Mac OS X" >&2
    else
      ISABELLE_JAVA_PLATFORM="$ISABELLE_PLATFORM64"
      ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM/Contents/Home"
    fi
    ;;
esac
"""


  /* extract archive */

  def extract_archive(dir: Path, archive: Path): (Version, JDK_Platform) =
  {
    try {
      val tmp_dir = dir + Path.explode("tmp")
      Isabelle_System.mkdirs(tmp_dir)
      Isabelle_System.bash(
        "tar -C " + File.bash_path(tmp_dir) + " -xzf " + File.bash_path(archive)).check
      val dir_entry =
        File.read_dir(tmp_dir) match {
          case List(s) => s
          case _ => error("Archive contains multiple directories")
        }
      val version = detect_version(dir_entry)

      val jdk_dir = tmp_dir + Path.explode(dir_entry)
      val platform =
        jdk_platforms.find(_.detect(jdk_dir)) getOrElse error("Failed to detect JDK platform")

      val platform_dir = dir + Path.explode(platform.name)
      if (platform_dir.is_dir) error("Directory already exists: " + platform_dir)
      Isabelle_System.bash(
        "mv " + File.bash_path(jdk_dir) + " " + File.bash_path(platform_dir)).check

      (version, platform)
    }
    catch { case ERROR(msg) => cat_error(msg, "The error(s) above occurred for " + archive) }
  }


  /* build jdk */

  def build_jdk(
    archives: List[Path],
    progress: Progress = No_Progress,
    target_dir: Path = Path.current)
  {
    if (Platform.is_windows) error("Cannot build jdk on Windows")

    Isabelle_System.with_tmp_dir("jdk")(dir =>
      {
        progress.echo("Extracting ...")
        val extracted = archives.map(extract_archive(dir, _))

        val version =
          extracted.map(_._1).toSet.toList match {
            case List(version) => version
            case Nil => error("No archives")
            case versions =>
              error("Archives contain multiple JDK versions: " +
                commas_quote(versions.map(_.short)))
          }

        val missing_platforms =
          jdk_platforms.filterNot(p1 => extracted.exists({ case (_, p2) => p1.name == p2.name }))
        if (missing_platforms.nonEmpty)
          error("Missing platforms: " + commas_quote(missing_platforms.map(_.name)))

        val jdk_name = "jdk-" + version.short
        val jdk_path = Path.explode(jdk_name)
        val component_dir = dir + jdk_path

        Isabelle_System.mkdirs(component_dir + Path.explode("etc"))
        File.write(component_dir + Path.explode("etc/settings"), settings)
        File.write(component_dir + Path.explode("README"), readme(version))

        for ((_, platform) <- extracted) {
          Isabelle_System.bash("mv " +
            File.bash_path(dir + Path.explode(platform.name)) + " " +
            File.bash_path(component_dir)).check
        }

        Isabelle_System.bash(cwd = component_dir.file,
          script = """
            chmod -R a+r . &&
            chmod -R a+X . &&
            find x86_64-darwin -name "._*" -exec rm -f {} ";"
          """).check

        progress.echo("Sharing ...")
        Isabelle_System.bash(cwd = component_dir.file,
          script = """
            cd x86-linux
            for FILE in $(find . -type f)
            do
              for OTHER in \
                "../x86_64-linux/$FILE" \
                "../x86-windows/$FILE" \
                "../x86_64-windows/$FILE" \
                "../x86_64-darwin/Contents/Home/$FILE"
              do
                if cmp -s "$FILE" "$OTHER"
                then
                  ln -f "$FILE" "$OTHER"
                fi
              done
            done
          """).check

        progress.echo("Archiving ...")
        Isabelle_System.bash("tar -C " + File.bash_path(dir) + " -czf " +
          File.bash_path(target_dir + jdk_path.ext("tar.gz")) + " " + jdk_name).check
      })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_jdk", "build Isabelle jdk component from original platform installations",
    args =>
    {
      var target_dir = Path.current

      val getopts = Getopts("""
Usage: Admin/build_jdk [OPTIONS] ARCHIVES...

  Options are:
    -D DIR       target directory (default ".")

  Build jdk component from tar.gz archives, with original jdk installations
  for Linux (x86, x86_64), Windows (x86, x86_64), Mac OS X (x86_64).
""",
        "D:" -> (arg => target_dir = Path.explode(arg)))

      val more_args = getopts(args)
      if (more_args.isEmpty) getopts.usage()

      val archives = more_args.map(Path.explode(_))
      val progress = new Console_Progress()

      build_jdk(archives = archives, progress = progress, target_dir = target_dir)
    }, admin = true)
}
