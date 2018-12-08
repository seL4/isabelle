/*  Title:      Pure/Admin/components.scala
    Author:     Makarius

Isabelle system components.
*/

package isabelle


import java.io.{File => JFile}


object Components
{
  /* archive name */

  object Archive
  {
    val suffix: String = ".tar.gz"
    def apply(name: String): String = name + suffix
    def unapply(archive: String): Option[String] = Library.try_unsuffix(suffix, archive)
    def get_name(archive: String): String =
      unapply(archive) getOrElse
        error("Bad component archive name (expecting .tar.gz): " + quote(archive))
  }


  /* component collections */

  def admin(dir: Path): Path = dir + Path.explode("Admin/components")

  def contrib(dir: Path = Path.current, name: String = ""): Path =
    dir + Path.explode("contrib") + Path.explode(name)

  def unpack(dir: Path, archive: Path, progress: Progress = No_Progress): String =
  {
    val name = Archive.get_name(archive.file_name)
    progress.echo("Unpacking " + name)
    Isabelle_System.gnutar("-xzf " + File.bash_path(archive), dir = dir).check
    name
  }

  def resolve(base_dir: Path, names: List[String],
    target_dir: Option[Path] = None,
    progress: Progress = No_Progress)
  {
    Isabelle_System.mkdirs(base_dir)
    for (name <- names) {
      val archive_name = Archive(name)
      val archive = base_dir + Path.explode(archive_name)
      if (!archive.is_file) {
        val remote = Isabelle_System.getenv("ISABELLE_COMPONENT_REPOSITORY") + "/" + archive_name
        progress.echo("Getting " + remote)
        Bytes.write(archive, Url.read_bytes(Url(remote)))
      }
      unpack(target_dir getOrElse base_dir, archive, progress = progress)
    }
  }

  def purge(dir: Path, platform: Platform.Family.Value)
  {
    def purge_platforms(platforms: String*): Set[String] =
      platforms.flatMap(name => List("x86-" + name, "x86_64-" + name)).toSet + "ppc-darwin"
    val purge_set =
      platform match {
        case Platform.Family.linux => purge_platforms("darwin", "cygwin", "windows")
        case Platform.Family.macos => purge_platforms("linux", "cygwin", "windows")
        case Platform.Family.windows => purge_platforms("linux", "darwin")
      }

    File.find_files(dir.file,
      (file: JFile) => file.isDirectory && purge_set(file.getName),
      include_dirs = true).foreach(Isabelle_System.rm_tree)
  }


  /* component directory content */

  def settings(dir: Path): Path = dir + Path.explode("etc/settings")
  def components(dir: Path): Path = dir + Path.explode("etc/components")

  def check_dir(dir: Path): Boolean =
    settings(dir).is_file || components(dir).is_file

  def read_components(dir: Path): List[String] =
    split_lines(File.read(components(dir))).filter(_.nonEmpty)

  def write_components(dir: Path, lines: List[String]): Unit =
    File.write(components(dir), terminate_lines(lines))
}
