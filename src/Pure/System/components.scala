/*  Title:      Pure/Admin/components.scala
    Author:     Makarius

Isabelle system components.
*/

package isabelle


import java.io.{File => JFile}


object Components
{
  /* component collections */

  def admin(dir: Path): Path = dir + Path.explode("Admin/components")

  def contrib(dir: Path = Path.current, name: String = ""): Path =
    dir + Path.explode("contrib") + Path.explode(name)

  def resolve(base_dir: Path, names: List[String],
    target_dir: Option[Path] = None,
    progress: Progress = No_Progress)
  {
    Isabelle_System.mkdirs(base_dir)
    for (name <- names) {
      val archive_name = name + ".tar.gz"
      val archive = base_dir + Path.explode(archive_name)
      if (!archive.is_file) {
        val remote = Isabelle_System.getenv("ISABELLE_COMPONENT_REPOSITORY") + "/" + archive_name
        progress.echo("Getting " + remote)
        Bytes.write(archive, Url.read_bytes(Url(remote)))
      }
      progress.echo("Unpacking " + archive_name)
      Isabelle_System.gnutar(
        "-C " + File.bash_path(target_dir getOrElse base_dir) +
        " -xzf " + File.bash_path(archive)).check
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
