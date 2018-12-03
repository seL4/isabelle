/*  Title:      Pure/Admin/components.scala
    Author:     Makarius

Isabelle system components.
*/

package isabelle


object Components
{
  /* component collections */

  def admin(dir: Path): Path = dir + Path.explode("Admin/components")

  def contrib(dir: Path = Path.current, name: String = ""): Path =
    dir + Path.explode("contrib") + Path.explode(name)


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
