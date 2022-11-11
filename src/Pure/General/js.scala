/*  Title:      Pure/General/json.scala
    Author:     Makarius

Support for JavaScript syntax.
*/

package isabelle


object JS {
  /* basic syntax */

  type Source = String

  def arguments(args: Source*): Source = args.mkString("(", ", ", ")")
  def function(f: Source, args: Source*): Source = f + arguments(args: _*)
  def selection(a: Source, arg: Source): Source = a + "[" + arg + "]"

  def commands(args: Source*): Source = args.mkString("; ")
  def command_list(args: List[Source]): Source = args.mkString("; ")


  /* JSON values */

  def value(t: JSON.T): Source = JSON.Format(t)
  def string(s: String): Source = value(s)

  def json_parse(arg: Source): Source = function("JSON.parse", arg)
  def json_print(arg: Source): Source = function("JSON.stringify", arg)


  /* file-system operations */

  def standard_path(p: Path, dir: Boolean = false): Source =
    string(File.standard_path(p) + (if (dir) "/" else ""))

  def platform_path(p: Path, dir: Boolean = false): Source =
    string(File.platform_path(p) + (if (dir) File.platform_path(Path.root) else ""))
}
