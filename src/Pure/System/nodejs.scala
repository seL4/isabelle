/*  Title:      Pure/System/nodejs.scala
    Author:     Makarius

Support for the Node.js platform, as provided by Isabelle/VSCodium component.

See also: https://nodejs.org/docs/latest-v16.x
*/

package isabelle


object Nodejs {
  /* require modules */

  def require_module(name: JS.Source, module: JS.Source): JS.Source =
    "const " + name + " = require(" + module + ")"

  def require_builtin(name: JS.Source): JS.Source =
    require_module(name, JS.string(name))

  def require_path(name: JS.Source, path: Path, dir: Boolean = false): JS.Source =
    require_module(name, JS.platform_path(path, dir = dir))


  /* file-system operations */

  def require_fs: JS.Source = require_builtin("fs")

  val encoding_utf8: JSON.T = JSON.Object("encoding" -> "utf8")

  def read_file(path: Path): JS.Source =
    JS.function("fs.readFileSync", JS.platform_path(path), JS.value(encoding_utf8))

  def write_file(path: Path, arg: JS.Source): JS.Source =
    JS.function("fs.writeFileSync", JS.platform_path(path), arg, JS.value(encoding_utf8))


  /* external process */

  def execute(js: String): Process_Result =
    Isabelle_System.bash("isabelle node -", input = js,
      description = "Node.js").check
}
