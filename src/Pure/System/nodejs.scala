/*  Title:      Pure/System/nodejs.scala
    Author:     Makarius

Support for the Node.js platform, in conjunction with Isabelle/VSCodium.

See also: https://nodejs.org/docs/latest-v22.x/api/index.html
*/

package isabelle


object Nodejs {
  /** independent installation **/

  val default_version = "22.17.0"

  def context(
    platform_context: Isabelle_Platform.Context = Isabelle_Platform.Context(),
    version: String = default_version
  ): Context = new Context(platform_context, version)

  def setup(
    base_dir: Path,
    platform_context: Isabelle_Platform.Context = Isabelle_Platform.Context(),
    version: String = default_version,
    packages: List[String] = Nil
  ): Directory = {
    context(platform_context = platform_context, version = version)
      .setup(base_dir, packages = packages)
  }

  class Context private[Nodejs](val platform_context: Isabelle_Platform.Context, version: String) {
    def platform: Isabelle_Platform = platform_context.isabelle_platform
    def progress: Progress = platform_context.progress

    override def toString: String =
      "node-" + version + "-" + platform.ISABELLE_PLATFORM(windows = true, apple = true)

    def arch: String = if (platform.is_arm) "arm64" else "x64"

    def platform_name: String =
      if (platform.is_windows) "win" else if (platform.is_macos) "darwin" else "linux"

    def full_name: String = "node-v" + version + "-" + platform_name + "-" + arch

    def download_ext: String = if (platform.is_windows) "zip" else "tar.gz"

    def download_url: String =
      "https://nodejs.org/dist/v" + version + "/" + full_name + "." + download_ext

    def setup(base_dir: Path, packages: List[String] = Nil): Directory = {
      Isabelle_System.with_tmp_file("node", ext = download_ext) { archive =>
        progress.echo("Getting Node.js ...")
        Isabelle_System.download_file(download_url, archive)

        progress.echo("Installing node ...")
        Isabelle_System.extract(archive, base_dir)
        val node_dir = new Directory(this, base_dir + Path.basic(full_name))

        for (name <- packages) node_dir.install(name)

        node_dir
      }
    }
  }

  class Directory private[Nodejs](val context: Context, val path: Path) {
    override def toString: String = path.toString

    def platform_context: Isabelle_Platform.Context = context.platform_context
    def progress: Progress = context.progress

    def bin_dir: Path =
      if (platform_context.isabelle_platform.is_windows) path
      else path + Path.basic("bin")

    def path_setup: String =
      "export PATH=" + Bash.string(platform_context.standard_path(bin_dir)) + """:"$PATH""""

    def install(name: String): Unit = {
      progress.echo("Installing " + name + " ...")
      Isabelle_System.bash(path_setup + "\nnpm install -g " + Bash.string(name), cwd = path).check
    }
  }



  /** source snippets **/

  /* require modules */

  def require_module(name: JS.Source, module: JS.Source): JS.Source =
    name + " = require(" + module + ")"

  def require_path(name: JS.Source, path: Path, dir: Boolean = false): JS.Source =
    require_module(name, JS.platform_path(path, dir = dir))

  def require_builtin(name: String): JS.Source =
    require_module("const " + name, JS.string(name))


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
