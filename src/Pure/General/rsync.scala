/*  Title:      Pure/General/rsync.scala
    Author:     Makarius

Support for rsync: see also https://rsync.samba.org
*/

package isabelle


object Rsync {
  sealed case class Context(progress: Progress, port: Int = SSH.default_port) {
    def command: String =
      "rsync --protect-args --archive --rsh=" + Bash.string("ssh -p " + port)
  }

  def rsync(
    context: Context,
    verbose: Boolean = false,
    thorough: Boolean = false,
    prune_empty_dirs: Boolean = false,
    dry_run: Boolean = false,
    clean: Boolean = false,
    list: Boolean = false,
    filter: List[String] = Nil,
    args: List[String] = Nil
  ): Process_Result = {
    val script =
      context.command +
        (if (verbose) " --verbose" else "") +
        (if (thorough) " --ignore-times" else " --omit-dir-times") +
        (if (prune_empty_dirs) " --prune-empty-dirs" else "") +
        (if (dry_run) " --dry-run" else "") +
        (if (clean) " --delete-excluded" else "") +
        (if (list) " --list-only --no-human-readable" else "") +
        filter.map(s => " --filter=" + Bash.string(s)).mkString +
        (if (args.nonEmpty) " " + Bash.strings(args) else "")
    context.progress.bash(script, echo = true)
  }

  def rsync_init(context: Context, target: String,
    contents: List[File.Content] = Nil
  ): Unit =
    Isabelle_System.with_tmp_dir("sync") { tmp_dir =>
      val init_dir = Isabelle_System.make_directory(tmp_dir + Path.explode("init"))
      contents.foreach(_.write(init_dir))
      rsync(context, thorough = true,
        args = List(File.bash_path(init_dir) + "/.", target)).check
    }

  def terminate(target: String): String =
    if (target.endsWith(":") || target.endsWith("/")) target + "."
    else if (target.endsWith(":.") || target.endsWith("/.")) target
    else target + "/."

  def append(target: String, rest: String): String =
    if (target.endsWith(":") || target.endsWith("/")) target + rest
    else target + "/" + rest
}
