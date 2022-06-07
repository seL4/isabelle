/*  Title:      Pure/General/rsync.scala
    Author:     Makarius

Support for rsync: see also https://rsync.samba.org
*/

package isabelle


object Rsync {
  def rsync(
    progress: Progress = new Progress,
    port: Int = SSH.default_port,
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
      "rsync --protect-args --archive --rsh=" + Bash.string("ssh -p " + port) +
        (if (verbose) " --verbose" else "") +
        (if (thorough) " --ignore-times" else " --omit-dir-times") +
        (if (prune_empty_dirs) " --prune-empty-dirs" else "") +
        (if (dry_run) " --dry-run" else "") +
        (if (clean) " --delete-excluded" else "") +
        (if (list) " --list-only --no-human-readable" else "") +
        filter.map(s => " --filter=" + Bash.string(s)).mkString +
        (if (args.nonEmpty) " " + Bash.strings(args) else "")
    progress.bash(script, echo = true)
  }

  def rsync_init(target: String,
    port: Int = SSH.default_port,
    contents: List[File.Content] = Nil
  ): Unit =
    Isabelle_System.with_tmp_dir("sync") { tmp_dir =>
      val init_dir = Isabelle_System.make_directory(tmp_dir + Path.explode("init"))
      contents.foreach(_.write(init_dir))
      rsync(port = port, thorough = true,
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
