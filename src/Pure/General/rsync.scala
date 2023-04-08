/*  Title:      Pure/General/rsync.scala
    Author:     Makarius

Support for rsync: see also https://rsync.samba.org
*/

package isabelle


object Rsync {
  sealed case class Context(progress: Progress,
    ssh: SSH.System = SSH.Local,
    archive: Boolean = true,
    protect_args: Boolean = true  // requires rsync 3.0.0, or later
  ) {
    def command: String = {
      val ssh_command = ssh.client_command
      "rsync" +
        if_proper(ssh_command, " --rsh=" + Bash.string(ssh_command)) +
        (if (archive) " --archive" else "") +
        (if (protect_args) " --protect-args" else "")
    }

    def target(path: Path, direct: Boolean = false): String = {
      val s = ssh.rsync_path(path)
      if (direct) Url.direct_path(s) else s
    }
  }

  def exec(
    context: Context,
    thorough: Boolean = false,
    prune_empty_dirs: Boolean = false,
    dry_run: Boolean = false,
    clean: Boolean = false,
    list: Boolean = false,
    filter: List[String] = Nil,
    args: List[String] = Nil
  ): Process_Result = {
    val progress = context.progress
    val script =
      context.command +
        (if (progress.verbose) " --verbose" else "") +
        (if (thorough) " --ignore-times" else " --omit-dir-times") +
        (if (prune_empty_dirs) " --prune-empty-dirs" else "") +
        (if (dry_run) " --dry-run" else "") +
        (if (clean) " --delete-excluded" else "") +
        (if (list) " --list-only --no-human-readable" else "") +
        filter.map(s => " --filter=" + Bash.string(s)).mkString +
        if_proper(args, " " + Bash.strings(args))
    progress.bash(script, echo = true)
  }

  def init(context: Context, target: Path,
    contents: List[File.Content] = Nil
  ): Unit =
    Isabelle_System.with_tmp_dir("sync") { tmp_dir =>
      val init_dir = Isabelle_System.make_directory(tmp_dir + Path.explode("init"))
      contents.foreach(_.write(init_dir))
      exec(context.copy(archive = false),
        thorough = true,
        args =
          List(if (contents.nonEmpty) "--archive" else "--dirs",
            File.bash_path(init_dir) + "/.", context.target(target))).check
    }
}
