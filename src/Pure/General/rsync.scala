/*  Title:      Pure/General/rsync.scala
    Author:     Makarius

Support for rsync: see also https://rsync.samba.org
*/

package isabelle


object Rsync {
  sealed case class Context(progress: Progress,
    ssh_port: Int = 0,
    ssh_control_path: String = "",
    archive: Boolean = true,
    protect_args: Boolean = true  // requires rsync 3.0.0, or later
  ) {
    def command: String = {
      val ssh_command = SSH.client_command(port = ssh_port, control_path = ssh_control_path)
      "rsync --rsh=" + Bash.string(ssh_command) +
        (if (archive) " --archive" else "") +
        (if (protect_args) " --protect-args" else "")
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

  def init(context: Context, target: String,
    contents: List[File.Content] = Nil
  ): Unit =
    Isabelle_System.with_tmp_dir("sync") { tmp_dir =>
      val init_dir = Isabelle_System.make_directory(tmp_dir + Path.explode("init"))
      contents.foreach(_.write(init_dir))
      exec(context.copy(archive = false),
        thorough = true,
        args =
          List(if (contents.nonEmpty) "--archive" else "--dirs",
            File.bash_path(init_dir) + "/.", target)).check
    }
}
